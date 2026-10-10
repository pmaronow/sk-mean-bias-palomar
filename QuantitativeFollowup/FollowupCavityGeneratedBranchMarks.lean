module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkCubic
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingApproximation

@[expose] public section

/-! The literal native branch weight is an atom attachment plus inherited
CDF copies. Its marginal budget is proved by the explicit program; it is
not imposed as a domination premise. Equal-time clusters use one arity. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 900000
variable {m : ℕ}

def cavityGeneratedBranchWeight (μ : Paper.ParisiMeasure) (i : Fin m) (l : ℕ)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ≥0∞ :=
  ((l - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Paper.parisiCDF μ (h i))

theorem cavityGeneratedBranchWeight_le (μ : Paper.ParisiMeasure) (i : Fin m) (l : ℕ)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedBranchWeight μ i l h ≤ ((l - 1 : ℕ) : ℝ≥0∞) := by
  have hc : ENNReal.ofReal (Paper.parisiCDF μ (h i)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ (h i))
  simpa only [cavityGeneratedBranchWeight, mul_one] using
    mul_le_mul_right hc ((l - 1 : ℕ) : ℝ≥0∞)

theorem cavityGeneratedBranchWeight_measurable (μ : Paper.ParisiMeasure)
    (i : Fin m) (l : ℕ) : Measurable (cavityGeneratedBranchWeight μ i l) := by
  exact ((Paper.parisiCDF_measurable μ).comp
    (measurable_subtype_coe.comp (measurable_pi_apply i))).ennreal_ofReal.const_mul _

def cavityGeneratedBranchMarkProgram (μ : Paper.ParisiMeasure)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (i : Fin m) (l : ℕ) :
    CavityGeneratedMarkProgram Paper.Overlap (m + 1) :=
  .add (.atom P (fun h => h i) (measurable_pi_apply i))
    (.inherited P i (l - 1) (cavityGeneratedBranchWeight μ i l)
      (cavityGeneratedBranchWeight_le μ i l))

theorem cavityGeneratedBranchMarkProgram_budget (μ : Paper.ParisiMeasure)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (i : Fin m)
    (l : ℕ) (hl : 1 ≤ l) :
    (cavityGeneratedBranchMarkProgram μ P i l).budget = l * P.budget := by
  simp only [cavityGeneratedBranchMarkProgram, CavityGeneratedMarkProgram.budget]
  calc
    P.budget + (l - 1) * P.budget = (1 + (l - 1)) * P.budget := by
      rw [Nat.add_mul, Nat.one_mul]
    _ = l * P.budget := by congr 1; omega

theorem cavityGeneratedBranchMarkProgram_measure (μ : Paper.ParisiMeasure)
    (a : ℝ) (P : CavityGeneratedMarkProgram Paper.Overlap m) (i : Fin m) (l : ℕ) :
    (cavityGeneratedBranchMarkProgram μ P i l).measure (parisiFreeMeasure μ a) =
      ((P.measure (parisiFreeMeasure μ a)).withDensity (fun h =>
        parisiFreeMeasure μ a {h i} + cavityGeneratedBranchWeight μ i l h)).map
          (fun h : CavityGeneratedHistory Paper.Overlap m =>
            (Fin.snoc h (h i) : CavityGeneratedHistory Paper.Overlap (m+1))) := by
  have hm : Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      (Fin.snoc h (h i) : CavityGeneratedHistory Paper.Overlap (m+1))) := by
    simpa only [Function.comp_def, cavityGeneratedHistoryAppend, id_eq] using
      cavityGeneratedHistoryAppend_measurable.comp
        (measurable_id.prodMk (measurable_pi_apply i))
  change ((P.measure (parisiFreeMeasure μ a)).withDensity (fun h => parisiFreeMeasure μ a {h i})).map _ +
    ((P.measure (parisiFreeMeasure μ a)).withDensity (cavityGeneratedBranchWeight μ i l)).map _ = _
  rw [show (fun h : CavityGeneratedHistory Paper.Overlap m =>
    parisiFreeMeasure μ a {h i} + cavityGeneratedBranchWeight μ i l h) =
      (fun h => parisiFreeMeasure μ a {h i}) + cavityGeneratedBranchWeight μ i l from rfl,
    withDensity_add_right _ (cavityGeneratedBranchWeight_measurable μ i l),
    Measure.map_add _ _ hm]

theorem cavityGeneratedBranchWeight_eq_native (μ : Paper.ParisiMeasure)
    (a : ℝ) (i : Fin m) (l : ℕ) (hl : 1 ≤ l)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    parisiFreeMeasure μ a {h i} + cavityGeneratedBranchWeight μ i l h =
      ENNReal.ofReal (nativeStreamingBranchCharge μ a (h i) l) := by
  have hlr : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hp : (0 : ℝ) ≤ ((l : ℝ) - 1) := by linarith
  have he : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hl)
  rw [nativeStreamingBranchCharge, ENNReal.ofReal_add measureReal_nonneg
    (mul_nonneg hp (Paper.parisiCDF_nonneg μ _)), ENNReal.ofReal_mul hp,
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  dsimp only [cavityGeneratedBranchWeight]
  rw [← he, ENNReal.ofReal_natCast]

end QuantitativeFollowup
