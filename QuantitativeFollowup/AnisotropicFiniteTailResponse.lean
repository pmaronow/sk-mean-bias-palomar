module
public import QuantitativeFollowup.AnisotropicWhitening

@[expose] public section

/-! Actual finite anisotropic tail gradients at every restart time, including
atoms and zero-length cells. All measurability and uniform spatial bounds are
derived from the genuine clamped Gaussian cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal ContDiff Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 800000

def anisotropicFiniteTailPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) : AnisotropicParameter n→ℝ := anisotropicTailRecursion D s q (k+2)

theorem contDiff_anisotropicFiniteTailPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) : ContDiff ℝ ∞ (anisotropicFiniteTailPotential D s q) := by
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact contDiff_anisotropicFinitePotential D _ _

def anisotropicFiniteTailMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) : Field n :=
  anisotropicResponseMap n (fderiv ℝ (anisotropicFiniteTailPotential D s q) P)

theorem anisotropicFiniteTailMagnetization_clamped (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) :
    anisotropicFiniteTailMagnetization D s q P=
      anisotropicMagnetization D (vectorClampedScheme s q q.property) (k+2) P := by
  unfold anisotropicFiniteTailMagnetization anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  rfl

theorem anisotropicFiniteTailMagnetization_component_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    |anisotropicFiniteTailMagnetization D s q P i|≤1 := by
  rw [anisotropicFiniteTailMagnetization_clamped]
  exact anisotropicMagnetization_component_bound D _ _ _ _

theorem norm_anisotropicFiniteTailMagnetization_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖anisotropicFiniteTailMagnetization D s q P‖≤Real.sqrt (n : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    _≤∑_ : Fin n,(1 : ℝ) := Finset.sum_le_sum fun i _=>by
      simpa only [Real.norm_eq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _)
        (anisotropicFiniteTailMagnetization_component_bound D s q P i) 2
    _=_ := by simp

theorem anisotropicFiniteTailDifferential_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) :
    LipschitzWith (‖anisotropicEnergyMap D‖₊^2) (fderiv ℝ (anisotropicFiniteTailPotential D s q)) := by
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact anisotropicFinitePotential_fderiv_lipschitz D _ _

theorem anisotropicFiniteTailMagnetization_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) :
    LipschitzWith (‖anisotropicResponseMap n‖₊*‖anisotropicEnergyMap D‖₊^2)
      (anisotropicFiniteTailMagnetization D s q) :=
  (anisotropicResponseMap n).lipschitzWith.comp (anisotropicFiniteTailDifferential_lipschitz D s q)

theorem measurable_anisotropicFiniteTailMagnetization (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : Measurable (fun z : Paper.Overlap×AnisotropicParameter n=>
      anisotropicFiniteTailMagnetization D s z.1 z.2) := by
  have hp : Measurable (fun z : Paper.Overlap×AnisotropicParameter n=>anisotropicFiniteTailPotential D s z.1 z.2) := by
    change Measurable (fun z : Paper.Overlap×AnisotropicParameter n=>anisotropicTailRecursion D s z.1 (k+2) z.2)
    simpa only [Function.comp_def] using
      (measurable_anisotropicTailRecursion_parameter D s (k+2)).comp
        (show Measurable (fun z : Paper.Overlap×AnisotropicParameter n=>((z.1 : ℝ),z.2)) from
          (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  let h := fun j : ℕ=>(1 : ℝ)/((j : ℝ)+1)
  have hpos (j : ℕ) : 0<h j := by dsimp only [h];positivity
  have hlim : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hpos⟩
  let Q := fun j : ℕ=>fun z : Paper.Overlap×AnisotropicParameter n=>
    (h j)⁻¹*(anisotropicFiniteTailPotential D s z.1 (z.2+h j • anisotropicCoordinateDirection n i)-
      anisotropicFiniteTailPotential D s z.1 z.2)
  have hQ (j : ℕ) : Measurable (Q j) :=
    measurable_const.mul ((hp.comp (show Measurable (fun z : Paper.Overlap×AnisotropicParameter n=>
      (z.1,z.2+h j • anisotropicCoordinateDirection n i)) from by fun_prop)).sub hp)
  apply measurable_of_tendsto_metrizable hQ
  apply tendsto_pi_nhds.mpr
  intro z
  have hd : HasDerivAt (fun r : ℝ=>anisotropicFiniteTailPotential D s z.1
      (z.2+r • anisotropicCoordinateDirection n i))
      (fderiv ℝ (anisotropicFiniteTailPotential D s z.1) z.2 (anisotropicCoordinateDirection n i)) 0 := by
    simpa only [zero_smul,add_zero] using hasDerivAt_affine_line_of_differentiable _
      ((contDiff_anisotropicFiniteTailPotential D s z.1).differentiable (by simp)) z.2
      (anisotropicCoordinateDirection n i) 0
  simpa only [Q,zero_smul,add_zero,zero_add,smul_eq_mul,Function.comp_def] using
    hd.tendsto_slope_zero_right.comp hlim

theorem tendstoUniformly_anisotropicFiniteDyadicTailMagnetization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j=>fun z : Paper.Overlap×AnisotropicParameter n=>
      anisotropicFiniteTailMagnetization D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) z.1 z.2)
      (fun z=>anisotropicMeasureTailMagnetization D μ z.1 z.2) atTop :=
  tendstoUniformly_anisotropicDyadicTailResponse D μ

end QuantitativeFollowup
