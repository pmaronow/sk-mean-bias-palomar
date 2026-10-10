module
public import QuantitativeFollowup.FollowupCavityGeneratedForestContinuity
public import QuantitativeFollowup.FollowupCavityGeneratedMarkCubic
public import QuantitativeFollowup.FollowupCavityOriginalPairDefect
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! An actual independent-tree three-defect moment integrated against a
generated mark program. Exact ancestral labels are structural inputs;
the mark marginal and cubic bounds are derived inside the theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ} {I : Type*} [Fintype I]
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGenerated_observationCommonLevel_le {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b e : ObservationLeaf T) :
    observationCommonLevel T b e ≤ j := by
  induction T with
  | leaf => exact le_refl 0
  | advance T ih => exact (ih b e).trans (Nat.le_succ _)
  | fork T U ihT ihU =>
      cases b with
      | inl b => cases e with
        | inl e => exact ihT b e
        | inr e => exact le_refl _
      | inr b => cases e with
        | inl e => exact le_refl _
        | inr e => exact ihU b e

def cavityGeneratedForestThreeDefectTest (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r)))
    (σ : CavityGeneratedForestTerminalSample (n:=n) J T) : ℝ :=
  |cavitySpinOverlapDefect n (q (c 0) (observationCommonLevel (T (c 0)) (b 0) (e 0)))
      (observationTerminalSpin (T (c 0)) (b 0) (σ (c 0)))
      (observationTerminalSpin (T (c 0)) (e 0) (σ (c 0))) *
    cavitySpinOverlapDefect n (q (c 1) (observationCommonLevel (T (c 1)) (b 1) (e 1)))
      (observationTerminalSpin (T (c 1)) (b 1) (σ (c 1)))
      (observationTerminalSpin (T (c 1)) (e 1) (σ (c 1))) *
    cavitySpinOverlapDefect n (q (c 2) (observationCommonLevel (T (c 2)) (b 2) (e 2)))
      (observationTerminalSpin (T (c 2)) (b 2) (σ (c 2)))
      (observationTerminalSpin (T (c 2)) (e 2) (σ (c 2)))|

def cavityGeneratedForestThreeDefectMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) : ℝ :=
  ∫ σ, cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q :
      Measure (CavityGeneratedForestTerminalSample (n:=n) J T))

theorem cavityGeneratedForestThreeDefectMoment_bounds (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) :
    cavityGeneratedForestThreeDefectMoment D μ a J T q c b e ∈ Icc (0:ℝ) 8 := by
  constructor
  · unfold cavityGeneratedForestThreeDefectMoment
    exact integral_nonneg fun σ =>
      (show 0 ≤ cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e σ from abs_nonneg _)
  · have hb (σ : CavityGeneratedForestTerminalSample (n:=n) J T) :
        cavityGeneratedForestThreeDefectTest J T q c b e σ ≤ 8 := by
      have hpair (r : Fin 3) := cavitySpinOverlapDefect_abs_le_two n
        (q (c r) (observationCommonLevel (T (c r)) (b r) (e r)))
        (q (c r) (observationCommonLevel (T (c r)) (b r) (e r))).property
        (observationTerminalSpin (T (c r)) (b r) (σ (c r)))
        (observationTerminalSpin (T (c r)) (e r) (σ (c r)))
      dsimp only [cavityGeneratedForestThreeDefectTest]
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul (hpair 0) (hpair 1) (abs_nonneg _) (by norm_num))
        (hpair 2) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hi : Integrable (cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e)
        (cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _) :=
      (integrable_const (8:ℝ)).mono' (measurable_of_finite _).aestronglyMeasurable
        (.of_forall fun σ => by
          rw [Real.norm_of_nonneg (show 0 ≤ cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e σ from abs_nonneg _)]
          exact hb σ)
    exact (integral_mono hi (integrable_const (8:ℝ)) hb).trans_eq (by simp)

theorem cavityGeneratedForestThreeDefectMoment_le (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hzero : ∀i, q i 0 = 1) (hroot : ∀i, q i (J i) = 0)
    (hq : ∀i l, l < J i → q i (l+1) ≤ q i l)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r)))
    (hbe : ∀r, b r ≠ e r) :
    cavityGeneratedForestThreeDefectMoment D μ a J T q c b e ≤
      (cavityCubicPairMoment D μ a (q (c 0) (observationCommonLevel (T (c 0)) (b 0) (e 0))) +
        cavityCubicPairMoment D μ a (q (c 1) (observationCommonLevel (T (c 1)) (b 1) (e 1))) +
        cavityCubicPairMoment D μ a (q (c 2) (observationCommonLevel (T (c 2)) (b 2) (e 2)))) / 3 := by
  rw [cavityGeneratedForestThreeDefectMoment,
    ←cavityGeneratedNativeForest_integral_terminal D μ a J T q]
  simpa only [cavityGeneratedForestThreeDefectTest, cavityGeneratedForestTerminalProjection,
    observationTerminalSpin_record] using
    cavityGeneratedNativeForest_three_defects_le D μ a J T q hzero hroot hq c b e hbe

theorem cavityGeneratedForestThreeDefectMoment_eq_zero_of_same (hn : 0 < n)
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hzero : ∀i, q i 0 = 1) (c : Fin 3 → I)
    (b e : (r : Fin 3) → ObservationLeaf (T (c r))) (r : Fin 3) (hr : b r = e r) :
    cavityGeneratedForestThreeDefectMoment D μ a J T q c b e = 0 := by
  have ht : cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e = 0 := by
    funext σ
    let delta (j : Fin 3) := cavitySpinOverlapDefect n
      (q (c j) (observationCommonLevel (T (c j)) (b j) (e j)))
      (observationTerminalSpin (T (c j)) (b j) (σ (c j)))
      (observationTerminalSpin (T (c j)) (e j) (σ (c j)))
    have hd : delta r = 0 := by
      dsimp only [delta]
      rw [←hr, observationCommonLevel_self, hzero]
      exact cavitySpinOverlapDefect_self n hn _
    change |delta 0 * delta 1 * delta 2| = 0
    fin_cases r
    · change delta 0 = 0 at hd
      simp only [hd, zero_mul, abs_zero]
    · change delta 1 = 0 at hd
      simp only [hd, mul_zero, zero_mul, abs_zero]
    · change delta 2 = 0 at hd
      simp only [hd, mul_zero, abs_zero]
  simp only [cavityGeneratedForestThreeDefectMoment, ht, Pi.zero_apply, integral_zero]

theorem continuous_cavityGeneratedForestThreeDefectMoment_family
    {H : Type*} [TopologicalSpace H] [FirstCountableTopology H]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : H → I → ℕ → Paper.Overlap)
    (hcts : ∀i p, p ≤ J i → Continuous (fun h => q h i p))
    (hmono : ∀h i p, p < J i → q h i (p+1) ≤ q h i p)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) :
    Continuous (fun h => cavityGeneratedForestThreeDefectMoment D μ a J T (q h) c b e) := by
  let f : H × CavityGeneratedForestTerminalSample (n:=n) J T → ℝ :=
    fun z => cavityGeneratedForestThreeDefectTest J T (q z.1) c b e z.2
  have hpair (r : Fin 3) : Continuous (fun z : H × CavityGeneratedForestTerminalSample (n:=n) J T =>
      cavitySpinOverlapDefect n (q z.1 (c r) (observationCommonLevel (T (c r)) (b r) (e r)))
        (observationTerminalSpin (T (c r)) (b r) (z.2 (c r)))
        (observationTerminalSpin (T (c r)) (e r) (z.2 (c r)))) := by
    have hs : Continuous (fun z : H × CavityGeneratedForestTerminalSample (n:=n) J T =>
        (observationTerminalSpin (T (c r)) (b r) (z.2 (c r)),
          observationTerminalSpin (T (c r)) (e r) (z.2 (c r)))) :=
      (continuous_of_discreteTopology (f:=fun σ : CavityGeneratedForestTerminalSample (n:=n) J T =>
        (observationTerminalSpin (T (c r)) (b r) (σ (c r)),
          observationTerminalSpin (T (c r)) (e r) (σ (c r))))).comp continuous_snd
    have hr := (continuous_of_discreteTopology (f:=fun z : Configuration (n+1) × Configuration (n+1) =>
      cavityRestOverlap n z.1 z.2)).comp hs
    have he := (continuous_of_discreteTopology (f:=fun z : Configuration (n+1) × Configuration (n+1) =>
      Paper.spinSign (z.1 (Fin.last n)) * Paper.spinSign (z.2 (Fin.last n)))).comp hs
    have ht : Continuous (fun z : H × CavityGeneratedForestTerminalSample (n:=n) J T =>
        (q z.1 (c r) (observationCommonLevel (T (c r)) (b r) (e r)) : ℝ)) :=
      (continuous_subtype_val : Continuous (fun x : Paper.Overlap => (x:ℝ))).comp
      ((hcts (c r) _ (cavityGenerated_observationCommonLevel_le _ _ _)).comp continuous_fst)
    convert he.mul (hr.sub ht) using 1
    funext z
    exact cavitySpinOverlapDefect_eq n _ _ _
  have hf : Continuous f := ((hpair 0).mul (hpair 1) |>.mul (hpair 2)).abs
  simpa only [cavityGeneratedForestThreeDefectMoment, f] using
    continuous_integral_probability_family f hf _
      (continuous_cavityGeneratedNativeForestTerminalProbability_family D μ a J T q hcts hmono)

theorem cavityGeneratedForest_three_defects_integrable
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : CavityGeneratedHistory Paper.Overlap m → I → ℕ → Paper.Overlap)
    (hcts : ∀i p, p ≤ J i → Continuous (fun h => q h i p))
    (hmono : ∀h i p, p < J i → q h i (p+1) ≤ q h i p)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) :
    Integrable (fun h => cavityGeneratedForestThreeDefectMoment D μ a J T (q h) c b e)
      (P.measure (parisiFreeMeasure μ a)) := by
  haveI := P.isFiniteMeasure_measure _ (cavityGenerated_free_mass_le_one μ a ha)
  apply (integrable_const (8:ℝ)).mono'
    (continuous_cavityGeneratedForestThreeDefectMoment_family D μ a J T q hcts hmono c b e).measurable.aestronglyMeasurable
  exact .of_forall fun h => by
    rw [Real.norm_of_nonneg (cavityGeneratedForestThreeDefectMoment_bounds D μ a J T (q h) c b e).1]
    exact (cavityGeneratedForestThreeDefectMoment_bounds D μ a J T (q h) c b e).2

theorem cavityGeneratedForest_three_defects_integral_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : CavityGeneratedHistory Paper.Overlap m → I → ℕ → Paper.Overlap)
    (hcts : ∀i p, p ≤ J i → Continuous (fun h => q h i p))
    (hzero : ∀h i, q h i 0 = 1) (hroot : ∀h i, q h i (J i) = 0)
    (hmono : ∀h i p, p < J i → q h i (p+1) ≤ q h i p)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r)))
    (hbe : ∀r, b r ≠ e r)
    (hlabels : ∀ᵐ h ∂P.measure (parisiFreeMeasure μ a), ∀r : Fin 3, ∃i : Fin m,
      q h (c r) (observationCommonLevel (T (c r)) (b r) (e r)) = h i) :
    (∫ h, cavityGeneratedForestThreeDefectMoment D μ a J T (q h) c b e
      ∂P.measure (parisiFreeMeasure μ a)) ≤
      (m:ℝ) * P.budget * cavityThirdMoment D μ a := by
  haveI := P.isFiniteMeasure_measure _ (cavityGenerated_free_mass_le_one μ a ha)
  have hs : Integrable (fun h => ∑i : Fin m, cavityCubicPairMoment D μ a (h i))
      (P.measure (parisiFreeMeasure μ a)) := by
    apply integrable_finset_sum
    intro i _
    apply (integrable_const (8:ℝ)).mono'
      ((continuous_cavityCubicPairMoment D μ a).measurable.comp (measurable_pi_apply i)).aestronglyMeasurable
    exact .of_forall fun h => by
      change ‖cavityCubicPairMoment D μ a (h i)‖ ≤ 8
      rw [Real.norm_of_nonneg (cavityCubicPairMoment_bounds D μ a (h i)).1]
      exact (cavityCubicPairMoment_bounds D μ a (h i)).2
  apply (integral_mono_ae
    (cavityGeneratedForest_three_defects_integrable D μ a ha P J T q hcts hmono c b e) hs ?_).trans
    (cavityGenerated_sum_marks_cubic_le D μ a ha P)
  filter_upwards [hlabels] with h hh
  have hbound (r : Fin 3) :
      cavityCubicPairMoment D μ a (q h (c r) (observationCommonLevel (T (c r)) (b r) (e r))) ≤
        ∑i : Fin m, cavityCubicPairMoment D μ a (h i) := by
    obtain ⟨i, hi⟩ := hh r
    rw [hi]
    exact Finset.single_le_sum (fun j _ => (cavityCubicPairMoment_bounds D μ a (h j)).1) (Finset.mem_univ i)
  exact (cavityGeneratedForestThreeDefectMoment_le D μ a J T (q h)
    (hzero h) (hroot h) (hmono h) c b e hbe).trans (by linarith [hbound 0, hbound 1, hbound 2])

end QuantitativeFollowup
