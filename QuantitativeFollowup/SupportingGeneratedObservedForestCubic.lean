module
public import QuantitativeFollowup.SupportingGeneratedIndexedForestCubic
public import QuantitativeFollowup.SupportingGeneratedAppendBridge

@[expose] public section

/-! Arbitrary measurable unary observation levels do not affect the cubic
estimate. The native law and its measurability are derived from the actual
clock family. A producer must supply its retained-fork labels and mark budget;
this supporting receiver does not assume any desired moment bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {I : Type*} [Fintype I]

theorem measurable_cavityGeneratedObservedForestThreeDefectMoment
    {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : X → I → ℕ → Paper.Overlap)
    (hqmeas : ∀i j, Measurable (fun x => q x i j)) (hq : ∀x i, Antitone (q x i))
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) :
    Measurable (fun x => cavityGeneratedForestThreeDefectMoment D μ a J T (q x) c b e) := by
  have hc := continuous_cavityGeneratedForestThreeDefectMoment_family
    (H:=I → ℕ → Paper.Overlap) D μ a J T
    (fun z i => cavityGeneratedClippedClock (z i))
    (fun i j _ => cavityGeneratedClippedClock_continuous (fun z : I → ℕ → Paper.Overlap => z i)
      (fun k => (continuous_apply k).comp (continuous_apply i)) j)
    (fun z i j _ => cavityGeneratedClippedClock_step_le (z i) j) c b e
  have hm := hc.measurable.comp
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hqmeas i j)
  have he : (fun x i => cavityGeneratedClippedClock (q x i)) = q := by
    funext x i
    exact printedGeneratedClippedClock_of_antitone (q x i) (hq x i)
  change Measurable (fun x => cavityGeneratedForestThreeDefectMoment D μ a J T
    ((fun x i => cavityGeneratedClippedClock (q x i)) x) c b e) at hm
  rw [he] at hm
  exact hm

theorem integrable_cavityGeneratedObservedForestThreeDefectMoment
    {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : X → I → ℕ → Paper.Overlap)
    (hqmeas : ∀i j, Measurable (fun x => q x i j)) (hq : ∀x i, Antitone (q x i))
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r)))
    (M : Measure X) [IsFiniteMeasure M] :
    Integrable (fun x => cavityGeneratedForestThreeDefectMoment D μ a J T (q x) c b e) M := by
  apply (integrable_const (8:ℝ)).mono'
    (measurable_cavityGeneratedObservedForestThreeDefectMoment D μ a J T q hqmeas hq c b e).aestronglyMeasurable
  exact .of_forall fun x => by
    rw [Real.norm_of_nonneg (cavityGeneratedForestThreeDefectMoment_bounds D μ a J T (q x) c b e).1]
    exact (cavityGeneratedForestThreeDefectMoment_bounds D μ a J T (q x) c b e).2

theorem cavityGeneratedObservedForest_three_defects_le_mark_sum
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hzero : ∀i, q i 0 = 1) (htop : ∀i, q i (J i) = 0)
    (hq : ∀i j, j < J i → q i (j+1) ≤ q i j)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hbranch : ∀i (l k : ObservationLeaf (T i)), l ≠ k →
      ∃s : Fin m, q i (observationCommonLevel (T i) l k) = h s)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) :
    cavityGeneratedForestThreeDefectMoment D μ a J T q c b e ≤
      ∑s : Fin m,cavityCubicPairMoment D μ a (h s) := by
  classical
  by_cases hbe : ∀r, b r ≠ e r
  · have hb (r : Fin 3) : cavityCubicPairMoment D μ a
        (q (c r) (observationCommonLevel (T (c r)) (b r) (e r))) ≤
        ∑s : Fin m,cavityCubicPairMoment D μ a (h s) := by
      obtain ⟨s,hs⟩ := hbranch (c r) (b r) (e r) (hbe r)
      rw [hs]
      exact Finset.single_le_sum (fun j _ => (cavityCubicPairMoment_bounds D μ a (h j)).1)
        (Finset.mem_univ s)
    exact (cavityGeneratedForestThreeDefectMoment_le D μ a J T q hzero htop hq c b e hbe).trans
      (by linarith [hb 0,hb 1,hb 2])
  · push Not at hbe
    obtain ⟨r,hr⟩ := hbe
    rw [cavityGeneratedForestThreeDefectMoment_eq_zero_of_same hn D μ a J T q hzero c b e r hr]
    exact Finset.sum_nonneg (fun s _ => (cavityCubicPairMoment_bounds D μ a (h s)).1)

theorem cavityGeneratedObservedForest_absolute_three_defects_of_budget
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : CavityGeneratedHistory Paper.Overlap m → I → ℕ → Paper.Overlap)
    (hqmeas : ∀i j, Measurable (fun h => q h i j)) (hq : ∀h i, Antitone (q h i))
    (hzero : ∀h i, q h i 0 = 1) (htop : ∀h i, q h i (J i) = 0)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hbranch : ∀ᵐh ∂M, ∀i (l k : ObservationLeaf (T i)), l ≠ k →
      ∃s : Fin m,q h i (observationCommonLevel (T i) l k) = h s)
    (C : ℝ) (hC : 0≤C)
    (hbudget : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks (ENNReal.ofReal C))
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r))) :
    (∫h,cavityGeneratedForestThreeDefectMoment D μ a J T (q h) c b e ∂M) ≤
      (m:ℝ)*C*cavityThirdMoment D μ a := by
  haveI : IsFiniteMeasure M := ⟨hbudget.1.trans_lt ENNReal.ofReal_lt_top⟩
  have hj (s : Fin m) : Integrable (fun h => cavityCubicPairMoment D μ a (h s)) M := by
    apply (integrable_const (8:ℝ)).mono'
      ((continuous_cavityCubicPairMoment D μ a).measurable.comp (measurable_pi_apply s)).aestronglyMeasurable
    exact .of_forall fun h => by
      change ‖cavityCubicPairMoment D μ a (h s)‖ ≤ 8
      rw [Real.norm_of_nonneg (cavityCubicPairMoment_bounds D μ a (h s)).1]
      exact (cavityCubicPairMoment_bounds D μ a (h s)).2
  have hm := integrable_cavityGeneratedObservedForestThreeDefectMoment D μ a J T q hqmeas hq c b e M
  calc
    _ ≤ ∫h,∑s : Fin m,cavityCubicPairMoment D μ a (h s) ∂M := by
      apply integral_mono_ae hm (integrable_finsetSum _ (fun s _ => hj s))
      exact hbranch.mono fun h hh => cavityGeneratedObservedForest_three_defects_le_mark_sum
        hn D μ a J T (q h) (hzero h) (htop h) (fun i j _ => hq h i (Nat.le_succ j)) h hh c b e
    _ = ∑s : Fin m,∫h,cavityCubicPairMoment D μ a (h s) ∂M :=
      integral_finsetSum _ (fun s _ => hj s)
    _ ≤ ∑s : Fin m,C*cavityThirdMoment D μ a :=
      Finset.sum_le_sum fun s _ => supporting_generated_coordinate_cubic_of_budget D μ a M C hC hbudget s
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end QuantitativeFollowup
