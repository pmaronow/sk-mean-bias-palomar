module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawPairRouting
public import QuantitativeFollowup.SupportingGeneratedObservedForestCubic

@[expose] public section

/-! Any three actual within-component leaf pairs of the observed forest
are controlled by its retained mark budget. Their choice is independent
of the number of defects appended by differentiation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {n m r d : ℕ}

def cavityGeneratedObservedRawForestThreeDefectMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j)))
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree (W.clock h) c b e

theorem measurable_cavityGeneratedObservedRawForestThreeDefectMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j))) :
    Measurable (cavityGeneratedObservedRawForestThreeDefectMoment D μ a W c b e) :=
  measurable_cavityGeneratedObservedForestThreeDefectMoment D μ a W.depth W.tree W.clock
    W.measurable_clock W.clock_antitone c b e

theorem cavityGeneratedObservedRawForestThreeDefectMoment_le_mark_sum
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j)))
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈W.supportSet) :
    cavityGeneratedObservedRawForestThreeDefectMoment D μ a W c b e h ≤
      ∑i : Fin m,cavityCubicPairMoment D μ a (h i) :=
  cavityGeneratedObservedForest_three_defects_le_mark_sum hn D μ a W.depth W.tree
    (W.clock h) (W.clock_terminal h) (W.clock_initial h)
    (fun i j _=>W.clock_antitone h i (Nat.le_succ j)) h
    (fun i l k hlk=>cavityGeneratedObservedRawForest_pair_clock_is_mark W i l k hlk h hh) c b e

theorem cavityGeneratedObservedRawForest_three_defects_of_budget
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (C : ℝ) (hC : 0≤C)
    (hbudget : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks (ENNReal.ofReal C))
    (c : Fin 3→Fin W.componentCount) (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j))) :
    (∫h,cavityGeneratedObservedRawForestThreeDefectMoment D μ a W c b e h ∂M) ≤
      (m:ℝ)*C*cavityThirdMoment D μ a :=
  cavityGeneratedObservedForest_absolute_three_defects_of_budget hn D μ a W.depth W.tree W.clock
    W.measurable_clock W.clock_antitone W.clock_terminal W.clock_initial M
    (hsupport.mono fun h hh i l k hlk=>
      cavityGeneratedObservedRawForest_pair_clock_is_mark W i l k hlk h hh) C hC hbudget c b e

theorem cavityGeneratedObservedRawForest_physical_three_defects_of_budget
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (C : ℝ) (hC : 0≤C)
    (hbudget : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks (ENNReal.ofReal C))
    (κ : ℝ) (r : ℕ) (c : Fin 3→Fin W.componentCount)
    (b e : (j : Fin 3)→ObservationLeaf (W.tree (c j))) :
    (∫h,cavityGeneratedObservedRawForestThreeDefectMoment D μ a W c b e h
      ∂(ENNReal.ofReal (|κ|^r) • M)) ≤
      |κ|^r*((m:ℝ)*C)*cavityThirdMoment D μ a := by
  rw [integral_smul_measure,ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg κ) r),smul_eq_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (cavityGeneratedObservedRawForest_three_defects_of_budget hn D μ a W M
      hsupport C hC hbudget c b e) (pow_nonneg (abs_nonneg κ) r)

def cavityGeneratedObservedRawTaggedThreeDefectMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (ι : Fin 3→Fin d) (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ,|cavityGeneratedObservedRawPairDefect W (A.pairs (ι 0)) h σ *
    cavityGeneratedObservedRawPairDefect W (A.pairs (ι 1)) h σ *
    cavityGeneratedObservedRawPairDefect W (A.pairs (ι 2)) h σ|
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))

theorem cavityGeneratedObservedRawTaggedThreeDefectMoment_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (ι : Fin 3→Fin d) (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedObservedRawTaggedThreeDefectMoment D μ a W A ι h =
      cavityGeneratedObservedRawForestThreeDefectMoment D μ a W
        (fun j=>(A.pairs (ι j)).component) (fun j=>(A.pairs (ι j)).first)
        (fun j=>(A.pairs (ι j)).second) h := rfl

end QuantitativeFollowup
