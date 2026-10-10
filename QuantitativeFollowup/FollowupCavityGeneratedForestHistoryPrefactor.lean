module
public import QuantitativeFollowup.FollowupCavityGeneratedForestBoundedPrefactor
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalDefectTests

@[expose] public section

/-! Bounded terminal prefactors may depend on the entire retained mark
history. The expectation uses the genuine independent forest law. Its
three-defect bound derives both the pair law and every mark marginal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {I : Type*} [Fintype I]

def cavityGeneratedForestHistoryPrefactorExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I→ℕ) (T : (i : I)→FiniteTerminalGenealogy (J i))
    (q : CavityGeneratedHistory Paper.Overlap m→I→ℕ→Paper.Overlap)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (F : CavityGeneratedHistory Paper.Overlap m→CavityGeneratedForestTerminalSample (n:=n) J T→ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  cavityGeneratedForestPrefactorExpectation D μ a J T (q h) c b e (F h)

theorem continuous_cavityGeneratedForestHistoryPrefactorExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I→ℕ) (T : (i : I)→FiniteTerminalGenealogy (J i))
    (q : CavityGeneratedHistory Paper.Overlap m→I→ℕ→Paper.Overlap)
    (hcts : ∀i p,p≤J i → Continuous (fun h=>q h i p))
    (hmono : ∀h i p,p<J i→q h i (p+1)≤q h i p)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (F : CavityGeneratedHistory Paper.Overlap m→CavityGeneratedForestTerminalSample (n:=n) J T→ℝ)
    (hF : ∀σ,Continuous (fun h=>F h σ)) :
    Continuous (cavityGeneratedForestHistoryPrefactorExpectation D μ a J T q c b e F) := by
  let f : CavityGeneratedHistory Paper.Overlap m×CavityGeneratedForestTerminalSample (n:=n) J T→ℝ :=
    fun z=>F z.1 z.2*cavityGeneratedForestThreeDefectSignedTest J T (q z.1) c b e z.2
  have hf : Continuous f := by
    apply continuous_prod_of_discrete_right.mpr
    intro σ
    have hp (r : Fin 3) : Continuous (fun h : CavityGeneratedHistory Paper.Overlap m=>
      cavitySpinOverlapDefect n (q h (c r) (observationCommonLevel (T (c r)) (b r) (e r)))
        (observationTerminalSpin (T (c r)) (b r) (σ (c r)))
        (observationTerminalSpin (T (c r)) (e r) (σ (c r)))) :=
      continuous_cavitySpinOverlapDefect_clock _
        (hcts (c r) _ (cavityGenerated_observationCommonLevel_le _ _ _)) _ _
    exact (hF σ).mul (((hp 0).mul (hp 1)).mul (hp 2))
  exact continuous_integral_probability_family f hf _
    (continuous_cavityGeneratedNativeForestTerminalProbability_family D μ a J T q hcts hmono)

theorem norm_cavityGeneratedForestHistoryPrefactorExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I→ℕ) (T : (i : I)→FiniteTerminalGenealogy (J i))
    (q : CavityGeneratedHistory Paper.Overlap m→I→ℕ→Paper.Overlap)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (F : CavityGeneratedHistory Paper.Overlap m→CavityGeneratedForestTerminalSample (n:=n) J T→ℝ)
    (hF : ∀h σ,|F h σ|≤1) (h : CavityGeneratedHistory Paper.Overlap m) :
    ‖cavityGeneratedForestHistoryPrefactorExpectation D μ a J T q c b e F h‖≤
      cavityGeneratedForestThreeDefectMoment D μ a J T (q h) c b e :=
  norm_cavityGeneratedForestPrefactorExpectation_le D μ a J T (q h) c b e (F h) (hF h)

theorem integrable_cavityGeneratedConstructedForestHistoryPrefactor
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0≤a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (r : Fin 3)→ObservationLeaf (W.tree (c r)))
    (F : CavityGeneratedHistory Paper.Overlap m→
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hcts : ∀σ,Continuous (fun h=>F h σ)) (hF : ∀h σ,|F h σ|≤1) :
    Integrable (cavityGeneratedForestHistoryPrefactorExpectation D μ a W.depth W.tree
      W.clockTemplate.clock c b e F)
      ((P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) := by
  have hM := cavityGeneratedForest_three_defects_integrable D μ a ha
    (P.restrict W.clockTemplate.orderSet) W.depth W.tree W.clockTemplate.clock
    (fun i p _=>W.clockTemplate.clock_continuous i p)
    (fun h i p _=>W.clockTemplate.clock_step_le h i p) c b e
  have hc := continuous_cavityGeneratedForestHistoryPrefactorExpectation D μ a W.depth W.tree
    W.clockTemplate.clock (fun i p _=>W.clockTemplate.clock_continuous i p)
    (fun h i p _=>W.clockTemplate.clock_step_le h i p) c b e F hcts
  exact hM.mono' hc.aestronglyMeasurable (.of_forall fun h=>
    norm_cavityGeneratedForestHistoryPrefactorExpectation_le D μ a _ _ _ c b e F hF h)

theorem cavityGeneratedConstructedForest_history_prefactor_three_defects_count_bound
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0≤a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (r : Fin 3)→ObservationLeaf (W.tree (c r)))
    (F : CavityGeneratedHistory Paper.Overlap m→
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hcts : ∀σ,Continuous (fun h=>F h σ)) (hF : ∀h σ,|F h σ|≤1)
    (L : ℕ) (hL : P.largestMultiplicity≤L) :
    ‖∫h,cavityGeneratedForestHistoryPrefactorExpectation D μ a W.depth W.tree
      W.clockTemplate.clock c b e F h
      ∂(P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)‖≤
      (cavityGeneratedThreeDefectCountConstant L P.constructorCount : ℝ)*cavityThirdMoment D μ a := by
  have hM := cavityGeneratedForest_three_defects_integrable D μ a ha
    (P.restrict W.clockTemplate.orderSet) W.depth W.tree W.clockTemplate.clock
    (fun i p _=>W.clockTemplate.clock_continuous i p)
    (fun h i p _=>W.clockTemplate.clock_step_le h i p) c b e
  have hI := integrable_cavityGeneratedConstructedForestHistoryPrefactor D μ a ha P W c b e F hcts hF
  have hN := hI.norm
  exact ((norm_integral_le_integral_norm _).trans
    (integral_mono hN hM (fun h=>norm_cavityGeneratedForestHistoryPrefactorExpectation_le
      D μ a _ _ _ c b e F hF h))).trans
    (cavityGeneratedConstructedForest_three_defects_count_bound hn D μ a ha P W c b e L hL)

end QuantitativeFollowup
