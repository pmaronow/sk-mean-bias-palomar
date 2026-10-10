module
public import QuantitativeFollowup.FollowupCavityGeneratedForestConstruction

@[expose] public section

/-! Bounded terminal factors in genuine generated three-defect terms.
The independent forest law and all mark measures remain literal. Only
the normalized terminal factor is bounded; no mark-marginal estimate is
an input, and interpolation prefactors are kept outside the count bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ} {I : Type*} [Fintype I]
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def cavityGeneratedForestThreeDefectSignedTest (J : I→ℕ)
    (T : (i : I)→FiniteTerminalGenealogy (J i)) (q : I→ℕ→Paper.Overlap)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (σ : CavityGeneratedForestTerminalSample (n:=n) J T) : ℝ :=
  cavitySpinOverlapDefect n (q (c 0) (observationCommonLevel (T (c 0)) (b 0) (e 0)))
    (observationTerminalSpin (T (c 0)) (b 0) (σ (c 0)))
    (observationTerminalSpin (T (c 0)) (e 0) (σ (c 0))) *
  cavitySpinOverlapDefect n (q (c 1) (observationCommonLevel (T (c 1)) (b 1) (e 1)))
    (observationTerminalSpin (T (c 1)) (b 1) (σ (c 1)))
    (observationTerminalSpin (T (c 1)) (e 1) (σ (c 1))) *
  cavitySpinOverlapDefect n (q (c 2) (observationCommonLevel (T (c 2)) (b 2) (e 2)))
    (observationTerminalSpin (T (c 2)) (b 2) (σ (c 2)))
    (observationTerminalSpin (T (c 2)) (e 2) (σ (c 2)))

def cavityGeneratedForestPrefactorExpectation (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I→ℕ)
    (T : (i : I)→FiniteTerminalGenealogy (J i)) (q : I→ℕ→Paper.Overlap)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (F : CavityGeneratedForestTerminalSample (n:=n) J T→ℝ) : ℝ :=
  ∫σ,F σ*cavityGeneratedForestThreeDefectSignedTest J T q c b e σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)

theorem norm_cavityGeneratedForestPrefactorExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I→ℕ) (T : (i : I)→FiniteTerminalGenealogy (J i)) (q : I→ℕ→Paper.Overlap)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (F : CavityGeneratedForestTerminalSample (n:=n) J T→ℝ) (hF : ∀σ,|F σ|≤1) :
    ‖cavityGeneratedForestPrefactorExpectation D μ a J T q c b e F‖≤
      cavityGeneratedForestThreeDefectMoment D μ a J T q c b e := by
  let P := cavityGeneratedNativeForestTerminalProbability D μ a J T q
  have hI : Integrable (fun σ=>‖F σ*cavityGeneratedForestThreeDefectSignedTest J T q c b e σ‖)
      (P : Measure _) :=
    continuousMap_integrable_probability
      ⟨_,continuous_of_discreteTopology⟩ P
  have hM : Integrable (cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e)
      (P : Measure _) :=
    continuousMap_integrable_probability ⟨_,continuous_of_discreteTopology⟩ P
  change ‖∫σ,F σ*cavityGeneratedForestThreeDefectSignedTest J T q c b e σ ∂(P : Measure (CavityGeneratedForestTerminalSample (n:=n) J T))‖≤
    ∫σ,cavityGeneratedForestThreeDefectTest (n:=n) J T q c b e σ
      ∂(P : Measure (CavityGeneratedForestTerminalSample (n:=n) J T))
  apply (norm_integral_le_integral_norm _).trans
    (integral_mono hI hM ?_)
  intro σ
  change ‖F σ*cavityGeneratedForestThreeDefectSignedTest J T q c b e σ‖≤
    |cavityGeneratedForestThreeDefectSignedTest J T q c b e σ|
  rw [Real.norm_eq_abs,abs_mul]
  exact (mul_le_mul_of_nonneg_right (hF σ) (abs_nonneg _)).trans_eq (one_mul _)

private theorem continuous_generatedSignedTest_family
    {H : Type*} [TopologicalSpace H]
    (J : I→ℕ) (T : (i : I)→FiniteTerminalGenealogy (J i))
    (q : H→I→ℕ→Paper.Overlap)
    (hcts : ∀i p,p≤J i → Continuous (fun h=>q h i p))
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r))) :
    Continuous (fun z : H×CavityGeneratedForestTerminalSample (n:=n) J T=>
      cavityGeneratedForestThreeDefectSignedTest J T (q z.1) c b e z.2) := by
  have hpair (r : Fin 3) : Continuous
      (fun z : H×CavityGeneratedForestTerminalSample (n:=n) J T=>
        cavitySpinOverlapDefect n (q z.1 (c r) (observationCommonLevel (T (c r)) (b r) (e r)))
          (observationTerminalSpin (T (c r)) (b r) (z.2 (c r)))
          (observationTerminalSpin (T (c r)) (e r) (z.2 (c r)))) := by
    have hs : Continuous (fun z : H×CavityGeneratedForestTerminalSample (n:=n) J T=>
        (observationTerminalSpin (T (c r)) (b r) (z.2 (c r)),
          observationTerminalSpin (T (c r)) (e r) (z.2 (c r)))) :=
      (continuous_of_discreteTopology (f:=fun σ : CavityGeneratedForestTerminalSample (n:=n) J T=>
        (observationTerminalSpin (T (c r)) (b r) (σ (c r)),
          observationTerminalSpin (T (c r)) (e r) (σ (c r))))).comp continuous_snd
    have hr := (continuous_of_discreteTopology
      (f:=fun z : Configuration (n+1)×Configuration (n+1)=>cavityRestOverlap n z.1 z.2)).comp hs
    have he := (continuous_of_discreteTopology
      (f:=fun z : Configuration (n+1)×Configuration (n+1)=>
        Paper.spinSign (z.1 (Fin.last n))*Paper.spinSign (z.2 (Fin.last n)))).comp hs
    have ht : Continuous (fun z : H×CavityGeneratedForestTerminalSample (n:=n) J T=>
        (q z.1 (c r) (observationCommonLevel (T (c r)) (b r) (e r)) : ℝ)) :=
      continuous_subtype_val.comp
        ((hcts (c r) _ (cavityGenerated_observationCommonLevel_le _ _ _)).comp continuous_fst)
    convert he.mul (hr.sub ht) using 1
    funext z
    exact cavitySpinOverlapDefect_eq n _ _ _
  exact ((hpair 0).mul (hpair 1)).mul (hpair 2)

theorem continuous_cavityGeneratedForestPrefactorExpectation_family
    {H : Type*} [TopologicalSpace H] [FirstCountableTopology H]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I→ℕ) (T : (i : I)→FiniteTerminalGenealogy (J i))
    (q : H→I→ℕ→Paper.Overlap)
    (hcts : ∀i p,p≤J i → Continuous (fun h=>q h i p))
    (hmono : ∀h i p,p<J i→q h i (p+1)≤q h i p)
    (c : Fin 3→I) (b e : (r : Fin 3)→ObservationLeaf (T (c r)))
    (F : CavityGeneratedForestTerminalSample (n:=n) J T→ℝ) :
    Continuous (fun h=>cavityGeneratedForestPrefactorExpectation D μ a J T (q h) c b e F) := by
  let f : H×CavityGeneratedForestTerminalSample (n:=n) J T→ℝ :=
    fun z=>F z.2*cavityGeneratedForestThreeDefectSignedTest J T (q z.1) c b e z.2
  have hf : Continuous f :=
    ((continuous_of_discreteTopology (f:=F)).comp continuous_snd).mul
      (continuous_generatedSignedTest_family J T q hcts c b e)
  exact continuous_integral_probability_family f hf _
    (continuous_cavityGeneratedNativeForestTerminalProbability_family D μ a J T q hcts hmono)

theorem cavityGeneratedConstructedForest_bounded_prefactor_three_defects_count_bound
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0≤a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (r : Fin 3)→ObservationLeaf (W.tree (c r)))
    (F : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hF : ∀σ,|F σ|≤1) (L : ℕ) (hL : P.largestMultiplicity≤L) :
    ‖∫h,cavityGeneratedForestPrefactorExpectation D μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e F
      ∂(P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)‖≤
      (cavityGeneratedThreeDefectCountConstant L P.constructorCount : ℝ)*cavityThirdMoment D μ a := by
  have hM := cavityGeneratedForest_three_defects_integrable D μ a ha
    (P.restrict W.clockTemplate.orderSet) W.depth W.tree W.clockTemplate.clock
    (fun i p _=>W.clockTemplate.clock_continuous i p)
    (fun h i p _=>W.clockTemplate.clock_step_le h i p) c b e
  have hcts := continuous_cavityGeneratedForestPrefactorExpectation_family D μ a
    W.depth W.tree W.clockTemplate.clock
    (fun i p _=>W.clockTemplate.clock_continuous i p)
    (fun h i p _=>W.clockTemplate.clock_step_le h i p) c b e F
  have hN : Integrable (fun h=>‖cavityGeneratedForestPrefactorExpectation D μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e F‖)
      ((P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) :=
    hM.mono' hcts.norm.measurable.aestronglyMeasurable (.of_forall fun h=>by
      rw [norm_norm]
      exact norm_cavityGeneratedForestPrefactorExpectation_le D μ a _ _ _ c b e F hF)
  exact ((norm_integral_le_integral_norm _).trans
    (integral_mono hN hM (fun h=>norm_cavityGeneratedForestPrefactorExpectation_le
      D μ a _ _ _ c b e F hF))).trans
    (cavityGeneratedConstructedForest_three_defects_count_bound hn D μ a ha P W c b e L hL)

end QuantitativeFollowup
