module
public import HexagonPaper.CavityVertexCancellationTreeKernel
public import QuantitativePaper.BrownianIndependentConditionalMean

@[expose] public section

/-! Fresh conditional continuations of every tagged vertex under the actual
complete root-tilted native tree law. The whole original tree is retained
in the conditioning sigma algebra, including its fields and marked spins. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

@[reducible] def treeNativePointLevel (q : ℕ→Paper.Overlap) :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→treePathWeightPoint T→Paper.Overlap
  | _,.leaf=>fun _=>q 0
  | _,@FiniteTerminalGenealogy.advance j T=>Sum.elim id (treeNativePointLevel q T)
  | j,.fork T U=>Sum.elim (fun _:Unit=>q j) (Sum.elim (treeNativePointLevel q T) (treeNativePointLevel q U))

def treeNativeFullPointLevel (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Unit⊕treePathWeightPoint T→Paper.Overlap :=
  Sum.elim (fun _:Unit=>q j) (treeNativePointLevel q T)

 theorem treeNativePointData_level (D : AnisotropicSpinModel n) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T) (v : treePathWeightPoint T) :
    (treeNativePointData D q T x Z v).1=treeNativePointLevel q T v := by
  induction T generalizing x with
  | leaf=>rfl
  | advance T ih=>cases v with
    | inl r=>rfl
    | inr w=>exact ih _ _ w
  | fork T U ihT ihU=>cases v with
    | inl _=>rfl
    | inr w=>cases w with
      | inl wT=>exact ihT _ _ wT
      | inr wU=>exact ihU _ _ wU

 theorem treeNativeFullPointData_level (D : AnisotropicSpinModel n) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T) (v : Unit⊕treePathWeightPoint T) :
    (treeNativeFullPointData D q T x Z v).1=treeNativeFullPointLevel q T v := by
  cases v with
  | inl _=>rfl
  | inr w=>exact treeNativePointData_level D q T x Z w

 theorem measurable_treeNativePointData_field (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : treePathWeightPoint T) :
    Measurable (fun z : AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T=>
      (treeNativePointData D q T z.1 z.2 v).2) := by
  induction T with
  | leaf=>exact (measurable_anisotropicObservationParameter D).comp measurable_fst
  | @advance j T ih=>cases v with
    | inl r=>exact (ContinuousMap.measurable_eval r).comp measurable_snd.fst
    | inr w=>
      exact (ih w).comp (((measurable_edgePathEndpoint D (q j)).comp
        measurable_snd.fst).prodMk measurable_snd.snd)
  | fork T U ihT ihU=>cases v with
    | inl _=>exact (measurable_anisotropicObservationParameter D).comp measurable_fst
    | inr w=>cases w with
      | inl wT=>exact (ihT wT).comp (measurable_fst.prodMk measurable_snd.fst)
      | inr wU=>exact (ihU wU).comp (measurable_fst.prodMk measurable_snd.snd)

 theorem measurable_treeNativeFullPointData_field (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T) :
    Measurable (fun z : AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T=>
      (treeNativeFullPointData D q T z.1 z.2 v).2) := by
  cases v with
  | inl _=>exact (measurable_anisotropicObservationParameter D).comp measurable_fst
  | inr w=>exact measurable_treeNativePointData_field D q T w

 def treeNativeVertexRestartResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T)
    (r : Paper.Overlap) (i : Fin n)
    (z : (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T)×
      VectorDisorderBrownianSample n) : ℝ :=
  let P:=(treeNativeFullPointData D q T z.1.1 z.1.2 v).2
  let x:=edgeObservationParameterInverse D P
  anisotropicMeasureTailMagnetization D μ r
    ((edgeStoppedDiffusionPath D μ x.1 (treeNativeFullPointLevel q T v) r x.2 z.2) r) i

 theorem treeNativeVertex_future_square_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v : Unit⊕treePathWeightPoint T) (r : Paper.Overlap) (i : Fin n) :
    ((treeNativeFullLaw D μ a q T).prod (vectorDisorderBrownianMeasure n))[
      (fun z=>(treeNativeVertexRestartResponse D μ q T v r i z)^2)|
      MeasurableSpace.comap Prod.fst inferInstance]=ᵐ[
        (treeNativeFullLaw D μ a q T).prod (vectorDisorderBrownianMeasure n)]
      fun z=>cavityTreePhysicalFutureSquare D μ (treeNativeFullPointLevel q T v) r
        (treeNativeFullPointData D q T z.1.1 z.1.2 v).2 i := by
  let P:=treeNativeFullLaw D μ a q T
  let V:=vectorDisorderBrownianMeasure n
  let ambient : MeasurableSpace ((AnisotropicObservationState n×
      Records (NativeTreePath n) (Configuration n) T)×VectorDisorderBrownianSample n) := inferInstance
  let m:MeasurableSpace ((AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T)×VectorDisorderBrownianSample n):=
    MeasurableSpace.comap (Prod.fst : (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T)×VectorDisorderBrownianSample n→(AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T))
      (inferInstance : MeasurableSpace (AnisotropicObservationState n×
        Records (NativeTreePath n) (Configuration n) T))
  letI : MeasurableSpace ((AnisotropicObservationState n×
      Records (NativeTreePath n) (Configuration n) T)×VectorDisorderBrownianSample n) := ambient
  let Q:=treeNativeFullPointLevel q T v
  let X : (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T)→AnisotropicObservationState n:=fun z=>
    edgeObservationParameterInverse D (treeNativeFullPointData D q T z.1 z.2 v).2
  let f : AnisotropicObservationState n×VectorDisorderBrownianSample n→ℝ:=fun z=>
    (anisotropicMeasureTailMagnetization D μ r ((edgeStoppedDiffusionPath D μ z.1.1 Q r z.1.2 z.2) r) i)^2
  have hXm : Measurable X:=
    (edgeObservationParameterInverse D).measurable.comp (measurable_treeNativeFullPointData_field D q T v)
  have hX : Measurable[m] (fun z : (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T)×VectorDisorderBrownianSample n=>X z.1):=
    hXm.comp (Measurable.of_comap_le le_rfl)
  have hf : Measurable f:=
    ((((EuclideanSpace.proj i).measurable.comp
      ((measurable_anisotropicMeasureTailMagnetization D μ).comp
        (measurable_const.prodMk ((ContinuousMap.measurable_eval r).comp
          (measurable_edgeStoppedDiffusionPath_start D μ Q r))))).pow_const 2))
  have hb z : ‖f z‖≤(1:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (anisotropicMeasureTailMagnetization_component_bound D μ r _ i)
  have hI : Indep (MeasurableSpace.comap (Prod.snd : (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T)×VectorDisorderBrownianSample n→_) inferInstance) m (P.prod V) := by
    exact (indepFun_prod (μ:=P) (ν:=V) (X:=id) (Y:=id) measurable_id measurable_id).symm
  have hh:=condExp_independent_noise m (P.prod V) measurable_fst.comap_le
    (fun z=>X z.1) hX Prod.snd measurable_snd V measurePreserving_snd.hasLaw hI f hf 1 hb
  refine hh.trans ?_
  exact .of_forall fun z=>by
    dsimp only
    unfold cavityTreePhysicalFutureSquare
    have hmtest : Measurable (fun Z : NativeTreePath n=>
        (anisotropicMeasureTailMagnetization D μ r (Z r) i)^2) :=
      (((EuclideanSpace.proj i).measurable.comp
        ((measurable_anisotropicMeasureTailMagnetization D μ).comp
          (measurable_const.prodMk (ContinuousMap.measurable_eval r)))).pow_const 2)
    rw [edgePhysicalPathKernel_apply,integral_map
      (measurable_edgeStoppedDiffusionPath D μ _ Q r _).aemeasurable hmtest.aestronglyMeasurable]

end HexagonPaper
