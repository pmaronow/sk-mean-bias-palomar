module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerDefinitions

@[expose] public section

/-! Exact pushforward from all recorded posterior Gaussian inputs to the
augmented normalized history. No invertibility of a covariance map is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1200000

 theorem independentHistory_projection {A B Z : Type*}
    (u : ℕ→A→Z→A) (v : ℕ→B→Z→B) (T : A→B)
    (hc : ∀i x z,T (u i x z)=v i (T x) z) (m : ℕ) (x : A) (z : Fin m→Z) :
    (fun i=>T (independentHistory u m (x,z) i))=
      independentHistory v m (T x,z) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    refine Fin.lastCases ?_ (fun k=>?_) i
    · simp only [independentHistory,Fin.snoc_last]
      rw [hc,←congrFun (ih (fun k=>z k.castSucc)) (Fin.last m)]
    · simp only [independentHistory,Fin.snoc_castSucc]
      exact congrFun (ih (fun k=>z k.castSucc)) k

variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem posteriorCoordinateHistory_fst
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (z : Fin N→FiniteStateGaussianInput I) :
    (fun i=>(posteriorCoordinateHistory L N H z i).1)=cascadePosteriorHistory L N H z :=
  independentHistory_projection (posteriorCoordinateUpdate L N) (cascadePosteriorUpdate L N)
    Prod.fst (fun _ _ _=>rfl) N (H,0) z

def posteriorCoordinateHistoryLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (r : ℕ) :=
  finiteHistoryLaw (Measure.dirac (H,0)) (posteriorCoordinateKernel V a L N) r

theorem posteriorCoordinateHistoryLaw_probability (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (r : ℕ) :
    IsProbabilityMeasure (posteriorCoordinateHistoryLaw V a L N H r) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (posteriorCoordinateKernel_markov V a ha L N) r

def posteriorCoordinateTerminalKernel (V : S→ℝ) (N : ℕ) :
    Kernel (FiniteHistory (PosteriorCoordinateState S I) N) S :=
  (finiteStateGibbsKernel V).comap (fun h=>(h (Fin.last N)).1) (by fun_prop)

instance posteriorCoordinateTerminalKernel_markov (V : S→ℝ) (N : ℕ) :
    IsMarkovKernel (posteriorCoordinateTerminalKernel (I:=I) V N) := by
  haveI:=isMarkovKernel_finiteStateGibbsKernel V
  unfold posteriorCoordinateTerminalKernel
  infer_instance

def posteriorCoordinatePosteriorLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) :=
  posteriorCoordinateHistoryLaw V a L N H N ⊗ₘ posteriorCoordinateTerminalKernel V N

theorem posteriorCoordinatePosteriorLaw_probability (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (posteriorCoordinatePosteriorLaw V a L N H) := by
  haveI:=posteriorCoordinateHistoryLaw_probability V a ha L N H N
  unfold posteriorCoordinatePosteriorLaw
  infer_instance

def posteriorCoordinateJointMap
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (p : (Fin N→FiniteStateGaussianInput I)×S) :=
  (posteriorCoordinateHistory L N H p.1,p.2)

theorem measurable_posteriorCoordinateJointMap
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) : Measurable (posteriorCoordinateJointMap L N H) :=
  (measurable_posteriorCoordinateHistory L N H).prodMap measurable_id

private theorem posteriorCoordinate_path_density (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (h : FiniteHistory (PosteriorCoordinateState S I) N) :
    finiteHistoryDensity (posteriorCoordinateWeight V a L N) N h=
      cascadePosteriorPathDensity V a L N (fun i=>(h i).1) := by
  rw [cascadePosteriorPathDensity,QuantitativePaper.finiteHistoryDensity_eq_prod,
    QuantitativePaper.finiteHistoryDensity_eq_prod]
  rfl

private theorem posteriorCoordinatePosteriorLaw_density (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) :
    posteriorCoordinatePosteriorLaw V a L N H=
      ((finiteHistoryLaw (Measure.dirac (H,0)) (posteriorCoordinateRawKernel L N) N).prod
        (Measure.count : Measure S)).withDensity
      (fun p=>cascadePosteriorJointDensity V a L N (fun i=>(p.1 i).1,p.2)) := by
  haveI:=isProbabilityMeasure_finiteHistoryLaw (Measure.dirac (H,0))
    (posteriorCoordinateRawKernel L N) (fun _=>inferInstance) N
  let w := fun (h : FiniteHistory (PosteriorCoordinateState S I) N) (σ : S)=>
    ENNReal.ofReal (gtStateGibbs V (h (Fin.last N)).1 σ)
  have hG : Measurable (fun z : FiniteStateField S×S=>gtStateGibbs V z.1 z.2) :=
    measurable_from_prod_countable_left fun σ=>(contDiff_gtStateGibbs V σ).continuous.measurable
  have hp : Measurable (fun z : FiniteHistory (PosteriorCoordinateState S I) N×S=>
      ((z.1 (Fin.last N)).1,z.2)) := by fun_prop
  have hw : Measurable (Function.uncurry w) := (hG.comp hp).ennreal_ofReal
  have he : posteriorCoordinateTerminalKernel (I:=I) V N=
      (Kernel.const (FiniteHistory (PosteriorCoordinateState S I) N) (Measure.count : Measure S)).withDensity w := by
    ext h : 1
    rw [Kernel.withDensity_apply _ hw,Kernel.const_apply]
    exact finiteStateGibbsKernel_apply V _
  haveI : IsSFiniteKernel ((Kernel.const (FiniteHistory (PosteriorCoordinateState S I) N)
      (Measure.count : Measure S)).withDensity w) := by rw [←he];infer_instance
  have hd := finiteHistoryLaw_withDensity (Measure.dirac (H,0))
    (posteriorCoordinateRawKernel L N) (posteriorCoordinateKernel V a L N)
    (fun _=>inferInstance) (posteriorCoordinateKernel_markov V a ha L N)
    (posteriorCoordinateWeight V a L N) (measurable_posteriorCoordinateWeight V a ha L N)
    (fun _=>rfl) N
  rw [posteriorCoordinatePosteriorLaw,posteriorCoordinateHistoryLaw,hd,he,
    Measure.withDensity_compProd_withDensity
      (measurable_finiteHistoryDensity _ (measurable_posteriorCoordinateWeight V a ha L N) N) hw,
    Measure.compProd_const]
  congr 1
  funext p
  rw [posteriorCoordinate_path_density]
  rfl

/-- The full recorded Gaussian posterior has exactly the augmented normalized
history law. This preserves every current raw input, including null directions. -/
theorem cascadePosteriorGaussianLaw_augmented_map (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) :
    (cascadePosteriorGaussianLaw V a L N H).map (posteriorCoordinateJointMap L N H)=
      posteriorCoordinatePosteriorLaw V a L N H := by
  let D := fun p : FiniteHistory (PosteriorCoordinateState S I) N×S=>
    cascadePosteriorJointDensity V a L N (fun i=>(p.1 i).1,p.2)
  have hproj : Measurable (fun h : FiniteHistory (PosteriorCoordinateState S I) N=>
      fun i=>(h i).1) := Measurable.of_eval fun i=>measurable_fst.comp (measurable_pi_apply i)
  have hD : Measurable D := (measurable_cascadePosteriorJointDensity V a ha L N).comp
    (hproj.prodMap measurable_id)
  have he : (fun z=>cascadePosteriorJointDensity V a L N (cascadePosteriorCoordinateMap L N H z))=
      D ∘ posteriorCoordinateJointMap L N H := by
    funext z
    simp only [D,Function.comp_def,posteriorCoordinateJointMap,cascadePosteriorCoordinateMap,
      posteriorCoordinateHistory_fst]
  rw [cascadePosteriorGaussianLaw,he]
  simp only [Function.comp_def]
  rw [map_withDensity_pullback _ _
    (measurable_posteriorCoordinateJointMap L N H) D hD]
  have hh := independentHistory_law (Measure.dirac (H,0)) (stdGaussian (FiniteStateGaussianInput I))
    (posteriorCoordinateUpdate L N) (measurable_posteriorCoordinateUpdate L N)
    (posteriorCoordinateRawKernel L N) (fun _=>inferInstance)
    (fun i p=>posteriorCoordinateRawKernel_apply L N i p) N
  rw [Measure.dirac_prod,Measure.map_map
    (measurable_independentHistory _ (measurable_posteriorCoordinateUpdate L N) N)
    measurable_prodMk_left] at hh
  change (Measure.pi (fun _ : Fin N=>stdGaussian (FiniteStateGaussianInput I))).map
    (posteriorCoordinateHistory L N H)=_ at hh
  change (((Measure.pi (fun _ : Fin N=>stdGaussian (FiniteStateGaussianInput I))).prod Measure.count).map
    (Prod.map (posteriorCoordinateHistory L N H) id)).withDensity D=_
  rw [←Measure.map_prod_map _ _ (measurable_posteriorCoordinateHistory L N H) measurable_id,
    hh,Measure.map_id,posteriorCoordinatePosteriorLaw_density V a ha L N H]

end FourPapersCommon
