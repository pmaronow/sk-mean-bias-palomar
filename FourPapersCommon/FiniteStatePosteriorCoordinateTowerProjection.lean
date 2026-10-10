module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTower
public import FourPapersCommon.KernelSamplingMap

@[expose] public section

/-! The retained-coordinate prefix projects to the original actual field
prefix. Hence the coordinate Stein tower can be stated solely with the
original Gaussian cascade fields, without discarding any raw input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal Topology
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper
set_option maxHeartbeats 1200000

 theorem finiteHistoryLaw_map_states {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) [IsProbabilityMeasure ν] (κ : ℕ→Kernel A A) (η : ℕ→Kernel B B)
    (hκ : ∀i,IsMarkovKernel (κ i)) (hη : ∀i,IsMarkovKernel (η i))
    (T : A→B) (hT : Measurable T) (hsection : ∀i x,(κ i x).map T=η i (T x)) (N : ℕ) :
    (finiteHistoryLaw ν κ N).map (fun h i=>T (h i))=finiteHistoryLaw (ν.map T) η N := by
  have hproj (n : ℕ) : Measurable (fun h : FiniteHistory A n=>fun i=>T (h i)) :=
    Measurable.of_eval fun _=>hT.comp (measurable_pi_apply _)
  haveI: IsProbabilityMeasure (ν.map T):=(Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  induction N with
  | zero =>
    rw [finiteHistoryLaw,Measure.map_map (hproj 0) (by fun_prop),finiteHistoryLaw,
      Measure.map_map (by fun_prop) hT]
    rfl
  | succ N ih =>
    haveI:=hκ N
    haveI:=hη N
    haveI:=isProbabilityMeasure_finiteHistoryLaw ν κ hκ N
    let κ' := (κ N).comap (fun h : FiniteHistory A N=>h (Fin.last N)) (measurable_pi_apply _)
    let η' := (η N).comap (fun h : FiniteHistory B N=>h (Fin.last N)) (measurable_pi_apply _)
    have hp := map_compProd_map_pair (finiteHistoryLaw ν κ N) κ' η'
      (fun h i=>T (h i)) T (hproj N) hT (fun h=>hsection N (h (Fin.last N)))
    rw [finiteHistoryLaw,Measure.map_map (hproj (N+1)) (historySplit N).symm.measurable]
    have hc : (fun h : FiniteHistory A (N+1)=>fun i=>T (h i)) ∘ (historySplit N).symm=
        (historySplit N).symm ∘ Prod.map (fun h : FiniteHistory A N=>fun i=>T (h i)) T := by
      funext p i
      refine Fin.lastCases ?_ (fun j=>?_) i <;>
        simp only [Function.comp_def,historySplit_symm_apply,Prod.map,Fin.snoc_last,Fin.snoc_castSucc]
    rw [hc,←Measure.map_map (historySplit N).symm.measurable ((hproj N).prodMap hT),hp,ih]
    rfl

variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem posteriorCoordinateKernel_fst_map (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N r : ℕ)
    (p : PosteriorCoordinateState S I) :
    (posteriorCoordinateKernel V a L N r p).map Prod.fst=cascadePosteriorKernel V a L N r p.1 := by
  have hmap : Measurable (posteriorCoordinateUpdate L N r p) :=
    (measurable_posteriorCoordinateUpdate L N r).comp (measurable_const.prodMk measurable_id)
  rw [posteriorCoordinateKernel_apply V a ha L,
    Measure.map_map measurable_fst hmap,
    cascadePosteriorKernel,finiteStateGaussianCascadeKernel]
  change _=finiteStateGaussianStepKernel (a (N-1-r)) (L (N-1-r))
    (finiteStateGaussianTerminalCascade V a L (N-1-r)) p.1
  rw [finiteStateGaussianStepKernel_apply _ _ _
      (contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-r)).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _
      (contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-r)).continuous.measurable]
  rfl

theorem posteriorCoordinateHistoryLaw_fst_map (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N r : ℕ)
    (H : FiniteStateField S) :
    (posteriorCoordinateHistoryLaw V a L N H r).map (fun h i=>(h i).1)=
      finiteHistoryLaw (Measure.dirac H) (cascadePosteriorKernel V a L N) r := by
  rw [posteriorCoordinateHistoryLaw,finiteHistoryLaw_map_states _ _ _
    (posteriorCoordinateKernel_markov V a ha L N) (cascadePosteriorKernel_markov V a ha L N)
    Prod.fst measurable_fst (posteriorCoordinateKernel_fst_map V a ha L N),Measure.map_dirac' measurable_fst]

theorem integral_posteriorCoordinateHistoryLaw_field (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N r : ℕ)
    (H : FiniteStateField S) (f : FiniteStateField S→ℝ) (hf : Measurable f) :
    (∫h,f (h (Fin.last r)).1 ∂posteriorCoordinateHistoryLaw V a L N H r)=
      ∫h,f (h (Fin.last r)) ∂finiteHistoryLaw (Measure.dirac H) (cascadePosteriorKernel V a L N) r := by
  rw [←posteriorCoordinateHistoryLaw_fst_map V a ha L N r H]
  have hproj : Measurable (fun h : FiniteHistory (PosteriorCoordinateState S I) r=>fun i=>(h i).1) :=
    Measurable.of_eval fun _=>measurable_fst.comp (measurable_pi_apply _)
  have hf' : Measurable (fun h : FiniteHistory (FiniteStateField S) r=>f (h (Fin.last r))) :=
    hf.comp (measurable_pi_apply (Fin.last r))
  exact (integral_map hproj.aemeasurable hf'.aestronglyMeasurable).symm

/-- The final Stein tower uses exactly the original normalized field prefix.
The raw Gaussian coordinate is retained on the left, including null modes. -/
theorem cascadePosteriorGaussianLaw_coordinate_ibp_field_prefix (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H K : FiniteStateField S) (r : Fin N) (i : Fin (Fintype.card I)) :
    (∫z,(finiteStateGaussianBasis I).repr (z.1 r) i*K z.2 ∂cascadePosteriorGaussianLaw V a L N H)=
      ∫h,(∫y,fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-r.val))) y
          (L (N-1-r.val) (finiteStateGaussianBasis I i)) K+
        a (N-1-r.val)*fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-r.val)) y K*
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-r.val)) y
            (L (N-1-r.val) (finiteStateGaussianBasis I i))
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (N-1-r.val) (h (Fin.last r.val)))
        ∂finiteHistoryLaw (Measure.dirac H) (cascadePosteriorKernel V a L N) r.val := by
  rw [cascadePosteriorGaussianLaw_coordinate_ibp V a ha L N H K r i]
  have hU := contDiff_two_finiteStateGaussianTerminalCascade V a ha L (N-1-r.val)
  have hD := hU.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)
  have hfirst := hD.continuous
  have hsecond := hD.continuous_fderiv (by norm_num)
  have hm := ((hsecond.clm_apply (continuous_const (y:=L (N-1-r.val) (finiteStateGaussianBasis I i)))).clm_apply
    (continuous_const (y:=K))).add
    (((hfirst.clm_apply (continuous_const (y:=K))).const_mul (a (N-1-r.val))).mul
      (hfirst.clm_apply (continuous_const (y:=L (N-1-r.val) (finiteStateGaussianBasis I i)))))
  exact integral_posteriorCoordinateHistoryLaw_field V a ha L N r.val H _
    (hm.measurable.stronglyMeasurable.integral_kernel).measurable

end FourPapersCommon
