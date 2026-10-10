module
public import QuantitativeFollowup.AnisotropicRecordedProfileTree
public import QuantitativeFollowup.AnisotropicNoiseProfileStability
public import FourPapersCommon.FiniteObservationTreeTopology
public import FourPapersCommon.FiniteStateGibbsContinuity

@[expose] public section

/-! Genuine weak convergence of full fixed-observation genealogy kernels.
All edge continuations are actual Picard restarts driven by independent
Wiener paths. Product forks preserve the shared incoming observation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal Topology BoundedContinuousFunction
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

instance anisotropicObservationRecords_borel {J : ℕ} (T : FiniteTerminalGenealogy J) :
    BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
  FiniteTerminalGenealogy.instBorelSpaceRecordsOfSecondCountableTopology T

instance anisotropicObservationRecords_opens {J : ℕ} (T : FiniteTerminalGenealogy J) :
    OpensMeasurableSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
  BorelSpace.opensMeasurable

instance anisotropicObservationJointRecords_opens {J : ℕ} (T : FiniteTerminalGenealogy J) :
    OpensMeasurableSpace (AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T) :=
  Prod.opensMeasurableSpace

def anisotropicRecordedProfileTreeProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (z : AnisotropicObservationState n) :
    ProbabilityMeasure (Records (AnisotropicObservationState n) (Configuration n) T) :=
  (anisotropicRecordedProfileTreeKernel D μ q T z).toProbabilityMeasure

def anisotropicRecordedProfileJointProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (z : AnisotropicObservationState n) :
    ProbabilityMeasure (AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T) :=
  (Measure.dirac z).toProbabilityMeasure |>.prod (anisotropicRecordedProfileTreeProbability D μ q T z)

theorem anisotropicRecordedProfileJointProbability_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (z : AnisotropicObservationState n) :
    (anisotropicRecordedProfileJointProbability D μ q T z:Measure _)=
      (Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) z := by
  rw [Kernel.prod_apply,Kernel.id_apply]
  rfl

theorem measurable_anisotropicRecordedProfileJointMean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J)
    (f : (AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)→ᵇℝ) :
    Measurable (fun z=>∫v,f v ∂(anisotropicRecordedProfileJointProbability D μ q T z:Measure _)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  simp_rw [anisotropicRecordedProfileJointProbability_kernel]
  exact f.continuous.measurable.stronglyMeasurable.integral_kernel.measurable

theorem anisotropicRecordedProfileTreeProbability_advance_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (z : AnisotropicObservationState n)
    (f : Records (AnisotropicObservationState n) (Configuration n) (.advance T)→ᵇℝ) :
    (∫v,f v ∂(anisotropicRecordedProfileTreeProbability D μ q (.advance T) z:Measure _))=
      ∫W,∫v,f v ∂(anisotropicRecordedProfileJointProbability D μ q T
        (anisotropicObservationNoiseAdvance D μ (q (J+1)) (q J) (z,W)):Measure _)
        ∂vectorWienerMeasure n := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  change (∫v,f v ∂((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
    anisotropicObservationTransition D μ (q (J+1)) (q J)) z)=_
  rw [Kernel.integral_comp (f.integrable _)]
  simp_rw [←anisotropicRecordedProfileJointProbability_kernel]
  rw [anisotropicObservationTransition_apply]
  have hm : Measurable (fun W : VectorWienerPath n=>
      (z.1,anisotropicRestartNoiseStatePath D μ (q (J+1)) (z,W) ((q J:ℝ)-(q (J+1):ℝ)))) := by
    simpa only [Function.comp_def,anisotropicObservationNoiseAdvance,id_eq] using
      (measurable_anisotropicObservationNoiseAdvance D μ (q (J+1)) (q J)).comp
        (measurable_const.prodMk measurable_id)
  exact integral_map hm.aemeasurable
    (measurable_anisotropicRecordedProfileJointMean D μ q T f).aestronglyMeasurable

theorem anisotropicRecordedProfileTreeProbability_fork (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T U : FiniteTerminalGenealogy J) (z : AnisotropicObservationState n) :
    anisotropicRecordedProfileTreeProbability D μ q (.fork T U) z=
      (anisotropicRecordedProfileTreeProbability D μ q T z).prod
        (anisotropicRecordedProfileTreeProbability D μ q U z) := by
  apply Subtype.ext
  exact Kernel.prod_apply _ _ _

theorem measurable_anisotropicRestartNoiseStatePath_section (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (g : AnisotropicDisorder n)
    (x : Field n) (r : ℝ) :
    Measurable (fun W : VectorWienerPath n=>anisotropicRestartNoiseStatePath D μ q ((g,x),W) r) := by
  have hm : Measurable (fun W : VectorWienerPath n=>(r,((g,x),W))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have h:=(measurable_uncurry_anisotropicRestartNoiseStatePath D μ q).comp hm
  simpa only [Function.comp_def] using h

theorem tendsto_anisotropicRecordedProfileJointProbability_of_tree {L : Type*} {l : Filter L}
    (D : AnisotropicSpinModel n) (μ : L→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (z : L→AnisotropicObservationState n) (w : AnisotropicObservationState n)
    (hz : Tendsto z l (𝓝 w))
    (ht : Tendsto (fun j=>anisotropicRecordedProfileTreeProbability D (μ j) q T (z j)) l
      (𝓝 (anisotropicRecordedProfileTreeProbability D ν q T w))) :
    Tendsto (fun j=>anisotropicRecordedProfileJointProbability D (μ j) q T (z j)) l
      (𝓝 (anisotropicRecordedProfileJointProbability D ν q T w)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  have h:=(ProbabilityMeasure.continuous_prod
    (α:=AnisotropicObservationState n)
    (β:=Records (AnisotropicObservationState n) (Configuration n) T)).tendsto _ |>.comp
      ((tendsto_dirac_probability hz).prodMk_nhds ht)
  simpa only [anisotropicRecordedProfileJointProbability,Function.comp_def] using h

theorem tendsto_anisotropicRecordedProfileTreeProbability {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hq : ∀j,j<J→q (j+1)≤q j) (g : AnisotropicDisorder n)
    {x : L→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun j=>anisotropicRecordedProfileTreeProbability D (μ j) q T (g,x j)) l
      (𝓝 (anisotropicRecordedProfileTreeProbability D ν q T (g,y))) := by
  induction T generalizing x y with
  | leaf =>
      have hP : Tendsto (fun j=>anisotropicEnergyMap D (anisotropicObservationParameter D (g,x j))) l
          (𝓝 (anisotropicEnergyMap D (anisotropicObservationParameter D (g,y)))) :=
        (anisotropicEnergyMap D).continuous.tendsto _ |>.comp
          ((tendsto_const_nhds (x:=anisotropicDisorderInjection n g)).add
            ((anisotropicUnitInput D).continuous.tendsto y |>.comp hx))
      exact (continuous_finiteStateGibbsProbability (fun _:Configuration n=>0)).tendsto _ |>.comp hP
  | @advance J T ih =>
      haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro f
      have hfun : (fun i:L=>∫v,f v ∂(anisotropicRecordedProfileTreeProbability D (μ i) q (.advance T) (g,x i):Measure _))=
          (fun i=>∫W,∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ i) q T
            (anisotropicObservationNoiseAdvance D (μ i) (q (J+1)) (q J) ((g,x i),W)):Measure _)
              ∂vectorWienerMeasure n) := by
        funext i
        exact anisotropicRecordedProfileTreeProbability_advance_integral D (μ i) q T (g,x i) f
      rw [hfun,anisotropicRecordedProfileTreeProbability_advance_integral D ν q T (g,y) f]
      have hqt:=hq J (Nat.lt_succ_self J)
      have hsub : ((q J:Paper.Overlap):ℝ)-((q (J+1):Paper.Overlap):ℝ)∈
          Icc (0:ℝ) (1-((q (J+1):Paper.Overlap):ℝ)) :=
        ⟨sub_nonneg.mpr hqt,sub_le_sub_right (q J).property.2 _⟩
      let X:=fun j W=>anisotropicRestartNoiseStatePath D (μ j) (q (J+1)) ((g,x j),W)
        (((q J:Paper.Overlap):ℝ)-((q (J+1):Paper.Overlap):ℝ))
      let Y:=fun W=>anisotropicRestartNoiseStatePath D ν (q (J+1)) ((g,y),W)
        (((q J:Paper.Overlap):ℝ)-((q (J+1):Paper.Overlap):ℝ))
      have hX (W : VectorWienerPath n) : Tendsto (fun j=>X j W) l (𝓝 (Y W)) :=
        tendsto_anisotropicRestartNoiseStatePath_profile D hμ g _ hx W _ hsub
      have hp (W : VectorWienerPath n) : Tendsto (fun j=>
          anisotropicRecordedProfileJointProbability D (μ j) q T (g,X j W)) l
          (𝓝 (anisotropicRecordedProfileJointProbability D ν q T (g,Y W))) := by
        exact tendsto_anisotropicRecordedProfileJointProbability_of_tree D μ ν q T
          (fun j=>(g,X j W)) (g,Y W) ((tendsto_const_nhds (x:=g)).prodMk_nhds (hX W))
            (ih (fun i hi=>hq i (by omega)) (hX W))
      have hm (j : L) : AEStronglyMeasurable (fun W=>∫v,f v
          ∂(anisotropicRecordedProfileJointProbability D (μ j) q T (g,X j W):Measure _))
          (vectorWienerMeasure n) := by
        have hs : Measurable (X j):=measurable_anisotropicRestartNoiseStatePath_section
          D (μ j) (q (J+1)) g (x j) ((q J:ℝ)-(q (J+1):ℝ))
        have hmap : Measurable (fun W : VectorWienerPath n=>(g,X j W)):=measurable_const.prodMk hs
        exact ((measurable_anisotropicRecordedProfileJointMean D (μ j) q T f).comp hmap).aestronglyMeasurable
      have hb (j : L) (W : VectorWienerPath n) :
          ‖∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ j) q T (g,X j W):Measure _)‖≤‖f‖ := by
        simpa only [probReal_univ,mul_one] using
          norm_integral_le_of_norm_le_const
            (μ:=(anisotropicRecordedProfileJointProbability D (μ j) q T (g,X j W):Measure _))
            (.of_forall f.norm_coe_le_norm)
      have hi:=tendsto_integral_filter_of_dominated_convergence (fun _:VectorWienerPath n=>‖f‖)
        (.of_forall hm) (.of_forall fun j=>.of_forall (hb j)) (integrable_const ‖f‖)
        (.of_forall fun W=>ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hp W) f)
      simpa only [anisotropicObservationNoiseAdvance,X,Y,Function.comp_def] using hi
  | fork T U ihT ihU =>
      haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) U):=inferInstance
      haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) U):=inferInstance
      haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) U):=inferInstance
      have h:=ProbabilityMeasure.continuous_prod.tendsto _ |>.comp
        ((ihT hq hx).prodMk_nhds (ihU hq hx))
      simpa only [anisotropicRecordedProfileTreeProbability_fork,Function.comp_def] using h

end QuantitativeFollowup
