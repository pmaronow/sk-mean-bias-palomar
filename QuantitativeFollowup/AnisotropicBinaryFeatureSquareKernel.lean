module
public import QuantitativeFollowup.AnisotropicNativePairConditionals
public import QuantitativeFollowup.AnisotropicBinaryFeatureLimits
public import FourPapersCommon.ConditionalKernelWeight
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! The actual conditional law of the continuous anisotropic pair-response
path gives a jointly measurable version of every future square conditional
on the whole native initial-disorder/Wiener past. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

abbrev AnisotropicContinuousPairPath := C(Paper.Overlap,ℝ)

theorem continuous_anisotropicProcessPairResponse_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n)
    (e : AnisotropicCouplingIndex n) :
    Continuous (fun q : Paper.Overlap=>anisotropicProcessPairResponse D μ q e sample) := by
  have hX:=(continuous_anisotropicMeasureState D μ sample).comp
    (continuous_subtype_val : Continuous (fun q : Paper.Overlap=>(q:ℝ)))
  have hP:=(continuous_const (y:=anisotropicDisorderInjection n sample.1)).add
    ((anisotropicFieldInjection n).continuous.comp hX)
  have h:=(continuous_anisotropicTailPairResponse_joint D μ e).comp (continuous_id.prodMk hP)
  simpa only [Function.comp_def,anisotropicProcessPairResponse,anisotropicProcessParameter,
    Pi.add_apply,id_eq] using h

def anisotropicContinuousPairPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    AnisotropicContinuousPairPath :=
  ⟨fun q=>anisotropicProcessPairResponse D μ q e sample,
    continuous_anisotropicProcessPairResponse_time D μ sample e⟩

theorem measurable_anisotropicContinuousPairPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : AnisotropicCouplingIndex n) :
    Measurable (anisotropicContinuousPairPath D μ e) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact measurable_anisotropicProcessPairResponse D μ q e

def anisotropicPairPathEval (q : Paper.Overlap) (f : AnisotropicContinuousPairPath) : ℝ :=
  (projIcc (-1) 1 (by norm_num) (f q):ℝ)

theorem continuous_anisotropicPairPathEval :
    Continuous (fun z : Paper.Overlap×AnisotropicContinuousPairPath=>anisotropicPairPathEval z.1 z.2) :=
  continuous_subtype_val.comp (continuous_projIcc.comp (continuous_snd.eval continuous_fst))

theorem anisotropicPairPathEval_bound (q : Paper.Overlap) (f : AnisotropicContinuousPairPath) :
    ‖anisotropicPairPathEval q f‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (projIcc (-1) 1 (by norm_num) (f q)).property

theorem anisotropicPairPathEval_actual (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (e : AnisotropicCouplingIndex n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicPairPathEval q (anisotropicContinuousPairPath D μ e sample)=
      anisotropicProcessPairResponse D μ q e sample := by
  have hb:=abs_le.mp (by simpa only [Real.norm_eq_abs] using anisotropicProcessPairResponse_bound D μ q e sample)
  exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hb)

def anisotropicPastPairPathKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    @Kernel (AnisotropicDisorderBrownianSample n) AnisotropicContinuousPairPath
      (anisotropicBrownianFiltration n (q:ℝ).toNNReal) inferInstance := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n):=inferInstance
  let P:=anisotropicMeasureSampleLaw D μ a
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  exact @condDistrib (AnisotropicDisorderBrownianSample n) (AnisotropicDisorderBrownianSample n)
    AnisotropicContinuousPairPath inferInstance inferInstance inferInstance ambient V
    (anisotropicContinuousPairPath D μ e) id P inferInstance

instance anisotropicPastPairPathKernel_markov (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    IsMarkovKernel (anisotropicPastPairPathKernel D μ a q e) := by
  unfold anisotropicPastPairPathKernel
  infer_instance

def anisotropicPastPairSquareKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q r : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫f,(anisotropicPairPathEval r f)^2 ∂anisotropicPastPairPathKernel D μ a q e sample

theorem norm_anisotropicPastPairSquareKernel_le (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q r : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicPastPairSquareKernel D μ a q r e sample‖ ≤ 1 := by
  unfold anisotropicPastPairSquareKernel
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=anisotropicPastPairPathKernel D μ a q e sample) (C:=1)
    (.of_forall fun f=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicPairPathEval_bound r f) 2).trans_eq (by norm_num))

theorem measurable_uncurry_anisotropicPastPairSquareKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    @Measurable (Paper.Overlap×AnisotropicDisorderBrownianSample n) ℝ
      ((inferInstance : MeasurableSpace Paper.Overlap).prod (anisotropicBrownianFiltration n (q:ℝ).toNNReal))
      inferInstance (fun z=>anisotropicPastPairSquareKernel D μ a q z.1 e z.2) := by
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=V
  let K : Kernel (AnisotropicDisorderBrownianSample n) AnisotropicContinuousPairPath:=
    anisotropicPastPairPathKernel D μ a q e
  let Q : Kernel (Paper.Overlap×AnisotropicDisorderBrownianSample n) AnisotropicContinuousPairPath:=
    K.comap Prod.snd measurable_snd
  have hF : StronglyMeasurable (fun z : (Paper.Overlap×AnisotropicDisorderBrownianSample n)×AnisotropicContinuousPairPath=>
      (anisotropicPairPathEval z.1.1 z.2)^2) :=
    ((continuous_anisotropicPairPathEval.measurable.comp (measurable_fst.fst.prodMk measurable_snd)).pow_const 2).stronglyMeasurable
  exact (hF.integral_kernel_prod_right' (κ:=Q)).measurable

theorem anisotropicPastPairSquareKernel_condExp (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q r : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    (anisotropicMeasureSampleLaw D μ a)[(fun p=>(anisotropicProcessPairResponse D μ r e p)^2)|
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSampleLaw D μ a]
      anisotropicPastPairSquareKernel D μ a q r e := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n):=inferInstance
  let P:=anisotropicMeasureSampleLaw D μ a
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  let F:=fun f : AnisotropicContinuousPairPath=>(anisotropicPairPathEval r f)^2
  have hF : Measurable F:=((continuous_anisotropicPairPathEval.measurable.comp
    ((measurable_const (a:=r)).prodMk measurable_id)).pow_const 2)
  have hb (f : AnisotropicContinuousPairPath) : ‖F f‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicPairPathEval_bound r f) 2).trans_eq (by norm_num)
  have hi : Integrable (fun p=>F (anisotropicContinuousPairPath D μ e p)) P:=
    (integrable_const (1:ℝ)).mono' (hF.comp (measurable_anisotropicContinuousPairPath D μ e)).aestronglyMeasurable
      (.of_forall fun p=>hb _)
  have he:= @condExp_ae_eq_integral_condDistrib
    (AnisotropicDisorderBrownianSample n) (AnisotropicDisorderBrownianSample n) AnisotropicContinuousPairPath ℝ
    inferInstance inferInstance inferInstance inferInstance ambient P inferInstance
    id (anisotropicContinuousPairPath D μ e) V inferInstance inferInstance
    (@measurable_id'' (AnisotropicDisorderBrownianSample n) V ambient ((anisotropicBrownianFiltration n).le _))
    (measurable_anisotropicContinuousPairPath D μ e).aemeasurable F hF.stronglyMeasurable hi
  unfold anisotropicPastPairSquareKernel
  simpa only [MeasurableSpace.comap_id,id_eq,F,anisotropicPairPathEval_actual,
    anisotropicPastPairSquareKernel,P,V,anisotropicPastPairPathKernel] using he

theorem anisotropicPastPairSquareKernel_weighted_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (Z : AnisotropicDisorderBrownianSample n→ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ≥0) (hB : ∀p,‖Z p‖ ≤ B) :
    (∫p,Z p*anisotropicPastPairSquareKernel D μ a q r e p ∂anisotropicMeasureSampleLaw D μ a)=
      ∫p,Z p*(anisotropicProcessPairResponse D μ r e p)^2 ∂anisotropicMeasureSampleLaw D μ a := by
  let P:=anisotropicMeasureSampleLaw D μ a
  have hZm:=hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hi : Integrable (fun p=>(anisotropicProcessPairResponse D μ r e p)^2) P :=
    (integrable_const (1:ℝ)).mono' ((measurable_anisotropicProcessPairResponse D μ r e).pow_const 2).aestronglyMeasurable
      (.of_forall fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound D μ r e p) 2).trans_eq (by norm_num))
  have hp : Integrable (Z*(fun p=>(anisotropicProcessPairResponse D μ r e p)^2)) P :=
    by simpa only [Pi.mul_def,mul_comm] using hi.mul_bdd hZm.aestronglyMeasurable (.of_forall hB)
  exact (weighted_kernelObservable_of_condExp_integrable (anisotropicBrownianFiltration n (q:ℝ).toNNReal)
    P ((anisotropicBrownianFiltration n).le _) _ _ hi (anisotropicPastPairSquareKernel_condExp D μ a q r e)
    Z hZ.stronglyMeasurable hp).symm

end QuantitativeFollowup
