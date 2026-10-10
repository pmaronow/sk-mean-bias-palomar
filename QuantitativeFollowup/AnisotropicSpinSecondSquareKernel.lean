module
public import QuantitativeFollowup.AnisotropicNativeSpinConditionals
public import QuantitativeFollowup.AnisotropicSpinSecondLimits
public import FourPapersCommon.ConditionalKernelWeight
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! The actual conditional law of the continuous anisotropic spin-response
path gives a jointly measurable version of every future square conditional
on the whole native initial-disorder/Wiener past. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

abbrev AnisotropicContinuousSpinPath := C(Paper.Overlap,ℝ)

theorem continuous_anisotropicProcessSpinResponse_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n)
    (e : Fin n) :
    Continuous (fun q : Paper.Overlap=>anisotropicProcessSpinResponse D μ q e sample) := by
  have hX:=(continuous_anisotropicMeasureState D μ sample).comp
    (continuous_subtype_val : Continuous (fun q : Paper.Overlap=>(q:ℝ)))
  have hP:=(continuous_const (y:=anisotropicDisorderInjection n sample.1)).add
    ((anisotropicFieldInjection n).continuous.comp hX)
  have h:=(continuous_anisotropicSpinResponse_joint D μ e).comp (continuous_id.prodMk hP)
  simpa only [Function.comp_def,ContinuousLinearMap.id_apply,anisotropicProcessSpinResponse,anisotropicProcessMagnetization,anisotropicProcessParameter,
    Pi.add_apply,id_eq] using h

def anisotropicContinuousSpinPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (e : Fin n) (sample : AnisotropicDisorderBrownianSample n) :
    AnisotropicContinuousSpinPath :=
  ⟨fun q=>anisotropicProcessSpinResponse D μ q e sample,
    continuous_anisotropicProcessSpinResponse_time D μ sample e⟩

theorem measurable_anisotropicContinuousSpinPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : Fin n) :
    Measurable (anisotropicContinuousSpinPath D μ e) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact measurable_anisotropicProcessSpinResponse D μ q e

def anisotropicSpinPathEval (q : Paper.Overlap) (f : AnisotropicContinuousSpinPath) : ℝ :=
  (projIcc (-1) 1 (by norm_num) (f q):ℝ)

theorem continuous_anisotropicSpinPathEval :
    Continuous (fun z : Paper.Overlap×AnisotropicContinuousSpinPath=>anisotropicSpinPathEval z.1 z.2) :=
  continuous_subtype_val.comp (continuous_projIcc.comp (continuous_snd.eval continuous_fst))

theorem anisotropicSpinPathEval_bound (q : Paper.Overlap) (f : AnisotropicContinuousSpinPath) :
    ‖anisotropicSpinPathEval q f‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (projIcc (-1) 1 (by norm_num) (f q)).property

theorem anisotropicSpinPathEval_actual (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (e : Fin n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicSpinPathEval q (anisotropicContinuousSpinPath D μ e sample)=
      anisotropicProcessSpinResponse D μ q e sample := by
  have hb:=abs_le.mp (by simpa only [Real.norm_eq_abs] using anisotropicProcessSpinResponse_bound D μ q e sample)
  exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hb)

def anisotropicPastSpinPathKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) (e : Fin n) :
    @Kernel (AnisotropicDisorderBrownianSample n) AnisotropicContinuousSpinPath
      (anisotropicBrownianFiltration n (q:ℝ).toNNReal) inferInstance := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n):=inferInstance
  let P:=anisotropicMeasureSampleLaw D μ a
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  exact @condDistrib (AnisotropicDisorderBrownianSample n) (AnisotropicDisorderBrownianSample n)
    AnisotropicContinuousSpinPath inferInstance inferInstance inferInstance ambient V
    (anisotropicContinuousSpinPath D μ e) id P inferInstance

instance anisotropicPastSpinPathKernel_markov (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) (e : Fin n) :
    IsMarkovKernel (anisotropicPastSpinPathKernel D μ a q e) := by
  unfold anisotropicPastSpinPathKernel
  infer_instance

def anisotropicPastSpinSquareKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q r : Paper.Overlap) (e : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫f,(anisotropicSpinPathEval r f)^2 ∂anisotropicPastSpinPathKernel D μ a q e sample

theorem norm_anisotropicPastSpinSquareKernel_le (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q r : Paper.Overlap) (e : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicPastSpinSquareKernel D μ a q r e sample‖ ≤ 1 := by
  unfold anisotropicPastSpinSquareKernel
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=anisotropicPastSpinPathKernel D μ a q e sample) (C:=1)
    (.of_forall fun f=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicSpinPathEval_bound r f) 2).trans_eq (by norm_num))

theorem measurable_uncurry_anisotropicPastSpinSquareKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : Fin n) :
    @Measurable (Paper.Overlap×AnisotropicDisorderBrownianSample n) ℝ
      ((inferInstance : MeasurableSpace Paper.Overlap).prod (anisotropicBrownianFiltration n (q:ℝ).toNNReal))
      inferInstance (fun z=>anisotropicPastSpinSquareKernel D μ a q z.1 e z.2) := by
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=V
  let K : Kernel (AnisotropicDisorderBrownianSample n) AnisotropicContinuousSpinPath:=
    anisotropicPastSpinPathKernel D μ a q e
  let Q : Kernel (Paper.Overlap×AnisotropicDisorderBrownianSample n) AnisotropicContinuousSpinPath:=
    K.comap Prod.snd measurable_snd
  have hF : StronglyMeasurable (fun z : (Paper.Overlap×AnisotropicDisorderBrownianSample n)×AnisotropicContinuousSpinPath=>
      (anisotropicSpinPathEval z.1.1 z.2)^2) :=
    ((continuous_anisotropicSpinPathEval.measurable.comp (measurable_fst.fst.prodMk measurable_snd)).pow_const 2).stronglyMeasurable
  exact (hF.integral_kernel_prod_right' (κ:=Q)).measurable

theorem anisotropicPastSpinSquareKernel_condExp (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q r : Paper.Overlap) (e : Fin n) :
    (anisotropicMeasureSampleLaw D μ a)[(fun p=>(anisotropicProcessSpinResponse D μ r e p)^2)|
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSampleLaw D μ a]
      anisotropicPastSpinSquareKernel D μ a q r e := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n):=inferInstance
  let P:=anisotropicMeasureSampleLaw D μ a
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  let F:=fun f : AnisotropicContinuousSpinPath=>(anisotropicSpinPathEval r f)^2
  have hF : Measurable F:=((continuous_anisotropicSpinPathEval.measurable.comp
    ((measurable_const (a:=r)).prodMk measurable_id)).pow_const 2)
  have hb (f : AnisotropicContinuousSpinPath) : ‖F f‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicSpinPathEval_bound r f) 2).trans_eq (by norm_num)
  have hi : Integrable (fun p=>F (anisotropicContinuousSpinPath D μ e p)) P:=
    (integrable_const (1:ℝ)).mono' (hF.comp (measurable_anisotropicContinuousSpinPath D μ e)).aestronglyMeasurable
      (.of_forall fun p=>hb _)
  have he:= @condExp_ae_eq_integral_condDistrib
    (AnisotropicDisorderBrownianSample n) (AnisotropicDisorderBrownianSample n) AnisotropicContinuousSpinPath ℝ
    inferInstance inferInstance inferInstance inferInstance ambient P inferInstance
    id (anisotropicContinuousSpinPath D μ e) V inferInstance inferInstance
    (@measurable_id'' (AnisotropicDisorderBrownianSample n) V ambient ((anisotropicBrownianFiltration n).le _))
    (measurable_anisotropicContinuousSpinPath D μ e).aemeasurable F hF.stronglyMeasurable hi
  unfold anisotropicPastSpinSquareKernel
  simpa only [MeasurableSpace.comap_id,id_eq,F,anisotropicSpinPathEval_actual,
    anisotropicPastSpinSquareKernel,P,V,anisotropicPastSpinPathKernel] using he

theorem anisotropicPastSpinSquareKernel_weighted_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (e : Fin n)
    (Z : AnisotropicDisorderBrownianSample n→ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ≥0) (hB : ∀p,‖Z p‖ ≤ B) :
    (∫p,Z p*anisotropicPastSpinSquareKernel D μ a q r e p ∂anisotropicMeasureSampleLaw D μ a)=
      ∫p,Z p*(anisotropicProcessSpinResponse D μ r e p)^2 ∂anisotropicMeasureSampleLaw D μ a := by
  let P:=anisotropicMeasureSampleLaw D μ a
  have hZm:=hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hi : Integrable (fun p=>(anisotropicProcessSpinResponse D μ r e p)^2) P :=
    (integrable_const (1:ℝ)).mono' ((measurable_anisotropicProcessSpinResponse D μ r e).pow_const 2).aestronglyMeasurable
      (.of_forall fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessSpinResponse_bound D μ r e p) 2).trans_eq (by norm_num))
  have hp : Integrable (Z*(fun p=>(anisotropicProcessSpinResponse D μ r e p)^2)) P :=
    by simpa only [Pi.mul_def,mul_comm] using hi.mul_bdd hZm.aestronglyMeasurable (.of_forall hB)
  exact (weighted_kernelObservable_of_condExp_integrable (anisotropicBrownianFiltration n (q:ℝ).toNNReal)
    P ((anisotropicBrownianFiltration n).le _) _ _ hi (anisotropicPastSpinSquareKernel_condExp D μ a q r e)
    Z hZ.stronglyMeasurable hp).symm

end QuantitativeFollowup
