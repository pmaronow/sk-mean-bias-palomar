module
public import HexagonPaper.EdgeLikelihoodPathKernelEndpoint
public import HexagonPaper.EdgeLikelihoodClosedAction

@[expose] public section

/-! Literal source edge exponent with the actual input vertex field.
The Gaussian path starts at that field. The equality is proved on the
actual reference kernel, so its density is valid without a path-coherence
hypothesis on the final tree density theorem. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem anisotropicObservationParameter_edgeInverse (D : AnisotropicSpinModel n)
    (P : AnisotropicParameter n):
    anisotropicObservationParameter D (edgeObservationParameterInverse D P)=P:=by
  change anisotropicDisorderInjection n (edgeParameterDisorderProjection n P)+
    anisotropicUnitInput D (anisotropicInverseNoiseMap D (edgeParameterFieldProjection n P))=P
  unfold anisotropicUnitInput
  rw [ContinuousLinearMap.comp_apply,anisotropicNoiseMap_inverseNoise]
  ext i
  cases i <;> simp [anisotropicDisorderInjection,anisotropicFieldInjection,
    edgeParameterDisorderProjection,edgeParameterFieldProjection]

theorem anisotropicObservationParameter_edgePathEndpoint (D : AnisotropicSpinModel n)
    (h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)):
    anisotropicObservationParameter D (edgePathEndpoint D h Z)=Z h:=
  anisotropicObservationParameter_edgeInverse D (Z h)

theorem edgeStoppedReferencePath_start (D : AnisotropicSpinModel n)
    (q h : Paper.Overlap) (hqh : q≤h) (x : AnisotropicObservationState n)
    (sample : VectorDisorderBrownianSample n):
    edgeStoppedReferencePath D x.1 q h x.2 sample q=anisotropicObservationParameter D x:=by
  have hs:edgeStopOverlap h q=q:=Subtype.ext (min_eq_left hqh)
  change anisotropicDisorderInjection n x.1+anisotropicUnitInput D x.2+
    anisotropicUnitInput D (disorderVectorBrownian
      (((edgeStopOverlap h q:Paper.Overlap):ℝ)-(q:ℝ)).toNNReal sample)=_
  rw [hs,sub_self,Real.toNNReal_zero]
  simp only [disorderVectorBrownian,vectorBrownian_zero,map_zero,add_zero]
  rfl

def edgePathSourceLog (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (x : AnisotropicObservationState n)
    (Z : C(Paper.Overlap,AnisotropicParameter n)):ℝ:=
  Paper.parisiCDF μ h*anisotropicMeasureTailPotential D μ h (Z h)-
    Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (anisotropicObservationParameter D x)-
    ∫r in Ioc q h,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap)

theorem measurable_edgePathSourceLog (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap):Measurable (Function.uncurry (edgePathSourceLog D μ q h)):=by
  have hj:Measurable (fun p:C(Paper.Overlap,AnisotropicParameter n)×Paper.Overlap=>
      anisotropicMeasureTailPotential D μ p.2 (p.1 p.2)):=by
    let A:=edgeTailPotentialMap D μ
    have hev:Continuous (fun p:C(Paper.Overlap,AnisotropicParameter n)×Paper.Overlap=>p.1 p.2):=
      continuous_eval
    let P:C(C(Paper.Overlap,AnisotropicParameter n)×Paper.Overlap,
      Paper.Overlap×AnisotropicParameter n):=⟨fun p=>(p.2,p.1 p.2),continuous_snd.prodMk hev⟩
    convert (A.comp P).continuous.measurable using 1
    rfl
  have hi:Measurable (fun Z:C(Paper.Overlap,AnisotropicParameter n)=>
      ∫r in Ioc q h,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap)):=
    hj.stronglyMeasurable.integral_prod_right'.measurable
  have hh:Measurable (fun Z:C(Paper.Overlap,AnisotropicParameter n)=>
      anisotropicMeasureTailPotential D μ h (Z h)):=by
    let P:C(C(Paper.Overlap,AnisotropicParameter n),Paper.Overlap×AnisotropicParameter n):=
      ⟨fun Z=>(h,Z h),continuous_const.prodMk (continuous_eval_const h)⟩
    convert ((edgeTailPotentialMap D μ).comp P).continuous.measurable using 1
    rfl
  have hq:Measurable (fun x:AnisotropicObservationState n=>
      anisotropicMeasureTailPotential D μ q (anisotropicObservationParameter D x)):=by
    have hpair:Measurable (fun x:AnisotropicObservationState n=>
        (q,anisotropicObservationParameter D x)):=
      measurable_const.prodMk (measurable_anisotropicObservationParameter D)
    convert (edgeTailPotentialMap D μ).continuous.measurable.comp hpair using 1
    rfl
  have hscaledh:Measurable (fun Z:C(Paper.Overlap,AnisotropicParameter n)=>
      Paper.parisiCDF μ h*anisotropicMeasureTailPotential D μ h (Z h)):=measurable_const.mul hh
  have hscaledq:Measurable (fun x:AnisotropicObservationState n=>
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (anisotropicObservationParameter D x)):=
    measurable_const.mul hq
  convert ((hscaledh.comp measurable_snd).sub
    (hscaledq.comp measurable_fst)).sub (hi.comp measurable_snd) using 1
  rfl

theorem edgePhysicalPathKernel_source_exp_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q≤h):
    edgePhysicalPathKernel D μ q h=(edgeReferencePathKernel D q h).withDensity
      (fun x Z=>ENNReal.ofReal (Real.exp (edgePathSourceLog D μ q h x Z))) := by
  rw [edgePhysicalPathKernel_exp_density D μ q h hqh]
  have hf:Measurable (Function.uncurry (fun (_:AnisotropicObservationState n) Z=>
      ENNReal.ofReal (Real.exp (edgePathLogDensity D μ q h Z)))):=by
    convert ((continuous_edgePathLogDensity D μ q h).measurable.comp
      (measurable_snd : Measurable (fun p:AnisotropicObservationState n×C(Paper.Overlap,AnisotropicParameter n)=>p.2))).exp.ennreal_ofReal using 1
    rfl
  have hg:Measurable (Function.uncurry (fun x Z=>
      ENNReal.ofReal (Real.exp (edgePathSourceLog D μ q h x Z)))):=by
    convert (measurable_edgePathSourceLog D μ q h).exp.ennreal_ofReal using 1
    rfl
  apply Kernel.withDensity_congr_ae (edgeReferencePathKernel D q h) hf hg
  intro x
  have hlog:edgePathLogDensity D μ q h =ᵐ[edgeReferencePathKernel D q h x]
      edgePathSourceLog D μ q h x:=by
    rw [edgeReferencePathKernel_apply]
    have hsource:Measurable (edgePathSourceLog D μ q h x):=by
      convert (measurable_edgePathSourceLog D μ q h).comp
        (measurable_prodMk_left : Measurable (fun Z:C(Paper.Overlap,AnisotropicParameter n)=>(x,Z))) using 1
      rfl
    apply (ae_map_iff (measurable_edgeStoppedReferencePath D x.1 q h x.2).aemeasurable
      (measurableSet_eq_fun (continuous_edgePathLogDensity D μ q h).measurable hsource)).2
    filter_upwards with sample
    rw [edgePathLogDensity_eq_closed_endpoints D μ q h hqh]
    rw [edgeStoppedReferencePath_start D q h hqh x sample]
    rfl
  exact hlog.fun_comp (fun r:ℝ=>ENNReal.ofReal (Real.exp r))

end HexagonPaper
