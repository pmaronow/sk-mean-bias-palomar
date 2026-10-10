module
public import HexagonPaper.EdgeLikelihoodPathKernel

@[expose] public section

/-! The full path kernel has the exact native recorded-tree endpoint
transition. Both the fixed disorder and the whitened field are recovered
from the physical parameter path, rather than introduced by a new law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def edgeParameterDisorderProjection (n : ℕ) : AnisotropicParameter n→L[ℝ]AnisotropicDisorder n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun P=>WithLp.toLp 2 (fun i=>P (Sum.inl i))
      map_add':=by intro x y;ext i;simp
      map_smul':=by intro c x;ext i;simp }

def edgeParameterFieldProjection (n : ℕ) : AnisotropicParameter n→L[ℝ]Field n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun P=>WithLp.toLp 2 (fun i=>P (Sum.inr i))
      map_add':=by intro x y;ext i;simp
      map_smul':=by intro c x;ext i;simp }

def edgeObservationParameterInverse (D : AnisotropicSpinModel n) :
    AnisotropicParameter n→L[ℝ]AnisotropicObservationState n :=
  (edgeParameterDisorderProjection n).prod
    ((anisotropicInverseNoiseMap D).comp (edgeParameterFieldProjection n))

theorem edgeObservationParameterInverse_apply (D : AnisotropicSpinModel n)
    (g : AnisotropicDisorder n) (x : Field n) :
    edgeObservationParameterInverse D
      (anisotropicDisorderInjection n g+anisotropicUnitInput D x)=(g,x) := by
  have hg:edgeParameterDisorderProjection n
      (anisotropicDisorderInjection n g+anisotropicUnitInput D x)=g:=by
    ext i
    simp [edgeParameterDisorderProjection,anisotropicDisorderInjection,
      anisotropicUnitInput,anisotropicFieldInjection]
  have hx:edgeParameterFieldProjection n
      (anisotropicDisorderInjection n g+anisotropicUnitInput D x)=anisotropicNoiseMap D x:=by
    ext i
    simp [edgeParameterFieldProjection,anisotropicDisorderInjection,
      anisotropicUnitInput,anisotropicFieldInjection]
  change (edgeParameterDisorderProjection n _,anisotropicInverseNoiseMap D
    (edgeParameterFieldProjection n _))=(g,x)
  rw [hg,hx,anisotropicInverseNoiseMap_noise]

def edgePathEndpoint (D : AnisotropicSpinModel n) (h : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) : AnisotropicObservationState n :=
  edgeObservationParameterInverse D (Z h)

theorem measurable_edgePathEndpoint (D : AnisotropicSpinModel n) (h : Paper.Overlap) :
    Measurable (edgePathEndpoint D h) :=
  (edgeObservationParameterInverse D).measurable.comp (ContinuousMap.measurable_eval h)

theorem edgePathEndpoint_noise (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (hqh : q≤h) (z : AnisotropicRestartNoiseData n) :
    edgePathEndpoint D h (edgeNoiseStoppedPath D μ q h z)=
      anisotropicObservationNoiseAdvance D μ q h z := by
  unfold edgePathEndpoint
  change edgeObservationParameterInverse D
    (anisotropicDisorderInjection n z.1.1+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D μ q z ((min (h:ℝ) (h:ℝ)-(q:ℝ)).toNNReal:ℝ)))=_
  rw [edgeObservationParameterInverse_apply,min_self,
    Real.coe_toNNReal _ (sub_nonneg.mpr hqh)]
  rfl

theorem edgePhysicalPathKernel_endpoint_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q≤h) :
    (edgePhysicalPathKernel D μ q h).map (edgePathEndpoint D h)=
      anisotropicObservationTransition D μ q h := by
  ext z : 1
  rw [Kernel.map_apply _ (measurable_edgePathEndpoint D h),edgePhysicalPathKernel_apply,
    Measure.map_map (measurable_edgePathEndpoint D h)
      (measurable_edgeStoppedDiffusionPath D μ z.1 q h z.2),
    anisotropicObservationTransition_apply]
  have hc:HasLaw (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n):=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  have hm:Measurable (fun W=>anisotropicObservationNoiseAdvance D μ q h (z,W)):=
    (measurable_anisotropicObservationNoiseAdvance D μ q h).comp measurable_prodMk_left
  rw [←hc.map_eq]
  change Measure.map (edgePathEndpoint D h ∘ edgeStoppedDiffusionPath D μ z.1 q h z.2)
      (vectorDisorderBrownianMeasure n)=
    Measure.map (fun W=>anisotropicObservationNoiseAdvance D μ q h (z,W))
      (Measure.map (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
        (vectorDisorderBrownianMeasure n))
  have hcanon:Measurable (fun p:VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2):=by
    convert measurable_vectorCanonicalBrownianPath.comp measurable_snd using 1
    rfl
  rw [Measure.map_map hm hcanon]
  congr 1
  funext sample
  change edgePathEndpoint D h (edgeStoppedDiffusionPath D μ z.1 q h z.2 sample)=_
  rw [←edgeNoiseStoppedPath_canonical,edgePathEndpoint_noise D μ q h hqh]
  rfl

end HexagonPaper
