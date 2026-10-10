module
public import HexagonPaper.VariableScalarClockDriverCoefficients
public import HexagonPaper.VariableScalarClockCoefficientState
public import HexagonPaper.VariableScalarClockStateLikelihood
public import HexagonPaper.ItoGaussianClockLaw

@[expose] public section

/-! Literal positive bounded measurable coefficient extension. The noise
is a true continuous realization of ∫sqrt(c)dB, its clock law is proved
from actual Wiener covariance, and the physical state is the true Picard
solution of the corresponding variable-coefficient drift equation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus FourPapersCommon
open Paper FRSB QuantitativeFollowup QuantitativePaper
open scoped Topology ENNReal NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem scalar_positive_bounded_coefficient_likelihoods
    (c : ℝ→ℝ) (hc : Measurable c) (M : ℝ)
    (hM : ∀q∈Icc (0:ℝ) 1,‖c q‖≤M)
    (hpos : ∀q∈Icc (0:ℝ) 1,0<c q) :
    let hint:=scalarCoefficient_intervalIntegrable c M hc.aestronglyMeasurable hM
    let hp:∀q∈Ioo (0:ℝ) 1,0<c q:=fun q hq=>hpos q ⟨hq.1.le,hq.2.le⟩
    let τ:=scalarCoefficientClock c hint hp
    let β:=Real.sqrt (scalarCoefficientPrimitive c 1)
    ∃L : Paper.BrownianSample→C(Paper.Overlap,ℝ),Measurable L ∧
      (∀q : Paper.Overlap,
        (naturalItoProcess Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (fun t=>(Paper.measurable_canonicalBrownian t).stronglyMeasurable) rfl
          (deterministicPredictableEmbedding (P:=Paper.canonicalBrownianMeasure)
            (Filtration.natural Paper.canonicalBrownian
              (fun t=>(Paper.measurable_canonicalBrownian t).stronglyMeasurable))
            (scalarCoefficientLp c hc M hM)) (q:ℝ).toNNReal : Paper.BrownianSample→ℝ)
              =ᵐ[Paper.canonicalBrownianMeasure] (fun sample=>L sample q)) ∧
      canonicalBrownianMeasure.map L=
        canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β 1) ∧
      (∀μ : Paper.ParisiMeasure,
        Measurable (fun sample=>scalarCoefficientStateFromNoise c hint hp μ (L sample)) ∧
        (∀sample q,scalarCoefficientStateFromNoise c hint hp μ (L sample) q=L sample q+
          ∫r in (0:ℝ)..(q:ℝ),c r*parisiCDF μ r*
            scalarCoefficientSpatialField c hint hp μ 1
              (r,scalarCoefficientStateFromNoise c hint hp μ (L sample)
                (projIcc 0 1 zero_le_one r))) ∧
        (∀q : Paper.Overlap,
          canonicalBrownianMeasure.map
            (fun sample=>scalarClockPathStop q
              (scalarCoefficientStateFromNoise c hint hp μ (L sample)))=
            (canonicalBrownianMeasure.map (fun sample=>scalarClockPathStop q (L sample))).withDensity
              (scalarClockPrefixPathDensity τ β μ q)) ∧
        (∀a : ℝ,a∈Icc (0:ℝ) 1→μ∈scalarFloor a→
          (canonicalBrownianMeasure.map
            (fun sample=>scalarCoefficientStateFromNoise c hint hp μ (L sample)))
              ⊗ₘ scalarFullPathSpinKernel=
            ((canonicalBrownianMeasure.map L).prod (Measure.count:Measure Bool)).withDensity
              (scalarClockJointPathDensity τ β μ a))) := by
  dsimp only
  let hint:=scalarCoefficient_intervalIntegrable c M hc.aestronglyMeasurable hM
  let hp:∀q∈Ioo (0:ℝ) 1,0<c q:=fun q hq=>hpos q ⟨hq.1.le,hq.2.le⟩
  let τ:=scalarCoefficientClock c hint hp
  let β:=Real.sqrt (scalarCoefficientPrimitive c 1)
  have hβ:β≠0:=(scalarCoefficientClock_temperature c hint hp).1.ne'
  obtain ⟨L,hL,hIto,hLaw⟩:=exists_deterministicIto_continuous_clock_law
    (scalarCoefficientLp c hc M hM) τ β
      (scalarCoefficientLp_clock_gram c hc M hM hp hint)
  refine ⟨L,hL,hIto,hLaw,?_⟩
  intro μ
  refine ⟨(continuous_scalarClockStateFromNoise τ β μ).measurable.comp hL,?_,?_,?_⟩
  · intro sample q
    exact scalarCoefficientStateFromNoise_integral_equation c hint hpos μ (L sample) q
  · intro q
    exact scalarClockStateFromNoise_likelihood L hL τ β hβ μ q hLaw
  · intro a ha hμ
    exact scalarClockStateFromNoise_joint_likelihood L hL τ β hβ μ a ha hμ hLaw

end HexagonPaper
