module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFutureLastDerivative

@[expose] public section

/-! Pointwise evaluation of the genuine finite future differential at the
actual native zero-row state. Repeated original nodes remain present;
no almost-everywhere identity is differentiated. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem cavityFiniteIncidentFutureSquare_average_last_derivative_at_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J p : ℕ) (hJ : J≤k+2) (hp : p≤J)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let r:=anisotropicSchemeNode s (k+2-p) (by omega)
    let z:=cavityRestSampleProjection n sample
    let hqr : (q:ℝ)≤r:=s.q_mono' _ (by omega) _ (by omega)
    fderiv ℝ (fun P=>(∑i : Fin n,cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ))
      (anisotropicProcessParameter D μ q sample) (anisotropicCoordinateDirection (n+1) (Fin.last n))=
      cavityRestFutureSquare Rest μ q r z*
        scalarFutureSquareDerivative (followupCavityScalarBeta n β ρ) μ q r hqr
          (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
            (sample.2 (Fin.last n))) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let r:=anisotropicSchemeNode s (k+2-p) (by omega)
  let z:=cavityRestSampleProjection n sample
  have hqr : q≤r:=s.q_mono' _ (by omega) _ (by omega)
  have hrest : cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample)=
      anisotropicDisorderInjection n z.1+
        anisotropicFieldInjection n (anisotropicMeasureState Rest μ q z) := by
    rw [cavityRestProcessParameter_zero μ n β ρ hβ hρ q sample]
    rfl
  have hlast : anisotropicProcessParameter D μ q sample (Sum.inr (Fin.last n))=
      parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
        (sample.2 (Fin.last n)) :=
    cavityZeroLastProcessParameter_eq_scalarState μ n β ρ hβ hρ q sample
  rw [cavityRestFutureSquare_eq_restartMeanSquare Rest μ q r hqr z]
  exact cavityFiniteIncidentFutureSquare_average_last_derivative s n β ρ hβ hρ J p hJ hp
    (anisotropicProcessParameter D μ q sample) z.1 (anisotropicMeasureState Rest μ q z)
    (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q (sample.2 (Fin.last n)))
    hrest hlast q r rfl rfl hqr

theorem cavityFiniteIncidentFutureSquare_average_old_derivative_at_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J p : ℕ) (hJ : J≤k+2) (hp : p≤J)
    (sample : AnisotropicDisorderBrownianSample (n+1)) (l : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let r:=anisotropicSchemeNode s (k+2-p) (by omega)
    let z:=cavityRestSampleProjection n sample
    let hqr : (q:ℝ)≤r:=s.q_mono' _ (by omega) _ (by omega)
    fderiv ℝ (fun P=>(∑i : Fin n,cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ))
      (anisotropicProcessParameter D μ q sample) (anisotropicCoordinateDirection (n+1) l.castSucc)=
      scalarFutureSquareProcess (followupCavityScalarBeta n β ρ) μ q r hqr
        (sample.2 (Fin.last n))*
      fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ z.1 q x r)
        (anisotropicMeasureState Rest μ q z) (EuclideanSpace.single l 1) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let r:=anisotropicSchemeNode s (k+2-p) (by omega)
  let z:=cavityRestSampleProjection n sample
  have hqr : q≤r:=s.q_mono' _ (by omega) _ (by omega)
  have hrest : cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample)=
      anisotropicDisorderInjection n z.1+
        anisotropicFieldInjection n (anisotropicMeasureState Rest μ q z) := by
    rw [cavityRestProcessParameter_zero μ n β ρ hβ hρ q sample]
    rfl
  have hlast : anisotropicProcessParameter D μ q sample (Sum.inr (Fin.last n))=
      parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
        (sample.2 (Fin.last n)) :=
    cavityZeroLastProcessParameter_eq_scalarState μ n β ρ hβ hρ q sample
  exact cavityFiniteIncidentFutureSquare_average_old_derivative s n β ρ hβ hρ J p hJ hp
    (anisotropicProcessParameter D μ q sample) z.1 (anisotropicMeasureState Rest μ q z)
    (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q (sample.2 (Fin.last n)))
    hrest hlast q r rfl rfl hqr l

end QuantitativeFollowup
