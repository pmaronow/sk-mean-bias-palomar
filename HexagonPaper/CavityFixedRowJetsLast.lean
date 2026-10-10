module
public import HexagonPaper.CavityFixedRowJetsCalculus
public import QuantitativeFollowup.SupportingPrintedCavityNativeRowDefinitions
public import Paper.ParisiCurvature

@[expose] public section

/-! Literal arbitrary-profile first isolated-spin observable derivative.
The incident coupling differentiates in the true unit chart, not a vanished
Gaussian coefficient. The scalar Hessian comes from the native separated
potential, and mixed derivatives commute by actual C-infinity regularity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem cavityFixedRow_native_pair_last_derivative (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    fderiv ℝ (fun Q=>anisotropicTailPairResponse D μ q Q (anisotropicCavityRowIndex n i)) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n))=
        anisotropicMeasureTailMagnetization R μ q (cavityRestParameterProjection n P) i*
          Paper.parisiHessian (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let P:=anisotropicParameterPoint g x
  let b:=anisotropicCoordinateDirection (n+1) (Fin.last n)
  let Mi:=anisotropicMeasureTailMagnetization R μ q (cavityRestParameterProjection n P) i
  have hb : cavityRestParameterProjection n b=0 := by
    ext l
    cases l <;> simp [b,cavityRestParameterProjection,anisotropicCoordinateDirection,
      anisotropicFieldInjection,EuclideanSpace.single_apply]
  have hpoint (t : ℝ) : P+t • b=anisotropicParameterPoint g
      (x+t • EuclideanSpace.single (Fin.last n) 1) := by
    change anisotropicParameterPoint g x+t • anisotropicFieldInjection (n+1)
      (EuclideanSpace.single (Fin.last n) 1)=_
    rw [←(anisotropicFieldInjection (n+1)).map_smul,cavityAnisotropicPoint_add_field]
  have he (t : ℝ) : anisotropicTailPairResponse D μ q (P+t • b) (anisotropicCavityRowIndex n i)=
      Mi*Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n)+t) := by
    dsimp only [D]
    rw [cavityFixedRow_native_tail_pair_product]
    simp only [map_add,map_smul,hb,smul_zero,add_zero]
    rw [hpoint,followupCavityMeasureGradient_last_zero]
    simp [Mi,R,P,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.single_apply]
  have hl:=hasDerivAt_affine_line_of_differentiable
    (fun Q=>anisotropicTailPairResponse D μ q Q (anisotropicCavityRowIndex n i))
    ((contDiff_cavityFixedRow_native_pair_response D μ q _).differentiable (by simp)) P b 0
  have hs:HasDerivAt (fun t : ℝ=>Mi*Paper.parisiGradient
      (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n)+t))
      (Mi*Paper.parisiHessian (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))) 0 := by
    have hh:=Paper.hasDerivAt_parisiGradient_spatial (followupCavityScalarBeta n β ρ)
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ (q:ℝ) (x (Fin.last n))
    have hc:=hh.comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_add (x (Fin.last n))) (by simp)
    simpa only [Paper.parisiHessianBCF_apply,Function.comp_def,id_eq,mul_one] using hc.const_mul Mi
  simp_rw [he] at hl
  have hh:=hl.unique hs
  simpa only [zero_smul,add_zero,D,R,P,b,Mi] using hh

def cavityFixedRowNativeLastSquare (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter (n+1)) (i : Fin n) (θ : ℝ) : ℝ :=
  (fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
    (anisotropicCouplingRescaling D P+θ • anisotropicCouplingDirection (anisotropicCavityRowIndex n i))
    (anisotropicCoordinateDirection (n+1) (Fin.last n)))^2

theorem cavityFixedRow_native_lastSquare_first (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    deriv (cavityFixedRowNativeLastSquare D μ q P i) 0=
      2*Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))*
        Paper.parisiHessian (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))*
          anisotropicMeasureTailMagnetization R μ q (cavityRestParameterProjection n P) i := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  let P:=anisotropicParameterPoint g x
  let H:=anisotropicCouplingRescaling D P
  let e:=anisotropicCavityRowIndex n i
  let K:=anisotropicCouplingDirection e
  let b:=anisotropicCoordinateDirection (n+1) (Fin.last n)
  have hU:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have hF:ContDiff ℝ ∞ (fun Q=>(fderiv ℝ U Q b)^2):=
    ((hU.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).pow 2
  change deriv (fun θ=>(fderiv ℝ U (H+θ • K) b)^2) 0=_
  rw [cavityPrintedFiniteRow_deriv_affine_line _ (hF.differentiable (by simp)),zero_smul,add_zero,
    cavityNativeSquare_first _ ((hU.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const)]
  rw [cavityFixedRow_native_field_unitCouplings D μ q P,
    followupCavityMeasureGradient_last_zero,
    cavityFixedRow_native_magnetization_row_first D μ q P e (Fin.last n),
    cavityFixedRow_native_pair_last_derivative μ n β ρ hβ hρ q g x i]
  ring

end HexagonPaper
