module
public import HexagonPaper.CavityFixedRowJetsLast

@[expose] public section

/-! Literal second incident-row derivative of the isolated-spin observable
for every profile, with the actual spatial derivative of its row Hessian. -/
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

theorem cavityFixedRow_native_pair_second_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) (i : Fin n) :
    let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
    let K:=anisotropicCouplingDirection e
    fderiv ℝ (fun Q=>fderiv ℝ (fun R=>fderiv ℝ U R K) Q K)
      (anisotropicCouplingRescaling D P) (anisotropicCoordinateDirection n i)=
      fderiv ℝ (fun Q=>anisotropicTailPairSecond D μ q Q e) P
        (anisotropicCoordinateDirection n i) := by
  dsimp only
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  let K:=anisotropicCouplingDirection e
  let A:=fun Q=>fderiv ℝ (fun R=>fderiv ℝ U R K) Q K
  have hU:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have hA:ContDiff ℝ ∞ A:=by
    exact (((hU.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).fderiv_right
      (m:=∞) (by simp)).clm_apply contDiff_const
  have he : (fun Q=>anisotropicTailPairSecond D μ q Q e)=A ∘ anisotropicCouplingRescaling D := by
    funext Q
    change fderiv ℝ (fderiv ℝ U) (anisotropicCouplingRescaling D Q) K K=
      fderiv ℝ (fun R=>fderiv ℝ U R K) (anisotropicCouplingRescaling D Q) K
    rw [(hasFDerivAt_exponential_directional_field U (hU.of_le (by simp))
      (anisotropicCouplingRescaling D Q) K).fderiv,ContinuousLinearMap.flip_apply]
    rfl
  rw [he,fderiv_comp P (hA.differentiable (by simp) _) (anisotropicCouplingRescaling D).differentiableAt,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv]
  rw [show anisotropicCouplingRescaling D (anisotropicCoordinateDirection n i)=
      anisotropicCoordinateDirection n i from anisotropicCouplingRescaling_field D _]

theorem cavityFixedRow_native_lastSquare_second (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Mi:=anisotropicMeasureTailMagnetization R μ q (cavityRestParameterProjection n P) i
    let m:=Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
    let h:=Paper.parisiHessian (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
    deriv (deriv (cavityFixedRowNativeLastSquare D μ q P i)) 0=
      2*Mi^2*h^2+2*m*fderiv ℝ (fun Q=>anisotropicTailPairSecond D μ q Q (anisotropicCavityRowIndex n i))
        P (anisotropicCoordinateDirection (n+1) (Fin.last n)) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  let P:=anisotropicParameterPoint g x
  let H:=anisotropicCouplingRescaling D P
  let e:=anisotropicCavityRowIndex n i
  let K:=anisotropicCouplingDirection e
  let b:=anisotropicCoordinateDirection (n+1) (Fin.last n)
  let F:=fun Q=>(fderiv ℝ U Q b)^2
  have hU:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have hF:ContDiff ℝ ∞ F:=((hU.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).pow 2
  change deriv (deriv (fun θ=>F (H+θ • K))) 0=_
  rw [cavityPrintedFiniteRow_deriv_deriv_affine_line F hF H K]
  change fderiv ℝ (fderiv ℝ F) H K K=_
  rw [←show fderiv ℝ (fun Q=>fderiv ℝ F Q K) H K=fderiv ℝ (fderiv ℝ F) H K K by
    rw [(hasFDerivAt_exponential_directional_field F (hF.of_le (by simp)) H K).fderiv]
    rfl]
  rw [cavityNativeDirectionalSquare_second U hU H b K]
  rw [cavityFixedRow_native_field_unitCouplings D μ q P,
    followupCavityMeasureGradient_last_zero]
  rw [←cavity_directional_second_symmetry U hU H b K,
    cavityFixedRow_native_magnetization_row_first D μ q P e (Fin.last n),
    cavityFixedRow_native_pair_last_derivative μ n β ρ hβ hρ q g x i,
    cavityFixedRow_native_pair_second_field D μ q P e (Fin.last n)]
  ring

end HexagonPaper
