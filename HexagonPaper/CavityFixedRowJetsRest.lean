module
public import HexagonPaper.CavityFixedRowJetsLastSecond

@[expose] public section

/-! Actual arbitrary-profile rest-spin row first derivatives at zero.
Every Hessian entry is a genuine field derivative of the native tail. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem cavityFixedRow_restDirection_projection (n : ℕ) (l : Fin n) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) l.castSucc)=
      anisotropicCoordinateDirection n l := by
  ext j
  cases j <;> simp [cavityRestParameterProjection,anisotropicCoordinateDirection,
    anisotropicFieldInjection,EuclideanSpace.single_apply]

theorem contDiff_cavityFixedRow_native_spin_response (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) :
    ContDiff ℝ ∞ (fun P=>anisotropicMeasureTailMagnetization D μ q P i) :=
  ((cavityTree_native_tail_smooth_and_jets D μ q).1.fderiv_right (m:=∞) (by simp)).clm_apply
    (contDiff_const (c:=anisotropicCoordinateDirection n i))

theorem cavityFixedRow_native_pair_rest_derivative (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i l : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Pr:=cavityRestParameterProjection n P
    fderiv ℝ (fun Q=>anisotropicTailPairResponse D μ q Q (anisotropicCavityRowIndex n i)) P
      (anisotropicCoordinateDirection (n+1) l.castSucc)=
        Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))*
          fderiv ℝ (fun Q=>anisotropicMeasureTailMagnetization R μ q Q i) Pr
            (anisotropicCoordinateDirection n l) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let P:=anisotropicParameterPoint g x
  let Pr:=cavityRestParameterProjection n P
  let b:=anisotropicCoordinateDirection (n+1) l.castSucc
  let br:=anisotropicCoordinateDirection n l
  let m:=Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
  let Mi:=fun Q=>anisotropicMeasureTailMagnetization R μ q Q i
  have hb : cavityRestParameterProjection n b=br := cavityFixedRow_restDirection_projection n l
  have hpoint (t : ℝ) : P+t • b=anisotropicParameterPoint g
      (x+t • EuclideanSpace.single l.castSucc 1) := by
    change anisotropicParameterPoint g x+t • anisotropicFieldInjection (n+1)
      (EuclideanSpace.single l.castSucc 1)=_
    rw [←(anisotropicFieldInjection (n+1)).map_smul,cavityAnisotropicPoint_add_field]
  have he (t : ℝ) : anisotropicTailPairResponse D μ q (P+t • b) (anisotropicCavityRowIndex n i)=
      Mi (Pr+t • br)*m := by
    dsimp only [D]
    rw [cavityFixedRow_native_tail_pair_product]
    simp only [map_add,map_smul,hb]
    rw [hpoint,followupCavityMeasureGradient_last_zero]
    simp [Mi,m,R,Pr,P,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.single_apply]
  have hl:=hasDerivAt_affine_line_of_differentiable
    (fun Q=>anisotropicTailPairResponse D μ q Q (anisotropicCavityRowIndex n i))
    ((contDiff_cavityFixedRow_native_pair_response D μ q _).differentiable (by simp)) P b 0
  have hr:=(hasDerivAt_affine_line_of_differentiable Mi
    ((contDiff_cavityFixedRow_native_spin_response R μ q i).differentiable (by simp)) Pr br 0).mul_const m
  simp_rw [he] at hl
  have hh:=hl.unique hr
  simpa only [zero_smul,add_zero,D,R,P,Pr,b,br,Mi,m,mul_comm] using hh

def cavityFixedRowNativeRestSquare (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter (n+1)) (i : Fin n) (θ : ℝ) : ℝ :=
  (n:ℝ)⁻¹*∑l : Fin n,(fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
    (anisotropicCouplingRescaling D P+θ • anisotropicCouplingDirection (anisotropicCavityRowIndex n i))
    (anisotropicCoordinateDirection (n+1) l.castSucc))^2

theorem cavityNativeSumSquares_first {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type} [Fintype ι] (F : ι→E→ℝ) (hF : ∀i,ContDiff ℝ ∞ (F i)) (H K : E) (c : ℝ) :
    fderiv ℝ (fun Q=>c*∑i,(F i Q)^2) H K=2*c*∑i,F i H*fderiv ℝ (F i) H K := by
  have hd (i : ι) : DifferentiableAt ℝ (fun Q=>(F i Q)^2) H:=
    ((hF i).differentiable (by simp) H).pow 2
  rw [fderiv_const_mul (DifferentiableAt.fun_sum (fun i _=>hd i)),ContinuousLinearMap.smul_apply,
    smul_eq_mul,fderiv_fun_sum (fun i _=>hd i),ContinuousLinearMap.sum_apply]
  simp_rw [cavityNativeSquare_first _ (hF _)]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum]
  ring

end HexagonPaper
