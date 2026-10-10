module
public import QuantitativePaper.VectorProfileTraceTimeGrowth
public import QuantitativePaper.VectorCompactSmoothItoTestJets
public import FourPapersCommon.ExponentialAffineChange

@[expose] public section

/-! Actual full profile jet envelopes give the precise field and time
growth bounds required by the localized finite-diffusion Dynkin theorem. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorProfileTestRestriction (θ : ℝ)
    (F : VectorProfileCellParameter n×Field n→ℝ) (z : VectorCompactTestParameter n) : ℝ:=
  F ((z.1,θ,z.2.1),z.2.2)

theorem vectorProfileTestRestriction_exponential_bounds
    (F : VectorProfileCellParameter n×Field n→ℝ) (l u a b θ : ℝ)
    (hf : ExponentialSmoothOn F (vectorProfileJointCylinder l u a b))
    (hl : 0≤l) (hu : u≤1) (ha : 0<a) (hb : b<1) (hθ : θ∈Ioo a b) :
    ContDiffOn ℝ ∞ (vectorProfileTestRestriction θ F) (Prod.fst ⁻¹' Ioo l u) ∧
    ∃B K : ℝ,0≤B ∧ 0≤K ∧
      (∀q∈Ioo l u,∀p : Couplings n×ℝ,∀x : Field n,∀r : ℕ,r≤2→
        ‖iteratedFDeriv ℝ r (fun y=>vectorProfileTestRestriction θ F (q,(p,y))) x‖≤
          B*Real.exp (K*(‖p‖+‖x‖))) ∧
      (∀q∈Ioo l u,∀p : Couplings n×ℝ,∀x : Field n,
        ‖vectorCompactSmoothTimeField (vectorProfileTestRestriction θ F) (q,(p,x))‖≤
          B*Real.exp (K*(‖p‖+‖x‖))) := by
  have hMem (q : ℝ) (hq : q∈Ioo l u) (p : Couplings n×ℝ) (x : Field n) :
      ((q,θ,p),x)∈vectorProfileJointCylinder l u a b:=⟨hq,hθ⟩
  have hSmooth (z : VectorCompactTestParameter n) (hz : z∈Prod.fst ⁻¹' Ioo l u) :
      ContDiffAt ℝ ∞ (vectorProfileTestRestriction θ F) z:=
    (hf.smooth _ (hMem z.1 hz z.2.1 z.2.2)).comp z
      ((contDiffAt_fst.prodMk (contDiffAt_const.prodMk (contDiffAt_fst.comp z contDiffAt_snd))).prodMk
        (contDiffAt_snd.comp z contDiffAt_snd))
  obtain ⟨C,R,hC,hR,hBound⟩:=hf.common_bound 2
  have hNorm (q : ℝ) (hq : q∈Ioo l u) (p : Couplings n×ℝ) (x : Field n) :
      ‖((q,θ,p),x)‖≤1+‖p‖+‖x‖:=by
    have hqabs : |q|≤1:=abs_le.mpr ⟨by linarith [hq.1],by linarith [hq.2]⟩
    have hθabs : |θ|≤1:=abs_le.mpr ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
    change max (max |q| (max |θ| ‖p‖)) ‖x‖≤1+‖p‖+‖x‖
    have hOne : 1≤1+‖p‖+‖x‖:=by linarith [norm_nonneg p,norm_nonneg x]
    apply max_le
    · apply max_le
      · exact hqabs.trans hOne
      · apply max_le
        · exact hθabs.trans hOne
        · linarith [norm_nonneg p,norm_nonneg x]
    · linarith [norm_nonneg p,norm_nonneg x]
  have hExp (q : ℝ) (hq : q∈Ioo l u) (p : Couplings n×ℝ) (x : Field n) :
      C*Real.exp (R*‖((q,θ,p),x)‖)≤(C*Real.exp R)*Real.exp (R*(‖p‖+‖x‖)):=by
    calc
      _≤C*Real.exp (R*(1+‖p‖+‖x‖)):=by gcongr;exact hNorm q hq p x
      _=_:=by rw [show R*(1+‖p‖+‖x‖)=R+R*(‖p‖+‖x‖) by ring,Real.exp_add];ring
  refine ⟨fun z hz=>(hSmooth z hz).contDiffWithinAt,C*Real.exp R,R,by positivity,hR,?_,?_⟩
  · intro q hq p x r hr
    let L:=ContinuousLinearMap.inr ℝ (VectorProfileCellParameter n) (Field n)
    have hA:=norm_iteratedFDeriv_precomp_affine_le_at L ((q,θ,p),0) F x
      (by simpa only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using
        hf.smooth _ (hMem q hq p x)) r
    change ‖iteratedFDeriv ℝ r (fun y=>F ((q,θ,p),y)) x‖≤_
    simp only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] at hA
    apply hA.trans
    apply (mul_le_mul_of_nonneg_right (hBound r hr _ (hMem q hq p x))
      (pow_nonneg (norm_nonneg _) _)).trans
    have hL : ‖L‖^r≤1:=by
      simpa using pow_le_one₀ (norm_nonneg L) (ContinuousLinearMap.norm_inr_le_one ℝ (VectorProfileCellParameter n) (Field n))
    exact (mul_le_mul_of_nonneg_left hL (by positivity)).trans (by simpa only [mul_one] using hExp q hq p x)
  · intro q hq p x
    have hLine : HasDerivAt (fun r : ℝ=>((r,θ,p),x)) ((1,(0,0)),0) q:=
      ((hasDerivAt_id q).prodMk (hasDerivAt_const q (θ,p))).prodMk (hasDerivAt_const q x)
    have hRaw:=((hf.smooth _ (hMem q hq p x)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q hLine
    have hTestLine : HasDerivAt (fun r=>vectorProfileTestRestriction θ F (r,(p,x)))
        (vectorCompactSmoothTimeField (vectorProfileTestRestriction θ F) (q,(p,x))) q:=
      by
        have hD : HasFDerivAt (vectorProfileTestRestriction θ F)
            (fderiv ℝ (vectorProfileTestRestriction θ F) (q,(p,x))) (q,(p,x)):=
          ((hSmooth (q,(p,x)) hq).differentiableAt (by simp)).hasFDerivAt
        exact hD.comp_hasDerivAt q ((hasDerivAt_id q).prodMk (hasDerivAt_const q (p,x)))
    have he:=hTestLine.unique hRaw
    rw [he]
    apply ((fderiv ℝ F ((q,θ,p),x)).le_opNorm _).trans
    have hd : ‖(((1,(0,0)),0) : VectorProfileCellParameter n×Field n)‖=1:=by simp
    rw [hd,mul_one]
    have hDeriv : ‖fderiv ℝ F ((q,θ,p),x)‖≤C*Real.exp (R*‖((q,θ,p),x)‖):=by
      simpa only [norm_iteratedFDeriv_one] using (hBound 1 (by norm_num) _ (hMem q hq p x))
    exact hDeriv.trans (hExp q hq p x)

end QuantitativePaper
