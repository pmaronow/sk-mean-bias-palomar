module
public import QuantitativePaper.VectorExponentialIto
public import FourPapersCommon.TimeCellLocalization

@[expose] public section

/-! Genuine exponential envelopes for the smooth extension of an
observable defined on a strict time cell. Outside the cutoff support all
jets vanish locally; inside the cell the actual product derivative applies. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem hasDerivAt_vectorCell_time {f : VectorCompactTestParameter n→ℝ}
    {q : ℝ} {p : Couplings n×ℝ} {x : Field n}
    (hf : ContDiffAt ℝ ∞ f (q,(p,x))) :
    HasDerivAt (fun r=>f (r,(p,x))) (vectorCompactSmoothTimeField f (q,(p,x))) q :=
  (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q
    ((hasDerivAt_id q).prodMk (hasDerivAt_const q (p,x)))

theorem vectorExponentialGenerator_congr_of_eventuallyEq
    (f g : VectorCompactTestParameter n→ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (hfg : f=ᶠ[𝓝 ((r:ℝ),(sample.1,X r sample))]g) :
    vectorExponentialGenerator f X d σ r sample=vectorExponentialGenerator g X d σ r sample := by
  have hs:=hfg.comp_tendsto (show ContinuousAt
    (fun y : Field n=>((r:ℝ),(sample.1,y))) (X r sample) from by fun_prop)
  dsimp only [Function.comp_def] at hs
  have hfirst:=hs.fderiv_eq (𝕜:=ℝ)
  have hsecond : vectorHessian (fun y=>f (r,(sample.1,y))) (X r sample)=
      vectorHessian (fun y=>g (r,(sample.1,y))) (X r sample):=
    (hs.fderiv (𝕜:=ℝ)).fderiv_eq
  have ht : vectorCompactSmoothTimeField f (r,(sample.1,X r sample))=
      vectorCompactSmoothTimeField g (r,(sample.1,X r sample)):=
    congrArg (fun L : VectorCompactTestParameter n→L[ℝ]ℝ=>L (1,(0,0))) (hfg.fderiv_eq (𝕜:=ℝ))
  simp only [vectorExponentialGenerator,hfirst,hsecond,ht]

theorem timeLocalized_vectorCell_exponential_bounds
    (ρ : ℝ→ℝ) (hρ : ContDiff ℝ ∞ ρ) (hsρ : HasCompactSupport ρ)
    (hρb : ∀q,‖ρ q‖≤1) (U : Set ℝ) (hU : IsOpen U) (hsU : tsupport ρ⊆U)
    (f : VectorCompactTestParameter n→ℝ)
    (hf : ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' U))
    (B K : ℝ) (hB : 0≤B)
    (hjets : ∀q∈U,∀p : Couplings n×ℝ,∀x : Field n,∀r : ℕ,r≤2→
      ‖iteratedFDeriv ℝ r (fun y=>f (q,(p,y))) x‖≤B*Real.exp (K*(‖p‖+‖x‖)))
    (htime : ∀q∈U,∀p : Couplings n×ℝ,∀x : Field n,
      ‖vectorCompactSmoothTimeField f (q,(p,x))‖≤B*Real.exp (K*(‖p‖+‖x‖))) :
    ∃B' : ℝ,0≤B' ∧
      (∀q : ℝ,∀p : Couplings n×ℝ,∀x : Field n,∀r : ℕ,r≤2→
        ‖iteratedFDeriv ℝ r (fun y=>timeLocalizedFunction ρ f (q,(p,y))) x‖≤
          B'*Real.exp (K*(‖p‖+‖x‖))) ∧
      (∀q : ℝ,∀p : Couplings n×ℝ,∀x : Field n,
        ‖vectorCompactSmoothTimeField (timeLocalizedFunction ρ f) (q,(p,x))‖≤
          B'*Real.exp (K*(‖p‖+‖x‖))) := by
  have hwhole:=contDiff_timeLocalizedFunction ρ f U hU hρ hsU hf
  obtain ⟨D,hD,hDb⟩:=hsρ.exists_bound_iteratedFDeriv hρ 1
  have hderiv (q : ℝ) : ‖deriv ρ q‖≤D:=by
    rw [norm_deriv_eq_norm_fderiv,←norm_iteratedFDeriv_one]
    exact hDb 1 le_rfl q
  refine ⟨(D+1)*B,by positivity,?_,?_⟩
  · intro q p x r hr
    by_cases hq : q∈U
    · have hfield : ContDiff ℝ ∞ (fun y : Field n=>f (q,(p,y))):=by
        apply contDiff_iff_contDiffAt.mpr
        intro y
        have hAt:=(hf (q,(p,y)) hq).contDiffAt
          ((hU.preimage continuous_fst).mem_nhds hq)
        exact hAt.comp y (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffAt
      have he : (fun y=>timeLocalizedFunction ρ f (q,(p,y)))=
          ρ q • (fun y=>f (q,(p,y))):=by funext y;rfl
      rw [he,iteratedFDeriv_const_smul_apply (hfield.of_le (by simp)).contDiffAt,norm_smul]
      apply (mul_le_mul (hρb q) (hjets q hq p x r hr) (norm_nonneg _)
        (by norm_num : (0:ℝ)≤1)).trans
      simp only [one_mul]
      have he : 0≤B*Real.exp (K*(‖p‖+‖x‖)):=mul_nonneg hB (Real.exp_pos _).le
      nlinarith [mul_nonneg hD he]
    · have hz:=timeLocalizedFunction_eventually_zero ρ f q (p,x) (fun h=>hq (hsU h))
      have hslice:=hz.comp_tendsto (show ContinuousAt
        (fun y : Field n=>(q,(p,y))) x from by fun_prop)
      dsimp only [Function.comp_def] at hslice
      rw [(hslice.iteratedFDeriv ℝ r).self_of_nhds]
      simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
      positivity
  · intro q p x
    by_cases hq : q∈U
    · have hAt:=(hf (q,(p,x)) hq).contDiffAt ((hU.preimage continuous_fst).mem_nhds hq)
      have he := (hasDerivAt_vectorCompactSmooth_time hwhole q p x).unique
        (hasDerivAt_timeLocalizedFunction ρ f q (p,x) _ _
          ((hρ.differentiable (by simp) q).hasDerivAt) (hasDerivAt_vectorCell_time hAt))
      rw [he]
      have hval : ‖f (q,(p,x))‖≤B*Real.exp (K*(‖p‖+‖x‖)):=by
        simpa only [norm_iteratedFDeriv_zero] using hjets q hq p x 0 (by omega)
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      apply (add_le_add (mul_le_mul (hderiv q) hval (norm_nonneg _) hD)
        (mul_le_mul (hρb q) (htime q hq p x) (norm_nonneg _) (by norm_num : (0:ℝ)≤1))).trans
      ring_nf
      exact le_refl _
    · have hz:=timeLocalizedFunction_eventually_zero ρ f q (p,x) (fun h=>hq (hsU h))
      have hh:=congrArg (fun L : VectorCompactTestParameter n→L[ℝ]ℝ=>L (1,(0,0)))
        (hz.fderiv_eq (𝕜:=ℝ))
      simp only [fderiv_const_apply,ContinuousLinearMap.zero_apply] at hh
      change vectorCompactSmoothTimeField (timeLocalizedFunction ρ f) (q,(p,x))=0 at hh
      rw [hh,norm_zero]
      positivity

end QuantitativePaper
