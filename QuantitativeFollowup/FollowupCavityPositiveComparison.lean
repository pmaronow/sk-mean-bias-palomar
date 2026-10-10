module
public import QuantitativeFollowup.FollowupCavitySixTermBounds
public import FourPapersCommon.FiniteCascadeTreeGaussianRowComparison

@[expose] public section

/-! Actual positive-observable comparison for simultaneous row/path cavity
interpolation. Zero incident variance and vanishing observables are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

def followupCavitySixTermResponse (n:ℕ)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)(u:ℝ):ℝ:=
  if hu:u∈Icc (0:ℝ) 1 then followupCavityAlpha n β ρ/2*
    cavityMarkedSixExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
      (followupCavityPhysicalRecordObservable n T F) else 0

theorem followupCavitySixTermResponse_abs_le_mean
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)(hF0:∀σ,0≤F σ)
    (u:ℝ)(hu:u∈Icc (0:ℝ) 1):
    |followupCavitySixTermResponse n β ρ hβ hρ s a T F u|≤
      (β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*
          followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u:=by
  obtain ⟨C,hC,hFb⟩:=exists_followupCavityPhysicalRecordObservable_bound T F
  have hnF:∀r,0≤followupCavityPhysicalRecordObservable n T F r:=fun r=>hF0 _
  have hb:=cavityMarkedSixExpectation_abs_le (followupCavitySpinModel n β ρ hβ hρ u hu) hn s a ha has hq T
    (followupCavityPhysicalRecordObservable n T F) (measurable_followupCavityPhysicalRecordObservable T F) C hC hFb hnF
  rw [←followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T F u hu] at hb
  have hE:0≤followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u:=by
    rw [followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T F u hu]
    exact integral_nonneg hnF
  have hα:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hαb:followupCavityAlpha n β ρ≤β^2:=by
    have hd:=(followupCavityD_window n hn β ρ ⟨hρ.1.le,hρ.2⟩).2
    dsimp only [followupCavityD,followupCavityC] at hd
    nlinarith [mul_nonneg (sq_nonneg β) hρ.1.le]
  rw [followupCavitySixTermResponse,dite_eq_left hu,abs_mul,abs_of_nonneg (by positivity:0≤followupCavityAlpha n β ρ/2)]
  apply (mul_le_mul_of_nonneg_left hb (by positivity:0≤followupCavityAlpha n β ρ/2)).trans
  nlinarith [mul_le_mul_of_nonneg_right hαb
    (show 0≤(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
      2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1)*
        followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u by positivity)]

private theorem physical_mean_nonneg
    (n:ℕ)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)(s:RSBScheme k)(a:ℝ)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)(hF0:∀σ,0≤F σ)
    (u:ℝ)(hu:u∈Icc (0:ℝ) 1):0≤followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u:=by
  rw [followupCavityPhysicalExpectation_eq_actual n β ρ hβ hρ s a hq T F u hu]
  exact integral_nonneg hF0

theorem followupCavityPhysicalExpectation_le_exp_forward
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)(hF0:∀σ,0≤F σ)
    (v w:ℝ)(hv:v∈Icc (0:ℝ) 1)(hw:w∈Icc (0:ℝ) 1)(hvw:v≤w):
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T F w≤
      followupCavityPhysicalExpectation n β ρ hβ hρ s a T F v*
        Real.exp ((β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
          2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*(w-v)):=by
  let f:=followupCavityPhysicalExpectation n β ρ hβ hρ s a T F
  let Q:=followupCavitySixTermResponse n β ρ hβ hρ s a T F
  let K:=β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
    2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1)
  have hf:ContinuousOn f (Icc v w):=(contDiffOn_followupCavityPhysicalExpectation n β ρ hβ hρ s a T F).continuousOn.mono
    (fun x hx=>⟨hv.1.trans hx.1,hx.2.trans hw.2⟩)
  have hder (x:ℝ)(hx:x∈Ico v w):HasDerivWithinAt f (Q x) (Ici x) x:=by
    have hx01:x∈Icc (0:ℝ) 1:=⟨hv.1.trans hx.1,hx.2.le.trans hw.2⟩
    by_cases hz:x=0
    · subst x
      simpa only [Q,followupCavitySixTermResponse,dite_eq_left hx01] using
        hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_zero hn β ρ hβ hρ s a ha has hq T F
    · simpa only [Q,followupCavitySixTermResponse,dite_eq_left hx01] using
        (hasDerivAt_followupCavityPhysicalExpectation_six_terms hn β ρ hβ hρ s a ha has hq T F x
          ⟨lt_of_le_of_ne hx01.1 (Ne.symm hz),hx01.2⟩).hasDerivWithinAt (s:=Ici x)
  have hg:=norm_le_gronwallBound_of_norm_deriv_right_le hf hder (δ:=f v) (K:=K) (ε:=0)
    (by rw [Real.norm_of_nonneg (physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 v hv)])
    (by
      intro x hx
      have hx01:x∈Icc (0:ℝ) 1:=⟨hv.1.trans hx.1,hx.2.le.trans hw.2⟩
      rw [Real.norm_eq_abs,Real.norm_of_nonneg (physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 x hx01),add_zero]
      exact followupCavitySixTermResponse_abs_le_mean hn β ρ hβ hρ s a ha has hq T F hF0 x hx01)
  have hh:=hg w ⟨hvw,le_rfl⟩
  change ‖f w‖≤gronwallBound (f v) K 0 (w-v) at hh
  rw [Real.norm_of_nonneg (physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 w hw),gronwallBound_ε0] at hh
  exact hh

theorem followupCavityPhysicalExpectation_le_exp_backward
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)(hF0:∀σ,0≤F σ)
    (v w:ℝ)(hv:v∈Icc (0:ℝ) 1)(hw:w∈Icc (0:ℝ) 1)(hwv:w≤v):
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T F w≤
      followupCavityPhysicalExpectation n β ρ hβ hρ s a T F v*
        Real.exp ((β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
          2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*(v-w)):=by
  let f:=followupCavityPhysicalExpectation n β ρ hβ hρ s a T F
  let Q:=followupCavitySixTermResponse n β ρ hβ hρ s a T F
  let K:=β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
    2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1)
  have hf:ContinuousOn (fun x=>f (v+w-x)) (Icc w v):=by
    apply (contDiffOn_followupCavityPhysicalExpectation n β ρ hβ hρ s a T F).continuousOn.comp
      (continuous_const.sub continuous_id).continuousOn
    intro x hx
    change v+w-x∈Icc (0:ℝ) 1
    constructor <;> linarith [hw.1,hv.2,hx.1,hx.2]
  have hder (x:ℝ)(hx:x∈Ico w v):HasDerivWithinAt (fun x=>f (v+w-x)) (-Q (v+w-x)) (Ici x) x:=by
    have hy:v+w-x∈Ioc (0:ℝ) 1:=⟨by linarith [hw.1,hx.2],by linarith [hv.2,hx.1]⟩
    have hd:=hasDerivAt_followupCavityPhysicalExpectation_six_terms hn β ρ hβ hρ s a ha has hq T F (v+w-x) hy
    have hc:=hd.comp x ((hasDerivAt_const x (v+w)).sub (hasDerivAt_id x))
    have hy01:v+w-x∈Icc (0:ℝ) 1:=⟨hy.1.le,hy.2⟩
    simpa only [f,Q,followupCavitySixTermResponse,dite_eq_left hy01,Function.comp_def,zero_sub,mul_neg_one] using
      hc.hasDerivWithinAt (s:=Ici x)
  have hg:=norm_le_gronwallBound_of_norm_deriv_right_le hf hder (δ:=f v) (K:=K) (ε:=0)
    (by
      change ‖f (v+w-w)‖≤f v
      simp only [add_sub_cancel_right]
      change ‖followupCavityPhysicalExpectation n β ρ hβ hρ s a T F v‖≤_
      rw [Real.norm_of_nonneg (physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 v hv)])
    (by
      intro x hx
      have hy:v+w-x∈Icc (0:ℝ) 1:=⟨by linarith [hw.1,hx.2],by linarith [hv.2,hx.1]⟩
      rw [norm_neg,Real.norm_eq_abs,Real.norm_of_nonneg (physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 (v+w-x) hy),add_zero]
      exact followupCavitySixTermResponse_abs_le_mean hn β ρ hβ hρ s a ha has hq T F hF0 (v+w-x) hy)
  have hh:=hg v ⟨hwv,le_rfl⟩
  change ‖f (v+w-v)‖≤gronwallBound (f v) K 0 (v-w) at hh
  rw [show v+w-v=w by ring,Real.norm_of_nonneg (physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 w hw),gronwallBound_ε0] at hh
  exact hh

theorem followupCavityPhysicalExpectation_comparison
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)(hF0:∀σ,0≤F σ)
    (u v:ℝ)(hu:u∈Icc (0:ℝ) 1)(hv:v∈Icc (0:ℝ) 1):
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u≤
      Real.exp (β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*
          followupCavityPhysicalExpectation n β ρ hβ hρ s a T F v:=by
  have hE:=physical_mean_nonneg n β ρ hβ hρ s a hq T F hF0 v hv
  have hK:0≤β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
    2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1):=by positivity
  rcases le_total v u with h|h
  · apply (followupCavityPhysicalExpectation_le_exp_forward hn β ρ hβ hρ s a ha has hq T F hF0 v u hv hu h).trans
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hu.2,hv.1])) hE
  · apply (followupCavityPhysicalExpectation_le_exp_backward hn β ρ hβ hρ s a ha has hq T F hF0 v u hv hu h).trans
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hv.2,hu.1])) hE

end QuantitativeFollowup
