module
public import FourPapersCommon.ExponentialSmoothBounds

@[expose] public section

/-! Genuine additive and inversion closure for exponential jet bounds. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ExponentialSmoothOn.const (c : F) (s : Set E) :
    ExponentialSmoothOn (fun _ : E=>c) s := by
  refine ⟨fun _ _=>contDiffAt_const,fun r=>⟨‖c‖,0,norm_nonneg _,le_rfl,?_⟩⟩
  intro x _
  cases r with
  | zero => simp only [norm_iteratedFDeriv_zero,zero_mul,Real.exp_zero,mul_one,le_refl]
  | succ r =>
    simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,zero_mul,Real.exp_zero,mul_one]
      using norm_nonneg c

theorem ExponentialSmoothOn.add {f g : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) (hg : ExponentialSmoothOn g s) :
    ExponentialSmoothOn (fun x=>f x+g x) s := by
  refine ⟨fun x hx=>(hf.smooth x hx).add (hg.smooth x hx),fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  obtain ⟨D,S,hD,hS,hd⟩:=hg.bound r
  refine ⟨C+D,R+S,add_nonneg hC hD,add_nonneg hR hS,fun x hx=>?_⟩
  rw [fun_iteratedFDeriv_add_apply ((hf.smooth x hx).of_le (by simp))
    ((hg.smooth x hx).of_le (by simp))]
  apply (norm_add_le _ _).trans
  have hR' : Real.exp (R*‖x‖)≤Real.exp ((R+S)*‖x‖):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) (norm_nonneg _))
  have hS' : Real.exp (S*‖x‖)≤Real.exp ((R+S)*‖x‖):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hR) (norm_nonneg _))
  exact (add_le_add ((hb x hx).trans (mul_le_mul_of_nonneg_left hR' hC))
    ((hd x hx).trans (mul_le_mul_of_nonneg_left hS' hD))).trans_eq (by ring)

theorem ExponentialSmoothOn.neg {f : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) : ExponentialSmoothOn (fun x=>-f x) s := by
  refine ⟨fun x hx=>(hf.smooth x hx).neg,fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  refine ⟨C,R,hC,hR,fun x hx=>?_⟩
  change ‖iteratedFDeriv ℝ r (-f) x‖≤_
  simpa only [iteratedFDeriv_neg_apply,norm_neg] using hb x hx

theorem ExponentialSmoothOn.sub {f g : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) (hg : ExponentialSmoothOn g s) :
    ExponentialSmoothOn (fun x=>f x-g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem ExponentialSmoothOn.inverse {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] [Nontrivial A]
    {f : E→A} {s : Set E} (hf : ExponentialSmoothOn f s)
    (hu : ∀x∈s,IsUnit (f x)) (D S : ℝ) (hD : 1≤D) (hS : 0≤S)
    (hb : ∀x∈s,‖Ring.inverse (f x)‖≤D*Real.exp (S*‖x‖)) :
    ExponentialSmoothOn (fun x=>Ring.inverse (f x)) s := by
  classical
  have hInv (x : E) (hx : x∈s) : ContDiffAt ℝ ∞ Ring.inverse (f x):=by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜:=ℝ) (hu x hx).unit).contDiffAt (n:=∞)
  refine ⟨fun x hx=>(hInv x hx).comp x (hf.smooth x hx),fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hfB⟩:=hf.common_bound r
  refine ⟨(r.factorial:ℝ)^2*D^(r+1)*C^r,(r+1:ℝ)*S+(r:ℝ)*R,
    by positivity,by positivity,fun x hx=>?_⟩
  let V:=D*Real.exp (S*‖x‖)
  let W:=C*Real.exp (R*‖x‖)
  have hV : 1≤V:=by
    have he : 1≤Real.exp (S*‖x‖):=Real.one_le_exp_iff.mpr (mul_nonneg hS (norm_nonneg _))
    exact (show 1≤D*1 by simpa using hD).trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans hD))
  have hW : 1≤W:=by
    have he : 1≤Real.exp (R*‖x‖):=Real.one_le_exp_iff.mpr (mul_nonneg hR (norm_nonneg _))
    exact (show 1≤C*1 by simpa using hC).trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans hC))
  have hI (j : ℕ) (hj : j≤r) :
      ‖iteratedFDeriv ℝ j Ring.inverse (f x)‖≤(r.factorial:ℝ)*V^(r+1) := by
    have hh:=DepthPaper.norm_iteratedFDeriv_inverse_le (hu x hx).unit j
    have he : (((hu x hx).unit⁻¹:Aˣ):A)=Ring.inverse (f x):=by
      simpa only [IsUnit.unit_spec] using (Ring.inverse_unit (hu x hx).unit).symm
    simp only [IsUnit.unit_spec,he] at hh
    apply hh.trans
    have hfac : (j.factorial:ℝ)≤r.factorial:=by exact_mod_cast Nat.factorial_le hj
    exact mul_le_mul hfac
      ((pow_le_pow_left₀ (norm_nonneg _) (hb x hx) (j+1)).trans
        (pow_le_pow_right₀ hV (by omega))) (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
  have hh:=DepthPaper.norm_iteratedFDeriv_comp_le_at (hInv x hx) (hf.smooth x hx) r
    ((r.factorial:ℝ)*V^(r+1)) W hI
    (fun j hj hjr=>(hfB j hjr x hx).trans (le_self_pow₀ hW (by omega)))
  change ‖iteratedFDeriv ℝ r (Ring.inverse∘f) x‖≤_
  apply hh.trans_eq
  dsimp only [V,W]
  rw [mul_pow,mul_pow,←Real.exp_nat_mul,←Real.exp_nat_mul]
  have he : Real.exp (((r+1:ℝ)*S+(r:ℝ)*R)*‖x‖)=
      Real.exp (((r+1:ℝ)*(S*‖x‖)))*Real.exp ((r:ℝ)*(R*‖x‖)):=by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

end FourPapersCommon
