module
public import QuantitativeFollowup.ExponentialNormedJetComposition

@[expose] public section

/-! Actual nonlinear coordinate changes with linear growth preserve all
exponential jet bounds on their genuine smooth domains. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup
open FourPapersCommon
set_option maxHeartbeats 2200000
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exponentialSmoothOn_comp_of_linear_growth (f : F→G) (V : Set F)
    (hf : ExponentialSmoothOn f V) (g : E→F) (U : Set E)
    (hg : ExponentialSmoothOn g U) (hmap : MapsTo g U V)
    (S T : ℝ) (hS : 0≤S) (hT : 0≤T) (hv : ∀x∈U,‖g x‖≤S+T*‖x‖) :
    ExponentialSmoothOn (f∘g) U := by
  refine ⟨fun x hx=>(hf.smooth _ (hmap hx)).comp x (hg.smooth x hx),fun r=>?_⟩
  obtain ⟨A,B,hA,hB,hfjet⟩:=hf.common_bound r
  obtain ⟨C,D,hC,hD,hgjet⟩:=hg.common_bound r
  refine ⟨(r.factorial:ℝ)*A*Real.exp (B*S)*C^r,B*T+(r:ℝ)*D,by positivity,by positivity,?_⟩
  intro x hx
  have houter (i : ℕ) (hi : i≤r) :
      ‖iteratedFDeriv ℝ i f (g x)‖≤A*Real.exp (B*S+(B*T)*‖x‖) := by
    apply (hfjet i hi _ (hmap hx)).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (zero_le_one.trans hA)
    nlinarith only [mul_le_mul_of_nonneg_left (hv x hx) hB]
  have hbase : 1≤C*Real.exp (D*‖x‖) :=
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg _)))
  apply (DepthPaper.norm_iteratedFDeriv_comp_le_at (hf.smooth _ (hmap hx)) (hg.smooth x hx)
    r (A*Real.exp (B*S+(B*T)*‖x‖)) (C*Real.exp (D*‖x‖)) houter
    (fun i hi hir=>(hgjet i hir x hx).trans (le_self_pow₀ hbase (by omega)))).trans_eq
  rw [mul_pow,←Real.exp_nat_mul,Real.exp_add]
  rw [show (B*T+(r:ℝ)*D)*‖x‖=(B*T)*‖x‖+(r:ℝ)*(D*‖x‖) by ring,Real.exp_add]
  ring

theorem exponentialSmoothOn_sqrt_comp_fst (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l u : ℝ) (hl : 0<l) :
    ExponentialSmoothOn (fun w : ℝ×E=>Real.sqrt w.1) ((Ioo l u)×ˢ(univ : Set E)) := by
  have hs : ExponentialSmoothOn Real.sqrt (Icc l u) := by
    refine ⟨fun x hx=>Real.contDiffAt_sqrt (ne_of_gt (hl.trans_le hx.1)),fun r=>?_⟩
    have hc : ContinuousOn (fun x : ℝ=>‖iteratedFDeriv ℝ r Real.sqrt x‖) (Icc l u) :=
      fun x hx=>((Real.contDiffAt_sqrt (n:=∞) (ne_of_gt (hl.trans_le hx.1))).continuousAt_iteratedFDeriv
        (by simp)).norm.continuousWithinAt
    obtain ⟨C,hC⟩:=isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨max 0 C,0,le_max_left _ _,le_rfl,?_⟩
    intro x hx
    simpa only [zero_mul,Real.exp_zero,mul_one,norm_norm] using (hC x hx).trans (le_max_right (0:ℝ) C)
  exact hs.precompCLM (ContinuousLinearMap.fst ℝ ℝ E) (fun w hw=>⟨hw.1.1.le,hw.1.2.le⟩)

end QuantitativeFollowup
