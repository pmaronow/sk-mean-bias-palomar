module
public import FourPapersCommon.SmoothUniformLimit
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Joint continuity of spatial derivatives from joint value continuity and
uniform spatial jet bounds. Parameters need no differentiable structure. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1000000
variable {A E F : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem continuous_fderiv_family_of_uniform_secondJet (f : A×E→F)
    (hf : Continuous f) (hs : ∀a,ContDiff ℝ ∞ (fun x => f (a,x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀a x,‖iteratedFDeriv ℝ 2 (fun y => f (a,y)) x‖ ≤ C) :
    Continuous (fun z : A×E => fderiv ℝ (fun y => f (z.1,y)) z.2) := by
  apply continuous_clm_apply.mpr
  intro v
  let δ := fun j : ℕ => ((j+1 : ℕ) : ℝ)⁻¹
  let F := fun j (z : A×E) => (δ j)⁻¹ • (f (z.1,z.2+δ j • v)-f z)
  have hδ (j : ℕ) : 0<δ j := by dsimp only [δ];positivity
  have hc (j : ℕ) : Continuous (F j) := by
    unfold F
    exact ((hf.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))).sub hf).const_smul _
  have hb (j : ℕ) (z : A×E) :
      ‖F j z-fderiv ℝ (fun y => f (z.1,y)) z.2 v‖ ≤ C*δ j*‖v‖^2 := by
    have hL := lipschitz_fderiv_of_secondJet_bound (fun y => f (z.1,y)) (hs z.1) C hC (hB z.1)
    have hh := firstTaylor_remainder_Banach (fun y => f (z.1,y)) ((hs z.1).differentiable (by simp))
      C.toNNReal hL z.2 (δ j • v)
    rw [Real.coe_toNNReal _ hC,norm_smul,Real.norm_eq_abs,abs_of_pos (hδ j)] at hh
    have he : F j z-fderiv ℝ (fun y => f (z.1,y)) z.2 v=
        (δ j)⁻¹ • (f (z.1,z.2+δ j • v)-f z-fderiv ℝ (fun y => f (z.1,y)) z.2 (δ j • v)) := by
      dsimp only [F]
      simp only [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ (hδ j).ne',one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hδ j))]
    refine (mul_le_mul_of_nonneg_left hh (inv_pos.mpr (hδ j)).le).trans_eq ?_
    field_simp
  have htδ : Tendsto δ atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : TendstoUniformly F (fun z : A×E => fderiv ℝ (fun y => f (z.1,y)) z.2 v) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have ht : Tendsto (fun j => C*δ j*‖v‖^2) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (htδ.const_mul C).mul_const (‖v‖^2)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
    intro z
    rw [dist_comm,dist_eq_norm]
    exact (hb j z).trans_lt hj
  exact hu.continuous (Eventually.of_forall hc).frequently

theorem continuous_iteratedFDeriv_family_of_uniform_jet_bounds (f : A×E→F)
    (hf : Continuous f) (hs : ∀a,ContDiff ℝ ∞ (fun x => f (a,x)))
    (C : ℕ→ℝ) (hC : ∀r,0≤C r)
    (hB : ∀r,2≤r → ∀a x,‖iteratedFDeriv ℝ r (fun y=>f (a,y)) x‖≤C r)
    (r : ℕ) :
    Continuous (fun z : A×E=>iteratedFDeriv ℝ r (fun y=>f (z.1,y)) z.2) := by
  induction r with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp hf
  | succ r ih =>
    let g : A×E→E[×r]→L[ℝ]F := fun z=>iteratedFDeriv ℝ r (fun y=>f (z.1,y)) z.2
    have hsg (a : A) : ContDiff ℝ ∞ (fun x=>g (a,x)) :=
      (hs a).iteratedFDeriv_right (by simp)
    have hbg (a : A) (x : E) : ‖iteratedFDeriv ℝ 2 (fun y=>g (a,y)) x‖≤C (r+2) := by
      rw [norm_secondJet_iteratedFDeriv _ (hs a)]
      exact hB (r+2) (by omega) a x
    have hd := continuous_fderiv_family_of_uniform_secondJet g ih hsg
      (C (r+2)) (hC _) hbg
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1)=>E) F).symm
    simpa only [g,iteratedFDeriv_succ_eq_comp_left,Function.comp_def] using L.continuous.comp hd

end FourPapersCommon
