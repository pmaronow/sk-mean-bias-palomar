module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeLimit
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

@[expose] public section

/-! Actual derivative closure from pointwise convergence on finite dimensional
fields. Compact-ball convergence and local difference quotients discharge the
uniform derivative Cauchy condition. -/
noncomputable section
open Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxHeartbeats 1600000

theorem norm_fderiv_sub_le_of_local_uniform_sub (f g : E→F)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (L : ℝ≥0)
    (hLf : LipschitzWith L (fderiv ℝ f)) (hLg : LipschitzWith L (fderiv ℝ g))
    (ε : ℝ) (hε : 0≤ε) (δ : ℝ) (hδ : 0<δ) (x : E)
    (hb : ∀y,dist y x≤δ→‖f y-g y‖≤ε) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ 2*ε/δ+2*L*δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have hfw := firstTaylor_remainder_Banach f hf L hLf x (δ•w)
  have hgw := firstTaylor_remainder_Banach g hg L hLg x (δ•w)
  have hv : ‖δ•w‖=δ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,hw,mul_one]
  rw [hv] at hfw hgw
  have hbshift := hb (x+δ•w) (by simpa only [dist_eq_norm,add_sub_cancel_left,hv] using le_rfl)
  have hbself := hb x (by simpa using hδ.le)
  have hval : ‖(f (x+δ•w)-f x)-(g (x+δ•w)-g x)‖≤2*ε := by
    calc
      _ = ‖(f (x+δ•w)-g (x+δ•w))-(f x-g x)‖ := by congr 1;abel
      _ ≤ ‖f (x+δ•w)-g (x+δ•w)‖+‖f x-g x‖ := norm_sub_le _ _
      _ ≤ 2*ε := by linarith
  have hder : ‖fderiv ℝ f x (δ•w)-fderiv ℝ g x (δ•w)‖≤2*ε+2*L*δ^2 := by
    calc
      _ = ‖((f (x+δ•w)-f x)-(g (x+δ•w)-g x))-
          (f (x+δ•w)-f x-fderiv ℝ f x (δ•w))+
          (g (x+δ•w)-g x-fderiv ℝ g x (δ•w))‖ := by congr 1;abel
      _ ≤ ‖(f (x+δ•w)-f x)-(g (x+δ•w)-g x)‖+
          ‖f (x+δ•w)-f x-fderiv ℝ f x (δ•w)‖+
          ‖g (x+δ•w)-g x-fderiv ℝ g x (δ•w)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hh : δ*‖(fderiv ℝ f x-fderiv ℝ g x) w‖≤2*ε+2*L*δ^2 := by
    simpa only [map_smul,ContinuousLinearMap.sub_apply,←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_pos hδ] using hder
  have he : 2*ε/δ+2*L*δ=(2*ε+2*L*δ^2)/δ := by field_simp
  rw [he]
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hh)

theorem tendstoUniformlyOn_compact_of_pointwise_lipschitz (f : ℕ→E→F) (g : E→F)
    (K : ℝ≥0) (hK : ∀j,LipschitzWith K (f j))
    (hp : ∀x,Tendsto (fun j=>f j x) atTop (𝓝 (g x)))
    (s : Set E) (hs : IsCompact s) : TendstoUniformlyOn f g atTop s := by
  haveI : CompactSpace s:=isCompact_iff_compactSpace.mp hs
  let H:=fun j (x : s)=>f j x
  have hHL (j) : LipschitzWith K (H j):=by simpa only [H,Function.comp_def,mul_one] using (hK j).comp (LipschitzWith.subtype_val s)
  have he := (LipschitzWith.uniformEquicontinuous H K hHL).equicontinuous
  have ht := (he.tendsto_uniformFun_iff_pi atTop (fun x : s=>g x)).mpr
    (tendsto_pi_nhds.mpr fun x=>hp x)
  have hu : TendstoUniformly H (fun x : s=>g x) atTop := by
    exact UniformFun.tendsto_iff_tendstoUniformly.mp ht
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hu

theorem uniformCauchySeqOn_fderiv_closedBall_of_pointwise [ProperSpace E]
    (f : ℕ→E→F) (g : E→F) (hf : ∀j,Differentiable ℝ (f j))
    (K L : ℝ≥0) (hK : ∀j,LipschitzWith K (f j))
    (hL : ∀j,LipschitzWith L (fderiv ℝ (f j)))
    (hp : ∀x,Tendsto (fun j=>f j x) atTop (𝓝 (g x))) (R : ℝ) :
    UniformCauchySeqOn (fun j=>fderiv ℝ (f j)) atTop (Metric.closedBall (0:E) R) := by
  have hu := (tendstoUniformlyOn_compact_of_pointwise_lipschitz f g K hK hp
    (Metric.closedBall (0:E) (R+1)) (isCompact_closedBall _ _)).uniformCauchySeqOn
  rw [Metric.uniformCauchySeqOn_iff] at hu ⊢
  intro ε hε
  let δ : ℝ:=min 1 (ε/(8*(L+1)))
  have hδ : 0<δ:=by dsimp only [δ];positivity
  have hδ1 : δ≤1:=min_le_left _ _
  have hδe : δ≤ε/(8*(L+1)):=min_le_right _ _
  obtain ⟨N,hN⟩ := hu (ε*δ/8) (by positivity)
  refine ⟨N,fun j hj k hk x hx=>?_⟩
  have hb (y : E) (hy : dist y x≤δ) : ‖f j y-f k y‖≤ε*δ/8 := by
    have hym : y∈Metric.closedBall (0:E) (R+1) := by
      rw [Metric.mem_closedBall] at hx ⊢
      calc
        dist y 0≤dist y x+dist x 0:=dist_triangle _ _ _
        _≤R+1:=by linarith
    simpa only [dist_eq_norm] using (hN j hj k hk y hym).le
  rw [dist_eq_norm]
  apply (norm_fderiv_sub_le_of_local_uniform_sub (f j) (f k) (hf j) (hf k)
    L (hL j) (hL k) (ε*δ/8) (by positivity) δ hδ x hb).trans_lt
  have he : 2*(ε*δ/8)/δ=ε/4 := by field_simp;ring
  rw [he]
  have hL1 : 0<(L:ℝ)+1:=by positivity
  have hbd : 2*(L:ℝ)*δ≤ε/4 := by
    apply (mul_le_mul_of_nonneg_left hδe (by positivity : 0≤2*(L:ℝ))).trans
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<8*((L:ℝ)+1))).mpr
    nlinarith [L.coe_nonneg]
  linarith

theorem exists_local_derivative_limit_of_pointwise [ProperSpace E] [CompleteSpace F]
    (f : ℕ→E→F) (g : E→F) (hf : ∀j,Differentiable ℝ (f j))
    (K L : ℝ≥0) (hK : ∀j,LipschitzWith K (f j))
    (hL : ∀j,LipschitzWith L (fderiv ℝ (f j)))
    (hp : ∀x,Tendsto (fun j=>f j x) atTop (𝓝 (g x))) :
    ∃ g' : E→(E→L[ℝ]F),
      TendstoLocallyUniformly (fun j=>fderiv ℝ (f j)) g' atTop ∧
      (∀x,HasFDerivAt g (g' x) x) ∧ Continuous g' ∧ ContDiff ℝ 1 g := by
  have hc (R : ℝ) := uniformCauchySeqOn_fderiv_closedBall_of_pointwise f g hf K L hK hL hp R
  let g' := fun x=>limUnder atTop (fun j=>fderiv ℝ (f j) x)
  have ht (x : E) : Tendsto (fun j=>fderiv ℝ (f j) x) atTop (𝓝 (g' x)) :=
    ((hc (‖x‖+1)).cauchySeq (by
      rw [Metric.mem_closedBall,dist_zero_right];linarith)).tendsto_limUnder
  have hu (R : ℝ) : TendstoUniformlyOn (fun j=>fderiv ℝ (f j)) g' atTop
      (Metric.closedBall (0:E) R) :=
    (hc R).tendstoUniformlyOn_of_tendsto (fun x _=>ht x)
  have hl : TendstoLocallyUniformly (fun j=>fderiv ℝ (f j)) g' atTop := by
    apply tendstoLocallyUniformly_of_forall_exists_nhds
    intro x
    refine ⟨Metric.ball (0:E) (‖x‖+1),Metric.isOpen_ball.mem_nhds ?_,
      (hu (‖x‖+1)).mono Metric.ball_subset_closedBall⟩
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  have hd (x) : HasFDerivAt g (g' x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (tendstoLocallyUniformlyOn_univ.mpr hl)
      (fun j x _=>(hf j x).hasFDerivAt) (fun x _=>hp x) (mem_univ x)
  have hg' : Continuous g' := hl.continuous
    ((Eventually.of_forall fun j=>(hL j).continuous).frequently)
  refine ⟨g',hl,hd,hg',contDiff_one_iff_fderiv.mpr ⟨fun x=>(hd x).differentiableAt,?_⟩⟩
  have he : fderiv ℝ g=g' := funext fun x=>(hd x).fderiv
  rw [he]
  exact hg'

end QuantitativeFollowup
