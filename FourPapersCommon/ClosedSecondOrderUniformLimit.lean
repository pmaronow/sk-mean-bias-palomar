module
public import FourPapersCommon.SecondOrderUniformLimit
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Genuine closed-interval derivative limits. One-sided finite differences
give uniform Cauchy estimates up to both endpoints. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem firstTaylor_remainder_Icc_of_derivative_Lipschitz (f : ℝ→ℝ)
    (hf : Differentiable ℝ f) (M : ℝ) (hM : 0≤M)
    (hL : ∀x∈Icc (0:ℝ) 1,∀y∈Icc (0:ℝ) 1,
      |deriv f y-deriv f x|≤M*|y-x|)
    (x y : ℝ) (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    |f y-f x-deriv f x*(y-x)|≤M*|y-x|^2 := by
  have hseg : segment ℝ x y⊆Icc (0:ℝ) 1:=(convex_Icc (0:ℝ) 1).segment_subset hx hy
  have hb (u : ℝ) (hu : u∈segment ℝ x y) :
      ‖deriv f u-deriv f x‖≤M*|y-x|:=by
    have hd:=dist_add_dist_of_mem_segment hu
    have hd' : |u-x|≤|y-x|:=by
      simp only [Real.dist_eq] at hd
      rw [abs_sub_comm x y] at hd
      rw [abs_sub_comm u x]
      linarith [abs_nonneg (u-y)]
    exact (hL x hx u (hseg hu)).trans (mul_le_mul_of_nonneg_left hd' hM)
  have hh:=(convex_segment x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f:=fun u=>f u-deriv f x*u) (f':=fun u=>deriv f u-deriv f x)
    (fun u _=>by simpa only [Pi.sub_def,id_eq,mul_one] using
      ((hf u).hasDerivAt.sub ((hasDerivAt_id u).const_mul (deriv f x))).hasDerivWithinAt)
    hb (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simp only [Real.norm_eq_abs] at hh
  have he : f y-deriv f x*y-(f x-deriv f x*x)=f y-f x-deriv f x*(y-x):=by ring
  simpa only [he,pow_two,mul_assoc] using hh

theorem uniformCauchySeqOn_deriv_Icc_of_uniformCauchy (f : ℕ→ℝ→ℝ)
    (hf : ∀j,Differentiable ℝ (f j)) (M : ℝ) (hM : 0≤M)
    (hL : ∀j,∀x∈Icc (0:ℝ) 1,∀y∈Icc (0:ℝ) 1,
      |deriv (f j) y-deriv (f j) x|≤M*|y-x|)
    (hu : UniformCauchySeqOn f atTop (Icc (0:ℝ) 1)) :
    UniformCauchySeqOn (fun j=>deriv (f j)) atTop (Icc (0:ℝ) 1) := by
  rw [Metric.uniformCauchySeqOn_iff] at hu ⊢
  intro ε hε
  let δ : ℝ:=min (1/2) (ε/(8*(M+1)))
  have hδ : 0<δ:=lt_min (by norm_num) (by positivity)
  have hδhalf : δ≤1/2:=min_le_left _ _
  have hδsmall : δ≤ε/(8*(M+1)):=min_le_right _ _
  obtain ⟨N,hN⟩:=hu (ε*δ/8) (by positivity)
  refine ⟨N,fun j hj k hk x hx=>?_⟩
  let v : ℝ:=if x≤1/2 then δ else -δ
  have hav : |v|=δ:=by unfold v;split <;> simp [abs_of_pos hδ]
  have hyv : x+v∈Icc (0:ℝ) 1:=by
    unfold v
    split <;> constructor <;> linarith [hx.1,hx.2]
  have hb (y : ℝ) (hy : y∈Icc (0:ℝ) 1) : |f j y-f k y|≤ε*δ/8:=by
    simpa only [Real.dist_eq] using (hN j hj k hk y hy).le
  have hjR:=firstTaylor_remainder_Icc_of_derivative_Lipschitz (f j) (hf j) M hM (hL j)
    x (x+v) hx hyv
  have hkR:=firstTaylor_remainder_Icc_of_derivative_Lipschitz (f k) (hf k) M hM (hL k)
    x (x+v) hx hyv
  simp only [add_sub_cancel_left,hav] at hjR hkR
  have hval : |(f j (x+v)-f j x)-(f k (x+v)-f k x)|≤2*(ε*δ/8):=by
    calc
      _=|(f j (x+v)-f k (x+v))-(f j x-f k x)|:=by congr 1;ring
      _≤|f j (x+v)-f k (x+v)|+|f j x-f k x|:=abs_sub _ _
      _≤_:=by linarith [hb (x+v) hyv,hb x hx]
  have hder : |(deriv (f j) x-deriv (f k) x)*v|≤2*(ε*δ/8)+2*M*δ^2:=by
    calc
      _=|((f j (x+v)-f j x)-(f k (x+v)-f k x))-
        (f j (x+v)-f j x-deriv (f j) x*v)+
        (f k (x+v)-f k x-deriv (f k) x*v)|:=by congr 1;ring
      _≤|(f j (x+v)-f j x)-(f k (x+v)-f k x)|+
        |f j (x+v)-f j x-deriv (f j) x*v|+
        |f k (x+v)-f k x-deriv (f k) x*v|:=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _≤_:=by linarith
  rw [abs_mul,hav] at hder
  have hbound : |deriv (f j) x-deriv (f k) x|≤ε/4+2*M*δ:=by
    have he : (ε/4+2*M*δ)*δ=2*(ε*δ/8)+2*M*δ^2:=by ring
    exact (le_of_mul_le_mul_right (hder.trans_eq he.symm) hδ)
  have hM1 : 0<M+1:=by linarith
  have hsmall : 2*M*δ≤ε/4:=by
    calc
      _≤2*M*(ε/(8*(M+1))):=mul_le_mul_of_nonneg_left hδsmall (by positivity)
      _≤ε/4:=by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
        field_simp
        nlinarith
  rw [Real.dist_eq]
  linarith

theorem hasDerivWithinAt_Icc_of_continuous_derivative (g D : ℝ→ℝ)
    (hg : ContinuousOn g (Icc (0:ℝ) 1)) (hD : ContinuousOn D (Icc (0:ℝ) 1))
    (hd : ∀x∈Ioo (0:ℝ) 1,HasDerivAt g (D x) x)
    (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    HasDerivWithinAt g (D x) (Icc (0:ℝ) 1) x := by
  have ht : Tendsto (fun y=>ContinuousLinearMap.toSpanSingleton ℝ (D y))
      (𝓝[Ioo (0:ℝ) 1] x) (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (D x))):=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.tendsto.comp
      ((hD x hx).mono Ioo_subset_Icc_self)
  have he : (fun y=>fderiv ℝ g y)=ᶠ[𝓝[Ioo (0:ℝ) 1] x]
      (fun y=>ContinuousLinearMap.toSpanSingleton ℝ (D y)):=by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [←toSpanSingleton_deriv,(hd y hy).deriv]
  have hh:=hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy=>(hd y hy).differentiableAt.differentiableWithinAt)
    (convex_Ioo (0:ℝ) 1) isOpen_Ioo
    (fun y hy=>(hg y (by simpa [closure_Ioo (by norm_num : (0:ℝ)≠1)] using hy)).mono
      Ioo_subset_Icc_self) (ht.congr' he.symm)
  simpa only [closure_Ioo (by norm_num : (0:ℝ)≠1),
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,one_mul] using hh.hasDerivWithinAt

theorem exists_uniform_derivative_limit_Icc (f : ℕ→ℝ→ℝ) (g : ℝ→ℝ)
    (hf : ∀j,ContDiff ℝ ∞ (f j)) (M : ℝ) (hM : 0≤M)
    (hL : ∀j,∀x∈Icc (0:ℝ) 1,∀y∈Icc (0:ℝ) 1,
      |deriv (f j) y-deriv (f j) x|≤M*|y-x|)
    (hu : TendstoUniformlyOn f g atTop (Icc (0:ℝ) 1)) :
    ∃D : ℝ→ℝ,TendstoUniformlyOn (fun j=>deriv (f j)) D atTop (Icc (0:ℝ) 1) ∧
      ContinuousOn D (Icc (0:ℝ) 1) ∧
      (∀x∈Icc (0:ℝ) 1,HasDerivWithinAt g (D x) (Icc (0:ℝ) 1) x) := by
  have hc:=uniformCauchySeqOn_deriv_Icc_of_uniformCauchy f
    (fun j=>(hf j).differentiable (by simp)) M hM hL hu.uniformCauchySeqOn
  let D : ℝ→ℝ:=fun x=>limUnder atTop (fun j=>deriv (f j) x)
  have ht (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
      Tendsto (fun j=>deriv (f j) x) atTop (𝓝 (D x)):=
    (hc.cauchySeq hx).tendsto_limUnder
  have hU:=hc.tendstoUniformlyOn_of_tendsto ht
  have hDc : ContinuousOn D (Icc (0:ℝ) 1):=hU.continuousOn
    (Eventually.of_forall (fun j=>((contDiff_infty_iff_deriv.mp (hf j)).2).continuous.continuousOn)).frequently
  have hgc : ContinuousOn g (Icc (0:ℝ) 1):=hu.continuousOn
    (Eventually.of_forall (fun j=>(hf j).continuous.continuousOn)).frequently
  have hd (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : HasDerivAt g (D x) x:=
    hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hU.mono Ioo_subset_Icc_self)
      (Eventually.of_forall (fun j y _=>((hf j).differentiable (by simp) y).hasDerivAt))
      (fun y hy=>hu.tendsto_at (Ioo_subset_Icc_self hy)) hx
  exact ⟨D,hU,hDc,hasDerivWithinAt_Icc_of_continuous_derivative g D hgc hDc hd⟩

theorem abs_bound_Icc_of_Ioo (f : ℝ→ℝ) (hf : Continuous f) (M : ℝ)
    (hB : ∀x∈Ioo (0:ℝ) 1,|f x|≤M) : ∀x∈Icc (0:ℝ) 1,|f x|≤M := by
  intro x hx
  apply le_on_closure hB hf.abs.continuousOn continuous_const.continuousOn
  simpa only [closure_Ioo (by norm_num : (0:ℝ)≠1)] using hx

theorem closed_second_order_uniform_limit (f : ℕ→ℝ→ℝ) (g : ℝ→ℝ)
    (hf : ∀j,ContDiff ℝ ∞ (f j)) (M L : ℝ) (hM : 0≤M) (hL : 0≤L)
    (h2 : ∀j,∀x∈Ioo (0:ℝ) 1,|deriv (deriv (f j)) x|≤M)
    (h3 : ∀j,∀x∈Ioo (0:ℝ) 1,|deriv (deriv (deriv (f j))) x|≤L)
    (hu : TendstoUniformlyOn f g atTop (Icc (0:ℝ) 1)) :
    ∃D1 D2 : ℝ→ℝ,
      ContinuousOn D1 (Icc (0:ℝ) 1) ∧ ContinuousOn D2 (Icc (0:ℝ) 1) ∧
      TendstoUniformlyOn (fun j=>deriv (f j)) D1 atTop (Icc (0:ℝ) 1) ∧
      TendstoUniformlyOn (fun j=>deriv (deriv (f j))) D2 atTop (Icc (0:ℝ) 1) ∧
      (∀x∈Icc (0:ℝ) 1,HasDerivWithinAt g (D1 x) (Icc (0:ℝ) 1) x) ∧
      (∀x∈Icc (0:ℝ) 1,HasDerivWithinAt D1 (D2 x) (Icc (0:ℝ) 1) x) ∧
      ContDiffOn ℝ 2 g (Icc (0:ℝ) 1) := by
  have hdf (j : ℕ) : ContDiff ℝ ∞ (deriv (f j)):=
    (contDiff_infty_iff_deriv.mp (hf j)).2
  have hddf (j : ℕ) : ContDiff ℝ ∞ (deriv (deriv (f j))):=
    (contDiff_infty_iff_deriv.mp (hdf j)).2
  have hdddf (j : ℕ) : ContDiff ℝ ∞ (deriv (deriv (deriv (f j)))):=
    (contDiff_infty_iff_deriv.mp (hddf j)).2
  have h2c j:=abs_bound_Icc_of_Ioo _ (hddf j).continuous M (h2 j)
  have h3c j:=abs_bound_Icc_of_Ioo _ (hdddf j).continuous L (h3 j)
  have hLip1 (j : ℕ) (x : ℝ) (hx : x∈Icc (0:ℝ) 1)
      (y : ℝ) (hy : y∈Icc (0:ℝ) 1) :
      |deriv (f j) y-deriv (f j) x|≤M*|y-x|:=by
    simpa only [Real.norm_eq_abs] using (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun z _=>(hdf j).differentiable (by simp) z)
      (fun z hz=>by simpa only [Real.norm_eq_abs] using h2c j z hz) hx hy
  obtain ⟨D1,hU1,hD1,hd1⟩:=exists_uniform_derivative_limit_Icc f g hf M hM hLip1 hu
  have hLip2 (j : ℕ) (x : ℝ) (hx : x∈Icc (0:ℝ) 1)
      (y : ℝ) (hy : y∈Icc (0:ℝ) 1) :
      |deriv (deriv (f j)) y-deriv (deriv (f j)) x|≤L*|y-x|:=by
    simpa only [Real.norm_eq_abs] using (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun z _=>(hddf j).differentiable (by simp) z)
      (fun z hz=>by simpa only [Real.norm_eq_abs] using h3c j z hz) hx hy
  obtain ⟨D2,hU2,hD2,hd2⟩:=exists_uniform_derivative_limit_Icc
    (fun j=>deriv (f j)) D1 hdf L hL hLip2 hU1
  refine ⟨D1,D2,hD1,hD2,hU1,hU2,hd1,hd2,?_⟩
  have huniq : UniqueDiffOn ℝ (Icc (0:ℝ) 1):=uniqueDiffOn_Icc (by norm_num)
  have hEq1 : EqOn (derivWithin g (Icc (0:ℝ) 1)) D1 (Icc (0:ℝ) 1):=
    fun x hx=>(hd1 x hx).derivWithin (huniq x hx)
  have hEq2 : EqOn (derivWithin D1 (Icc (0:ℝ) 1)) D2 (Icc (0:ℝ) 1):=
    fun x hx=>(hd2 x hx).derivWithin (huniq x hx)
  have hC1 : ContDiffOn ℝ 1 D1 (Icc (0:ℝ) 1):=
    (contDiffOn_one_iff_derivWithin huniq).mpr
      ⟨fun x hx=>(hd2 x hx).differentiableWithinAt,hD2.congr (fun x hx=>hEq2 hx)⟩
  have hh : ContDiffOn ℝ (1+1) g (Icc (0:ℝ) 1):=
    (contDiffOn_succ_iff_derivWithin huniq).mpr
      ⟨fun x hx=>(hd1 x hx).differentiableWithinAt,by simp,
        hC1.congr (fun x hx=>hEq1 hx)⟩
  simpa only [one_add_one_eq_two] using hh

end FourPapersCommon
