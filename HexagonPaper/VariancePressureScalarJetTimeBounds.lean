module
public import FRSB.GradientTimeLipschitz
public import FRSB.ParisiGridTopology

@[expose] public section

/-! All-order time Lipschitz estimates of genuine positive spatial jets.
Every CDF atom is retained by finite-cell telescoping and the uniform weak
jet limit. No ordinary time derivative is required at an atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper FRSB
open scoped Topology NNReal BigOperators ContDiff
namespace HexagonPaper
open SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def nativeJetTimeBound (β:ℝ) (j:ℕ) : ℝ := β^2/2 *
  (uniformSpatialConstant β (j+2) +
    ∑k∈Finset.range (j+2), ((j+1).choose k:ℝ)*
      uniformSpatialConstant β k*uniformSpatialConstant β (j+1-k))

theorem norm_cellTimeForcing_le_nativeJetTimeBound (β:ℝ) (μ:Paper.ParisiMeasure)
    (m:ℝ) (hm:m∈Icc (0:ℝ) 1) (r:ℕ) (hr:1≤r) (t x:ℝ) :
    ‖cellTimeForcing β μ m r t x‖≤nativeJetTimeBound β (r-1) := by
  have he:r-1+1=r:=Nat.sub_add_cancel hr
  unfold nativeJetTimeBound
  simp only [he,show r-1+2=r+1 by omega]
  rw [cellTimeForcing_eq,norm_mul,norm_neg,
    Real.norm_of_nonneg (by positivity : 0≤β^2/2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_parisiSpatialJet_succ_le β μ (r+1) t x).trans
      (norm_spatialDerivativeBCF_le_uniform β μ (r+1))
  · rw [norm_mul,Real.norm_of_nonneg hm.1]
    apply (mul_le_mul_of_nonneg_right hm.2 (norm_nonneg _)).trans
    simp only [one_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (by positivity : 0≤(r.choose k:ℝ))]
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left
        ((norm_parisiSpatialJet_succ_le β μ k t x).trans
          (norm_spatialDerivativeBCF_le_uniform β μ k)) (by positivity))
      ((norm_parisiSpatialJet_succ_le β μ (r-k) t x).trans
        (norm_spatialDerivativeBCF_le_uniform β μ (r-k)))
      (norm_nonneg _) (mul_nonneg (by positivity) (uniformSpatialConstant_pos β k).le)

 theorem finiteNativeJet_time_cell_bound (β : ℝ) (hβ : β ≠ 0) (j : ℕ)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) {l r : ℝ} (hl : s.q p ≤ l)
    (hlr : l ≤ r) (hr : r ≤ s.q (p+1)) (x : ℝ) :
    ‖parisiSpatialJet β (parisiSchemeMeasure s) (j+1) r x-
      parisiSpatialJet β (parisiSchemeMeasure s) (j+1) l x‖ ≤ nativeJetTimeBound β j*(r-l) := by
  have hh := closed_interval_increment_bound
    (fun t => parisiSpatialJet β (parisiSchemeMeasure s) (j+1) t x) (fun _ => 0)
    (fun _ => nativeJetTimeBound β j)
    ((continuous_parisiSpatialJet_succ β (parisiSchemeMeasure s) j).comp
      (continuous_id.prodMk continuous_const))
    (fun _ _ => intervalIntegrable_const) (fun _ _ => intervalIntegrable_const) hq
    (by
      intro a b ha hab hb
      have hd (t : ℝ) (ht : t ∈ Icc a b) :=
        hasDerivAt_finiteCell_spatialJet_time s β hβ hp hq (j+1)
          ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩ x
      have hm : s.m p ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩
      have hbnd := Convex.norm_image_sub_le_of_norm_deriv_le (C:=nativeJetTimeBound β j)
        (fun t ht => (hd t ht).differentiableAt)
        (fun t ht => by
          rw [(hd t ht).deriv]
          simpa only [Nat.add_sub_cancel] using
            norm_cellTimeForcing_le_nativeJetTimeBound β _ _ hm (j+1) (by omega) t x)
        (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      simpa only [intervalIntegral.integral_zero,sub_zero,intervalIntegral.integral_const,
        smul_eq_mul,Real.norm_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hbnd)
    hl hlr hr
  simpa only [intervalIntegral.integral_zero,sub_zero,intervalIntegral.integral_const,
    smul_eq_mul,mul_comm] using hh

 theorem gridNativeJet_time_bound (β : ℝ) (hβ : β ≠ 0) (j : ℕ) (μ : Paper.ParisiMeasure) (n : ℕ)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hrt : r ≤ t) (x : ℝ) :
    ‖parisiSpatialJet β (parisiGridMeasure μ n) (j+1) t x-
      parisiSpatialJet β (parisiGridMeasure μ n) (j+1) r x‖ ≤ nativeJetTimeBound β j*(t-r) := by
  let T := fun i => min t (max r (hjbGridTime n i))
  let F := fun i => parisiSpatialJet β (parisiGridMeasure μ n) (j+1) (T i) x
  have hgrid : Monotone (hjbGridTime n) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hTmono : Monotone T := (monotone_const.min (monotone_const.max hgrid))
  have htel := parisiGradientMesh_norm_telescope F (fun _ => nativeJetTimeBound β j) T (n+1)
    (fun _ _ => intervalIntegrable_const) (by
      intro i hi
      by_cases he : T i=T (i+1)
      · simp only [F,he,sub_self,intervalIntegral.integral_same,norm_zero,le_refl]
      · have hlt : T i<T (i+1) := lt_of_le_of_ne (hTmono (Nat.le_succ i)) he
        have hir : r<hjbGridTime n (i+1) := by
          by_contra hh
          have hmax0 : max r (hjbGridTime n i)=r := max_eq_left
            ((hgrid (Nat.le_succ i)).trans (le_of_not_gt hh))
          have hmax1 : max r (hjbGridTime n (i+1))=r := max_eq_left (le_of_not_gt hh)
          exact he (by simp only [T,hmax0,hmax1])
        have hit : hjbGridTime n i<t := by
          by_contra hh
          have hmin0 : min t (max r (hjbGridTime n i))=t := min_eq_left
            ((le_of_not_gt hh).trans (le_max_right _ _))
          have hmin1 : min t (max r (hjbGridTime n (i+1)))=t := min_eq_left
            (((le_of_not_gt hh).trans (hgrid (Nat.le_succ i))).trans (le_max_right _ _))
          exact he (by simp only [T,hmin0,hmin1])
        have ha : hjbGridTime n i≤T i := le_min hit.le (le_max_right _ _)
        have hb : T (i+1)≤hjbGridTime n (i+1) := by
          dsimp only [T]
          rw [max_eq_right hir.le]
          exact min_le_right _ _
        let s := parisiGridRSBScheme μ n
        obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q μ n i hi
        have hq : s.q (i+1)<s.q (i+1+1) := by
          simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hjbGridTime_step_lt n i
        have hh := finiteNativeJet_time_cell_bound β hβ j s (p:=i+1) (by omega) hq
          (by simpa only [s,hq0] using ha) hlt.le
          (by simpa only [s,show i+1+1=i+2 by omega,hq1] using hb) x
        rw [parisiSchemeMeasure_grid_eq μ n] at hh
        simpa only [F,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh)
  have hg0 : hjbGridTime n 0=0 := by simp [hjbGridTime]
  have hg1 : hjbGridTime n (n+1)=1 := by
    unfold hjbGridTime
    exact div_self (by positivity)
  have h0 : T 0=r := by simp only [T,hg0,max_eq_left hr.1,min_eq_right hrt]
  have h1 : T (n+1)=t := by simp only [T,hg1,max_eq_right hr.2,min_eq_left ht.2]
  simpa only [F,h0,h1,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using htel

theorem nativeSpatialJet_grid_tendsto (β:ℝ) (μ:Paper.ParisiMeasure)
    (j:ℕ) (t x:ℝ) (ht:t∈Icc (0:ℝ) 1) :
    Tendsto (fun n=>parisiSpatialJet β (parisiGridMeasure μ n) (j+1) t x)
      atTop (𝓝 (parisiSpatialJet β μ (j+1) t x)) := by
  have h:=(BoundedContinuousFunction.evalCLM ℝ (⟨t,ht⟩,x)).continuous.continuousAt.tendsto.comp
    (tendsto_spatialDerivativeBCF_of_weak β j μ (parisiGridMeasure μ)
      (tendsto_parisiGridMeasure μ))
  simpa only [Function.comp_def,BoundedContinuousFunction.evalCLM_apply,parisiSpatialJet,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
    Paper.parisiSlabExtend,projIcc_of_mem _ ht] using h

theorem nativeSpatialJet_time_bound (β:ℝ) (hβ:β≠0) (μ:Paper.ParisiMeasure)
    (j:ℕ) {r t:ℝ} (hr:r∈Icc (0:ℝ) 1) (ht:t∈Icc (0:ℝ) 1) (x:ℝ) :
    ‖parisiSpatialJet β μ (j+1) t x-parisiSpatialJet β μ (j+1) r x‖≤
      nativeJetTimeBound β j*‖t-r‖ := by
  wlog hrt:r≤t generalizing r t
  · have hh:=this ht hr (le_of_not_ge hrt)
    simpa only [norm_sub_rev] using hh
  have hh:=le_of_tendsto
    (((nativeSpatialJet_grid_tendsto β μ j t x ht).sub
      (nativeSpatialJet_grid_tendsto β μ j r x hr)).norm)
    (.of_forall fun n=>gridNativeJet_time_bound β hβ j μ n hr ht hrt x)
  simpa only [Real.norm_of_nonneg (sub_nonneg.mpr hrt)] using hh


end HexagonPaper
