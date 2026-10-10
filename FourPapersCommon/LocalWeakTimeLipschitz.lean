module
public import FourPapersCommon.WeakTimeLipschitz

@[expose] public section

/-! A bound for the actual distributional source on one closed time strip
gives a Lipschitz bound on that strip, including its two endpoints. -/
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem norm_normedBump_convolution_le_on_strip (w : ℝ×ℝ→ℝ)
    (hw : Measurable w) (A B M : ℝ) (hM : 0≤M)
    (hb : ∀p:ℝ×ℝ,p.1∈Icc A B→‖w p‖≤M)
    (φ : ContDiffBump (0:ℝ×ℝ)) (p : ℝ×ℝ)
    (hR : φ.rOut ≤ min (p.1-A) (B-p.1)) :
    ‖(w ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (φ.normed volume)) p‖≤M := by
  have hh:=dist_convolution_le (μ:=volume) (x₀:=p) (z₀:=(0:ℝ)) hM
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed
    hw.aestronglyMeasurable (by
      intro y hy
      have hd : dist y.1 p.1<φ.rOut:=
        (le_max_left (dist y.1 p.1) (dist y.2 p.2)).trans_lt
          (show max (dist y.1 p.1) (dist y.2 p.2)<φ.rOut from hy)
      rw [Real.dist_eq,abs_lt] at hd
      have hyI : y.1∈Icc A B:=by
        constructor <;> linarith [hR.trans (min_le_left _ _),hR.trans (min_le_right _ _)]
      simpa only [dist_zero_right] using hb y hyI)
  rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by ext;rfl)]
  change ‖∫t,(φ.normed volume) t*w (p-t)‖≤M
  simpa only [dist_zero_right,convolution_def,lsmul_apply,smul_eq_mul] using hh

theorem weakTime_norm_sub_le_on_strip_interior (u w : ℝ×ℝ→ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (hwm : Measurable w) (A B M : ℝ) (hA : 0≤A) (hB : B≤1)
    (hb : ∀p:ℝ×ℝ,p.1∈Icc A B→‖w p‖≤M)
    (x : ℝ) {a b : ℝ} (ha : a∈Ioo A B) (hb' : b∈Ioo A B) (hab : a≤b) :
    ‖u (b,x)-u (a,x)‖≤M*(b-a) := by
  have hM : 0≤M := (norm_nonneg (w (a,x))).trans (hb (a,x) ⟨ha.1.le,ha.2.le⟩)
  let F : ℕ→ℝ→ℝ:=fun n t=>timeMollification u ((Paper.parisiPlaneBump n).normed volume) t x
  have hn : ∀ᶠn in atTop,(Paper.parisiPlaneBump n).rOut < min (a-A) (B-b) :=
    Paper.parisiPlaneBump_rOut_tendsto.eventually
      (eventually_lt_nhds (lt_min (sub_pos.mpr ha.1) (sub_pos.mpr hb'.2)))
  have hbound : ∀ᶠn in atTop,‖F n b-F n a‖≤M*(b-a) := by
    filter_upwards [hn] with n hn
    have hd (t : ℝ) (ht : t∈Icc a b) :=
      hasDerivAt_timeMollification_of_weak u w hu hw (Paper.parisiPlaneBump n) t x
        (by linarith [ht.1,hn.trans_le (min_le_left _ _)])
        (by linarith [ht.2,hn.trans_le (min_le_right _ _)])
    apply norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht=>(hd t ht).hasDerivWithinAt)
      (fun t ht=>norm_normedBump_convolution_le_on_strip w hwm A B M hM hb _ (t,x) (by
        change (Paper.parisiPlaneBump n).rOut ≤ min (t-A) (B-t)
        apply le_min
        · linarith [ht.1,hn.trans_le (min_le_left _ _)]
        · linarith [ht.2,hn.trans_le (min_le_right _ _)]))
      b ⟨hab,le_rfl⟩
  have hF (t : ℝ) : Tendsto (fun n=>F n t) atTop (𝓝 (u (t,x))) := by
    have hh:=ContDiffBump.convolution_tendsto_right_of_continuous (μ:=volume)
      Paper.parisiPlaneBump_rOut_tendsto hu (t,x)
    apply hh.congr
    intro n
    dsimp only [F,timeMollification]
    rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by ext;rfl)]
    rfl
  exact le_of_tendsto ((hF b).sub (hF a)).norm hbound

theorem lipschitzOnWith_weakTime_section_on_strip (u w : ℝ×ℝ→ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (hwm : Measurable w) (A B M : ℝ) (hA : 0≤A) (hB : B≤1) (hAB : A<B)
    (hb : ∀p:ℝ×ℝ,p.1∈Icc A B→‖w p‖≤M) (x : ℝ) :
    LipschitzOnWith M.toNNReal (fun t=>u (t,x)) (Icc A B) := by
  have hM : 0≤M := (norm_nonneg (w (A,x))).trans (hb (A,x) ⟨le_rfl,hAB.le⟩)
  have hi (a : ℝ) (ha : a∈Ioo A B) (b : ℝ) (hb' : b∈Ioo A B) :
      ‖u (a,x)-u (b,x)‖≤M*‖a-b‖ := by
    rcases le_total a b with hab|hba
    · simpa only [norm_sub_rev,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hab),neg_sub] using
        weakTime_norm_sub_le_on_strip_interior u w hu hw hwm A B M hA hB hb x ha hb' hab
    · simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hba)] using
        weakTime_norm_sub_le_on_strip_interior u w hu hw hwm A B M hA hB hb x hb' ha hba
  let S : Set (ℝ×ℝ):={p|‖u (p.1,x)-u (p.2,x)‖≤M*‖p.1-p.2‖}
  have hS : IsClosed S:=isClosed_le
    ((hu.comp (continuous_fst.prodMk continuous_const)).sub
      (hu.comp (continuous_snd.prodMk continuous_const))).norm
    (continuous_const.mul (continuous_fst.sub continuous_snd).norm)
  have hs : Ioo A B×ˢIoo A B⊆S:=fun p hp=>hi _ hp.1 _ hp.2
  have hc : Icc A B×ˢIcc A B⊆S:=by
    have hh:=closure_minimal hs hS
    simpa only [closure_prod_eq,closure_Ioo hAB.ne] using hh
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb'
  simpa only [S,mem_setOf_eq,dist_eq_norm,Real.coe_toNNReal _ hM] using
    (hc (show (a,b)∈Icc A B×ˢIcc A B from ⟨ha,hb'⟩))

end FourPapersCommon
