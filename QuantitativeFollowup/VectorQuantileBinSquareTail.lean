module
public import QuantitativeFollowup.KernelLevelBounds
public import QuantitativeFollowup.VectorTwoSidedMoment
public import QuantitativeFollowup.VectorSelfOverlapMoments
public import FourPapersCommon.MonotoneBinIntervals

@[expose] public section

/-! Genuine second-moment and tail bounds inside a quantile level bin.
The level range describes the actual bin; all conditional-kernel, threshold
and endpoint-window inputs are constructed and discharged here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_quantile_bin_one_sided_square_tails (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (I : Set ℝ) (hI : I.OrdConnected) (hDom : I⊆Ioc (0:ℝ) (1-s))
    (a d u θ : ℝ) (hd : 0≤d) (hu : 0<u) (hθ : 0<θ) (hdθ : d≤θ/2)
    (hRange : ∀w∈I,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+d))
    (hThreshold : ∀ᵐw ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w))
    {v : ℝ} (hvI : v∈I) (hv : v∈Ioo (sInf I) (sSup I)) :
    (∫z,{z | θ<vectorCenteredSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v) z}.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht.le (parisiFreeQuantile μ s v) z^2) z
      ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤16*(1/((n:ℝ)*((1-t)*β^2)*u))/(sSup I-v) ∧
    (∫z,{z | vectorCenteredSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v) z< -θ}.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht.le (parisiFreeQuantile μ s v) z^2) z
      ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤16*(1/((n:ℝ)*((1-t)*β^2)*u))/(v-sInf I) := by
  have hb : BddBelow I:=⟨0,fun w hw=>(hDom hw).1.le⟩
  have ha : BddAbove I:=⟨1-s,fun w hw=>(hDom hw).2⟩
  have hwin:=ordConnected_inner_windows_subset I hI hb ha hv
  let Ip:=Ioo v (sSup I)
  let Im:=Ioo (sInf I) v
  let xp:=sSup I-v
  let xm:=v-sInf I
  let q:=parisiFreeQuantile μ s v
  let κp:=quantileSetKernel μ s Ip xp
  let κm:=quantileSetKernel μ s Im xm
  have hxp : 0<xp:=sub_pos.mpr hv.2
  have hxm : 0<xm:=sub_pos.mpr hv.1
  have hDp : Ip⊆Ioc (0:ℝ) (1-s):=hwin.2.trans hDom
  have hDm : Im⊆Ioc (0:ℝ) (1-s):=hwin.1.trans hDom
  have hlenp : volume.real Ip=xp:=by
    exact Real.volume_real_Ioo_of_le hv.2.le
  have hlenm : volume.real Im=xm:=by
    exact Real.volume_real_Ioo_of_le hv.1.le
  have hLp:=memLp_quantileSetKernel μ s Ip xp hxp
  have hLm:=memLp_quantileSetKernel μ s Im xm hxm
  have hnp:=integral_quantileSetKernel_normalized μ s Ip xp hDp hxp hlenp
  have hnm:=integral_quantileSetKernel_normalized μ s Im xm hDm hxm hlenm
  have hSp : ∀ᵐp ∂parisiFreeMeasure μ s,κp p≠0→q≤p := by
    apply ae_quantileSetKernel_future μ s Ip xp hDp q
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    exact parisiFreeQuantile_monotone μ s hw.1.le
  have hSm : ∀ᵐp ∂parisiFreeMeasure μ s,κm p≠0→p≤q := by
    apply ae_quantileSetKernel_past μ s Im xm hDm q
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    exact parisiFreeQuantile_monotone μ s hw.2.le
  have hrp : ∀ᵐw ∂volume.restrict Ip,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+d) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    exact hRange w (hwin.2 hw)
  have hrm : ∀ᵐw ∂volume.restrict Im,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+d) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    exact hRange w (hwin.1 hw)
  have hmeanp:=vectorKernelOverlapLevel_quantileSet_bounds μ s Ip xp hDp hxp hlenp a (a+d) hrp
  have hmeanm:=vectorKernelOverlapLevel_quantileSet_bounds μ s Im xm hDm hxm hlenm a (a+d) hrm
  have hqRange:=hRange v hvI
  have htp : ∀ᵐw ∂volume.restrict Ip,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w) :=
    hThreshold.filter_mono (ae_mono (Measure.restrict_mono_set volume hwin.2))
  have htm : ∀ᵐw ∂volume.restrict Im,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w) :=
    hThreshold.filter_mono (ae_mono (Measure.restrict_mono_set volume hwin.1))
  have hp:=vectorCenteredSelfOverlap_upper_tail hn μ s β t hβ ht hs hμ hmin
    κp (measurable_quantileSetKernel μ s Ip xp)
    (fun p=>(quantileSetKernel_nonneg_le μ s Ip xp hxp p).1)
    hLp hnp q hSp θ hθ (by dsimp only [q,κp];linarith [hmeanp.2,hqRange.1])
  have hm:=vectorCenteredSelfOverlap_lower_tail hn μ s β t hβ ht hs hμ hmin
    κm (measurable_quantileSetKernel μ s Im xm)
    (fun p=>(quantileSetKernel_nonneg_le μ s Im xm hxm p).1)
    hLm hnm q hSm θ hθ (by dsimp only [q,κm];linarith [hmeanm.1,hqRange.2])
  have hvp:=vector_quantile_set_score_variance hn μ s β t hβ ht hs hμ hmin Ip xp u hDp hxp hlenp hu htp
  have hvm:=vector_quantile_set_score_variance hn μ s β t hβ ht hs hμ hmin Im xm u hDm hxm hlenm hu htm
  constructor
  · exact hp.trans (by
      convert mul_le_mul_of_nonneg_left hvp (by norm_num : (0:ℝ)≤16) using 1 <;>
        simp only [xp,div_eq_mul_inv,mul_inv_rev] <;> ring)
  · exact hm.trans (by
      convert mul_le_mul_of_nonneg_left hvm (by norm_num : (0:ℝ)≤16) using 1 <;>
        simp only [xm,div_eq_mul_inv,mul_inv_rev] <;> ring)

end QuantitativeFollowup
