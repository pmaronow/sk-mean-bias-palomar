module
public import QuantitativePaper.ResponseCroppedMidpoint
public import FourPapersCommon.ClosedNonnegativeSourceFTC

@[expose] public section

/-! Genuine weighted curvature integrability and midpoint bound without
endpoint first- or second-derivative hypotheses. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 2000000

theorem response_nonnegative_curvature_midpoint_bound (f f₁ f₂ : ℝ→ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) (hconv : ConvexOn ℝ (Icc (0:ℝ) 1) f)
    (hdf : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f (f₁ x) x)
    (hdf₁ : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f₁ (f₂ x) x)
    (hnonneg : ∀x∈Ioo (0:ℝ) 1,0≤f₂ x)
    (hi₂ : ∀a∈Ioo (0:ℝ) 1,∀b∈Ioo (0:ℝ) 1,a≤b→IntervalIntegrable f₂ volume a b) :
    IntervalIntegrable (fun θ=>min θ (1-θ)*f₂ θ) volume 0 1 ∧
      (∫θ in (0:ℝ)..1,min θ (1-θ)*f₂ θ)≤f 0+f 1-2*f (1/2):=by
  let l:=sourceLeftCrop 0 1
  let u:=sourceRightCrop 0 1
  let g : ℝ→ℝ:=fun θ=>min θ (1-θ)*f₂ θ
  have hbds (j : ℕ):0<l j ∧ l j<1/2 ∧ 1/2<u j ∧ u j<1:=by
    have hh:=sourceCrop_bounds (by norm_num : (0:ℝ)<1) j
    have he : l j+u j=1:=by dsimp [l,u,sourceLeftCrop,sourceRightCrop];ring
    exact ⟨hh.1,by linarith [hh.2.1],by linarith [hh.2.1],hh.2.2⟩
  have hsub (j : ℕ):Ioc (l j) (u j)⊆Ioc (0:ℝ) 1:=fun x hx=>
    ⟨(hbds j).1.trans hx.1,hx.2.trans (hbds j).2.2.2.le⟩
  have hlocal (j : ℕ):IntervalIntegrable g volume (l j) (u j):=by
    apply (hi₂ (l j) ⟨(hbds j).1,by linarith [(hbds j).2.1]⟩
      (u j) ⟨by linarith [(hbds j).2.2.1],(hbds j).2.2.2⟩ (by linarith [(hbds j).2.1,(hbds j).2.2.1])).continuousOn_mul
    exact (continuous_id.min (continuous_const.sub continuous_id)).continuousOn
  have hfi (j : ℕ):IntegrableOn g (Ioc (l j) (u j)) (volume.restrict (Ioc (0:ℝ) 1)):=by
    rw [IntegrableOn,Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (hsub j)]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [(hbds j).2.1,(hbds j).2.2.1])).mp (hlocal j)
  have hcover : AECover (volume.restrict (Ioc (0:ℝ) 1)) atTop (fun j=>Ioc (l j) (u j)):=
    aecover_Ioc_of_Ioc (tendsto_sourceLeftCrop 0 1) (tendsto_sourceRightCrop 0 1)
  have hng : 0≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)] g:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with x hx hx1
    exact mul_nonneg (le_min hx.1.le (by linarith [hx.2]))
      (hnonneg x ⟨hx.1,lt_of_le_of_ne hx.2 hx1⟩)
  have hbounded (j : ℕ):(∫x in Ioc (l j) (u j),g x∂volume.restrict (Ioc (0:ℝ) 1))≤
      f 0+f 1-2*f (1/2):=by
    rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (hsub j)]
    rw [←intervalIntegral.integral_of_le (by linarith [(hbds j).2.1,(hbds j).2.2.1] : l j≤u j)]
    exact response_cropped_curvature_le_midpoint f f₁ f₂ hf hconv hdf hdf₁ (l j) (u j)
      (hbds j).1 (hbds j).2.1 (hbds j).2.2.1 (hbds j).2.2.2
      (hi₂ _ ⟨(hbds j).1,by linarith [(hbds j).2.1]⟩ _
        ⟨by linarith [(hbds j).2.2.1],(hbds j).2.2.2⟩ (by linarith [(hbds j).2.1,(hbds j).2.2.1]))
  have hi:=hcover.integrable_of_integral_bounded_of_nonneg_ae
    (f 0+f 1-2*f (1/2)) hfi hng (.of_forall hbounded)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hi,?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  exact le_of_tendsto (hcover.integral_tendsto_of_countably_generated hi) (.of_forall hbounded)

end QuantitativePaper
