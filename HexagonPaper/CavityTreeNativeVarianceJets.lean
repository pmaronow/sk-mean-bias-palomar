module
public import HexagonPaper.CavityTreeNativeAllJets
public import QuantitativeFollowup.AnisotropicVariancePotentialContinuity

@[expose] public section

/-! Actual joint continuity of every native row/field jet as the positive
auxiliary variance varies. This follows from the genuine uniform variance
stability, actual spatial smoothness, and uniform positive jet bounds. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ContDiff
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem cavityTree_native_tail_variance_joint_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n):
    Continuous (fun z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n=>
      anisotropicMeasureTailPotential (anisotropicReplaceVariance D i z.1.1.val) μ z.1.2 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let F:=fun z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n=>
    anisotropicMeasureTailPotential (anisotropicReplaceVariance D i z.1.1.val) μ z.1.2 z.2
  let G:=fun z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n=>
    anisotropicMeasureTailPotential (anisotropicReplaceVariance D i z₀.1.1.val) μ z.1.2 z.2
  have hb (z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n):
      ‖F z-G z‖≤(1/2:ℝ)*|z.1.1.val-z₀.1.1.val| := by
    have h:=anisotropicMeasureTailPotential_variance_abs_sub_le D μ z.1.2 z.2 i
      z.1.1.val z₀.1.1.val z.1.1.property z₀.1.1.property
    rw [Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith [z.1.2.property.1]) (abs_nonneg _))
  have ht:Tendsto (fun z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n=>
      (1/2:ℝ)*|z.1.1.val-z₀.1.1.val|) (𝓝 z₀) (𝓝 0) := by
    have hc:Continuous (fun z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n=>
      (1/2:ℝ)*|z.1.1.val-z₀.1.1.val|):=by fun_prop
    simpa only [sub_self,abs_zero,mul_zero] using hc.tendsto z₀
  have hd:Tendsto (fun z=>F z-G z) (𝓝 z₀) (𝓝 0):=
    squeeze_zero_norm hb ht
  let V:C(Paper.Overlap×AnisotropicParameter n,ℝ):=
    ⟨fun z=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i z₀.1.1.val) μ z.1 z.2,
      continuous_anisotropicMeasureTailPotential_joint (anisotropicReplaceVariance D i z₀.1.1.val) μ⟩
  let A:C(({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n,Paper.Overlap×AnisotropicParameter n):=
    ⟨fun z=>(z.1.2,z.2),(continuous_snd.comp continuous_fst).prodMk continuous_snd⟩
  have hg:Continuous G:=by
    convert (V.comp A).continuous using 1
    rfl
  have hh:=hd.add (hg.tendsto z₀)
  change Tendsto F (𝓝 z₀) (𝓝 (F z₀))
  have hz:G z₀=F z₀:=rfl
  simpa only [sub_add_cancel,zero_add,hz] using hh

theorem cavityTree_native_tail_variance_jet_joint_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) (r : ℕ):
    Continuous (fun z:({b:ℝ//0<b}×Paper.Overlap)×AnisotropicParameter n=>
      iteratedFDeriv ℝ r (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i z.1.1.val)
        μ z.1.2) z.2) := by
  apply continuous_iteratedFDeriv_family_of_uniform_jet_bounds _
    (cavityTree_native_tail_variance_joint_continuous D μ i)
    (fun z=>(cavityTree_native_tail_smooth_and_jets (anisotropicReplaceVariance D i z.1.val) μ z.2).1)
    (anisotropicSpatialJetBound D) (anisotropicSpatialJetBound_nonneg D) _ r
  intro k hk z P
  have h:=cavityTree_native_tail_positive_jet_bound (anisotropicReplaceVariance D i z.1.val) μ z.2 k
    (by omega) P
  unfold anisotropicSpatialJetBound at h
  rw [anisotropicReplaceVariance_energyMap] at h
  exact h

end HexagonPaper
