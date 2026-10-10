module
public import QuantitativeFollowup.AnisotropicVarianceResponseFinite
public import QuantitativeFollowup.AnisotropicTailContinuity
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Genuine stability under a positive diagonal covariance perturbation.
The finite response bound is uniform in depth, restart time and starting
parameter, so it passes to the actual arbitrary-profile potential. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
variable {n k : ℕ}

theorem anisotropicFiniteTailPotential_variance_abs_sub_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n)
    (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    |anisotropicFiniteTailPotential (anisotropicReplaceVariance D i b) s q P-
      anisotropicFiniteTailPotential (anisotropicReplaceVariance D i c) s q P|≤
      ((1-(q:ℝ))/2)*|b-c| := by
  have hd (x : ℝ) (hx : x∈Ioi (0:ℝ)):=
    (hasDerivAt_anisotropicFiniteTailPotential_variance D s q P i x hx).hasDerivWithinAt (s:=Ioi 0)
  have hbound (x : ℝ) (_ : x∈Ioi (0:ℝ)) :
      ‖anisotropicFiniteTailVarianceResponse (anisotropicReplaceVariance D i x) s q P i‖≤
      (1-(q:ℝ))/2 := by
    have he:=anisotropicFiniteTailVarianceResponse_mem_Icc (anisotropicReplaceVariance D i x) s q P i
    simpa only [Real.norm_eq_abs,abs_of_nonneg he.1] using he.2
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Ioi (0:ℝ)) hc hb

theorem anisotropicFiniteTailPotential_variance_abs_sub_le_half (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n)
    (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    |anisotropicFiniteTailPotential (anisotropicReplaceVariance D i b) s q P-
      anisotropicFiniteTailPotential (anisotropicReplaceVariance D i c) s q P|≤
      (1/2 : ℝ)*|b-c| :=
  (anisotropicFiniteTailPotential_variance_abs_sub_le D s q P i b c hb hc).trans
    (mul_le_mul_of_nonneg_right (by linarith [q.property.1]) (abs_nonneg _))

theorem anisotropicMeasureTailPotential_variance_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n)
    (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    |anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q P-
      anisotropicMeasureTailPotential (anisotropicReplaceVariance D i c) μ q P|≤
      ((1-(q:ℝ))/2)*|b-c| := by
  have ht:=((tendsto_anisotropicDyadicTailPotential (anisotropicReplaceVariance D i b) μ q P).sub
    (tendsto_anisotropicDyadicTailPotential (anisotropicReplaceVariance D i c) μ q P)).abs
  apply le_of_tendsto ht
  exact .of_forall fun j=>anisotropicFiniteTailPotential_variance_abs_sub_le D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q P i b c hb hc

theorem tendstoUniformly_anisotropicVarianceDyadicTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) :
    TendstoUniformly (fun j=>fun z : Paper.Overlap×AnisotropicParameter n=>
      anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ z.1 j z.2)
      (fun z=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ z.1 z.2)
        atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have heps : 0<ε/2:=by positivity
  have hu:=tendstoUniformly_anisotropicDyadicTailPotential (anisotropicReplaceVariance D i b) μ
  rw [Metric.tendstoUniformly_iff] at hu
  have hn : ∀ᶠj in atTop,(1/2 : ℝ)*|bj j-b|<ε/2 := by
    have hlim:=((ht.sub (tendsto_const_nhds (x:=b))).abs).const_mul (1/2 : ℝ)
    simp only [sub_self,abs_zero,mul_zero] at hlim
    exact hlim.eventually (gt_mem_nhds heps)
  filter_upwards [hu (ε/2) heps,hn,ht.eventually (Ioi_mem_nhds hb)] with j hj hbj hpos
  intro z
  have hf:=anisotropicFiniteTailPotential_variance_abs_sub_le_half D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) z.1 z.2 i (bj j) b hpos hb
  have hg:=hj z
  rw [Real.dist_eq,abs_sub_comm] at hg
  rw [Real.dist_eq,abs_sub_comm]
  change |anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ z.1 j z.2-
    anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ z.1 z.2|<ε
  apply (abs_sub_le _ (anisotropicDyadicTailPotential (anisotropicReplaceVariance D i b) μ z.1 j z.2) _).trans_lt
  have hf' : |anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ z.1 j z.2-
      anisotropicDyadicTailPotential (anisotropicReplaceVariance D i b) μ z.1 j z.2|<ε/2 :=
    hf.trans_lt hbj
  linarith

theorem tendsto_anisotropicVarianceDyadicTailPotential_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b))
    {zj : ℕ→Paper.Overlap×AnisotropicParameter n} {z : Paper.Overlap×AnisotropicParameter n}
    (hz : Tendsto zj atTop (𝓝 z)) :
    Tendsto (fun j=>anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j))
      μ (zj j).1 j (zj j).2) atTop
      (𝓝 (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ z.1 z.2)) :=
  (tendstoUniformly_anisotropicVarianceDyadicTailPotential D μ i hb ht).tendsto_comp
    (continuous_anisotropicMeasureTailPotential_joint (anisotropicReplaceVariance D i b) μ).continuousAt hz

end QuantitativeFollowup
