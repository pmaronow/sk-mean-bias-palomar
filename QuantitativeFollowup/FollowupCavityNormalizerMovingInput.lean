module
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! A moving-input chain rule that only needs continuity of the spatial
partial differential. The parameter derivative is taken at the fixed
starting input, so joint parameter-derivative continuity is not assumed. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

private theorem moving_spatial_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ→E→ℝ) (g : ℝ→E) (u : ℝ)
    (hF : ∀t,Differentiable ℝ (F t))
    (hc : ContinuousAt (fun z : ℝ×E=>fderiv ℝ (F z.1) z.2) (u,g u))
    (hg : ContinuousAt g u) :
    (fun t=>F t (g t)-F t (g u)-fderiv ℝ (F u) (g u) (g t-g u)) =o[𝓝 u]
      (fun t=>g t-g u) := by
  rw [isLittleO_iff]
  intro ε hε
  have hct : Tendsto (fun z : ℝ×E=>fderiv ℝ (F z.1) z.2)
      (𝓝 u ×ˢ 𝓝 (g u)) (𝓝 (fderiv ℝ (F u) (g u))) := by
    simpa only [ContinuousAt,nhds_prod_eq] using hc
  have hc' : ∀ᶠt in 𝓝 u,∀z∈segment ℝ (g u) (g t),
      ‖fderiv ℝ (F t) z-fderiv ℝ (F u) (g u)‖<ε := by
    simp_rw [Metric.tendsto_nhds,dist_eq_norm_sub] at hct
    exact (hct ε hε).segment_of_prod_nhds tendsto_const_nhds hg

  filter_upwards [hc'] with t ht
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _=>(hF t z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz=>(ht z hz).le) (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

 theorem hasDerivAt_moving_input_of_spatial_differential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ→E→ℝ) (g : ℝ→E) (u d : ℝ) (g' : E)
    (hF : ∀t,Differentiable ℝ (F t))
    (hc : ContinuousAt (fun z : ℝ×E=>fderiv ℝ (F z.1) z.2) (u,g u))
    (hd : HasDerivAt (fun t=>F t (g u)) d u) (hg : HasDerivAt g g' u) :
    HasDerivAt (fun t=>F t (g t)) (d+fderiv ℝ (F u) (g u) g') u := by
  let D:=fderiv ℝ (F u) (g u)
  have he : (fun t=>F t (g t)-F t (g u)-D (g t-g u)) =o[𝓝 u]
      (fun t=>g t-g u) := by
    exact moving_spatial_remainder F g u hF hc hg.continuousAt
  have he':=(he.trans_isBigO hg.isBigO_sub)
  have hlin:=D.hasFDerivAt.comp_hasDerivAt u (hg.sub_const (g u))
  have hs:=(hd.add hlin).isLittleO
  apply HasDerivAt.of_isLittleO
  convert he'.add hs using 1
  · funext t
    simp only [D,Pi.add_apply,Function.comp_apply,map_sub,sub_self,map_zero,smul_eq_mul]
    ring

end QuantitativeFollowup
