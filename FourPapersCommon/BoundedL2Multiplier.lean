module
public import FourPapersCommon.EndpointFixedL2Compression

@[expose] public section

/-! Multiplication by a genuine bounded measurable coefficient on L² and
on its closed endpoint-fixed subspace. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem memLp_boundedCoefficient_mul (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) (f : Lp ℝ 2 ν) :
    MemLp (fun q=>k q*f q) 2 ν := by
  apply (Lp.memLp f).of_le_mul (c:=K) (hk.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact .of_forall fun q=>by change ‖k q*f q‖ ≤ K*‖f q‖;rw [norm_mul];exact mul_le_mul_of_nonneg_right (hK q) (norm_nonneg _)

def boundedCoefficientLp (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) (f : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  (memLp_boundedCoefficient_mul ν k hk K hK f).toLp (fun q=>k q*f q)

theorem boundedCoefficientLp_coeFn (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) (f : Lp ℝ 2 ν) :
    boundedCoefficientLp ν k hk K hK f=ᵐ[ν]fun q=>k q*f q :=
  (memLp_boundedCoefficient_mul ν k hk K hK f).coeFn_toLp

def boundedL2Multiplier (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) : Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 ν :=
  ({toFun:=boundedCoefficientLp ν k hk K hK
    map_add':=by
      intro f g
      change boundedCoefficientLp ν k hk K hK (f+g)=boundedCoefficientLp ν k hk K hK f+boundedCoefficientLp ν k hk K hK g
      apply Lp.ext
      filter_upwards [boundedCoefficientLp_coeFn ν k hk K hK (f+g),
        boundedCoefficientLp_coeFn ν k hk K hK f,boundedCoefficientLp_coeFn ν k hk K hK g,
        Lp.coeFn_add f g,Lp.coeFn_add (boundedCoefficientLp ν k hk K hK f) (boundedCoefficientLp ν k hk K hK g)] with q hfg hf hg hin hout
      simp only [hfg,hout,Pi.add_apply,hf,hg,hin]
      ring
    map_smul':=by
      intro c f
      change boundedCoefficientLp ν k hk K hK (c • f)=c • boundedCoefficientLp ν k hk K hK f
      apply Lp.ext
      filter_upwards [boundedCoefficientLp_coeFn ν k hk K hK (c • f),
        boundedCoefficientLp_coeFn ν k hk K hK f,Lp.coeFn_smul c f,
        Lp.coeFn_smul c (boundedCoefficientLp ν k hk K hK f)] with q hcf hf hin hout
      simp only [hcf,hout,Pi.smul_apply,hf,hin,smul_eq_mul]
      ring
    } : Lp ℝ 2 ν→ₗ[ℝ]Lp ℝ 2 ν).mkContinuous K (fun f=>by
      change ‖boundedCoefficientLp ν k hk K hK f‖ ≤ K*‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [boundedCoefficientLp_coeFn ν k hk K hK f] with q hq
      rw [hq,norm_mul]
      exact mul_le_mul_of_nonneg_right (hK q) (norm_nonneg _))

def endpointFixedL2Multiplier (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) : endpointFixedL2 ν→L[ℝ]endpointFixedL2 ν :=
  (boundedL2Multiplier ν k hk K hK).restrict (fun f hf=>by
    rw [mem_endpointFixedL2_iff] at hf ⊢
    filter_upwards [boundedCoefficientLp_coeFn ν k hk K hK f,hf] with q hq he
    intro h
    change boundedCoefficientLp ν k hk K hK f q=0
    rw [hq,he h,mul_zero])

theorem endpointFixedL2Multiplier_coeFn (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) (f : endpointFixedL2 ν) :
    (endpointFixedL2Multiplier ν k hk K hK f : Lp ℝ 2 ν)=ᵐ[ν]fun q=>k q*f.val q :=
  boundedCoefficientLp_coeFn ν k hk K hK f.val

theorem endpointFixedL2Multiplier_inner (ν : Measure Paper.Overlap) (k : Paper.Overlap→ℝ)
    (hk : Measurable k) (K : ℝ) (hK : ∀q,‖k q‖ ≤ K) (f : endpointFixedL2 ν) :
    inner ℝ f (endpointFixedL2Multiplier ν k hk K hK f)=∫q,k q*(f.val q)^2 ∂ν := by
  change inner ℝ f.val (endpointFixedL2Multiplier ν k hk K hK f).val=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [endpointFixedL2Multiplier_coeFn ν k hk K hK f] with q hq
  rw [hq]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end FourPapersCommon
