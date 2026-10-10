module
public import FRSB.SupportMinimum
public import FRSB.TerminalOverlap
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! The actual support maximum lies within one inverse temperature of one.
The contact and curvature inequalities are supplied by actual minimality. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace QuantitativePaper
open FRSB
set_option maxHeartbeats 800000

theorem scalar_support_max_ge_one_sub_inv (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hμ : FRSB.IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈parisiSupport μ)
    (hmax : ∀x∈parisiSupport μ,x≤q) : 1-1/β≤q := by
  have hqI:=FRSB.parisiSupport_subset μ hq
  obtain ⟨r,hr,hrq⟩:=hq
  have hg:=FRSB.Gamma_eq_overlap_of_support β hβ.ne' μ hμ r hr
  have hp:=FRSB.GammaPrime_le_one_of_support β hβ.ne' μ hμ r hr
  rw [hrq] at hg hp
  have hid (ω : Paper.BrownianSample) :
      FRSB.C β μ q ω=1-(FRSB.M β μ q ω)^2 := by
    rw [FRSB.C_eq_hessian]
    simp only [FRSB.M,FRSB.jetProcess,FRSB.parisiSpatialJet_one]
    rw [FRSB.parisiHessian_terminal_region β hβ.ne' μ hqI hmax ⟨le_rfl,hqI.2⟩,
      FRSB.parisiGradient_terminal_region β hβ.ne' μ hqI hmax ⟨le_rfl,hqI.2⟩]
    linarith [tanh_sq_add_sech_sq (FRSB.optimalStateReal β μ ω q)]
  have hmem : MemLp (FRSB.C β μ q) 2 canonicalBrownianMeasure :=
    MemLp.of_bound (FRSB.measurable_C β hβ.ne' μ hqI).aestronglyMeasurable 1
      (.of_forall fun ω=>FRSB.norm_C_le_one β μ q ω)
  have hint : (∫ω,FRSB.C β μ q ω ∂canonicalBrownianMeasure)=1-q := by
    simp_rw [hid]
    rw [integral_sub (integrable_const 1) (FRSB.integrable_M_sq β μ q hqI),
      integral_const]
    try simp only [probReal_univ,one_smul]
    exact congrArg (fun x:ℝ=>1-x) hg
  have hv:=variance_nonneg (FRSB.C β μ q) canonicalBrownianMeasure
  rw [variance_eq_sub hmem,hint] at hv
  change 0≤FRSB.curvatureMoment2 β μ q-(1-q)^2 at hv
  change β^2*FRSB.curvatureMoment2 β μ q≤1 at hp
  have hmul:=mul_le_mul_of_nonneg_left (show (1-q)^2≤FRSB.curvatureMoment2 β μ q by linarith)
    (sq_nonneg β)
  have hinv : 0<1/β:=one_div_pos.mpr hβ
  have he : β^2*(1/β)^2=1:=by field_simp
  have hsq : (1-q)^2≤(1/β)^2:=by
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hβ)).mp
    rw [he]
    exact hmul.trans hp
  have hlin : 1-q≤1/β:=(sq_le_sq₀ (sub_nonneg.mpr hqI.2) hinv.le).mp hsq
  linarith

theorem exists_scalar_support_endpoint_with_uniform_lower (β : ℝ) (hβ : 1<β)
    (μ : Paper.ParisiMeasure) (hμ : FRSB.IsParisiMinimizer β 0 μ) :
    ∃q∈Ioo (0:ℝ) 1, parisiSupport μ⊆Icc (0:ℝ) q ∧
      q∈parisiSupport μ ∧ 1-1/β≤q := by
  obtain ⟨q,hq,hz,htop,hsub⟩:=FRSB.minimizer_support_endpoints β hβ μ hμ
  exact ⟨q,hq,hsub,htop,scalar_support_max_ge_one_sub_inv β
    (zero_lt_one.trans hβ) μ hμ q htop (fun x hx=>(hsub hx).2)⟩

end QuantitativePaper
