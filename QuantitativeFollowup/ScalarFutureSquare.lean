module
public import QuantitativeFollowup.ScalarRestartKernel
public import QuantitativeFollowup.ScalarKernelPairings
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-! Actual fresh-restart square kernel and its conditional law.  This
identifies the paper's g_r^q, rather than introducing an arbitrary
conditional mean with the desired moments as assumptions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarFutureSquare (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) : ℝ → ℝ :=
  scalarTransitionExpectation β μ r q hrq (fun x => parisiGradient β μ (q,x)^2)

theorem measurable_scalarFutureSquare (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    Measurable (scalarFutureSquare β μ r q hrq) :=
  measurable_scalarTransitionExpectation β hβ μ r q hrq _
    (((continuous_parisiGradient β μ).measurable.comp (measurable_const.prodMk measurable_id)).pow_const 2)

theorem scalarFutureSquare_nonneg_le_one (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) :
    0 ≤ scalarFutureSquare β μ r q hrq x ∧ scalarFutureSquare β μ r q hrq x ≤ 1 := by
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  have hb := norm_scalarTransitionExpectation_le β μ r q hrq
    (fun y => parisiGradient β μ (q,y)^2) 1 (fun y => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ (q,y))) x
  change ‖scalarFutureSquare β μ r q hrq x‖ ≤ 1 at hb
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)

theorem scalarGradient_physicalSplitState (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (ω : Paper.BrownianSample) :
    parisiGradient β μ (q,parisiPhysicalSplitState β 0 μ q ω)=M β μ q ω := by
  simp only [parisiPhysicalSplitState,parisiNoiseStatePath_canonical β 0 hβ,
    M,jetProcess,parisiSpatialJet_one,optimalStateReal_eq_selected β hβ μ]

def scalarFutureSquareProcess (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (ω : Paper.BrownianSample) : ℝ :=
  scalarFutureSquare β μ r q hrq (parisiPhysicalSplitState β 0 μ r ω)

theorem measurable_scalarFutureSquareProcess_past (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    Measurable[canonicalBrownianFiltration (r : ℝ).toNNReal]
      (scalarFutureSquareProcess β μ r q hrq) :=
  (measurable_scalarFutureSquare β hβ μ r q hrq).comp
    (measurable_parisiPhysicalSplitState_past β 0 hβ μ r)

theorem scalarFutureSquareProcess_memLp_two (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    MemLp (scalarFutureSquareProcess β μ r q hrq) 2 canonicalBrownianMeasure := by
  apply MemLp.of_bound ((measurable_scalarFutureSquareProcess_past β hβ μ r q hrq).mono
    (canonicalBrownianFiltration.le _) le_rfl).aestronglyMeasurable 1
  exact .of_forall fun ω => by
    change ‖scalarFutureSquare β μ r q hrq (parisiPhysicalSplitState β 0 μ r ω)‖ ≤ 1
    rw [Real.norm_of_nonneg (scalarFutureSquare_nonneg_le_one β μ r q hrq _).1]
    exact (scalarFutureSquare_nonneg_le_one β μ r q hrq _).2

theorem scalarFutureSquare_weighted_expectation (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q)
    (Z : Paper.BrownianSample → ℝ)
    (hZ : Measurable[canonicalBrownianFiltration (r : ℝ).toNNReal] Z)
    (K : ℝ) (hbZ : ∀ ω, ‖Z ω‖ ≤ K) :
    (∫ ω, Z ω * M β μ q ω^2 ∂canonicalBrownianMeasure)=
      ∫ ω, Z ω * scalarFutureSquareProcess β μ r q hrq ω ∂canonicalBrownianMeasure := by
  have hbF : ∀ x : ℝ, ‖parisiGradient β μ (q,x)^2‖ ≤ 1 := by
    intro x
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ (q,x))
  have he := scalarTransition_weighted_expectation β 0 hβ μ r q hrq
    (fun x => parisiGradient β μ (q,x)^2)
    (((continuous_parisiGradient β μ).measurable.comp (measurable_const.prodMk measurable_id)).pow_const 2)
    1 hbF Z hZ K hbZ
  simpa only [scalarGradient_physicalSplitState β hβ μ,
    scalarFutureSquareProcess,scalarFutureSquare] using he

theorem integral_scalarFutureSquareProcess (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    (∫ ω, scalarFutureSquareProcess β μ r q hrq ω ∂canonicalBrownianMeasure)=Gamma β μ q := by
  simpa only [one_mul,Gamma] using (scalarFutureSquare_weighted_expectation β hβ μ r q hrq
    (fun _ => 1) measurable_const 1 (fun _ => by norm_num)).symm

/-- True whole-past conditional expectation for the explicit restart kernel. -/
theorem condExp_scalarFutureSquareProcess (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    canonicalBrownianMeasure[(fun ω => M β μ q ω^2) |
      canonicalBrownianFiltration (r : ℝ).toNNReal]=ᵐ[canonicalBrownianMeasure]
      scalarFutureSquareProcess β μ r q hrq := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (canonicalBrownianFiltration.le _)
    (integrable_M_sq β μ q q.property)
  · intro A hA hfinite
    exact (scalarFutureSquareProcess_memLp_two β hβ μ r q hrq).integrable (by norm_num) |>.integrableOn
  · intro A hA hfinite
    let Z : Paper.BrownianSample → ℝ := A.indicator (fun _ => 1)
    have hZ : Measurable[canonicalBrownianFiltration (r : ℝ).toNNReal] Z :=
      measurable_const.indicator hA
    have hbZ : ∀ ω, ‖Z ω‖ ≤ 1 := by
      intro ω
      by_cases hω : ω∈A <;> simp [Z,hω]
    have he := scalarFutureSquare_weighted_expectation β hβ μ r q hrq Z hZ 1 hbZ
    have hAm := (canonicalBrownianFiltration.le (r : ℝ).toNNReal) A hA
    have hind (f : Paper.BrownianSample → ℝ) :
        (∫ ω, Z ω * f ω ∂canonicalBrownianMeasure)=∫ ω in A,f ω ∂canonicalBrownianMeasure := by
      rw [← integral_indicator hAm]
      apply integral_congr_ae
      exact .of_forall fun ω => by
        by_cases hω : ω∈A <;> simp [Z,hω]
    rw [hind,hind] at he
    exact he.symm
  · exact (measurable_scalarFutureSquareProcess_past β hβ μ r q hrq).aestronglyMeasurable

theorem scalarFutureSquare_variance_bound (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    variance (scalarFutureSquareProcess β μ r q hrq) canonicalBrownianMeasure ≤ Gamma β μ q := by
  have hf := scalarFutureSquareProcess_memLp_two β hβ μ r q hrq
  have hsq := integral_mono hf.integrable_sq (hf.integrable (by norm_num)) (fun ω => by
    have hb := scalarFutureSquare_nonneg_le_one β μ r q hrq (parisiPhysicalSplitState β 0 μ r ω)
    change scalarFutureSquare β μ r q hrq _^2 ≤ scalarFutureSquare β μ r q hrq _
    nlinarith)
  rw [integral_scalarFutureSquareProcess β hβ μ r q hrq] at hsq
  rw [variance_eq_sub hf,integral_scalarFutureSquareProcess β hβ μ r q hrq]
  change (∫ ω,scalarFutureSquareProcess β μ r q hrq ω^2 ∂canonicalBrownianMeasure)-
    Gamma β μ q^2 ≤ Gamma β μ q
  linarith [sq_nonneg (Gamma β μ q)]

/-- Literal covariance bound (6.2, final clause), with the constructed g. -/
theorem scalar_square_future_covariance_bound (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    |covariance (fun ω => M β μ r ω^2) (scalarFutureSquareProcess β μ r q hrq)
      canonicalBrownianMeasure| ≤ Real.sqrt (Gamma β μ r * Gamma β μ q) := by
  let g := scalarFutureSquareProcess β μ r q hrq
  let g0 := fun ω => g ω-Gamma β μ q
  have hg := scalarFutureSquareProcess_memLp_two β hβ μ r q hrq
  have hg0 : MemLp g0 2 canonicalBrownianMeasure := hg.sub (memLp_const _)
  have hvar : (∫ ω,g0 ω^2 ∂canonicalBrownianMeasure) ≤ Gamma β μ q := by
    have he : (∫ ω,g0 ω^2 ∂canonicalBrownianMeasure)=variance g canonicalBrownianMeasure := by
      rw [variance_eq_integral hg.aestronglyMeasurable.aemeasurable,
        integral_scalarFutureSquareProcess β hβ μ r q hrq]
    rw [he]
    exact scalarFutureSquare_variance_bound β hβ μ r q hrq
  have hcs := integral_mul_abs_le_sqrt_moment_bounds _ _
    (scalarCenteredSquare_memLp_two β μ r r.property) hg0 _ _
    (scalarCenteredSquare_secondMoment_le β μ r r.property) hvar
  simpa only [covariance,Gamma,scalarCenteredSquare,g0,g,
    integral_scalarFutureSquareProcess β hβ μ r q hrq] using hcs

end QuantitativeFollowup
