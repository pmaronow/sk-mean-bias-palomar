module
public import FourPapersCommon.FiniteStateCascadePosteriorStieltjes
public import FourPapersCommon.FiniteStateCascadeCovarianceComparison
public import QuantitativeFollowup.CanonicalJetBounds

@[expose] public section

/-! The actual full finite-state Hessian has norm at most one, uniformly in
all Gaussian maps, terminal offsets, masses, and cascade depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ContDiff BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT QuantitativeFollowup QuantitativePaper
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 150000

theorem finiteStateCascadeObservableVariance_le_norm_sq (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    finiteStateCascadeObservableVariance V a L j H K≤‖K‖^2 := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  rw [finiteStateCascadeObservableVariance_eq_variance V a ha L j H K]
  apply (variance_le_expectation_sq (measurable_of_finite _).aestronglyMeasurable).trans
  calc
    _≤∫_ : S,‖K‖^2 ∂finiteStateCascadeGibbsKernel V a L j H := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro σ
      simpa only [sq_abs,Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg (K σ))
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K σ) 2
    _=_ := by simp

theorem norm_finiteStateCascade_hessian_le_one (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    ‖hessianOperator (finiteStateGaussianTerminalCascade V a L j) H‖≤1 := by
  let F := finiteStateGaussianTerminalCascade V a L j
  have hs : (hessianOperator F H).IsSymmetric := by
    intro u v
    change inner ℝ (hessianOperator F H u) v=inner ℝ u (hessianOperator F H v)
    rw [inner_hessianOperator]
    conv_rhs=>rw [real_inner_comm]
    rw [inner_hessianOperator]
    exact ((contDiff_finiteStateGaussianTerminalCascade V a ha L j).contDiffAt.isSymmSndFDerivAt (by simp)).eq u v
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le
  intro K
  simp only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real,abs_div,abs_sq]
  rw [inner_hessianOperator,abs_of_nonneg (finiteStateCascadeHessian_nonneg V a ha L j H K)]
  have hb := (finiteStateCascadeHessian_covariance_bounds V a ha
    (fun i=>(hdec (Nat.zero_le i)).trans ha1) (fun i=>hdec (Nat.le_succ i)) L j H K).2.trans
      (finiteStateCascadeObservableVariance_le_norm_sq V a ha L j H K)
  by_cases hK : K=0
  · simp [hK,directionalHessian]
  · exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hK))).mpr (by simpa using hb)

theorem norm_finiteStateCascade_secondJet_le_one (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ 2 (finiteStateGaussianTerminalCascade V a L j) H‖≤1 := by
  have he := norm_iteratedFDeriv_hessianOperator (finiteStateGaussianTerminalCascade V a L j)
    ((contDiff_finiteStateGaussianTerminalCascade V a ha L j).of_le (by simp)) 0 (by omega) H
  simp only [norm_iteratedFDeriv_zero,zero_add] at he
  rw [←he]
  exact norm_finiteStateCascade_hessian_le_one V a ha ha1 hdec L j H

theorem norm_finiteStateCascade_firstJet_le_one (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ 1 (finiteStateGaussianTerminalCascade V a L j) H‖≤1 := by
  rw [norm_iteratedFDeriv_one]
  exact norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)

theorem norm_cascadeTerminal_affine_firstJet_le_one (V : S→ℝ) (w H : FiniteStateField S) (σ : S) :
    ‖iteratedFDeriv ℝ 1 (fun Q : FiniteStateField S=>V σ+(Q+w) σ) H‖≤1 := by
  have he : (fun Q : FiniteStateField S=>V σ+(Q+w) σ)=
      fun Q=>V σ+w σ+(EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ) Q := by
    funext Q;simp [add_assoc,add_comm,add_left_comm]
  rw [he,norm_iteratedFDeriv_one,fderiv_const_add,ContinuousLinearMap.fderiv]
  apply (EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ).opNorm_le_bound (by norm_num)
  intro Q
  simpa only [one_mul,EuclideanSpace.coe_proj] using PiLp.norm_apply_le Q σ

theorem cascadeTerminal_affine_higherJet_zero (V : S→ℝ) (w H : FiniteStateField S) (σ : S)
    (r : ℕ) (hr : 2≤r) : iteratedFDeriv ℝ r (fun Q : FiniteStateField S=>V σ+(Q+w) σ) H=0 := by
  have he : fderiv ℝ (fun Q : FiniteStateField S=>V σ+(Q+w) σ)=
      fun _=>(EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ) := by
    have hf : (fun Q : FiniteStateField S=>V σ+(Q+w) σ)=
        fun Q=>V σ+w σ+(EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ) Q := by
      funext Q;simp [add_assoc,add_comm,add_left_comm]
    rw [hf]
    funext Q
    rw [fderiv_const_add,ContinuousLinearMap.fderiv]
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  apply norm_eq_zero.mp
  rw [←norm_iteratedFDeriv_fderiv,he,iteratedFDeriv_const_of_ne (by omega : i≠0),Pi.zero_apply,norm_zero]

theorem norm_cascadePosteriorLogDensity_firstJet_le_two (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    ‖iteratedFDeriv ℝ 1 (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤2 := by
  simpa only [one_add_one_eq_two] using norm_cascadePosteriorLogDensity_jet_le V a ha ha1 hdec L 1 1 1 (by norm_num)
    (fun j H=>norm_finiteStateCascade_firstJet_le_one V a ha L j H)
    (fun w H σ=>norm_cascadeTerminal_affine_firstJet_le_one V w H σ) j H z

theorem norm_cascadePosteriorLogDensity_secondJet_le_one (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    ‖iteratedFDeriv ℝ 2 (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤1 := by
  simpa only [zero_add] using norm_cascadePosteriorLogDensity_jet_le V a ha ha1 hdec L 2 0 1 (by norm_num)
    (fun j H=>norm_finiteStateCascade_secondJet_le_one V a ha ha1 hdec L j H)
    (fun w H σ=>by rw [cascadeTerminal_affine_higherJet_zero V w H σ 2 (by omega),norm_zero]) j H z

end FourPapersCommon
