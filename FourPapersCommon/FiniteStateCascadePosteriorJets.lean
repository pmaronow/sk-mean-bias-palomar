module
public import FourPapersCommon.FiniteStateCascadeUniformHessian
public import QuantitativePaper.NormalizedExponentialJets

@[expose] public section

/-! Actual normalized posterior differentiation. The resulting bounds do
not depend on cascade depth or on the sizes of the Gaussian increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT QuantitativePaper
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem norm_cascadePosterior_coordinateDual_le_one (σ : S) :
    ‖(EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ)‖ ≤ 1 := by
  apply (EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ).opNorm_le_bound (by norm_num)
  intro K
  simpa only [one_mul,EuclideanSpace.coe_proj] using PiLp.norm_apply_le K σ

theorem integrable_cascadePosterior_exp_dual (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0 ≤ a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Integrable (fun z : (Fin j→Field n)×S=>
      Real.exp (cascadePosteriorLogDensity V a L j H z) •
        (EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ))
      (cascadePosteriorGaussianBase S (Fin n) j) := by
  apply Integrable.mono' (integrable_cascadePosterior_exp V a ha L j H)
  · exact ((measurable_cascadePosteriorLogDensity V a ha L j H).exp.smul
      ((measurable_of_finite (fun σ : S=>(EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ))).comp
        measurable_snd)).aestronglyMeasurable
  · exact Eventually.of_forall fun z=>by
      rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (norm_cascadePosterior_coordinateDual_le_one z.2) (Real.exp_pos _).le

theorem integral_cascadePosterior_exp_dual_eq_fderiv (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0 ≤ a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    (∫z : (Fin j→Field n)×S,Real.exp (cascadePosteriorLogDensity V a L j H z) •
      (EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ)
      ∂cascadePosteriorGaussianBase S (Fin n) j)=
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H := by
  ext K
  rw [ContinuousLinearMap.integral_apply (integrable_cascadePosterior_exp_dual V a ha L j H) K]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,EuclideanSpace.coe_proj]
  exact integral_cascadePosterior_exp_coordinate V a ha L j H K

theorem cascadePosteriorLogDensity_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0 ≤ a i) (ha1 : a 0 ≤ 1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (z : (Fin j→Field n)×S) :
    LipschitzWith 2 (fun H=>cascadePosteriorLogDensity V a L j H z) := by
  have hs := (contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp
    (contDiff_id.prodMk (contDiff_const (c:=z.1)))
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro H
  rw [←NNReal.coe_le_coe,coe_nnnorm,←norm_iteratedFDeriv_one]
  exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j H z

theorem aestronglyMeasurable_cascadePosterior_exponentialJet (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0 ≤ a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j r : ℕ) (H : FiniteStateField S) :
    AEStronglyMeasurable (fun z : (Fin j→Field n)×S=>iteratedFDeriv ℝ r
      (fun Q=>Real.exp (cascadePosteriorLogDensity V a L j Q z) •
        (EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ)) H)
      (cascadePosteriorGaussianBase S (Fin n) j) := by
  letI : MeasurableSpace (FiniteStateField S [×r]→L[ℝ] (FiniteStateField S→L[ℝ]ℝ)) := borel _
  haveI : BorelSpace (FiniteStateField S [×r]→L[ℝ] (FiniteStateField S→L[ℝ]ℝ)) := ⟨rfl⟩
  let f := fun z : (Fin j→Field n)×S=>iteratedFDeriv ℝ r
    (fun Q=>Real.exp (cascadePosteriorLogDensity V a L j Q z) •
      (EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ)) H
  have hc (σ : S) : Continuous (fun z : Fin j→Field n=>f (z,σ)) := by
    let F := fun z : (Fin j→Field n)×FiniteStateField S=>
      Real.exp (cascadePosteriorLogDensity V a L j z.2 (z.1,σ)) •
        (EuclideanSpace.proj σ : FiniteStateField S→L[ℝ]ℝ)
    have hF : ContDiff ℝ ∞ F :=
      ((contDiff_cascadePosteriorLogDensity V a ha L j σ).comp
        (contDiff_snd.prodMk contDiff_fst)).exp.smul_const _
    have hcF := continuous_fieldSlice_iteratedFDeriv F hF r
    exact hcF.comp (continuous_id.prodMk (continuous_const (y:=H)))
  have hm : Measurable f := measurable_from_prod_countable_left fun σ=>(hc σ).measurable
  have hs : TopologicalSpace.IsSeparable (⋃σ : S,range (fun z : Fin j→Field n=>f (z,σ))) :=
    .iUnion fun σ=>TopologicalSpace.isSeparable_range (hc σ)
  apply StronglyMeasurable.aestronglyMeasurable
  apply stronglyMeasurable_iff_measurable_separable.mpr
  refine ⟨hm,hs.mono ?_⟩
  rintro _ ⟨⟨z,σ⟩,rfl⟩
  exact mem_iUnion.mpr ⟨σ,mem_range.mpr ⟨z,rfl⟩⟩

theorem norm_finiteStateCascade_jet_from_posterior (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0 ≤ a i) (ha1 : a 0 ≤ 1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hB : ∀i,1 ≤ i→i ≤ N→∀j H z,
      ‖iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖ ≤ K^i)
    (j r : ℕ) (hr : r ≤ N) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ (r+1) (finiteStateGaussianTerminalCascade V a L j) H‖ ≤ (r.factorial : ℝ)*K^r := by
  have hh := normalizedExponentialExpectation_jets N (cascadePosteriorGaussianBase S (Fin n) j)
    (fun H z=>cascadePosteriorLogDensity V a L j H z)
    (fun z=>(EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ)) K 1 hK
    (fun z=>((contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp
      (contDiff_id.prodMk contDiff_const)).of_le (by simp))
    ⟨2,fun z=>cascadePosteriorLogDensity_lipschitz V a ha ha1 hdec L j z⟩
    (fun i hi hiN H z=>hB i hi hiN j H z)
    (fun z=>norm_cascadePosterior_coordinateDual_le_one z.2)
    (fun i _ H=>aestronglyMeasurable_cascadePosterior_exponentialJet V a ha L j i H)
    (fun H=>integrable_cascadePosterior_exp V a ha L j H)
    (fun H=>integral_cascadePosterior_exp V a ha L j H)
  have he : (fun H=>∫z,Real.exp (cascadePosteriorLogDensity V a L j H z) •
      (EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ)
      ∂cascadePosteriorGaussianBase S (Fin n) j)=
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) :=
    funext (integral_cascadePosterior_exp_dual_eq_fderiv V a ha L j)
  rw [←norm_iteratedFDeriv_fderiv,←he]
  simpa only [one_mul] using hh.2 r hr H

theorem norm_finiteStateCascade_thirdJet_le_eight (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0 ≤ a i) (ha1 : a 0 ≤ 1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ 3 (finiteStateGaussianTerminalCascade V a L j) H‖ ≤ 8 := by
  have hB (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ 2) (j : ℕ) (H : FiniteStateField S)
      (z : (Fin j→Field n)×S) :
      ‖iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖ ≤ (2 : ℝ)^i := by
    rcases (show i=1 ∨ i=2 by omega) with rfl|rfl
    · simpa only [pow_one] using norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j H z
    · exact (norm_cascadePosteriorLogDensity_secondJet_le_one V a ha ha1 hdec L j H z).trans (by norm_num)
  have hh := norm_finiteStateCascade_jet_from_posterior V a ha ha1 hdec L 2 2 (by norm_num)
    hB j 2 le_rfl H
  norm_num [Nat.factorial] at hh ⊢
  exact hh

end FourPapersCommon
