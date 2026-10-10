module
public import FourPapersCommon.FiniteCascadeRecordTranslation
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import OverlapPaper.ReplicaSourceGroupBaseline

@[expose] public section

/-! State permutations transport the actual finite Gaussian logarithmic
averages and their normalized transition kernels. Gaussian inputs are
changed by their genuine orthogonal maps. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon OverlapPaper SpinGlass.AT
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

def cavityStatePermutation (e : S ≃ S) :
    FiniteStateField S ≃ₗᵢ[ℝ] FiniteStateField S :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem cavityStatePermutation_apply (e : S ≃ S)
    (H : FiniteStateField S) (s : S) :
    cavityStatePermutation e H s = H (e.symm s) := rfl

theorem cavityStatePermutation_partition (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (H : FiniteStateField S) :
    gtStatePartition V (cavityStatePermutation e H) = gtStatePartition V H := by
  unfold gtStatePartition
  calc
    _ = ∑s : S, Real.exp (H (e.symm s) + V (e.symm s)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [cavityStatePermutation_apply, ←hV (e.symm s), e.apply_symm_apply]
    _ = _ := e.symm.sum_comp (fun s => Real.exp (H s + V s))

theorem cavityStatePermutation_terminal (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (H : FiniteStateField S) :
    gtStateLogPartition V (cavityStatePermutation e H) = gtStateLogPartition V H := by
  simp only [gtStateLogPartition, cavityStatePermutation_partition e V hV]

theorem cavityGaussianRaw_statePermutation (P : FiniteStateField S ≃ₗᵢ[ℝ] FiniteStateField S)
    (A : FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (hL : ∀z, P (L z) = L (A z)) (H : FiniteStateField S) :
    (finiteStateGaussianRawKernel L H).map P = finiteStateGaussianRawKernel L (P H) := by
  rw [finiteStateGaussianRawKernel_apply, Measure.map_map P.continuous.measurable
    (by fun_prop), finiteStateGaussianRawKernel_apply]
  calc
    _ = (stdGaussian (FiniteStateGaussianInput I)).map
        ((fun z => P H + L z) ∘ A) := by
      congr 1
      funext z
      simp only [Function.comp_def, map_add, hL]
    _ = _ := by
      rw [←Measure.map_map (by fun_prop) A.continuous.measurable, stdGaussian_map A]

theorem cavityGaussianStep_statePermutation
    (P : FiniteStateField S ≃ₗᵢ[ℝ] FiniteStateField S)
    (A : FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (hL : ∀z, P (L z) = L (A z)) (a : ℝ)
    (F : FiniteStateField S → ℝ) (hF : Measurable F)
    (hFP : ∀H, F (P H) = F H) (H : FiniteStateField S) :
    finiteStateGaussianStep a L F (P H) = finiteStateGaussianStep a L F H := by
  have hm : Measurable (fun z => F (P H + L z)) := hF.comp (by fun_prop)
  have hc := sourceLogAverage_map (stdGaussian (FiniteStateGaussianInput I)) A
    A.continuous.measurable a (fun z => F (P H + L z)) hm
  rw [stdGaussian_map A] at hc
  unfold finiteStateGaussianStep
  rw [hc]
  congr 1
  funext z
  rw [←hL z, ←map_add, hFP]

theorem cavityGaussianCascade_statePermutation (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (a : ℕ → ℝ) (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (hL : ∀j z, cavityStatePermutation e (L j z) = L j (A j z))
    (j : ℕ) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascade V a L j (cavityStatePermutation e H) =
      finiteStateGaussianTerminalCascade V a L j H := by
  induction j generalizing H with
  | zero => exact cavityStatePermutation_terminal e V hV H
  | succ j ih =>
      exact cavityGaussianStep_statePermutation _ (A j) (L j) (hL j) (a j) _
        (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable ih H

theorem cavityGaussianStepLaw_statePermutation
    (P : FiniteStateField S ≃ₗᵢ[ℝ] FiniteStateField S)
    (A : FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (hL : ∀z, P (L z) = L (A z)) (a : ℝ)
    (F : FiniteStateField S → ℝ) (hF : Measurable F)
    (hFP : ∀H, F (P H) = F H) (H : FiniteStateField S) :
    (finiteStateGaussianStepLaw a L F H).map P =
      finiteStateGaussianStepLaw a L F (P H) := by
  unfold finiteStateGaussianStepLaw
  rw [←cavityGaussianRaw_statePermutation P A L hL H,
    tilted_map_eq _ _ P.continuous.measurable _ (hF.const_mul a)]
  have he : (fun Q => a * F (P Q)) = (fun Q => a * F Q) := by
    funext Q
    rw [hFP]
  rw [he]

theorem cavityGaussianCascadeKernel_statePermutation (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (a : ℕ → ℝ) (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (hL : ∀j z, cavityStatePermutation e (L j z) = L j (A j z)) (j : ℕ) :
    (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j).map
        (cavityStatePermutation e) =
      (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j).comap
        (cavityStatePermutation e) (cavityStatePermutation e).continuous.measurable := by
  ext H B hB
  rw [Kernel.map_apply _ (cavityStatePermutation e).continuous.measurable, Kernel.comap_apply]
  have hm := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable
  change (finiteStateGaussianStepKernel (a j) (L j)
      (finiteStateGaussianTerminalCascade V a L j) H).map _ B =
    finiteStateGaussianStepKernel (a j) (L j)
      (finiteStateGaussianTerminalCascade V a L j) (cavityStatePermutation e H) B
  rw [finiteStateGaussianStepKernel_apply _ _ _ hm,
    finiteStateGaussianStepKernel_apply _ _ _ hm,
    cavityGaussianStepLaw_statePermutation _ (A j) (L j) (hL j) (a j) _ hm
      (cavityGaussianCascade_statePermutation e V hV a ha L A hL j)]

theorem cavityGibbsKernel_statePermutation (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) :
    (finiteStateGibbsKernel V).map e = (finiteStateGibbsKernel V).comap
      (cavityStatePermutation e) (cavityStatePermutation e).continuous.measurable := by
  have he : Measurable e := measurable_of_countable _
  apply Kernel.ext
  intro H
  rw [Kernel.map_apply _ he, Kernel.comap_apply]
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.map_apply he (measurableSet_singleton s)]
  have hs : e ⁻¹' {s} = {e.symm s} := by
    ext t
    exact e.apply_eq_iff_eq_symm_apply
  rw [hs, finiteStateGibbsKernel_singleton, finiteStateGibbsKernel_singleton]
  congr 1
  unfold gtStateGibbs
  rw [cavityStatePermutation_apply, cavityStatePermutation_partition e V hV,
    ←hV (e.symm s), e.apply_symm_apply]

end QuantitativeFollowup
