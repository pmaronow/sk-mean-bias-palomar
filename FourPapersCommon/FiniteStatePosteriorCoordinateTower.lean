module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerMeans

@[expose] public section

/-! Literal unbounded Gaussian-coordinate posterior tower and Stein response.
The complete Gaussian record, zero covariance directions, actual remaining
spin law, and actual normalized prefix law are retained throughout. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal Topology
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper
set_option maxHeartbeats 1400000

def posteriorCoordinateTruncation (n : ℕ) (x : ℝ) : ℝ :=
  if |x|≤(n:ℝ) then x else 0

theorem measurable_posteriorCoordinateTruncation (n : ℕ) : Measurable (posteriorCoordinateTruncation n) :=
  measurable_id.ite (measurableSet_le measurable_id.abs measurable_const) measurable_const

theorem abs_posteriorCoordinateTruncation_le (n : ℕ) (x : ℝ) :
    |posteriorCoordinateTruncation n x|≤ min |x| (n:ℝ) := by
  unfold posteriorCoordinateTruncation
  split_ifs with hx
  · simp only [min_eq_left hx,le_refl]
  · simp only [abs_zero]
    exact le_min (abs_nonneg _) (Nat.cast_nonneg _)

theorem tendsto_posteriorCoordinateTruncation (x : ℝ) :
    Tendsto (fun n=>posteriorCoordinateTruncation n x) atTop (𝓝 x) := by
  obtain ⟨N,hN⟩:=exists_nat_gt |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (if_pos (hN.le.trans (by exact_mod_cast hn))).symm

variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The coordinate times an arbitrary terminal feature is genuinely
integrable in the full all-noise posterior. -/
theorem integrable_cascadePosteriorGaussianLaw_input_feature (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H K : FiniteStateField S) (r : Fin N) (i : Fin (Fintype.card I)) :
    Integrable (fun z : (Fin N→FiniteStateGaussianInput I)×S=>
      (finiteStateGaussianBasis I).repr (z.1 r) i*K z.2)
      (cascadePosteriorGaussianLaw V a L N H) := by
  have hb:=(integrable_cascadePosteriorGaussianLaw_input_coordinate V a ha L N H r i).norm.mul_const ‖K‖
  apply hb.mono'
  · exact (((continuous_finiteStateGaussianInput_coordinate i).measurable.comp
      ((measurable_pi_apply r).comp measurable_fst)).mul
        ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)).aestronglyMeasurable
  · exact .of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2) (abs_nonneg _)

private theorem coordinateSpinLaw_truncation_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (d : ℕ) (H K : FiniteStateField S) (i : Fin (Fintype.card I)) (n : ℕ) :
    |∫z,posteriorCoordinateTruncation n ((finiteStateGaussianBasis I).repr z.1 i)*K z.2
      ∂finiteStateGaussianCoordinateSpinLaw V a L d H|≤posteriorCoordinateMomentBound a L d*‖K‖ := by
  haveI:=finiteStateGaussianCoordinateSpinLaw_probability V a ha L d H
  let b := fun z : FiniteStateGaussianInput I×S=>
    min |(finiteStateGaussianBasis I).repr z.1 i| (n:ℝ)*‖K‖
  have hb : Integrable b (finiteStateGaussianCoordinateSpinLaw V a L d H) :=
    source_bounded_integrable _ _
      (((((continuous_finiteStateGaussianInput_coordinate i).measurable.comp measurable_fst).abs).min measurable_const).mul_const _)
      ((n:ℝ)*‖K‖) (fun z=>by
        rw [abs_mul,abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _)),abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
  have hh := norm_integral_le_of_norm_le hb (.of_forall fun z=>by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (abs_posteriorCoordinateTruncation_le n _)
      (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2)
      (abs_nonneg _) (le_min (abs_nonneg _) (Nat.cast_nonneg _)))
  apply hh.trans
  rw [show b=(fun z : FiniteStateGaussianInput I×S=>min |(finiteStateGaussianBasis I).repr z.1 i| (n:ℝ)*‖K‖) from rfl,
    integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_coordinateSpin_truncated_abs_le V a ha L d H i n) (norm_nonneg _)

/-- Exact genuine tower from a recorded raw Gaussian coordinate and terminal
feature to the actual current-input/future-spin law. No regularity, conditional
law, or coordinate integrability is supplied as a premise. -/
theorem cascadePosteriorGaussianLaw_coordinate_feature_tower (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H K : FiniteStateField S) (r : Fin N) (i : Fin (Fintype.card I)) :
    (∫z,(finiteStateGaussianBasis I).repr (z.1 r) i*K z.2 ∂cascadePosteriorGaussianLaw V a L N H)=
      ∫h,(∫z,(finiteStateGaussianBasis I).repr z.1 i*K z.2
        ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) (h (Fin.last r.val)).1)
        ∂posteriorCoordinateHistoryLaw V a L N H r.val := by
  let g := fun n z=>posteriorCoordinateTruncation n ((finiteStateGaussianBasis I).repr z i)
  have hgm (n : ℕ) : Measurable (g n) :=
    (measurable_posteriorCoordinateTruncation n).comp (continuous_finiteStateGaussianInput_coordinate i).measurable
  have hgb (n : ℕ) (z : FiniteStateGaussianInput I) : |g n z|≤(n:ℝ) :=
    (abs_posteriorCoordinateTruncation_le n _).trans (min_le_right _ _)
  have hgdom (n : ℕ) (z : FiniteStateGaussianInput I) : |g n z|≤|(finiteStateGaussianBasis I).repr z i| :=
    (abs_posteriorCoordinateTruncation_le n _).trans (min_le_left _ _)
  have hglim (z : FiniteStateGaussianInput I) : Tendsto (fun n=>g n z) atTop (𝓝 ((finiteStateGaussianBasis I).repr z i)) :=
    tendsto_posteriorCoordinateTruncation _
  have hleft := tendsto_integral_of_dominated_convergence
    (F:=fun (n : ℕ) (z : (Fin N→FiniteStateGaussianInput I)×S)=>g n (z.1 r)*K z.2)
    (f:=fun z : (Fin N→FiniteStateGaussianInput I)×S=>(finiteStateGaussianBasis I).repr (z.1 r) i*K z.2)
    (fun z : (Fin N→FiniteStateGaussianInput I)×S=>|(finiteStateGaussianBasis I).repr (z.1 r) i| *‖K‖)
    (fun n=>((hgm n).comp ((measurable_pi_apply r).comp measurable_fst) |>.mul
      ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)).aestronglyMeasurable)
    ((integrable_cascadePosteriorGaussianLaw_input_coordinate V a ha L N H r i).norm.mul_const ‖K‖)
    (fun n=>.of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hgdom n _) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2)
        (abs_nonneg _) (abs_nonneg _))
    (.of_forall fun z=>(hglim (z.1 r)).mul_const (K z.2))
  have hpoint (Q : FiniteStateField S) :
      Tendsto (fun n=>∫z,g n z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) Q)
        atTop (𝓝 (∫z,(finiteStateGaussianBasis I).repr z.1 i*K z.2
          ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) Q)) :=
    tendsto_integral_of_dominated_convergence
      (fun z : FiniteStateGaussianInput I×S=>|(finiteStateGaussianBasis I).repr z.1 i*K z.2|)
      (fun n=>((hgm n).comp measurable_fst |>.mul
        ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)).aestronglyMeasurable)
      (integrable_finiteStateGaussianCoordinateSpinLaw_feature V a ha L (N-1-r.val) Q K i).norm
      (fun n=>.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul,abs_mul]
        exact mul_le_mul_of_nonneg_right (hgdom n _) (abs_nonneg _))
      (.of_forall fun z=>(hglim z.1).mul_const (K z.2))
  haveI:=posteriorCoordinateHistoryLaw_probability V a ha L N H r.val
  have hmeanm (n : ℕ) : Measurable (fun Q=>∫z,g n z.1*K z.2
      ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) Q) :=
    measurable_coordinateSpinLaw_feature_mean V a ha L (N-1-r.val) K (g n) (hgm n) (fun Q=>by
      haveI:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz _
        (finiteStateGaussianTerminalCascade_lipschitz V a ha L (N-1-r.val)) (L (N-1-r.val)) Q (a (N-1-r.val)))
      exact source_bounded_integrable _ _ (hgm n) (n:ℝ) (hgb n))
  have hright := tendsto_integral_of_dominated_convergence
    (μ:=posteriorCoordinateHistoryLaw V a L N H r.val)
    (F:=fun (n : ℕ) (h : FiniteHistory (PosteriorCoordinateState S I) r.val)=>
      ∫z,g n z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) (h (Fin.last r.val)).1)
    (f:=fun h : FiniteHistory (PosteriorCoordinateState S I) r.val=>
      ∫z,(finiteStateGaussianBasis I).repr z.1 i*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) (h (Fin.last r.val)).1)
    (fun _ : FiniteHistory (PosteriorCoordinateState S I) r.val=>posteriorCoordinateMomentBound a L (N-1-r.val)*‖K‖)
    (fun n=>((hmeanm n).comp (measurable_fst.comp (measurable_pi_apply _))).aestronglyMeasurable)
    (integrable_const _)
    (fun n=>.of_forall fun h=>by
      simpa only [Real.norm_eq_abs,g] using coordinateSpinLaw_truncation_bound V a ha L (N-1-r.val) (h (Fin.last r.val)).1 K i n)
    (.of_forall fun h=>hpoint (h (Fin.last r.val)).1)
  have he : (fun n=>∫z,g n (z.1 r)*K z.2 ∂cascadePosteriorGaussianLaw V a L N H)=
      (fun n=>∫h,(∫z,g n z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) (h (Fin.last r.val)).1)
        ∂posteriorCoordinateHistoryLaw V a L N H r.val) :=
    funext fun n=>cascadePosteriorGaussianLaw_coordinate_feature_tower_bounded V a ha L N H K r (g n) (hgm n) (n:ℝ) (hgb n)
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Literal current-coordinate Stein formula under the actual entire
normalized Gaussian posterior, with its actual prefix average. -/
theorem cascadePosteriorGaussianLaw_coordinate_ibp (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H K : FiniteStateField S) (r : Fin N) (i : Fin (Fintype.card I)) :
    (∫z,(finiteStateGaussianBasis I).repr (z.1 r) i*K z.2 ∂cascadePosteriorGaussianLaw V a L N H)=
      ∫h,(∫y,fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-r.val))) y
          (L (N-1-r.val) (finiteStateGaussianBasis I i)) K+
        a (N-1-r.val)*fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-r.val)) y K*
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-r.val)) y
            (L (N-1-r.val) (finiteStateGaussianBasis I i))
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (N-1-r.val) (h (Fin.last r.val)).1)
        ∂posteriorCoordinateHistoryLaw V a L N H r.val := by
  rw [cascadePosteriorGaussianLaw_coordinate_feature_tower V a ha L N H K r i]
  simp_rw [finiteStateGaussianCoordinateSpinLaw_coordinate_ibp V a ha L (N-1-r.val)]

end FourPapersCommon
