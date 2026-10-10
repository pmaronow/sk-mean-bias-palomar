module
public import QuantitativePaper.VectorFiniteTiltedKernelPairing

@[expose] public section

/-! Actual terminal-spin backward pairings conditional on the whole Wiener
past of the finite diffusion, with any fractional initial tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorFinite_backward_pairing_between (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (d : Configuration n→ℝ) (R : ℝ) (hR : ∀ σ,|d σ|≤R)
    (i j : ℕ) (hij : i≤j) (hj : j≤k+2)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫sample,Z sample*vectorBackwardMean s β t d j
      (vectorFiniteJointState s β t ht.le (s.q j).toNNReal sample)
      ∂vectorFiniteDisorderTilt s β t a)=
      ∫sample,Z sample*vectorBackwardMean s β t d i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hij
  induction u with
  | zero=>rfl
  | succ u ihu=>
    have hpast : Measurable[vectorBrownianFiltration n (s.q (i+u)).toNNReal] Z :=
      hZ.mono ((vectorBrownianFiltration n).mono
        (Real.toNNReal_le_toNNReal (s.q_mono' (i+u) (by omega) i (by omega)))) le_rfl
    have he := vectorFinite_cell_kernel_pairing_tilt s β t a hβ ht (i+u) (by omega)
      (vectorBackwardMean s β t d (i+u+1)) (measurable_vectorBackwardMean s β t d _)
      R (fun x=>by simpa only [Real.norm_eq_abs] using abs_vectorBackwardMean_le s β t d R hR _ x)
      Z hpast C hC
    have he' : (∫sample,Z sample*vectorBackwardMean s β t d (i+u+1)
        (vectorFiniteJointState s β t ht.le (s.q (i+u+1)).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a)=
        ∫sample,Z sample*vectorBackwardMean s β t d (i+u)
          (vectorFiniteJointState s β t ht.le (s.q (i+u)).toNNReal sample)
          ∂vectorFiniteDisorderTilt s β t a := by
      refine he.trans (integral_congr_ae (.of_forall fun sample=>?_))
      exact congrArg (fun v : ℝ=>Z sample*v)
        (vectorBackwardMean_kernel s β t d (i+u)
          (vectorFiniteJointState s β t ht.le (s.q (i+u)).toNNReal sample)).symm
    simpa only [Nat.add_assoc] using he'.trans (ihu (by omega) (by omega))

theorem vectorFinite_terminal_mean_pairing_past (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (d : Configuration n→ℝ)
    (i : ℕ) (hi : i≤k+2) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫sample,Z sample*terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorFiniteState s β t ht.le 1 sample)) d
      ∂vectorFiniteDisorderTilt s β t a)=
      ∫sample,Z sample*vectorBackwardMean s β t d i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  have he := vectorFinite_backward_pairing_between s β t a hβ ht d
    (∑σ : Configuration n,|d σ|)
    (fun σ=>Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ))
    i (k+2) hi le_rfl Z hZ C hC
  simpa only [vectorBackwardMean_terminal,s.q_top,Real.toNNReal_one,vectorFiniteJointState] using he

end QuantitativePaper
