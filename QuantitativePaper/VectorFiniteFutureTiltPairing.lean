module
public import QuantitativePaper.VectorFiniteFuturePairing
public import QuantitativePaper.VectorFiniteTiltedKernelPairing

@[expose] public section

/-! The actual normalized fractional disorder tilt retains the same future
Gaussian kernels, even for tests of the whole original earlier Wiener past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFinite_future_weighted_pairing_tilt (s : RSBScheme k)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (i u : ℕ) (hi : i ≤ u) (hu : u ≤ k+2)
    (F : VectorState n → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀x, ‖F x‖ ≤ B)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p*F (vectorFiniteJointState s β t ht.le (s.q u).toNNReal p)
      ∂vectorFiniteDisorderTilt s β t a) =
      ∫p, Z p*vectorFiniteFutureExpectation s β t i u F
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p)
        ∂vectorFiniteDisorderTilt s β t a := by
  induction u generalizing F with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    rfl
  | succ u ih =>
    by_cases hiu : i=u+1
    · subst i
      simp only [vectorFiniteFutureExpectation, Nat.sub_self, sourceKernelExpectation]
    · have hi' : i ≤ u := by omega
      have hu' : u ≤ k+1 := by omega
      let G := fun x : VectorState n => ∫y, F y ∂vectorProfileKernel s β t u x
      haveI := vectorProfileKernel_markov (n:=n) s β t u
      have hGm : Measurable G := hF.stronglyMeasurable.integral_kernel.measurable
      have hGb (x : VectorState n) : ‖G x‖ ≤ B := by
        simpa only [probReal_univ, mul_one] using
          (norm_integral_le_of_norm_le_const (μ:=vectorProfileKernel s β t u x) (.of_forall hB))
      have hZu : Measurable[vectorBrownianFiltration n (s.q u).toNNReal] Z :=
        hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono
          (s.q_mono' u (by omega) i hi'))) le_rfl
      calc
        _ = ∫p, Z p*G (vectorFiniteJointState s β t ht.le (s.q u).toNNReal p)
            ∂vectorFiniteDisorderTilt s β t a :=
          vectorFinite_cell_kernel_pairing_tilt s β t a hβ ht u hu' F hF B hB Z hZu C hC
        _ = ∫p, Z p*vectorFiniteFutureExpectation s β t i u G
            (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p)
            ∂vectorFiniteDisorderTilt s β t a :=
          ih hi' (by omega) G hGm hGb
        _ = _ := by
          apply integral_congr_ae
          exact .of_forall fun p => congrArg (fun r => Z p*r)
            (vectorFiniteFutureExpectation_step s β t i u hi' hu' F _).symm

end QuantitativePaper
