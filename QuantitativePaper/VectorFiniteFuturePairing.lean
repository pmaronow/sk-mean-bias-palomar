module
public import QuantitativePaper.VectorFutureCovarianceKernels
public import QuantitativePaper.VectorFiniteConditionalKernel
public import FourPapersCommon.KernelExpectationPrepend

@[expose] public section

/-! Genuine bounded future-state observables paired with arbitrary
integrable weights in the whole earlier Wiener past of the actual diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorDepthKernel_eq_profile (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i ≤ k+1) :
    vectorDepthKernel (n:=n) s β t (k+1-i) = vectorProfileKernel s β t i := by
  have h1 : k+2-(k+1-i)=i+1 := by omega
  have h2 : k+1-(k+1-i)=i := by omega
  simp only [vectorDepthKernel, vectorProfileKernel, ite_eq_left hi, h1, h2]

def vectorFiniteFutureExpectation (s : RSBScheme k) (β t : ℝ) (i u : ℕ)
    (F : VectorState n → ℝ) : VectorState n → ℝ :=
  sourceKernelExpectation (fun j => vectorDepthKernel s β t (k+2-u+j)) (u-i) F

theorem vectorFiniteFutureExpectation_step (s : RSBScheme k) (β t : ℝ)
    (i u : ℕ) (hi : i ≤ u) (hu : u ≤ k+1) (F : VectorState n → ℝ) (x : VectorState n) :
    vectorFiniteFutureExpectation s β t i (u+1) F x =
      vectorFiniteFutureExpectation s β t i u (fun y => ∫z, F z ∂vectorProfileKernel s β t u y) x := by
  have hq : u+1-i=(u-i)+1 := by omega
  have hp : k+2-(u+1)+1=k+2-u := by omega
  have hp' : k+2-(u+1)=k+1-u := by omega
  unfold vectorFiniteFutureExpectation
  rw [hq, sourceKernelExpectation_prepend, hp, hp', vectorDepthKernel_eq_profile s β t u hu]

theorem vectorFinite_future_integrable_weighted_pairing (s : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (i u : ℕ) (hi : i ≤ u) (hu : u ≤ k+2)
    (F : VectorState n → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀x, ‖F x‖ ≤ B)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p, Z p*F (vectorFiniteJointState s β t ht.le (s.q u).toNNReal p)
      ∂vectorDisorderBrownianMeasure n) =
      ∫p, Z p*vectorFiniteFutureExpectation s β t i u F
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p)
        ∂vectorDisorderBrownianMeasure n := by
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
            ∂vectorDisorderBrownianMeasure n :=
          vectorFinite_cell_integrable_weighted_pairing s β t hβ ht u hu' F hF B hB Z hZu hZi
        _ = ∫p, Z p*vectorFiniteFutureExpectation s β t i u G
            (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p)
            ∂vectorDisorderBrownianMeasure n :=
          ih hi' (by omega) G hGm hGb
        _ = _ := by
          apply integral_congr_ae
          exact .of_forall fun p => congrArg (fun r => Z p*r)
            (vectorFiniteFutureExpectation_step s β t i u hi' hu' F _).symm

end QuantitativePaper
