module
public import QuantitativeFollowup.AnisotropicFiniteConditionalKernel
public import FourPapersCommon.KernelExpectationPrepend

@[expose] public section

/-! Genuine bounded future-state observables paired with arbitrary
integrable weights in the whole earlier Wiener past of the actual diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def anisotropicDepthKernel (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    Kernel (AnisotropicParameter n) (AnisotropicParameter n) :=
  finiteStateGaussianStepKernel (anisotropicSchemeMass s j) (anisotropicSchemeInput D s j)
    (anisotropicFinitePotential D s j)

instance anisotropicDepthKernel_markov (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    IsMarkovKernel (anisotropicDepthKernel D s j) :=
  isMarkovKernel_finiteStateGaussianStepKernel _ _ _ (anisotropicFinitePotential_lipschitz D s j)

theorem anisotropicDepthKernel_eq_profile (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) :
    anisotropicDepthKernel D s (k+1-i)=anisotropicFiniteTransition D s i := rfl

def anisotropicFiniteFutureExpectation (D : AnisotropicSpinModel n) (s : RSBScheme k) (i u : ℕ)
    (F : AnisotropicParameter n → ℝ) : AnisotropicParameter n → ℝ :=
  sourceKernelExpectation (fun j => anisotropicDepthKernel D s (k+2-u+j)) (u-i) F

theorem anisotropicFiniteFutureExpectation_step (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i u : ℕ) (hi : i ≤ u) (hu : u ≤ k+1) (F : AnisotropicParameter n → ℝ) (x : AnisotropicParameter n) :
    anisotropicFiniteFutureExpectation D s i (u+1) F x =
      anisotropicFiniteFutureExpectation D s i u (fun y => ∫z, F z ∂anisotropicFiniteTransition D s u y) x := by
  have hq : u+1-i=(u-i)+1 := by omega
  have hp : k+2-(u+1)+1=k+2-u := by omega
  have hp' : k+2-(u+1)=k+1-u := by omega
  unfold anisotropicFiniteFutureExpectation
  rw [hq, sourceKernelExpectation_prepend, hp, hp', anisotropicDepthKernel_eq_profile D s u]

theorem anisotropicFinite_future_integrable_weighted_pairing (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (i u : ℕ) (hi : i ≤ u) (hu : u ≤ k+2)
    (F : AnisotropicParameter n → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀x, ‖F x‖ ≤ B)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p, Z p*F (anisotropicFinitePhysicalParameter D s g (s.q u).toNNReal p)
      ∂vectorDisorderBrownianMeasure n) =
      ∫p, Z p*anisotropicFiniteFutureExpectation D s i u F
        (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal p)
        ∂vectorDisorderBrownianMeasure n := by
  induction u generalizing F with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    rfl
  | succ u ih =>
    by_cases hiu : i=u+1
    · subst i
      simp only [anisotropicFiniteFutureExpectation, Nat.sub_self, sourceKernelExpectation]
    · have hi' : i ≤ u := by omega
      have hu' : u ≤ k+1 := by omega
      let G := fun x : AnisotropicParameter n => ∫y, F y ∂anisotropicFiniteTransition D s u x
      haveI := anisotropicFiniteTransition_markov D s u
      have hGm : Measurable G := hF.stronglyMeasurable.integral_kernel.measurable
      have hGb (x : AnisotropicParameter n) : ‖G x‖ ≤ B := by
        simpa only [probReal_univ, mul_one] using
          (norm_integral_le_of_norm_le_const (μ:=anisotropicFiniteTransition D s u x) (.of_forall hB))
      have hZu : Measurable[vectorBrownianFiltration n (s.q u).toNNReal] Z :=
        hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono
          (s.q_mono' u (by omega) i hi'))) le_rfl
      calc
        _ = ∫p, Z p*G (anisotropicFinitePhysicalParameter D s g (s.q u).toNNReal p)
            ∂vectorDisorderBrownianMeasure n :=
          anisotropicFinite_cell_integrable_weighted_pairing D s g u hu' F hF B hB Z hZu hZi
        _ = ∫p, Z p*anisotropicFiniteFutureExpectation D s i u G
            (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal p)
            ∂vectorDisorderBrownianMeasure n :=
          ih hi' (by omega) G hGm hGb
        _ = _ := by
          apply integral_congr_ae
          exact .of_forall fun p => congrArg (fun r => Z p*r)
            (anisotropicFiniteFutureExpectation_step D s i u hi' hu' F _).symm

end QuantitativeFollowup
