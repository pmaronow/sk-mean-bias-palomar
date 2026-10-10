module
public import QuantitativePaper.VectorFiniteKernelPairing
public import QuantitativePaper.VectorFourierTests

@[expose] public section

/-! Whole-past restricted transition laws for the actual finite-profile
vector diffusion, derived from its genuine Itô/Fourier pairings. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorFinite_restricted_transition_law (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (A : Set (VectorDisorderBrownianSample n))
    (hA : MeasurableSet[vectorBrownianFiltration n (s.q i).toNNReal] A) :
    ((vectorDisorderBrownianMeasure n).restrict A).map
      (vectorFiniteJointState s β t ht.le (s.q (i+1)).toNNReal)=
      (vectorProfileKernel s β t i) ∘ₘ
        ((vectorDisorderBrownianMeasure n).restrict A).map
          (vectorFiniteJointState s β t ht.le (s.q i).toNNReal) := by
  letI := vectorProfileKernel_markov (n:=n) s β t i
  apply FourPapersCommon.restricted_transitionLaw_of_weighted_fourier
    (vectorBrownianFiltration n (s.q i).toNNReal) (vectorDisorderBrownianMeasure n)
    ((vectorBrownianFiltration n).le _) _ _
    (measurable_vectorFiniteJointState s β t ht.le _)
    (measurable_vectorFiniteJointState s β t ht.le _) (vectorProfileKernel s β t i)
    ?_ ?_ A hA
  · intro L Z hZ hZb
    exact vectorFinite_cell_kernel_pairing s β t hβ ht i hi (vectorCosineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hZb)
  · intro L Z hZ hZb
    exact vectorFinite_cell_kernel_pairing s β t hβ ht i hi (vectorSineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hZb)

end QuantitativePaper
