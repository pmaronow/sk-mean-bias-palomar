module
public import QuantitativePaper.VectorFinitePastSpinPairing
public import QuantitativePaper.VectorDyadicTime

@[expose] public section

/-! Exact restarted-tail gradients at actual profile nodes, including
repeated nodes, and the literal dyadic backward spin response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorTailRecursion_at_node (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i≤k+2) (p : Couplings n×ℝ) :
    vectorTailRecursion s β t (s.q i) p (k+2)=vectorRecursion s β t p (k+2-i) := by
  have he : k+2-(k+2-i)=i := by omega
  rw [vectorTailRecursion_constant_suffix s β t (s.q i) p (k+2-i) (by omega)
    (by rw [he]) (by omega) le_rfl]
  exact vectorTailRecursion_prefix_of_le s β t (s.q i) p (by omega) (by rw [he])

theorem vectorFiniteTailGradient_at_node (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i≤k+2) (p : Couplings n×ℝ) (x : Field n) :
    vectorFiniteTailGradient s β t ⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ p x=
      vectorMagnetization s β t p (k+2-i) x := by
  rw [vectorFiniteTailGradient,vectorTailRecursion_at_node s β t i hi p]
  exact (vectorMagnetization_eq_gradient s β t p (k+2-i) x).symm

def vectorDyadicSpinMean (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorDyadicTailGradient μ β t (Paper.parisiGridRound (vectorDyadicIndex j) q) j sample.1
    (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample)

theorem vectorDyadicSpinMean_eq_backward (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    vectorDyadicSpinMean μ β t ht q j sample l=
      vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
        (fun σ=>Paper.spinSign (σ l)) (vectorDyadicTimeIndex q j)
        (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
          (vectorDyadicTime q j) sample) := by
  rw [vectorBackwardMean_spin]
  unfold vectorDyadicSpinMean vectorDyadicTailGradient vectorDyadicState vectorFiniteJointState
  have hi : vectorDyadicTimeIndex q j≤(vectorDyadicIndex j+1)+2 :=
    (vectorDyadicTimeIndex_le q j).trans (by omega)
  have he := vectorFiniteTailGradient_at_node (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
    (vectorDyadicTimeIndex q j) hi sample.1
    (vectorFiniteState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
      (vectorDyadicTime q j) sample)
  have hq : (⟨(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q
      (vectorDyadicTimeIndex q j),
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_nonneg hi,
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_le_one hi⟩ : Paper.Overlap)=
      Paper.parisiGridRound (vectorDyadicIndex j) q := by
    apply Subtype.ext
    exact vectorDyadicTimeIndex_node μ q j
  rw [hq] at he
  exact congrArg (fun x : Field n=>x l) he

end QuantitativePaper
