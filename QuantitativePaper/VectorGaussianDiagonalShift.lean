module
public import QuantitativePaper.VectorMeasureMild
public import QuantitativePaper.VectorColeHopfOrderAllMass

@[expose] public section

/-! The diagonal Gaussian is an actual additive constant in the finite
spin partition and every Gaussian recursion, hence also in the original
measure limit. This permits its exact removal at every interpolation time. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 300000

theorem terminalPotential_add_const {n : ℕ} (E : Configuration n→ℝ) (c : ℝ) :
    terminalPotential (fun σ=>c+E σ)=c+terminalPotential E := by
  unfold terminalPotential terminalPartition
  simp_rw [Real.exp_add]
  rw [←Finset.mul_sum]
  change Real.log (Real.exp c*terminalPartition E)=c+Real.log (terminalPartition E)
  rw [Real.log_mul (Real.exp_ne_zero _) (terminalPartition_pos E).ne',Real.log_exp]

theorem vectorTerminalPotential_diagonal_shift {n : ℕ} (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorTerminalPotential n β t p x=β*Real.sqrt t*p.2+
      vectorTerminalPotential n β t (p.1,0) x := by
  have he : vectorTerminalExponent n β t p x=
      fun σ=>β*Real.sqrt t*p.2+vectorTerminalExponent n β t (p.1,0) x σ := by
    funext σ
    simp only [vectorTerminalExponent,add_zero]
    ring
  rw [vectorTerminalPotential,he,terminalPotential_add_const]
  rfl

theorem vectorRecursion_diagonal_shift {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    vectorRecursion s β t p j x=β*Real.sqrt t*p.2+
      vectorRecursion s β t (p.1,0) j x := by
  induction j generalizing x with
  | zero=>exact vectorTerminalPotential_diagonal_shift β t p x
  | succ j ih=>
    have he : vectorRecursion s β t p j=
        fun y=>β*Real.sqrt t*p.2+vectorRecursion s β t (p.1,0) j y := funext ih
    rw [vectorRecursion,he,vectorColeHopfStep_add_const_all_mass _ _
      (vectorRecursion_lipschitz s β t (p.1,0) j)]
    rfl

theorem vectorMeasurePotential_diagonal_shift {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasurePotential μ β t p x=β*Real.sqrt t*p.2+
      vectorMeasurePotential μ β t (p.1,0) x := by
  have hlim := (tendsto_vectorDyadicPotential μ β t ht (p.1,0) x).const_add (β*Real.sqrt t*p.2)
  have he : (fun j=>vectorDyadicPotential μ β t j p x)=
      fun j=>β*Real.sqrt t*p.2+vectorDyadicPotential μ β t j (p.1,0) x := by
    funext j
    exact vectorRecursion_diagonal_shift _ β t p _ x
  rw [←he] at hlim
  exact tendsto_nhds_unique (tendsto_vectorDyadicPotential μ β t ht p x) hlim

theorem vectorMeasureTailPotential_diagonal_shift {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t q p x=β*Real.sqrt t*p.2+
      vectorMeasureTailPotential μ β t q (p.1,0) x := by
  have htshift {k : ℕ} (s : RSBScheme k) (j : ℕ) (hj : j ≤ k+2) :
      ∀x,vectorTailRecursion s β t q p j x=β*Real.sqrt t*p.2+
        vectorTailRecursion s β t q (p.1,0) j x := by
    induction j with
    | zero=>exact vectorTerminalPotential_diagonal_shift β t p
    | succ j ih=>
      intro y
      rw [vectorTailRecursion,show vectorTailRecursion s β t q p j=
        (fun z=>β*Real.sqrt t*p.2+vectorTailRecursion s β t q (p.1,0) j z) from funext (ih (by omega)),
        vectorColeHopfStep_add_const_all_mass _ _ (vectorTailRecursion_lipschitz s β t q q.property (p.1,0) (j:=j) (by omega))]
      rfl
  have hlim := (tendsto_vectorDyadicTailPotential μ β t q ht q.property (p.1,0) x).const_add (β*Real.sqrt t*p.2)
  have he : (fun j=>vectorDyadicTailPotential μ β t q j p x)=
      fun j=>β*Real.sqrt t*p.2+vectorDyadicTailPotential μ β t q j (p.1,0) x := by
    funext j
    exact htshift _ _ le_rfl x
  rw [←he] at hlim
  exact tendsto_nhds_unique (tendsto_vectorDyadicTailPotential μ β t q ht q.property p x) hlim

end QuantitativePaper
