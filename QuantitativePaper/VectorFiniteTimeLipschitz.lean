module
public import QuantitativePaper.FiniteGeneratorBounds
public import QuantitativePaper.VectorFiniteCellContinuity

@[expose] public section

/-! The actual finite-cell time field is uniformly spatially Lipschitz.
Every jet and generator input is discharged for the concrete recursion. -/
noncomputable section
open Set
open scoped ContDiff NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 400000

theorem vectorFiniteCellTimeField_eq_generator {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) :
    vectorFiniteCellTimeField s β t p i q x=
      -((1-t)*β^2)/2*finiteGaussianGenerator (vectorFiniteCellPotential s β t p i q)
        (fun l : Fin n => EuclideanSpace.single l (1 : ℝ)) (s.m i) x := by
  unfold vectorFiniteCellTimeField finiteGaussianGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [vectorStepResponse_recursion_heat_generator]
  rfl

theorem vectorFiniteCellTimeField_uniform_spatial_lipschitz {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) :
    ∃L : ℝ,0 ≤ L ∧ ∀q : ℝ,∀p : Couplings n×ℝ,
      LipschitzWith L.toNNReal (vectorFiniteCellTimeField s β t p i q) := by
  obtain ⟨K,hK,hB⟩ := vectorFiniteCellPotential_uniform_field_jets (n := n) s β t i 3
  let L := |(1-t)*β^2|/2*(n : ℝ)*(K^3+2*|s.m i| * K^3)
  have hL : 0 ≤ L := by dsimp only [L];positivity
  refine ⟨L,hL,?_⟩
  intro q p
  have hf : ContDiff ℝ 3 (vectorFiniteCellPotential s β t p i q) :=
    (contDiff_vectorColeHopfStep_recursion_field s β t _ _ p (k+1-i)).of_le (by simp)
  have hh := finiteGaussianGenerator_lipschitz (vectorFiniteCellPotential s β t p i q) hf
    (fun l : Fin n => EuclideanSpace.single l (1 : ℝ))
    (fun l => by simp [PiLp.norm_single]) K hK (fun j hj0 hj x => hB q j hj0 hj p x) (s.m i)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.coe_toNNReal _ hL,
    vectorFiniteCellTimeField_eq_generator,vectorFiniteCellTimeField_eq_generator,
    ←mul_sub,abs_mul,abs_div,abs_neg,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hb := hh.dist_le_mul x y
  rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity),Fintype.card_fin] at hb
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ |(1-t)*β^2|/2)
  convert hm using 1 <;> dsimp only [L] <;> ring

end QuantitativePaper
