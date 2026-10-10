module
public import QuantitativePaper.VectorProfileCellRepresentation
public import QuantitativePaper.VectorFiniteCellPDE
public import QuantitativePaper.VectorTailCellIdentification

@[expose] public section

/-! The actual physical affine-profile cell satisfies the literal vector
Parisi PDE. The finite scheme and restarted tail identities are proved from
the actual Gaussian recursion. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def vectorProfilePhysicalCell (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (w : ℝ×(ℝ×VectorParameter n)) : ℝ:=
  vectorProfileCellFunction s₀ s₁ β t ((1-t)*β^2) (s₀.q (i+1)) i (k+1-i) w

theorem vectorProfilePhysicalCell_eq_finiteCell (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorProfilePhysicalCell s₀ s₁ β t i (q,θ,p,x)=
      vectorFiniteCellPotential (vectorProfileScheme s₀ s₁ θ hθ) β t p i q x := by
  unfold vectorProfilePhysicalCell vectorProfileCellFunction vectorFiniteCellPotential
  rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ]
  rfl

theorem vectorProfilePhysicalCell_eq_tail (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (hi : i ≤ k+1) (q θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1)
    (hq : q∈Icc (s₀.q i) (s₀.q (i+1))) (p : Couplings n×ℝ) (x : Field n) :
    vectorProfilePhysicalCell s₀ s₁ β t i (q,θ,p,x)=
      vectorProfileTailRecursion s₀ s₁ β t q θ p (k+2) x := by
  rw [vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i q θ hθ,
    vectorProfileTailRecursion_eq_scheme s₀ s₁ β t q θ hθ]
  exact congrFun (vectorTailRecursion_eq_finiteCell (vectorProfileScheme s₀ s₁ θ hθ) β t q p i hi hq).symm x

theorem hasDerivAt_vectorProfilePhysicalCell_PDE (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (q θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1)
    (hq : q<s₀.q (i+1)) (p : Couplings n×ℝ) (x : Field n) :
    HasDerivAt (fun r=>vectorProfilePhysicalCell s₀ s₁ β t i (r,θ,p,x))
      (-((1-t)*β^2)/2*(vectorLaplacian (fun y=>vectorProfilePhysicalCell s₀ s₁ β t i (q,θ,p,y)) x+
        vectorProfileMass s₀ s₁ θ i*‖gradient (fun y=>vectorProfilePhysicalCell s₀ s₁ β t i (q,θ,p,y)) x‖^2)) q := by
  have heq : (fun r=>vectorProfilePhysicalCell s₀ s₁ β t i (r,θ,p,x))=
      (fun r=>vectorFiniteCellPotential (vectorProfileScheme s₀ s₁ θ hθ) β t p i r x):=
    funext (fun r=>vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i r θ hθ p x)
  have hef : (fun y=>vectorProfilePhysicalCell s₀ s₁ β t i (q,θ,p,y))=
      vectorFiniteCellPotential (vectorProfileScheme s₀ s₁ θ hθ) β t p i q:=
    funext (fun y=>vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i q θ hθ p y)
  rw [heq,hef]
  exact hasDerivAt_vectorFiniteCellPotential_PDE (vectorProfileScheme s₀ s₁ θ hθ) β t hβ ht p i q hq x

end QuantitativePaper
