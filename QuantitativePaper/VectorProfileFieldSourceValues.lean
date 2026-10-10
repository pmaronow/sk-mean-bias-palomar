module
public import QuantitativePaper.VectorProfileFieldSources

@[expose] public section

/-! Literal field-coordinate source terms for actual profile variations. -/
noncomputable section
open scoped Matrix.Norms.Elementwise MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
variable {n k : ℕ}

def vectorProfileFieldSecondVariationSource (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i z
  (1-t)*responseMatrixFrobeniusSquare
    (CFC.sqrt (vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m)*
      vectorProfileCellBMatrix s₀ s₁ β t i z.1 m*
      vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m)

def vectorProfileFieldCurvaturePairingSource (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i z
  (1-t)*(β*(s₁.m i-s₀.m i))*Matrix.trace
    (vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m*
      vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m)+
    2*Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m*
      vectorProfileCellBMatrix s₀ s₁ β t i z.1 m*
      vectorProfileCellHessianTimeMatrix s₀ s₁ β t i z.1 m)

def vectorProfileFieldTraceTimeSource (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i z
  2*responseMatrixFrobeniusSquare
    (CFC.sqrt ((vectorProfileCellHessianMatrix s₀ s₁ β t i z.1 m)⁻¹)*
      vectorProfileCellHessianTimeMatrix s₀ s₁ β t i z.1 m)

end QuantitativePaper
