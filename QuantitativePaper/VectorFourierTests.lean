module
public import QuantitativePaper.VectorJointObservableRecursion
public import FourPapersCommon.CircularJetBounds

@[expose] public section

/-! Actual Fourier observables belong to the bounded smooth test class
needed to identify the finite diffusion and branching laws. -/
noncomputable section
open scoped ContDiff
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}

def vectorSineTestData (L : VectorParameter n→L[ℝ] ℝ) :
    VectorBoundedC3 (fun p=>Real.sin (L p)) where
  regularity := L.contDiff.sin
  bounds := fun j=>‖L‖^j
  bounds_nonneg := fun j=>pow_nonneg (norm_nonneg L) j
  jets := fun j _=>norm_iteratedFDeriv_sin_clm_le L j

def vectorCosineTestData (L : VectorParameter n→L[ℝ] ℝ) :
    VectorBoundedC3 (fun p=>Real.cos (L p)) where
  regularity := L.contDiff.cos
  bounds := fun j=>‖L‖^j
  bounds_nonneg := fun j=>pow_nonneg (norm_nonneg L) j
  jets := fun j _=>norm_iteratedFDeriv_cos_clm_le L j

end QuantitativePaper
