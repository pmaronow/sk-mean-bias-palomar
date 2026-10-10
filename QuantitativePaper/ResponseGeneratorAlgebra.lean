module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Tactic

@[expose] public section

/-! Exact noncommutative matrix algebra for the response generator.
The hypotheses below are pointwise jet equations. Their identification with
the actual Legendre response and its generator is a separate analytic step;
these helpers do not assert the midpoint theorem from assumed conclusions. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

def responseMatrixPair (A B : Mat) : ℝ := Matrix.trace (A.transpose * B)

def responseMatrixFrobeniusSquare (A : Mat) : ℝ := ∑ i, ∑ j, (A i j)^2

theorem responseMatrixPair_self (A : Mat) :
    responseMatrixPair A A = responseMatrixFrobeniusSquare A := by
  unfold responseMatrixPair Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [responseMatrixFrobeniusSquare, pow_two]

theorem responseMatrixPair_symm_left (A B : Mat) (hA : A.IsSymm) :
    responseMatrixPair A B = Matrix.trace (A * B) := by
  simp only [responseMatrixPair, hA.eq]

theorem responseMatrixPair_square (h Z : Mat) (hh : h.IsSymm) :
    responseMatrixPair (h*h) Z = Matrix.trace (h*Z*h) := by
  rw [responseMatrixPair, Matrix.transpose_mul, hh.eq]
  exact (Matrix.trace_mul_cycle h Z h).symm

/-- The scalar generator cancellation in the second profile variation. -/
theorem response_generator_second_variation (h B Z hθθ : Mat) (r zq : ℝ)
    (hh : h.IsSymm)
    (hsecond : hθθ = (2 : ℝ) • (h*B*h*B*h) - h*Z*h)
    (hzq : zq = r/2*Matrix.trace hθθ) :
    zq+r/2*responseMatrixPair (h*h) Z = r*Matrix.trace (h*B*h*B*h) := by
  rw [hzq, hsecond, Matrix.trace_sub, Matrix.trace_smul,
    responseMatrixPair_square h Z hh]
  simp only [smul_eq_mul]
  ring

/-- The trace reaction, including the exact coefficient of γ. -/
theorem response_generator_trace (h N hdot : Mat) (r γ : ℝ)
    (hh : h.IsSymm)
    (hjet : hdot = -(r/2) • (h*(N+(2*γ) • (1 : Mat))*h)) :
    Matrix.trace hdot+r/2*responseMatrixPair (h*h) N =
      -r*γ*Matrix.trace (h*h) := by
  rw [hjet, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.trace_smul, responseMatrixPair_square h N hh]
  simp only [smul_eq_mul]
  ring

/-- Cyclicity gives the two identical time-derivative trace terms. -/
theorem response_trace_square_variation (h B hdot : Mat)
    (hh : h.IsSymm) (hB : B.IsSymm) (hd : hdot.IsSymm) :
    Matrix.trace ((hdot*h+h*hdot)*B) = 2*Matrix.trace (h*B*hdot) := by
  rw [Matrix.add_mul, Matrix.trace_add]
  have h₁ : Matrix.trace (hdot*h*B) = Matrix.trace (h*B*hdot) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  have h₂ : Matrix.trace (h*hdot*B) = Matrix.trace (h*B*hdot) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
      hh.eq, hB.eq, hd.eq]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle' B hdot h
  rw [h₁, h₂]
  ring

/-- The inverse-weighted positive source after the trace reaction is
differentiated in time. No commutation of h with its time derivative is used. -/
theorem response_generator_trace_time (h K hdot : Mat) [Invertible h]
    (r : ℝ) (hh : h.IsSymm) (hd : hdot.IsSymm)
    (hjet : hdot = -(r/2) • (h*K*h)) :
    -(r/2)*responseMatrixPair (hdot*h+h*hdot) K =
      2*Matrix.trace (hdot*h⁻¹*hdot) := by
  have hS : (hdot*h+h*hdot).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_mul, hh.eq, hd.eq]
    exact add_comm _ _
  have hi : h⁻¹*hdot*h⁻¹ = -(r/2) • K := by
    rw [hjet]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      Matrix.inv_mul_cancel_left_of_invertible]
    simp only [← Matrix.mul_assoc, Matrix.mul_inv_cancel_right_of_invertible]
  rw [responseMatrixPair_symm_left _ _ hS]
  calc
    -(r/2)*Matrix.trace ((hdot*h+h*hdot)*K) =
        Matrix.trace ((hdot*h+h*hdot)*(h⁻¹*hdot*h⁻¹)) := by
      rw [hi, Matrix.mul_smul, Matrix.trace_smul]
      rfl
    _ = Matrix.trace (hdot*h*(h⁻¹*hdot*h⁻¹)) +
        Matrix.trace (h*hdot*(h⁻¹*hdot*h⁻¹)) := by
      rw [Matrix.add_mul, Matrix.trace_add]
    _ = Matrix.trace (hdot*hdot*h⁻¹) + Matrix.trace (hdot*h⁻¹*hdot) := by
      congr 1
      · simp only [← Matrix.mul_assoc, Matrix.mul_inv_cancel_right_of_invertible]
      · rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible]
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle h⁻¹ hdot hdot
    _ = 2*Matrix.trace (hdot*h⁻¹*hdot) := by
      rw [← Matrix.trace_mul_cycle hdot h⁻¹ hdot]
      ring

/-- The generator of Tr(h²B) from the genuine pointwise B equation and
the ordinary product derivative. -/
theorem response_generator_curvature_pairing (h B hdot Bdot Z : Mat)
    (r v sq : ℝ) (hh : h.IsSymm) (hB : B.IsSymm) (hd : hdot.IsSymm)
    (hBjet : Bdot+(r/2) • Z = (r*v) • (1 : Mat))
    (hsq : sq = Matrix.trace ((hdot*h+h*hdot)*B+(h*h)*Bdot)) :
    sq+r/2*responseMatrixPair (h*h) Z =
      r*v*Matrix.trace (h*h)+2*Matrix.trace (h*B*hdot) := by
  have hsqpair : responseMatrixPair (h*h) Z = Matrix.trace ((h*h)*Z) := by
    rw [responseMatrixPair, Matrix.transpose_mul, hh.eq]
  have htr := congrArg (fun X : Mat=>Matrix.trace ((h*h)*X)) hBjet
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.mul_one, smul_eq_mul] at htr
  rw [hsq, Matrix.trace_add, response_trace_square_variation h B hdot hh hB hd,
    hsqpair]
  linarith

def responseXiEnergy (h hdot : Mat) (φ φ' : ℝ) : ℝ :=
  φ'^2*Matrix.trace h+4*φ*φ'*Matrix.trace hdot+
    4*φ^2*Matrix.trace (hdot*h⁻¹*hdot)

def responseXiPairing (h B hdot : Mat) (φ φ' : ℝ) : ℝ :=
  φ'*Matrix.trace (h*h*B)+2*φ*Matrix.trace (h*B*hdot)

/-- Literal square-energy identity after the actual generator product
rule is identified. The inverse-weight form avoids choosing a square root. -/
theorem response_Xi_energy_identity (h hdot : Mat) (φ φ' Lphidot : ℝ)
    (hgen : Lphidot = 2*φ*φ'*Matrix.trace hdot+
      2*φ^2*Matrix.trace (hdot*h⁻¹*hdot)) :
    responseXiEnergy h hdot φ φ' = φ'^2*Matrix.trace h+2*Lphidot := by
  rw [hgen, responseXiEnergy]
  ring

/-- Jumps of the mass change the trace time derivative by precisely the
Stieltjes correction used in the paper. -/
theorem response_trace_time_jump (h N dotLeft dotRight : Mat)
    (r γLeft γRight : ℝ) (hh : h.IsSymm)
    (hleft : dotLeft = -(r/2) • (h*(N+(2*γLeft) • (1 : Mat))*h))
    (hright : dotRight = -(r/2) • (h*(N+(2*γRight) • (1 : Mat))*h)) :
    Matrix.trace dotRight-Matrix.trace dotLeft =
      -r*(γRight-γLeft)*Matrix.trace (h*h) := by
  have hl := response_generator_trace h N dotLeft r γLeft hh hleft
  have hr := response_generator_trace h N dotRight r γRight hh hright
  nlinarith

theorem responseMatrixPair_comm (A B : Mat) :
    responseMatrixPair A B = responseMatrixPair B A := by
  unfold responseMatrixPair
  rw [← Matrix.trace_transpose (A.transpose*B), Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- The response source really is the Frobenius square, with any genuine
symmetric square root. Later analytic specializations can use CFC.sqrt. -/
theorem response_second_variation_frobenius (h B R : Mat)
    (hh : h.IsSymm) (hB : B.IsSymm) (hR : R.IsSymm) (hsq : R*R = h) :
    Matrix.trace (h*B*h*B*h) = responseMatrixFrobeniusSquare (R*B*h) := by
  rw [← responseMatrixPair_self, responseMatrixPair, Matrix.transpose_mul,
    Matrix.transpose_mul, hh.eq, hB.eq, hR.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R R (B*h), hsq]

/-- Literal curvature pairing with Xi, expressed through a true symmetric
square root and its inverse. -/
theorem response_Xi_frobenius_pairing (h B hdot R : Mat) [Invertible R]
    (hh : h.IsSymm) (hB : B.IsSymm) (hR : R.IsSymm)
    (hsq : R*R = h) (φ φ' : ℝ) :
    responseMatrixPair (R*B*h) (φ' • R+(2*φ) • (R⁻¹*hdot)) =
      responseXiPairing h B hdot φ φ' := by
  unfold responseMatrixPair responseXiPairing
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hh.eq, hB.eq, hR.eq,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul]
  have h₁ : Matrix.trace (h*B*R*R) = Matrix.trace (h*h*B) := by
    rw [Matrix.mul_assoc (h*B) R R, hsq, Matrix.trace_mul_cycle]
  have h₂ : h*B*R*(R⁻¹*hdot) = h*B*hdot := by
    simp only [← Matrix.mul_assoc, Matrix.mul_inv_cancel_right_of_invertible]
  simp only [← Matrix.mul_assoc] at h₂ ⊢
  rw [h₁, h₂]
  simp only [smul_eq_mul]

theorem responseMatrixFrobeniusSquare_add_smul (A C : Mat) (a b : ℝ) :
    responseMatrixFrobeniusSquare (a • A+b • C) =
      a^2*responseMatrixPair A A+2*a*b*responseMatrixPair A C+
        b^2*responseMatrixPair C C := by
  rw [← responseMatrixPair_self]
  unfold responseMatrixPair
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]
  have hc : Matrix.trace (C.transpose*A) = Matrix.trace (A.transpose*C) := by
    exact responseMatrixPair_comm C A
  rw [hc]
  ring

theorem response_Xi_frobenius_energy (h hdot R : Mat) [Invertible R]
    (hd : hdot.IsSymm) (hR : R.IsSymm) (hsq : R*R = h) (φ φ' : ℝ) :
    responseMatrixFrobeniusSquare (φ' • R+(2*φ) • (R⁻¹*hdot)) =
      responseXiEnergy h hdot φ φ' := by
  have h₁ : responseMatrixPair R R = Matrix.trace h := by
    rw [responseMatrixPair_symm_left R R hR, hsq]
  have h₂ : responseMatrixPair R (R⁻¹*hdot) = Matrix.trace hdot := by
    rw [responseMatrixPair_symm_left R _ hR, Matrix.mul_inv_cancel_left_of_invertible]
  have h₃ : responseMatrixPair (R⁻¹*hdot) (R⁻¹*hdot) =
      Matrix.trace (hdot*h⁻¹*hdot) := by
    rw [responseMatrixPair, Matrix.transpose_mul, hd.eq, hR.inv.eq]
    have hi : R⁻¹*R⁻¹ = h⁻¹ := by rw [← Matrix.mul_inv_rev, hsq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R⁻¹ R⁻¹ hdot, hi]
  rw [responseMatrixFrobeniusSquare_add_smul, h₁, h₂, h₃, responseXiEnergy]
  ring

theorem responseMatrixFrobeniusSquare_nonneg (A : Mat) :
    0 ≤ responseMatrixFrobeniusSquare A := by
  exact Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>sq_nonneg (A i j)

theorem response_Xi_energy_nonneg (h hdot R : Mat) [Invertible R]
    (hd : hdot.IsSymm) (hR : R.IsSymm) (hsq : R*R = h) (φ φ' : ℝ) :
    0 ≤ responseXiEnergy h hdot φ φ' := by
  rw [← response_Xi_frobenius_energy h hdot R hd hR hsq φ φ']
  exact responseMatrixFrobeniusSquare_nonneg _

/-- The time-only test multiplier gives exactly the paper's Xi pairing. -/
theorem response_generator_test_pairing (h B hdot : Mat) (r v φ φ' Ls : ℝ)
    (hgen : Ls = r*v*Matrix.trace (h*h)+2*Matrix.trace (h*B*hdot)) :
    φ'*Matrix.trace (h*h*B)+φ*Ls =
      r*v*φ*Matrix.trace (h*h)+responseXiPairing h B hdot φ φ' := by
  rw [hgen, responseXiPairing]
  ring

open scoped MatrixOrder

/-- The paper's canonical square root, without an assumed factorization. -/
theorem response_second_variation_cfc_frobenius (h B : Mat)
    (hh : h.PosSemidef) (hB : B.IsSymm) :
    Matrix.trace (h*B*h*B*h) =
      responseMatrixFrobeniusSquare (CFC.sqrt h*B*h) := by
  have hR : (CFC.sqrt h).IsSymm :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg h)).isHermitian.isSymm
  exact response_second_variation_frobenius h B (CFC.sqrt h)
    hh.isHermitian.isSymm hB hR (CFC.sqrt_mul_sqrt_self h hh.nonneg)

theorem response_second_variation_source_nonneg (h B : Mat)
    (hh : h.PosSemidef) (hB : B.IsSymm) :
    0 ≤ Matrix.trace (h*B*h*B*h) := by
  rw [response_second_variation_cfc_frobenius h B hh hB]
  exact responseMatrixFrobeniusSquare_nonneg _

def responseXiMatrix (h hdot : Mat) (φ φ' : ℝ) : Mat :=
  φ' • CFC.sqrt h+(2*φ) • ((CFC.sqrt h)⁻¹*hdot)

theorem response_Xi_cfc_energy (h hdot : Mat) (hh : h.PosDef)
    (hd : hdot.IsSymm) (φ φ' : ℝ) :
    responseMatrixFrobeniusSquare (responseXiMatrix h hdot φ φ') =
      responseXiEnergy h hdot φ φ' := by
  have hR : (CFC.sqrt h).IsSymm :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg h)).isHermitian.isSymm
  have hs : CFC.sqrt h*CFC.sqrt h = h :=
    CFC.sqrt_mul_sqrt_self h hh.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt h*CFC.sqrt h) := hs.symm ▸ hh.isUnit
  let _ := ((Commute.refl (CFC.sqrt h)).isUnit_mul_iff.mp hu).1.invertible
  exact response_Xi_frobenius_energy h hdot (CFC.sqrt h) hd hR hs φ φ'

theorem response_Xi_cfc_pairing (h B hdot : Mat) (hh : h.PosDef)
    (hB : B.IsSymm) (φ φ' : ℝ) :
    responseMatrixPair (CFC.sqrt h*B*h) (responseXiMatrix h hdot φ φ') =
      responseXiPairing h B hdot φ φ' := by
  have hR : (CFC.sqrt h).IsSymm :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg h)).isHermitian.isSymm
  have hs : CFC.sqrt h*CFC.sqrt h = h :=
    CFC.sqrt_mul_sqrt_self h hh.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt h*CFC.sqrt h) := hs.symm ▸ hh.isUnit
  let _ := ((Commute.refl (CFC.sqrt h)).isUnit_mul_iff.mp hu).1.invertible
  exact response_Xi_frobenius_pairing h B hdot (CFC.sqrt h)
    hh.isHermitian.isSymm hB hR hs φ φ'

theorem response_inverse_weight_frobenius (h hdot : Mat) (hh : h.PosDef)
    (hd : hdot.IsSymm) :
    Matrix.trace (hdot*h⁻¹*hdot) =
      responseMatrixFrobeniusSquare (CFC.sqrt (h⁻¹)*hdot) := by
  have hR : (CFC.sqrt (h⁻¹)).IsSymm :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (h⁻¹))).isHermitian.isSymm
  have hs : CFC.sqrt (h⁻¹)*CFC.sqrt (h⁻¹) = h⁻¹ :=
    CFC.sqrt_mul_sqrt_self (h⁻¹) hh.inv.posSemidef.nonneg
  rw [← responseMatrixPair_self, responseMatrixPair, Matrix.transpose_mul, hd.eq, hR.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt (h⁻¹)) (CFC.sqrt (h⁻¹)) hdot, hs]

theorem response_generator_trace_time_cfc (h K hdot : Mat)
    (hh : h.PosDef) (hd : hdot.IsSymm) (r : ℝ)
    (hjet : hdot = -(r/2) • (h*K*h)) :
    -(r/2)*responseMatrixPair (hdot*h+h*hdot) K =
      2*responseMatrixFrobeniusSquare (CFC.sqrt (h⁻¹)*hdot) := by
  let _ := hh.isUnit.invertible
  rw [response_generator_trace_time h K hdot r hh.isHermitian.isSymm hd hjet,
    response_inverse_weight_frobenius h hdot hh hd]

end QuantitativePaper
