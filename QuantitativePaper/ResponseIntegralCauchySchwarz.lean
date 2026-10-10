module
public import QuantitativePaper.ResponseGeneratorAlgebra
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

/-! Integral Cauchy–Schwarz for the literal matrix pairing. It uses
only actual scalar integrability and the genuine nonnegative Frobenius
square, so no stochastic or Hilbert-valued measurability is hidden. -/
noncomputable section
open MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem response_integral_matrix_pair_cauchy_schwarz
    (P : Measure Ω) (A B : Ω→Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (fun ω=>responseMatrixFrobeniusSquare (A ω)) P)
    (hB : Integrable (fun ω=>responseMatrixFrobeniusSquare (B ω)) P)
    (hPair : Integrable (fun ω=>responseMatrixPair (A ω) (B ω)) P) :
    (∫ω,responseMatrixPair (A ω) (B ω)∂P)^2≤
      (∫ω,responseMatrixFrobeniusSquare (A ω)∂P)*
      (∫ω,responseMatrixFrobeniusSquare (B ω)∂P) := by
  let a:=∫ω,responseMatrixFrobeniusSquare (A ω)∂P
  let b:=∫ω,responseMatrixPair (A ω) (B ω)∂P
  let c:=∫ω,responseMatrixFrobeniusSquare (B ω)∂P
  have hquad (v : ℝ) : 0≤a*(v*v)+(2*b)*v+c:=by
    have hn:=integral_nonneg (μ:=P) (f:=fun ω=>responseMatrixFrobeniusSquare (v •A ω+(1:ℝ) •B ω)) (fun ω=>
      responseMatrixFrobeniusSquare_nonneg (v •A ω+(1:ℝ) •B ω))
    have he : (fun ω=>responseMatrixFrobeniusSquare (v •A ω+(1:ℝ) •B ω))=
        (fun ω=>v^2*responseMatrixFrobeniusSquare (A ω)+
          (2*v)*responseMatrixPair (A ω) (B ω)+responseMatrixFrobeniusSquare (B ω)):=by
      funext ω
      rw [responseMatrixFrobeniusSquare_add_smul,responseMatrixPair_self,responseMatrixPair_self]
      ring
    rw [he] at hn
    have h₁:=integral_add ((hA.const_mul (v^2)).add (hPair.const_mul (2*v))) hB
    have h₂:=integral_add (hA.const_mul (v^2)) (hPair.const_mul (2*v))
    simp only [Pi.add_apply] at h₁ h₂
    rw [h₁,h₂,integral_const_mul,integral_const_mul] at hn
    change 0≤v^2*a+(2*v)*b+c at hn
    nlinarith only [hn]
  have hd:=discrim_le_zero hquad
  unfold discrim at hd
  change b^2≤a*c
  nlinarith only [hd]

end QuantitativePaper
