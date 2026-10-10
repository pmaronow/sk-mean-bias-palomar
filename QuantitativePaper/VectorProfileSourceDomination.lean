module
public import QuantitativePaper.VectorProfileActualXi

@[expose] public section

/-! The signed pairing source is controlled by the two genuine
nonnegative profile energies, using the literal canonical Xi matrix. -/
noncomputable section
open Set
open scoped Matrix.Norms.Elementwise MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem responseMatrixPair_abs_young (A B : Matrix (Fin n) (Fin n) ℝ) :
    |responseMatrixPair A B|≤
      (responseMatrixFrobeniusSquare A+responseMatrixFrobeniusSquare B)/2 := by
  have hp:=responseMatrixFrobeniusSquare_nonneg ((1:ℝ) •A+(1:ℝ) •B)
  have hm:=responseMatrixFrobeniusSquare_nonneg ((1:ℝ) •A+(-1:ℝ) •B)
  rw [responseMatrixFrobeniusSquare_add_smul,responseMatrixPair_self,responseMatrixPair_self] at hp hm
  apply abs_le.mpr
  constructor <;> nlinarith

theorem vectorProfileFieldCurvaturePairingSource_abs_bound
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
    let H:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
    |vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i (a,x)|≤
      |(1-t)*(β*(s₁.m i-s₀.m i))*Matrix.trace (H*H)|+
        vectorProfileFieldSecondVariationSource s₀ s₁ β t i (a,x)/(2*(1-t))+
        vectorProfileFieldTraceTimeSource s₀ s₁ β t i (a,x) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  let H:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
  let B:=vectorProfileCellBMatrix s₀ s₁ β t i a m
  let A:=CFC.sqrt H*B*H
  let X:=vectorProfileCellFieldXi s₀ s₁ β t i 1 0 (a,x)
  have hp:=vectorProfileCellFieldXi_curvature_pairing s₀ s₁ β t hβ ht i hi a hq hθ x 1 0
  change responseMatrixPair A X=_ at hp
  simp only [zero_mul,one_mul,zero_add,mul_one] at hp
  have he:=vectorProfileCellFieldXi_energy s₀ s₁ β t hβ ht i hi a hq hθ x 1 0
  change responseMatrixFrobeniusSquare X=_ at he
  simp only [zero_pow (by norm_num : 2≠0),one_pow,zero_mul,mul_zero,zero_add,one_mul] at he
  have hZ : vectorProfileFieldSecondVariationSource s₀ s₁ β t i (a,x)=
      (1-t)*responseMatrixFrobeniusSquare A:=rfl
  have hS : vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i (a,x)=
      responseMatrixPair A X+(1-t)*(β*(s₁.m i-s₀.m i))*Matrix.trace (H*H):=by linarith
  change |vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i (a,x)|≤_
  rw [hS]
  apply (abs_add_le _ _).trans
  apply (add_le_add (responseMatrixPair_abs_young A X) le_rfl).trans_eq
  rw [he,hZ]
  field_simp [sub_ne_zero.mpr ht.ne']
  ring

end QuantitativePaper
