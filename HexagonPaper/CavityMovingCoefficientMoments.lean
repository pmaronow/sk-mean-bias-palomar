module
public import HexagonPaper.CavityMovingCoefficientObservableContinuity

@[expose] public section

/-! The four literal raw moments used to normalize the actual retained
magnetization covariance, with dimension-only bounds for every spatial jet. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

inductive CavityMovingCoefficientMomentKind where
  | normalizer | lastSquare | restSquare | product

def cavityMovingCoefficientMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    CavityMovingCoefficientMomentKind→AnisotropicParameter (n+1)→ℝ
  | .normalizer=>fun _=>1
  | .lastSquare=>cavityFixedRowNativeLastFieldSquare D μ p
  | .restSquare=>cavityFixedRowNativeRestFieldSquare D μ p
  | .product=>fun P=>cavityFixedRowNativeLastFieldSquare D μ p P*
      cavityFixedRowNativeRestFieldSquare D μ p P

def cavityMovingCoefficientMomentBound (n : ℕ) : CavityMovingCoefficientMomentKind→ℕ→ℝ
  | .normalizer=>fun _=>1
  | .lastSquare=>cavityFixedRowSquareJetBound (n+1)
  | .restSquare=>fun r=>|(n : ℝ)⁻¹| * (n : ℝ)*cavityFixedRowSquareJetBound (n+1) r
  | .product=>fun r=>∑j∈Finset.range (r+1),(r.choose j : ℝ)*
      cavityFixedRowSquareJetBound (n+1) j*
      (|(n : ℝ)⁻¹| * (n : ℝ)*cavityFixedRowSquareJetBound (n+1) (r-j))

theorem cavityMovingCoefficientMomentBound_nonneg (kind : CavityMovingCoefficientMomentKind) (r : ℕ) :
    0≤cavityMovingCoefficientMomentBound n kind r := by
  cases kind with
  | normalizer=>exact zero_le_one
  | lastSquare=>exact cavityFixedRowSquareJetBound_nonneg _ _
  | restSquare=>exact (mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (cavityFixedRowSquareJetBound_nonneg _ _))
  | product=>exact (Finset.sum_nonneg fun j _=>mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (cavityFixedRowSquareJetBound_nonneg _ j))
      (mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
        (cavityFixedRowSquareJetBound_nonneg _ (r-j))))

theorem cavityMovingCoefficientMoment_smooth (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (kind : CavityMovingCoefficientMomentKind) :
    ContDiff ℝ ∞ (cavityMovingCoefficientMoment D μ p kind) := by
  cases kind with
  | normalizer=>exact contDiff_const
  | lastSquare=>exact (boundedJets_cavityFixedRowNativeLastFieldSquare D μ p).1
  | restSquare=>exact (boundedJets_cavityFixedRowNativeRestFieldSquare D μ p).1
  | product=>exact ((boundedJets_cavityFixedRowNativeLastFieldSquare D μ p).1.mul
      (boundedJets_cavityFixedRowNativeRestFieldSquare D μ p).1)

theorem cavityMovingCoefficientMoment_jet_bound (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (kind : CavityMovingCoefficientMomentKind)
    (r : ℕ) (P : AnisotropicParameter (n+1)) :
    ‖iteratedFDeriv ℝ r (cavityMovingCoefficientMoment D μ p kind) P‖≤
      cavityMovingCoefficientMomentBound n kind r := by
  cases kind with
  | normalizer=>
    by_cases hr : r=0
    · subst r; simp [cavityMovingCoefficientMoment,cavityMovingCoefficientMomentBound]
    · simp [cavityMovingCoefficientMoment,cavityMovingCoefficientMomentBound,iteratedFDeriv_const_of_ne hr]
  | lastSquare=>exact cavityFixedRow_native_square_jet_uniform D μ p (Fin.last n) r P
  | restSquare=>simpa only [cavityMovingCoefficientMoment,cavityMovingCoefficientMomentBound] using
      cavityFixedRow_native_restSquare_jet_uniform D μ p r P
  | product=>
    apply (norm_iteratedFDeriv_mul_le
      (cavityMovingCoefficientMoment_smooth D μ p .lastSquare)
      (cavityMovingCoefficientMoment_smooth D μ p .restSquare) P (by simp)).trans
    change _ ≤ ∑j∈Finset.range (r+1),(r.choose j : ℝ)*
      cavityFixedRowSquareJetBound (n+1) j*
      (|(n : ℝ)⁻¹| * (n : ℝ)*cavityFixedRowSquareJetBound (n+1) (r-j))
    apply Finset.sum_le_sum
    intro j _
    have hlast : ‖iteratedFDeriv ℝ j (cavityFixedRowNativeLastFieldSquare D μ p) P‖ ≤
        cavityFixedRowSquareJetBound (n+1) j :=
      cavityFixedRow_native_square_jet_uniform D μ p (Fin.last n) j P
    have hh := mul_le_mul hlast
      (cavityFixedRow_native_restSquare_jet_uniform D μ p (r-j) P) (norm_nonneg _)
      (cavityFixedRowSquareJetBound_nonneg _ j)
    simpa only [mul_assoc,cavityMovingCoefficientMoment]
      using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

theorem continuous_cavityMovingCoefficientMoment_variance
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) (kind : CavityMovingCoefficientMomentKind) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter (n+1)=>
      cavityMovingCoefficientMoment (anisotropicReplaceVariance D i z.1.val) μ p kind z.2) := by
  cases kind with
  | normalizer=>exact continuous_const
  | lastSquare=>exact continuous_cavityMovingVarianceLastSquare D μ i p
  | restSquare=>exact continuous_cavityMovingVarianceRestSquare D μ i p
  | product=>exact ((continuous_cavityMovingVarianceLastSquare D μ i p).mul
      (continuous_cavityMovingVarianceRestSquare D μ i p))

theorem cavityMovingCoefficientMoment_row_jet_joint_continuous
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) (kind : CavityMovingCoefficientMomentKind)
    (P : {b : ℝ // 0<b}→AnisotropicParameter (n+1)) (hP : Continuous P) (r : ℕ) :
    Continuous (fun z : {b : ℝ // 0<b}×Field n=>iteratedFDeriv ℝ r
      (fun y=>cavityMovingCoefficientMoment (anisotropicReplaceVariance D i z.1.val) μ p kind
        (P z.1+cavityNativeFixedRowParameterChart n y)) z.2) := by
  let G := fun b : {b : ℝ // 0<b}=>cavityMovingCoefficientMoment
    (anisotropicReplaceVariance D i b.val) μ p kind
  exact cavityMovingAffineObservable_jet_joint_continuous (n:=n+1) (m:=n) G
    (continuous_cavityMovingCoefficientMoment_variance D μ i p kind)
    (fun b=>cavityMovingCoefficientMoment_smooth _ μ p kind)
    (cavityMovingCoefficientMomentBound n kind) (cavityMovingCoefficientMomentBound_nonneg kind)
    (fun r b P=>cavityMovingCoefficientMoment_jet_bound _ μ p kind r P)
    P hP (cavityNativeFixedRowParameterChart n) r

end HexagonPaper
