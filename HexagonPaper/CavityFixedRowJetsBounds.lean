module
public import HexagonPaper.CavityFixedRowJetsMatrix
public import QuantitativePaper.BoundedJets

@[expose] public section

/-! Uniform genuine all-order field-observable jet bounds. Constants depend
only on the number of spins, never on profile, level, couplings or field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def cavityFixedRowFieldJetBound (n r : ℕ) : ℝ :=cavityTreeUniformParameterJetBound n (r+1)
def cavityFixedRowSquareJetBound (n r : ℕ) : ℝ :=
  ∑j∈Finset.range (r+1),(r.choose j:ℝ)*cavityFixedRowFieldJetBound n j*
    cavityFixedRowFieldJetBound n (r-j)

theorem cavityFixedRowFieldJetBound_nonneg (n r : ℕ) : 0≤cavityFixedRowFieldJetBound n r :=
  anisotropicSpatialJetBound_nonneg _ _
theorem cavityFixedRowSquareJetBound_nonneg (n r : ℕ) : 0≤cavityFixedRowSquareJetBound n r :=
  Finset.sum_nonneg (fun j _=>mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (cavityFixedRowFieldJetBound_nonneg n j))
    (cavityFixedRowFieldJetBound_nonneg n (r-j)))

theorem cavityFixedRow_native_field_jet_uniform (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) (r : ℕ)
    (P : AnisotropicParameter n) :
    ‖iteratedFDeriv ℝ r (fun Q=>fderiv ℝ
      (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) Q
        (anisotropicCoordinateDirection n i)) P‖≤cavityFixedRowFieldJetBound n r := by
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  have hd : ContDiff ℝ ∞ (fderiv ℝ U):=
    (cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.fderiv_right
      (m:=∞) (by simp)
  apply (norm_iteratedFDeriv_clm_apply_const hd.contDiffAt (by simp)).trans
  rw [norm_iteratedFDeriv_fderiv]
  have hb:‖anisotropicCoordinateDirection n i‖=1:=by
    have he : anisotropicCoordinateDirection n i=
        EuclideanSpace.single (Sum.inr i : AnisotropicCouplingIndex n⊕Fin n) (1:ℝ) := by
      ext j
      cases j <;> simp [anisotropicCoordinateDirection,anisotropicFieldInjection,EuclideanSpace.single_apply]
    rw [he]
    simp
  rw [hb,one_mul]
  exact cavityTree_native_unit_tail_positive_jet_bound D μ q (r+1) (by omega) P

theorem cavityFixedRow_native_square_jet_uniform (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) (r : ℕ)
    (P : AnisotropicParameter n) :
    ‖iteratedFDeriv ℝ r (fun Q=>(fderiv ℝ
      (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) Q
        (anisotropicCoordinateDirection n i))^2) P‖≤cavityFixedRowSquareJetBound n r := by
  let F:=fun Q=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) Q
    (anisotropicCoordinateDirection n i)
  have hF:ContDiff ℝ ∞ F:=
    ((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.fderiv_right
      (m:=∞) (by simp)).clm_apply contDiff_const
  change ‖iteratedFDeriv ℝ r (fun Q=>(F Q)^2) P‖≤_
  simp only [pow_two]
  apply (norm_iteratedFDeriv_mul_le hF hF P (by simp)).trans
  apply Finset.sum_le_sum
  intro j _
  have hb:=mul_le_mul (cavityFixedRow_native_field_jet_uniform D μ q i j P)
    (cavityFixedRow_native_field_jet_uniform D μ q i (r-j) P)
    (norm_nonneg _) (cavityFixedRowFieldJetBound_nonneg n j)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (r.choose j))

def cavityFixedRowNativeLastFieldSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter (n+1)) : ℝ :=
  (fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) P
    (anisotropicCoordinateDirection (n+1) (Fin.last n)))^2

def cavityFixedRowNativeRestFieldSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter (n+1)) : ℝ :=
  (n:ℝ)⁻¹*∑l : Fin n,(fderiv ℝ
    (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) P
      (anisotropicCoordinateDirection (n+1) l.castSucc))^2

theorem cavityFixedRow_native_restSquare_jet_uniform (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (r : ℕ)
    (P : AnisotropicParameter (n+1)) :
    ‖iteratedFDeriv ℝ r (cavityFixedRowNativeRestFieldSquare D μ q) P‖≤
      |(n:ℝ)⁻¹| * (n:ℝ)*cavityFixedRowSquareJetBound (n+1) r := by
  let F:=fun l : Fin n=>fun Q=>(fderiv ℝ
    (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) Q
      (anisotropicCoordinateDirection (n+1) l.castSucc))^2
  have hF (l : Fin n):ContDiff ℝ ∞ (F l):=
    (((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.fderiv_right
      (m:=∞) (by simp)).clm_apply contDiff_const).pow 2
  change ‖iteratedFDeriv ℝ r (fun Q=>(n:ℝ)⁻¹ • ∑l,F l Q) P‖≤_
  rw [iteratedFDeriv_const_smul_apply' ((ContDiff.sum (fun l _=>hF l)).of_le (by simp)).contDiffAt,
    norm_smul,Real.norm_eq_abs,iteratedFDeriv_fun_sum_apply (fun l _=>(hF l).of_le (by simp) |>.contDiffAt)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)).trans
  have hs:(∑l : Fin n,‖iteratedFDeriv ℝ r (F l) P‖)≤
      (n:ℝ)*cavityFixedRowSquareJetBound (n+1) r:=by
    calc
      _≤∑_l : Fin n,cavityFixedRowSquareJetBound (n+1) r:=
        Finset.sum_le_sum (fun l _=>cavityFixedRow_native_square_jet_uniform D μ q l.castSucc r P)
      _=_:=by simp
  exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_eq (by ring)

theorem boundedJets_cavityFixedRowNativeLastFieldSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    BoundedJets (cavityFixedRowNativeLastFieldSquare D μ q) := by
  refine ⟨?_,fun r=>⟨cavityFixedRowSquareJetBound (n+1) r,
    cavityFixedRowSquareJetBound_nonneg (n+1) r,fun P=>?_⟩⟩
  · exact (((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.fderiv_right
      (m:=∞) (by simp)).clm_apply contDiff_const).pow 2
  · exact cavityFixedRow_native_square_jet_uniform D μ q (Fin.last n) r P

theorem boundedJets_cavityFixedRowNativeRestFieldSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    BoundedJets (cavityFixedRowNativeRestFieldSquare D μ q) := by
  refine ⟨?_,fun r=>⟨|(n:ℝ)⁻¹| * (n:ℝ)*cavityFixedRowSquareJetBound (n+1) r,
    mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (cavityFixedRowSquareJetBound_nonneg (n+1) r),fun P=>?_⟩⟩
  · exact contDiff_const.mul (ContDiff.sum (fun l _=>
      (((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.fderiv_right
        (m:=∞) (by simp)).clm_apply contDiff_const).pow 2))
  · exact cavityFixedRow_native_restSquare_jet_uniform D μ q r P

end HexagonPaper
