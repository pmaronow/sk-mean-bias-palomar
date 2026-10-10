module
public import QuantitativeFollowup.AnisotropicShiftEnergy

@[expose] public section

/-! Genuine continuity and finite-profile global bounds of the actual
selected-coordinate Hessian energy. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

theorem anisotropicFieldHessian_quadratic_eq_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    inner ℝ w (anisotropicFieldHessian D s j P w)=
      directionalHessian (anisotropicFinitePotential D s j) P (anisotropicFieldInjection n w) := by
  have he : (fun r : ℝ => anisotropicFinitePotential D s j (P+anisotropicFieldInjection n (0+r • w)))=
      fun r => anisotropicFinitePotential D s j (P+r • anisotropicFieldInjection n w) := by
    funext r
    rw [zero_add,map_smul]
  rw [real_inner_comm,anisotropicFieldHessian,inner_hessianOperator]
  change directionalHessian (fun v => anisotropicFinitePotential D s j (P+anisotropicFieldInjection n v)) 0 w=_
  rw [directionalHessian_eq_secondDeriv_line _
    ((contDiff_anisotropicTranslatedFieldPotential D s j P).of_le (by simp)),he,
    ←directionalHessian_eq_secondDeriv_line _ ((contDiff_anisotropicFinitePotential D s j).of_le (by simp))]

theorem norm_anisotropicSelectedMagnetization_le_sqrt (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) :
    ‖anisotropicSelectedMagnetization D s J i z‖≤Real.sqrt (J.card : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _ : J,(1 : ℝ) := Finset.sum_le_sum fun l _ => by
      have hb := anisotropicMagnetization_component_bound D s (k+2-i)
        (anisotropicEuclideanStateLinear D s i z) l.val
      change ‖anisotropicEuclideanMagnetization D s i z l.val‖^2≤1
      rw [Real.norm_eq_abs,sq_abs]
      change |anisotropicEuclideanMagnetization D s i z l.val|≤1 at hb
      have hab := abs_le.mp hb
      nlinarith [sq_nonneg (anisotropicEuclideanMagnetization D s i z l.val)]
    _ = _ := by simp

theorem continuous_anisotropicSelfOverlapEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) : Continuous (anisotropicSelfOverlapEnergy D s J i) := by
  let U := anisotropicFinitePotential D s (k+2-i)
  let P := anisotropicEuclideanStateLinear D s i
  let v := fun z => anisotropicFieldInjection n (anisotropicSelectedMean D s J i z)
  have hv : Continuous v := (anisotropicFieldInjection n).continuous.comp
    ((anisotropicSelectedInsertion J).continuous.comp (contDiff_anisotropicSelectedMagnetization D s J i).continuous)
  have hdu : ContDiff ℝ ∞ (fderiv ℝ U) := (contDiff_anisotropicFinitePotential D s _).fderiv_right (by simp)
  have hddu : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ U)) := hdu.fderiv_right (by simp)
  have he : anisotropicSelfOverlapEnergy D s J i=fun z => fderiv ℝ (fderiv ℝ U) (P z) (v z) (v z) := by
    funext z
    exact anisotropicFieldHessian_quadratic_eq_parameter D s _ _ _
  rw [he]
  exact ((hddu.continuous.comp P.continuous).clm_apply hv).clm_apply hv

theorem exists_anisotropicSelfOverlapEnergy_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    ∃B : ℝ,0≤B ∧ ∀z : AnisotropicGaussianSpace n k,|anisotropicSelfOverlapEnergy D s J i z|≤B := by
  obtain ⟨K,hK,hb⟩ := (boundedPositiveJets_anisotropicFinitePotential D s (k+2-i)).2 2 (by omega)
  let R := ‖anisotropicFieldInjection n‖*‖anisotropicSelectedInsertion J‖*Real.sqrt (J.card : ℝ)
  have hR : 0≤R := mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨K*R^2,mul_nonneg hK (sq_nonneg _),fun z => ?_⟩
  let U := anisotropicFinitePotential D s (k+2-i)
  let P := anisotropicEuclideanStateLinear D s i z
  let v := anisotropicFieldInjection n (anisotropicSelectedMean D s J i z)
  have hv : ‖v‖≤R := by
    apply ((anisotropicFieldInjection n).le_opNorm _).trans
    change _≤‖anisotropicFieldInjection n‖*‖anisotropicSelectedInsertion J‖*Real.sqrt (J.card : ℝ)
    apply (mul_le_mul_of_nonneg_left ((anisotropicSelectedInsertion J).le_opNorm _) (norm_nonneg _)).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (norm_anisotropicSelectedMagnetization_le_sqrt D s J i z)
      (mul_nonneg (norm_nonneg (anisotropicFieldInjection n)) (norm_nonneg (anisotropicSelectedInsertion J)))
  unfold anisotropicSelfOverlapEnergy
  rw [anisotropicFieldHessian_quadratic_eq_parameter]
  change |fderiv ℝ (fderiv ℝ U) P v v|≤_
  have hh := ((fderiv ℝ (fderiv ℝ U) P v).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ U) P).le_opNorm v) (norm_nonneg _))
  rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,Real.norm_eq_abs] at hh
  have hnorm : ‖iteratedFDeriv ℝ 2 U P‖≤K := hb P
  have hs := pow_le_pow_left₀ (norm_nonneg _) hv 2
  nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 U P),norm_nonneg v]

end QuantitativeFollowup
