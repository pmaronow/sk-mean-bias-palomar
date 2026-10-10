module
public import QuantitativeFollowup.AnisotropicTailTimeGenerator

@[expose] public section

/-! The Gaussian trace is exactly the manuscript's variance-weighted sum
of actual field-coordinate derivatives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 600000

private theorem timeUnit_single (D : AnisotropicSpinModel n) (i : Fin n) :
    anisotropicUnitInput D (EuclideanSpace.single i 1) =
      Real.sqrt (D.variance i) • anisotropicCoordinateDirection n i := by
  classical
  unfold anisotropicUnitInput anisotropicCoordinateDirection
  rw [ContinuousLinearMap.comp_apply,←map_smul]
  congr 1
  ext j
  simp only [anisotropicNoiseMap_apply,EuclideanSpace.single_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases h : i=j
  · subst j
    simp
  · simp [h,Ne.symm h]

theorem anisotropicTailTimeGenerator_coordinates (D : AnisotropicSpinModel n)
    (a : ℝ) (F : AnisotropicParameter n → ℝ) (P : AnisotropicParameter n) :
    finiteStateGaussianGeneratorField a (anisotropicUnitInput D) F P =
      (∑ i : Fin n,D.variance i *
        (fderiv ℝ (fderiv ℝ F) P (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)+
          a*(fderiv ℝ F P (anisotropicCoordinateDirection n i))^2))/2 := by
  classical
  unfold finiteStateGaussianGeneratorField
  congr 1
  apply Fintype.sum_equiv (Fintype.equivFin (Fin n)).symm
  intro i
  simp only [finiteStateGaussianBasis,OrthonormalBasis.reindex_apply,EuclideanSpace.basisFun_apply]
  rw [timeUnit_single]
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [mul_pow,Real.sq_sqrt (D.variance_pos _).le]
  ring_nf
  rw [Real.sq_sqrt (D.variance_pos _).le]
  ring

end QuantitativeFollowup
