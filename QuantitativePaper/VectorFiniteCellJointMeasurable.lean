module
public import QuantitativePaper.VectorPartialJets
public import QuantitativePaper.VectorFiniteCellGenerator

@[expose] public section

/-! Actual joint disorder/time/field measurability of the finite-cell tests.
Spatial derivatives are literal Frechet partial derivatives of the proved
jointly smooth potential. -/
noncomputable section
open MeasureTheory Set FourPapersCommon
open scoped ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem continuous_vectorFiniteCell_fderiv_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (q : ℝ) :
    Continuous (fun z : VectorParameter n => fderiv ℝ (vectorFiniteCellPotential s β t z.1 i q) z.2) :=
  (contDiff_fieldSlice_fderiv
    (fun z : VectorParameter n => vectorFiniteCellPotential s β t z.1 i q z.2)
    ((contDiff_vectorFiniteCellPotential_joint s β t i q).of_le (by simp : (1 : ℕ∞ω)+1≤∞))).continuous

theorem continuous_vectorFiniteCell_hessian_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (q : ℝ) :
    Continuous (fun z : VectorParameter n => vectorHessian (vectorFiniteCellPotential s β t z.1 i q) z.2) :=
  continuous_fieldSlice_hessian
    (fun z : VectorParameter n => vectorFiniteCellPotential s β t z.1 i q z.2)
    ((contDiff_vectorFiniteCellPotential_joint s β t i q).of_le (by simp))

theorem continuous_vectorFiniteCell_gradient_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (q : ℝ) :
    Continuous (fun z : VectorParameter n => gradient (vectorFiniteCellPotential s β t z.1 i q) z.2) := by
  exact (InnerProductSpace.toDual ℝ (Field n)).symm.continuous.comp
    (continuous_vectorFiniteCell_fderiv_parameter s β t i q)

theorem measurable_vectorFiniteCellPotential_time_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) :
    Measurable (fun z : ℝ×VectorParameter n => vectorFiniteCellPotential s β t z.2.1 i z.1 z.2.2) := by
  change Measurable (Function.uncurry (fun q (z : VectorParameter n) =>
    vectorFiniteCellPotential s β t z.1 i q z.2))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro z
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellPotential_time_field s β t z.1 i).comp
        (show Continuous (fun q : ℝ => (q,z.2)) from continuous_id.prodMk continuous_const)
  · intro q
    exact (contDiff_vectorFiniteCellPotential_joint s β t i q).continuous.measurable

theorem continuous_vectorFiniteCellTimeField_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (q : ℝ) :
    Continuous (fun z : VectorParameter n => vectorFiniteCellTimeField s β t z.1 i q z.2) := by
  have hH := continuous_vectorFiniteCell_hessian_parameter (n := n) s β t i q
  have hG := continuous_vectorFiniteCell_gradient_parameter (n := n) s β t i q
  have hTrace : Continuous (fun z : VectorParameter n =>
      vectorBilinearTrace (vectorHessian (vectorFiniteCellPotential s β t z.1 i q) z.2)) := by
    unfold vectorBilinearTrace
    apply continuous_finsetSum
    intro l _
    exact (show Continuous (fun H : Field n→L[ℝ] Field n→L[ℝ] ℝ =>
      H (EuclideanSpace.single l (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))) from by fun_prop).comp hH
  have he : (fun z : VectorParameter n => vectorFiniteCellTimeField s β t z.1 i q z.2)=
      fun z => -((1-t)*β^2)/2*(vectorBilinearTrace
        (vectorHessian (vectorFiniteCellPotential s β t z.1 i q) z.2)+
          (s.m i)*‖gradient (vectorFiniteCellPotential s β t z.1 i q) z.2‖^2) := by
    funext z
    rw [vectorFiniteCellTimeField_eq_generator,finiteGaussianGenerator_euclidean,
      vectorBilinearTrace_hessian_eq_laplacian]
  rw [he]
  exact continuous_const.mul (hTrace.add (continuous_const.mul (hG.norm.pow 2)))

theorem measurable_vectorFiniteCellTimeField_time_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (hi : i≤k+1) :
    Measurable (fun z : ℝ×VectorParameter n => vectorFiniteCellTimeField s β t z.2.1 i z.1 z.2.2) := by
  change Measurable (Function.uncurry (fun q (z : VectorParameter n) =>
    vectorFiniteCellTimeField s β t z.1 i q z.2))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro z
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellTimeField s β t z.1 i hi).comp
        (show Continuous (fun q : ℝ => (q,z.2)) from continuous_id.prodMk continuous_const)
  · intro q
    exact (continuous_vectorFiniteCellTimeField_parameter s β t i q).measurable

end QuantitativePaper
