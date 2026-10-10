module
public import FourPapersCommon.GenericFiniteStateCascadeBounds
public import Targets.CoupledCascadeVariance

@[expose] public section

/-! Genuine covariance-variance differentiation of a finite-state Gaussian
step. Gaussian coordinates are transported by an actual orthonormal basis;
the heat identity is obtained from the audited multidimensional Stein theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 2000000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianBasis (I : Type*) [Fintype I] :
    OrthonormalBasis (Fin (Fintype.card I)) ℝ (FiniteStateGaussianInput I) :=
  (EuclideanSpace.basisFun I ℝ).reindex (Fintype.equivFin I)

def finiteStateGaussianCoordinateField
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    (Fin (Fintype.card I) → ℝ) →L[ℝ] FiniteStateField S :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (L (finiteStateGaussianBasis I i))

@[simp] theorem finiteStateGaussianCoordinateField_apply
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (y : Fin (Fintype.card I) → ℝ) :
    finiteStateGaussianCoordinateField L y = ∑ i, y i • L (finiteStateGaussianBasis I i) := by
  simp [finiteStateGaussianCoordinateField]

@[simp] theorem finiteStateGaussianCoordinateField_single
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (i : Fin (Fintype.card I)) :
    finiteStateGaussianCoordinateField L (Pi.single i 1) = L (finiteStateGaussianBasis I i) := by
  classical
  simp [finiteStateGaussianCoordinateField_apply, Pi.single_apply]

theorem norm_finiteStateGaussianCoordinateField_le
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (y : Fin (Fintype.card I) → ℝ) :
    ‖finiteStateGaussianCoordinateField L y‖ ≤ ‖L‖*SpinGlass.Targets.l1 y := by
  rw [finiteStateGaussianCoordinateField_apply]
  calc
    _ ≤ ∑ i, ‖y i • L (finiteStateGaussianBasis I i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |y i| *‖L‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (by simpa using L.le_opNorm (finiteStateGaussianBasis I i)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

private theorem integral_gaussian_basis (g : FiniteStateGaussianInput I → ℝ)
    (hg : Measurable g) :
    (∫ z, g z ∂stdGaussian (FiniteStateGaussianInput I)) =
      ∫ y, g (∑ i, y i • finiteStateGaussianBasis I i) ∂SpinGlass.Targets.piGauss (Fintype.card I) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (finiteStateGaussianBasis I)]
  exact integral_map (Measurable.aemeasurable (by fun_prop)) hg.aestronglyMeasurable

theorem finiteStateGaussianStep_eq_coordinateStep (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F) (H : FiniteStateField S) :
    finiteStateGaussianStep a (Real.sqrt v • L) F H =
      SpinGlass.Targets.parisiStepPi (Fintype.card I) a v
        (fun y => F (H+finiteStateGaussianCoordinateField L y)) 0 := by
  have heq (y : Fin (Fintype.card I) → ℝ) :
      H+(Real.sqrt v • L) (∑ i, y i • finiteStateGaussianBasis I i) =
      H+finiteStateGaussianCoordinateField L (fun i => Real.sqrt v*y i) := by
    simp only [smul_apply, map_sum, map_smul, finiteStateGaussianCoordinateField_apply,
      smul_smul, mul_comm]
  simp only [finiteStateGaussianStep, OverlapPaper.sourceLogAverage, SpinGlass.Targets.parisiStepPi]
  split_ifs
  · rw [integral_gaussian_basis (fun z => F (H+(Real.sqrt v • L) z)) (by fun_prop)]
    congr 1
    funext y
    simp only [Pi.zero_apply, zero_add, heq]
  · rw [integral_gaussian_basis (fun z => Real.exp (a*F (H+(Real.sqrt v • L) z)))
      (by fun_prop)]
    simp only [Pi.zero_apply, zero_add, heq, div_eq_mul_inv]
    ring

def finiteStateGaussianVarianceGenerator (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  (∑ i, SpinGlass.Targets.pairedTiltMean a v
    (fun y => F (H+finiteStateGaussianCoordinateField L y))
    (fun y => fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)
      (L (finiteStateGaussianBasis I i)) (L (finiteStateGaussianBasis I i)) +
      a*(fderiv ℝ F (H+finiteStateGaussianCoordinateField L y)
        (L (finiteStateGaussianBasis I i)))^2) 0)/2

theorem hasDerivAt_finiteStateGaussianStep_variance (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B)
    (H : FiniteStateField S) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => finiteStateGaussianStep a (Real.sqrt w • L) F H)
      (finiteStateGaussianVarianceGenerator a v L F H) v := by
  classical
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  let A := fun y : Fin (Fintype.card I) → ℝ => F (H+finiteStateGaussianCoordinateField L y)
  let A' := fun i (y : Fin (Fintype.card I) → ℝ) =>
    fderiv ℝ F (H+finiteStateGaussianCoordinateField L y) (L (finiteStateGaussianBasis I i))
  let A'' := fun i (y : Fin (Fintype.card I) → ℝ) =>
    fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)
      (L (finiteStateGaussianBasis I i)) (L (finiteStateGaussianBasis I i))
  have hL (i : Fin (Fintype.card I)) : ‖L (finiteStateGaussianBasis I i)‖ ≤ ‖L‖ := by
    simpa using L.le_opNorm (finiteStateGaussianBasis I i)
  have hb (y) : |A y| ≤ |F H|+(C*‖L‖)*SpinGlass.Targets.l1 y := by
    have hs := hLip.norm_sub_le (H+finiteStateGaussianCoordinateField L y) H
    rw [add_sub_cancel_left, Real.norm_eq_abs] at hs
    change |A y-F H| ≤ C*‖finiteStateGaussianCoordinateField L y‖ at hs
    calc
      _ = |(A y-F H)+F H| := by congr 1; ring
      _ ≤ |A y-F H|+|F H| := abs_add_le _ _
      _ = |F H|+|A y-F H| := add_comm _ _
      _ ≤ |F H|+C*‖finiteStateGaussianCoordinateField L y‖ := add_le_add le_rfl hs
      _ ≤ |F H|+C*(‖L‖*SpinGlass.Targets.l1 y) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_finiteStateGaussianCoordinateField_le L y) C.2)
      _ = _ := by ring
  have hb' (i y) : |A' i y| ≤ C*‖L‖ := by
    have hh := (fderiv ℝ F (H+finiteStateGaussianCoordinateField L y)).le_opNorm (L (finiteStateGaussianBasis I i))
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul (hC _) (hL i) (norm_nonneg _) C.2)
  have hb'' (i y) : |A'' i y| ≤ B*‖L‖^2 := by
    have h1 := (fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)).le_opNorm
      (L (finiteStateGaussianBasis I i))
    have h2 := (fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)
      (L (finiteStateGaussianBasis I i))).le_opNorm (L (finiteStateGaussianBasis I i))
    rw [Real.norm_eq_abs] at h2
    have h3 := mul_le_mul (hB (H+finiteStateGaussianCoordinateField L y)) (hL i) (norm_nonneg _) B.2
    have h4 := mul_le_mul (h1.trans h3) (hL i) (norm_nonneg _) (mul_nonneg B.2 (norm_nonneg _))
    exact h2.trans (by nlinarith [h4])
  have hline (x z : Fin (Fintype.card I) → ℝ) (r : ℝ) :
      HasDerivAt (fun b => A (x+b • z)) (∑ i, z i*A' i (x+r • z)) r := by
    have hs : HasDerivAt (fun b => H+finiteStateGaussianCoordinateField L (x+b • z))
        (finiteStateGaussianCoordinateField L z) r := by
      simpa only [map_add, map_smul, one_smul, id_eq, add_assoc] using
        (((hasDerivAt_id r).smul_const (finiteStateGaussianCoordinateField L z)).const_add
          (H+finiteStateGaussianCoordinateField L x))
    have hd := hF1.differentiable_one.differentiableAt.hasFDerivAt.comp_hasDerivAt r hs
    convert hd using 1
    · rfl
    · simp only [A', finiteStateGaussianCoordinateField_apply, map_sum, map_smul,
        smul_eq_mul]
  have hsecond (i : Fin (Fintype.card I)) (y : Fin (Fintype.card I) → ℝ) (r : ℝ) :
      HasDerivAt (fun b => A' i (y+b • Pi.single i 1)) (A'' i (y+r • Pi.single i 1)) r := by
    have hs : HasDerivAt (fun b => H+finiteStateGaussianCoordinateField L (y+b • Pi.single i 1))
        (L (finiteStateGaussianBasis I i)) r := by
      simpa only [map_add, map_smul, finiteStateGaussianCoordinateField_single, one_smul, id_eq, add_assoc] using
        (((hasDerivAt_id r).smul_const (L (finiteStateGaussianBasis I i))).const_add
          (H+finiteStateGaussianCoordinateField L y))
    have hd := (hD.differentiable_one.differentiableAt.hasFDerivAt.clm_apply
      (hasFDerivAt_const (L (finiteStateGaussianBasis I i))
        (H+finiteStateGaussianCoordinateField L (y+r • Pi.single i 1)))).comp_hasDerivAt r hs
    convert hd using 1
    · rfl
    · simp only [A'', add_apply, ContinuousLinearMap.comp_apply, zero_apply,
        ContinuousLinearMap.flip_apply, map_zero, zero_add]
  have hh := SpinGlass.Targets.hasDerivAt_parisiStepPi_variance
    (A := A) (A' := A') (A'' := A'')
    (C := |F H|) (D := (C : ℝ)*‖L‖) (B := (C : ℝ)*‖L‖) (H := (B : ℝ)*‖L‖^2)
    (by positivity) (by positivity)
    (hF.continuous.comp (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).measurable
    (fun i => (((hD.continuous.comp (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).clm_apply
      continuous_const)).measurable)
    (fun i => (((hD.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).clm_apply
        continuous_const |>.clm_apply continuous_const).measurable)
    hb hb' hb'' hline hsecond a 0 hv
  have heq : (fun w => finiteStateGaussianStep a (Real.sqrt w • L) F H) =
      (fun w => SpinGlass.Targets.parisiStepPi (Fintype.card I) a w A 0) :=
    funext fun w => finiteStateGaussianStep_eq_coordinateStep a w L F hF.continuous.measurable H
  rw [heq]
  exact hh

theorem hasDerivAt_finiteStateGaussianTerminalCascade_outer_variance [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (mass : ℝ)
    (M : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) {v : ℝ} (hv : 0 < v) :
    HasDerivAt
      (fun w => finiteStateGaussianStep mass (Real.sqrt w • M)
        (finiteStateGaussianTerminalCascade V a L j) H)
      (finiteStateGaussianVarianceGenerator mass v M
        (finiteStateGaussianTerminalCascade V a L j) H) v :=
  hasDerivAt_finiteStateGaussianStep_variance mass M _
    (contDiff_two_finiteStateGaussianTerminalCascade V a ha L j) 1
    (finiteStateCascadeHessianBound a j)
    (fun _ => norm_fderiv_le_of_lipschitz ℝ
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L j))
    (finiteStateGaussianTerminalCascade_C2_bounds V a ha L j).2 H hv

end FourPapersCommon
