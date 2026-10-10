module
public import QuantitativeFollowup.FollowupCavityInterpolationHeat
public import QuantitativeFollowup.FollowupCavityRootScore

@[expose] public section

/-! Actual simultaneous root/path score. Its root curvature is the true
recorded terminal-feature response; its path term retains every shared
Gaussian edge and the literal node-variance derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityInterpolationRecordScore (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (alpha b : ℝ) (r : CavityPathRecordSpace T n) : ℝ:=
  (1/2:ℝ)*(∑e,if p e then (D.coupling e)^2*cavityPathRecordFeatureCurvature D s a i T b e r else 0)-
    alpha*cavityPathRecordScore D s a i T b r

theorem cavityInterpolation_root_hessian_trace (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) :
    (∑e,if cavityRootCouplingMask p T e then
      fderiv ℝ (fderiv ℝ (fun z=>cavityPathNumerator D s a i T σ (b,z))) y
        (EuclideanSpace.basisFun _ ℝ e) (EuclideanSpace.basisFun _ ℝ e) else 0)=
    cavityPathNumerator D s a i T σ (b,y)*
      (∑e,if p e then (D.coupling e)^2*cavityPathRecordFeatureCurvature D s a i T b e
        (cavityPathFixedRecord D s i T σ y) else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [cavityRootCouplingMask,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,
    Finset.sum_const_zero,add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:p e=true
  · simp only [ite_eq_left he]
    simpa only [EuclideanSpace.basisFun_apply,mul_assoc] using
      cavityPath_root_hessian_recorded_curvature D s a i T σ b y e
  · simp only [ite_eq_right he,mul_zero]

theorem cavityPathRecordScore_fixed_record (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) :
    cavityPathRecordScore D s a i T b (cavityPathFixedRecord D s i T σ y)=
      cavityPathScoreGenerator D s a i T σ b y := by
  have hsp:=finiteCascadeRecordTerminalSpins_referenceRoot
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T (anisotropicRootEnergyMap D) 0 y σ
  change finiteCascadeRecordTerminalSpins T (cavityPathFixedRecord D s i T σ y).2=σ at hsp
  have hmean (v : FiniteCascadeRecordVertex T) :
      cavityPathRecordMean D s i T b v (cavityPathFixedRecord D s i T σ y)=
        cavityPathSelectedVertexMean D s i T b y v := by
    unfold cavityPathRecordMean cavityPathSelectedVertexMean
    rw [cavityPathVertexField_eq_fixed_record]
  have hH (v : FiniteCascadeRecordVertex T) :
      cavityPathRecordHessian D s i T b v (cavityPathFixedRecord D s i T σ y)=
        cavityPathVertexBinaryHessian D s i T b y v := by
    unfold cavityPathRecordHessian cavityPathVertexBinaryHessian
    rw [cavityPathVertexField_eq_fixed_record]
  have hB (v : FiniteCascadeRecordVertex T) :
      cavityPathRecordParameter D s i T b v (cavityPathFixedRecord D s i T σ y)=
        cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth
          (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i) := by
    unfold cavityPathRecordParameter
    rw [cavityPathVertexField_eq_fixed_record]
  rw [cavityPathScoreGenerator_eq_shared_clock]
  unfold cavityPathRecordScore cavityPathRecordClockGram cavityPathRecordSignedMarks
    cavityPathSharedClockGram cavityPathSignedMarks cavityPathParameterCharge
  simp_rw [hsp,hmean,hH,hB]

theorem cavityInterpolationHeatGenerator_eq_record_score (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (alpha b : ℝ) (hb : 0<b)
    (y : CavityPathGaussianSpace T n) :
    cavityInterpolationHeatGenerator D p s a i T σ alpha b y=
      cavityPathNumerator D s a i T σ (b,y)*cavityInterpolationRecordScore D p s a i T alpha b
        (cavityPathFixedRecord D s i T σ y) := by
  have hpath:=cavityPathHeatGenerator_eq_score D s a i T hj σ b hb y
  have hrec:=cavityPathRecordScore_fixed_record D s a i T σ b y
  unfold cavityInterpolationHeatGenerator cavityInterpolationRecordScore
  rw [cavityInterpolation_root_hessian_trace,hrec]
  unfold cavityPathHeatGenerator at hpath
  linear_combination -alpha*hpath

theorem hasDerivAt_cavityInterpolationSpinWeight_record_score (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (d alpha u : ℝ)
    (ha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    HasDerivAt (fun q=>cavityInterpolationSpinWeight D p s a i T σ q (d-alpha*q))
      (∫z : CavityPathGaussianSpace T n,
        cavityPathNumerator D s a i T σ
          (d-alpha*u,cavityInterpolationGaussianScale p i T u (d-alpha*u) z)*
        cavityInterpolationRecordScore D p s a i T alpha (d-alpha*u)
          (cavityPathFixedRecord D s i T σ
            (cavityInterpolationGaussianScale p i T u (d-alpha*u) z))
          ∂stdGaussian (CavityPathGaussianSpace T n)) u := by
  simpa only [cavityInterpolationHeatGenerator_eq_record_score D p s a i T hj σ alpha (d-alpha*u) hb]
    using hasDerivAt_cavityInterpolationSpinWeight D p s a i T hj σ d alpha u ha hu hb

end QuantitativeFollowup
