module
public import QuantitativeFollowup.FollowupCavityPathVarianceCoordinates
public import FourPapersCommon.FiniteCascadeTreeVertexLinear

@[expose] public section

/-! The actual physical grid supplies the common-path Gaussian clock. No
clock or covariance equality is assumed, including at repeated nodes. -/
noncomputable section
open scoped BigOperators
open FourPapersCommon FiniteTerminalGenealogy QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def cavityPhysicalEdgeCoefficient (s : RSBScheme k) (j : ℕ) : ℝ :=
  Real.sqrt (s.q (k+2-j)-s.q (k+1-j))

def cavityPhysicalCommonOverlap (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) : ℝ :=
  s.q (k+2-finiteCascadeCommonPathDepth T v w)

theorem cavityPhysicalEdgeCoefficient_square (s : RSBScheme k) (j : ℕ) :
    cavityPhysicalEdgeCoefficient s j ^ 2 = s.q (k+2-j)-s.q (k+2-(j+1)) := by
  rw [show k+2-(j+1)=k+1-j by omega]
  exact Real.sq_sqrt (cavityCellVariance_nonneg s j)

theorem cavityPhysicalPath_covariance_clock (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    (∑e : GaussianCoordinateIndex (Fin n) T,
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e *
        finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i w e) =
      cavityPhysicalCommonOverlap s T v w-s.q (k+2-j) := by
  rw [finiteCascadePathCoefficient_covariance]
  exact finiteCascadeCommonPathQuadratic_eq_clock _ (fun p => s.q (k+2-p))
    (cavityPhysicalEdgeCoefficient_square s) T v w

theorem cavityPhysicalPath_covariance_clock_zero_root (s : RSBScheme k)
    (hq : s.q 1=0) (i : Fin n) (T : FiniteTerminalGenealogy (k+1))
    (v w : FiniteCascadeRecordVertex T) :
    (∑e : GaussianCoordinateIndex (Fin n) T,
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e *
        finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i w e) =
      cavityPhysicalCommonOverlap s T v w := by
  rw [cavityPhysicalPath_covariance_clock]
  simp [hq]

def cavitySelectedPathMask (i : Fin n) (l : Fin n) : ℝ := if l=i then 1 else 0

theorem cavityPhysicalInput_selected (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) :
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s j).comp
      (finiteGaussianDiagonal (cavitySelectedPathMask i)) =
        cavityPhysicalEdgeCoefficient s j • (EuclideanSpace.proj i).smulRight (cavityCoordinateFeature i) := by
  apply finiteStateCLM_eq_of_single
  intro l
  rw [ContinuousLinearMap.comp_apply,finiteGaussianDiagonal_single,map_smul]
  ext σ
  simp only [PiLp.smul_apply,smul_eq_mul,cavityFiniteEnergyInput_single,
    smul_apply,ContinuousLinearMap.smulRight_apply]
  rw [anisotropicReplaceVariance_variance D i l 1 (by norm_num)]
  by_cases hl : l=i
  · simp [cavitySelectedPathMask,hl,cavityPhysicalEdgeCoefficient,cavityCoordinateFeature_apply]
  · simp [cavitySelectedPathMask,hl,Ne.symm hl]

def cavitySelectedPathFieldCLM (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    FiniteStateGaussianInput (GaussianCoordinateIndex (Fin n) T) →L[ℝ]
      FiniteStateField (Configuration n) :=
  (finiteCascadeRecordVertexCLM (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T v).comp
    ((0 : FiniteStateGaussianInput (GaussianCoordinateIndex (Fin n) T) →L[ℝ]
      FiniteStateField (Configuration n)).prod
      (finiteGaussianDiagonal (finiteCascadeEdgeMultiplier (cavitySelectedPathMask i) T)))

theorem cavitySelectedPathFieldCLM_apply (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (z : FiniteStateGaussianInput (GaussianCoordinateIndex (Fin n) T)) :
    cavitySelectedPathFieldCLM D s i T v z =
      (∑e : GaussianCoordinateIndex (Fin n) T,
        finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e*z e) •
          cavityCoordinateFeature i := by
  change finiteCascadeRecordVertexCLM _ T v
    (0,finiteGaussianDiagonal (finiteCascadeEdgeMultiplier (cavitySelectedPathMask i) T) z)=_
  rw [←finiteCascadeRecordVertexCLM_coordinate_scaling]
  have he : (fun p => (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s p).comp
      (finiteGaussianDiagonal (cavitySelectedPathMask i))) =
    fun p => cavityPhysicalEdgeCoefficient s p • (EuclideanSpace.proj i).smulRight (cavityCoordinateFeature i) := by
    funext p
    exact cavityPhysicalInput_selected D s i p
  rw [he]
  simpa using finiteCascadeRecordVertexCLM_rank_one (cavityPhysicalEdgeCoefficient s) i
    (cavityCoordinateFeature i) T v 0 z

theorem cavitySelectedPathFieldCLM_single (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (GaussianCoordinateIndex (Fin n) T)] (v : FiniteCascadeRecordVertex T)
    (e : GaussianCoordinateIndex (Fin n) T) :
    cavitySelectedPathFieldCLM D s i T v (EuclideanSpace.single e 1) =
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e • cavityCoordinateFeature i := by
  classical
  rw [cavitySelectedPathFieldCLM_apply]
  simp

theorem cavitySelectedPathField_spectral_clock (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (GaussianCoordinateIndex (Fin n) T)]
    (v w : FiniteCascadeRecordVertex T) (σ τ : Configuration n) :
    (∑e : GaussianCoordinateIndex (Fin n) T,
      cavitySelectedPathFieldCLM D s i T v (EuclideanSpace.single e 1) σ *
        cavitySelectedPathFieldCLM D s i T w (EuclideanSpace.single e 1) τ) =
      (cavityPhysicalCommonOverlap s T v w-s.q (k+2-j))*Paper.spinSign (σ i)*Paper.spinSign (τ i) := by
  classical
  simp_rw [cavitySelectedPathFieldCLM_single,PiLp.smul_apply,smul_eq_mul,cavityCoordinateFeature_apply]
  calc
    _ = (∑e : GaussianCoordinateIndex (Fin n) T,
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e *
        finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i w e)*
          Paper.spinSign (σ i)*Paper.spinSign (τ i) := by
        rw [Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        ring
    _ = _ := by rw [cavityPhysicalPath_covariance_clock]

end QuantitativeFollowup
