module
public import QuantitativeFollowup.FollowupCavityPathSelectedFields

@[expose] public section

/-! Contraction of the genuine selected-edge score against its actual
shared-path covariance. It retains arbitrary branch locations and repeats. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

private theorem basisFun_eq_single {A : Type} [Fintype A] [DecidableEq A] (e : A) :
    EuclideanSpace.basisFun A ℝ e=EuclideanSpace.single e 1 := by
  ext d
  simp [EuclideanSpace.basisFun_apply,PiLp.single_apply]

theorem finiteCascadeCommonPathDepth_self {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v : FiniteCascadeRecordVertex T) : finiteCascadeCommonPathDepth T v v=v.depth := by
  induction v with
  | root T => cases T <;> rfl
  | child v ih => exact ih
  | left v ih => exact ih
  | right v ih => exact ih

def cavityPathSharedClockGram (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) : ℝ :=
  ((cavityPathSignedMarks D s a i T σ b y).map (fun c=>
    ((cavityPathSignedMarks D s a i T σ b y).map (fun d=>
      c.1*d.1*(cavityPhysicalCommonOverlap s T c.2 d.2-s.q (k+2-j)))).sum)).sum

theorem cavityPathSpatialScore_selected_trace_clock (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) :
    (∑e,if cavitySelectedRootPathMask i T e then
      (cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2 else 0)=
      cavityPathSharedClockGram D s a i T σ b y := by
  classical
  have he : (∑e,if cavitySelectedRootPathMask i T e then
      (cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2 else 0)=
      ∑e : GaussianCoordinateIndex (Fin n) T,
        ((cavityPathSignedMarks D s a i T σ b y).map (fun c=>
          c.1*finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e)).sum^2 := by
    simp only [cavitySelectedRootPathMask,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Bool.false_eq_true,ite_false,Finset.sum_const_zero,zero_add]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hm : cavitySelectedEdgeMask i T e=true
    · simp only [if_pos hm]
      rw [basisFun_eq_single,cavityPathSpatialScore_selected_single D s a i T σ b y e hm]
    · simp only [if_neg hm]
      have hz : cavitySelectedEdgeMask i T e=false:=Bool.eq_false_iff.mpr hm
      simp_rw [finiteCascadePathCoefficient_eq_zero_of_unselected s i T _ e hz]
      simp
  rw [he,finite_weighted_gram_contraction]
  unfold cavityPathSharedClockGram
  simp_rw [cavityPhysicalPath_covariance_clock]

def cavityPathVertexBinaryHessian (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (y : CavityPathGaussianSpace T n)
    (v : FiniteCascadeRecordVertex T) : ℝ :=
  fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth))
      (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i) (cavityCoordinateFeature i)

theorem cavityPathSpatialSecondCharge_selected_trace_clock (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (y : CavityPathGaussianSpace T n) :
    (∑e,if cavitySelectedRootPathMask i T e then
      cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e) else 0)=
      ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
        c.1*(s.q (k+2-c.2.depth)-s.q (k+2-j))*cavityPathVertexBinaryHessian D s i T b y c.2)).sum := by
  classical
  have he : (∑e,if cavitySelectedRootPathMask i T e then
      cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e) else 0)=
      ∑e : GaussianCoordinateIndex (Fin n) T,
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
          c.1*(finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e)^2*
            cavityPathVertexBinaryHessian D s i T b y c.2)).sum := by
    simp only [cavitySelectedRootPathMask,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Bool.false_eq_true,ite_false,Finset.sum_const_zero,zero_add]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hm : cavitySelectedEdgeMask i T e=true
    · simp only [if_pos hm]
      rw [basisFun_eq_single]
      unfold cavityPathSpatialSecondCharge chargedDirectionalCurvature exponentialDensityHessian
      simp_rw [cavityPathVertexField_selected_single D s i T _ e hm]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      apply congrArg List.sum
      apply List.map_congr_left
      intro c _
      unfold cavityPathVertexBinaryHessian
      ring
    · simp only [if_neg hm]
      have hz : cavitySelectedEdgeMask i T e=false:=Bool.eq_false_iff.mpr hm
      simp_rw [finiteCascadePathCoefficient_eq_zero_of_unselected s i T _ e hz]
      simp
  rw [he,finset_sum_list_map_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  have hh : (∑e : GaussianCoordinateIndex (Fin n) T,
      (finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e)^2)=
      s.q (k+2-c.2.depth)-s.q (k+2-j):=by
    simp_rw [pow_two]
    rw [cavityPhysicalPath_covariance_clock]
    unfold cavityPhysicalCommonOverlap
    rw [finiteCascadeCommonPathDepth_self]
  calc
    _=c.1*(∑e : GaussianCoordinateIndex (Fin n) T,
        (finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e)^2)*
          cavityPathVertexBinaryHessian D s i T b y c.2:=by
      rw [Finset.mul_sum,Finset.sum_mul]
    _=_:=by rw [hh]

theorem cavityPathScoreGenerator_eq_shared_clock (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) :
    cavityPathScoreGenerator D s a i T σ b y=
      -cavityPathParameterCharge D s a i T b y+(1/2:ℝ)*
        (cavityPathSharedClockGram D s a i T σ b y-
          ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
            c.1*(s.q (k+2-c.2.depth)-s.q (k+2-j))*cavityPathVertexBinaryHessian D s i T b y c.2)).sum) := by
  unfold cavityPathScoreGenerator
  have he (e : AnisotropicCouplingIndex n⊕GaussianCoordinateIndex (Fin n) T) :
      (if cavitySelectedRootPathMask i T e then
        (cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2-
          cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e) else 0)=
        (if cavitySelectedRootPathMask i T e then
          (cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.basisFun _ ℝ e))^2 else 0)-
            (if cavitySelectedRootPathMask i T e then
              cavityPathSpatialSecondCharge D s a i T b y (EuclideanSpace.basisFun _ ℝ e) else 0):=by
    split <;> simp_all only [sub_zero]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,cavityPathSpatialScore_selected_trace_clock,
    cavityPathSpatialSecondCharge_selected_trace_clock]

end QuantitativeFollowup
