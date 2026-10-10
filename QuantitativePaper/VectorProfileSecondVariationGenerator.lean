module
public import QuantitativePaper.VectorProfileCellVariations
public import QuantitativePaper.ResponseGeneratorAlgebra
public import FourPapersCommon.EuclideanOperatorTrace
public import FourPapersCommon.AffineSecondDerivative

@[expose] public section

/-! The actual finite-profile second Legendre variation satisfies the
literal magnetization generator equation on every strict cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileCellHessianMatrix (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Matrix (Fin n) (Fin n) ℝ:=
  euclideanOperatorMatrix (vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)

def vectorProfileCellBMatrix (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Matrix (Fin n) (Fin n) ℝ:=
  euclideanOperatorMatrix (vectorProfileCellB s₀ s₁ β t i a m)

def vectorProfileCellZMatrix (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Matrix (Fin n) (Fin n) ℝ:=
  euclideanOperatorMatrix (hessianOperator (vectorProfileCellSecondVariation s₀ s₁ β t i a) m)

theorem vectorProfileCellHessianMatrix_symmetric (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (i : ℕ) (a : VectorProfileCellParameter n)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    (vectorProfileCellHessianMatrix s₀ s₁ β t i a m).IsSymm := by
  unfold vectorProfileCellHessianMatrix
  rw [vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ i a m hm,euclideanOperatorMatrix_smul]
  have hs:=euclideanOperatorMatrix_hessian_symmetric
    (vectorRecursion (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1)
      β t a.2.2 (k+2)) (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))
    (((contDiff_vectorRecursion_joint _ β t (k+2)).contDiffAt.comp _
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num))
  change (β • euclideanOperatorMatrix (hessianOperator _ _)).IsSymm
  rw [Matrix.IsSymm,Matrix.transpose_smul,hs.eq]

theorem vectorProfileCellSecondVariation_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun r=>vectorProfileCellSecondVariation s₀ s₁ β t i (r,a.2) m) a.1=
      (1-t)/2*euclideanOperatorTrace
        (deriv (deriv (fun θ=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (a.1,θ,a.2.2) m)) a.2.1) := by
  let H : ℝ→(Field n→L[ℝ]Field n):=
    fun θ=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (a.1,θ,a.2.2) m
  have hH : ContDiffAt ℝ ∞ H a.2.1:=ContDiffAt.comp
    (f := fun θ : ℝ=>((θ,a.2.2),m))
    (g := fun z : VectorProfileParameter n×Field n=>vectorProfilePhysicalHessian
      s₀ s₁ β t (vectorProfileCellOverlap a.1) (k+2) z.1.1 z.1.2 z.2) a.2.1
    (contDiffAt_vectorProfilePhysicalHessian_joint s₀ s₁ β t hβ ht.le
      (vectorProfileCellOverlap a.1) (k+2) le_rfl (a.2.1,a.2.2) hθ m hm) (by fun_prop)
  have hf : ContDiffAt ℝ ∞ (fun θ=>euclideanOperatorTrace (H θ)) a.2.1:=
    ContDiffAt.comp (f := H) (g := euclideanOperatorTraceCLM (n:=n)) a.2.1
      euclideanOperatorTraceCLM.contDiff.contDiffAt hH
  let R : ℝ→ℝ:=fun θ=>(1-t)/2*euclideanOperatorTrace (H θ)+
    (1-t)*(β*vectorProfileMass s₀ s₁ θ i)/2*‖m‖^2
  have he : (fun θ=>deriv (fun r=>vectorProfileCellEnergyLegendrePotential
      s₀ s₁ β t i ((r,θ,a.2.2),m)) a.1)=ᶠ[𝓝 a.2.1]R:=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    exact (hasDerivAt_vectorProfileCellEnergyLegendrePotential_time s₀ s₁ β t hβ ht i hi
      (a.1,θ,a.2.2) hq hθ' m hm).deriv
  rw [vectorProfileCellSecondVariation_time_commute s₀ s₁ β t hβ ht i hi a hq hθ m hm,
    he.deriv.deriv_eq]
  have hR : R=(fun θ=>(1-t)/2*euclideanOperatorTrace (H θ)+
      ((1-t)*β/2*(s₁.m i-s₀.m i)*‖m‖^2)*θ+
      (1-t)*β/2*s₀.m i*‖m‖^2):=by
    funext θ
    unfold R vectorProfileMass
    ring
  rw [hR,deriv_deriv_affine_add _ _ _ _ _ hf,deriv_deriv_euclideanOperatorTrace H a.2.1 hH]

theorem vectorProfileCellSecondVariation_generator (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun r=>vectorProfileCellSecondVariation s₀ s₁ β t i (r,a.2) m) a.1+
      (1-t)/2*responseMatrixPair
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (vectorProfileCellZMatrix s₀ s₁ β t i a m)=
      (1-t)*Matrix.trace
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellBMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellBMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m) := by
  let h:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
  let B:=vectorProfileCellBMatrix s₀ s₁ β t i a m
  let Z:=vectorProfileCellZMatrix s₀ s₁ β t i a m
  let H2:=deriv (deriv (fun θ=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (a.1,θ,a.2.2) m)) a.2.1
  have hSecond : euclideanOperatorMatrix H2=(2 : ℝ) • (h*B*h*B*h)-h*Z*h:=by
    have he:=(hasDerivAt_deriv_vectorProfileCellPhysicalHessian_profile s₀ s₁ β t hβ ht i a hθ m hm).deriv
    change H2=_ at he
    rw [he,euclideanOperatorMatrix_sub,euclideanOperatorMatrix_smul]
    simp only [euclideanOperatorMatrix_mul]
    rfl
  exact response_generator_second_variation h B Z (euclideanOperatorMatrix H2) (1-t) _
    (vectorProfileCellHessianMatrix_symmetric s₀ s₁ β t hβ i a m hm) hSecond
    (vectorProfileCellSecondVariation_time s₀ s₁ β t hβ ht i hi a hq hθ m hm)

end QuantitativePaper
