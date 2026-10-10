module
public import QuantitativePaper.VectorProfileRawExponentialSmooth
public import QuantitativePaper.VectorProfileInverseBounds
public import QuantitativePaper.VectorExponentialLocalization

@[expose] public section

/-! Actual raw Hessian inversion has exponential bounds for all spatial
and parameter jets, from proved coercivity and genuine inversion calculus. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem exponentialSmoothOn_vectorProfileCellRawHessianInverse (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hl : s₀.q i≤l) (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      Ring.inverse (hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (z.1,y)) z.2))
      (vectorProfileJointCylinder l u a b) := by
  letI : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let U:=vectorProfileJointCylinder (n:=n) l u a b
  let H : (VectorProfileCellParameter n×Field n)→(Field n→L[ℝ]Field n):=
    fun z=>hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (z.1,y)) z.2
  have hU:=isOpen_vectorProfileJointCylinder (n:=n) l u a b
  have hH : ExponentialSmoothOn H U:=
    (exponentialSmoothOn_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi l u a b hu ha hb).partialHessian hU
  have hq (z : VectorProfileCellParameter n×Field n) (hz : z∈U) :
      z.1.1∈Icc (s₀.q i) (s₀.q (i+1)):=⟨hl.trans hz.1.1.le,hz.1.2.trans hu |>.le⟩
  have hq01 (z : VectorProfileCellParameter n×Field n) (hz : z∈U) : z.1.1∈Icc (0:ℝ) 1:=
    ⟨(s₀.q_nonneg (by omega)).trans (hq z hz).1,
      (hq z hz).2.trans (s₀.q_le_one (by omega))⟩
  have hθ (z : VectorProfileCellParameter n×Field n) (hz : z∈U) : z.1.2.1∈Icc (0:ℝ) 1:=
    ⟨(ha.trans hz.2.1).le,(hz.2.2.trans hb).le⟩
  have hUnit (z : VectorProfileCellParameter n×Field n) (hz : z∈U) : IsUnit (H z):=by
    dsimp only [H]
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi z.1 (hq z hz) (hθ z hz)]
    exact vectorFieldHessian_isUnit _ β t z.1.2.2 (k+2) z.2
  obtain ⟨D,hD,hInv⟩:=exists_uniform_vectorProfile_inverse_bound (n:=n) hn s₀ s₁ β t (k+2) le_rfl
  let R:=2*(vectorDisorderNormConstant n β t+Real.sqrt (n:ℝ))
  have hR : 0≤R:=by
    dsimp [R]
    exact mul_nonneg (by norm_num) (add_nonneg (vectorDisorderNormConstant_nonneg n β t) (Real.sqrt_nonneg _))
  have hInvBound (z : VectorProfileCellParameter n×Field n) (hz : z∈U) :
      ‖Ring.inverse (H z)‖≤(D+1)*Real.exp (R*‖z‖) := by
    let θ : Paper.Overlap:=⟨z.1.2.1,hθ z hz⟩
    let q : Paper.Overlap:=⟨z.1.1,hq01 z hz⟩
    have he : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (z.1,y))=
        vectorProfileTailRecursion s₀ s₁ β t q θ z.1.2.2 (k+2):=by
      funext y
      exact vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi z.1.1 z.1.2.1 (hθ z hz)
        (hq z hz) z.1.2.2 y
    have hh:=hInv θ q z.1.2.2 z.2
    dsimp only [H]
    rw [he]
    apply hh.trans
    have hp : ‖z.1.2.2‖≤‖z‖:=
      (norm_snd_le z.1.2).trans ((norm_snd_le z.1).trans (norm_fst_le z))
    have hx : ‖z.2‖≤‖z‖:=norm_snd_le z
    have heB:=vectorDisorderEnvelope_le_norm n β t z.1.2.2
    have hB:=vectorDisorderNormConstant_nonneg n β t
    apply mul_le_mul (by linarith : D≤D+1) _ (Real.exp_pos _).le (by linarith)
    apply Real.exp_le_exp.mpr
    dsimp only [R]
    nlinarith [mul_le_mul_of_nonneg_left hp hB,
      mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (n:ℝ))]
  exact hH.inverse hUnit (D+1) R (by linarith) hR hInvBound

end QuantitativePaper
