module
public import QuantitativePaper.VectorProfileClosedRawJets
public import FourPapersCommon.RetainedExponentialInverse
public import QuantitativePaper.VectorProfileInverseBounds
public import QuantitativePaper.VectorExponentialLocalization

@[expose] public section

/-! Actual continuous inverse-Hessian values with a uniform exponential
bound on closed overlap cells, including their zero-variance endpoints. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem retainedExponentialContinuousOn_vectorProfileCellRawHessianInverse (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      Ring.inverse (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2))
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  letI : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let Q:=Icc (s₀.q i) (s₀.q (i+1))
  let V:=vectorProfileRetainedDomain n A B
  let H : ℝ→VectorProfileParameter n×Field n→Field n→L[ℝ]Field n:=fun q z=>
    hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2
  have hH : RetainedExponentialContinuousOn H Q V:=
    (retainedJetExponentialOn_vectorProfileCellRawHessian (n:=n) s₀ s₁ β t ht i hi A B hA hB).values
  have hθ (z : VectorProfileParameter n×Field n) (hz : z∈V) : z.1.1∈Icc (0:ℝ) 1:=
    ⟨(hA.trans hz.1).le,(hz.2.trans hB).le⟩
  have hUnit (q : ℝ) (hq : q∈Q) (z : VectorProfileParameter n×Field n) (hz : z∈V) : IsUnit (H q z):=by
    dsimp only [H]
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi (q,z.1) hq (hθ z hz)]
    exact vectorFieldHessian_isUnit _ β t z.1.2 (k+2) z.2
  obtain ⟨D,hD,hInv⟩:=exists_uniform_vectorProfile_inverse_bound (n:=n) hn s₀ s₁ β t (k+2) le_rfl
  let R:=2*(vectorDisorderNormConstant n β t+Real.sqrt (n:ℝ))
  have hR : 0≤R:=by
    dsimp [R]
    exact mul_nonneg (by norm_num) (add_nonneg (vectorDisorderNormConstant_nonneg n β t) (Real.sqrt_nonneg _))
  apply hH.inverse hUnit (D+1) R (by linarith) hR
  intro q hq z hz
  let θ : Paper.Overlap:=⟨z.1.1,hθ z hz⟩
  let q₀ : Paper.Overlap:=⟨q,⟨(s₀.q_nonneg (by omega)).trans hq.1,
    hq.2.trans (s₀.q_le_one (by omega))⟩⟩
  have he : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),y))=
      vectorProfileTailRecursion s₀ s₁ β t q₀ θ z.1.2 (k+2):=by
    funext y
    exact vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi q z.1.1 (hθ z hz) hq z.1.2 y
  have hh:=hInv θ q₀ z.1.2 z.2
  dsimp only [H]
  rw [he]
  apply hh.trans
  have hp : ‖z.1.2‖≤‖z‖:=(norm_snd_le z.1).trans (norm_fst_le z)
  have hx : ‖z.2‖≤‖z‖:=norm_snd_le z
  have heB:=vectorDisorderEnvelope_le_norm n β t z.1.2
  have hC:=vectorDisorderNormConstant_nonneg n β t
  apply mul_le_mul (by linarith : D≤D+1) _ (Real.exp_pos _).le (by linarith)
  apply Real.exp_le_exp.mpr
  dsimp only [R]
  nlinarith [mul_le_mul_of_nonneg_left hp hC,
    mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (n:ℝ))]

end QuantitativePaper
