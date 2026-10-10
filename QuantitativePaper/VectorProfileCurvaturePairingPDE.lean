module
public import QuantitativePaper.VectorProfileTraceReaction

@[expose] public section

/-! Actual first profile variation and its Hessian time equation. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileCellCurvaturePairing (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : ℝ:=
  Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
    vectorProfileCellHessianMatrix s₀ s₁ β t i a m*vectorProfileCellBMatrix s₀ s₁ β t i a m)

theorem contDiffAt_vectorProfileCellFirstVariation (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellFirstVariation s₀ s₁ β t i z.1 z.2) (a,m) := by
  let U : ℝ×(ℝ×((Couplings n×ℝ)×Field n))→ℝ:=fun z=>
    vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i
      ((z.2.1,z.1,z.2.2.1),z.2.2.2)
  let z₀ : ℝ×(ℝ×((Couplings n×ℝ)×Field n)) := (a.2.1,a.1,a.2.2,m)
  have hU : ContDiffAt ℝ ∞ U z₀:=ContDiffAt.comp
    (f := fun z : ℝ×(ℝ×((Couplings n×ℝ)×Field n))=>((z.2.1,z.1,z.2.2.1),z.2.2.2))
    (g := vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i) z₀
    (contDiffAt_vectorProfileCellEnergyLegendrePotential s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (by fun_prop)
  have hD:=contDiffAt_partialParamDerivative (1 : ℝ) U z₀ hU
  have hh:=ContDiffAt.comp
    (f := fun z : VectorProfileCellParameter n×Field n=>(z.1.2.1,z.1.1,z.1.2.2,z.2))
    (g := partialParamDerivative (1 : ℝ) U) (a,m) hD (by fun_prop)
  simpa only [Function.comp_def,partialParamDerivative,fderiv_apply_one_eq_deriv,U,
    vectorProfileCellFirstVariation] using hh

theorem vectorProfileCellFirstVariation_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun q=>vectorProfileCellFirstVariation s₀ s₁ β t i (q,a.2) m) a.1=
      -(1-t)/2*vectorProfileCellCurvaturePairing s₀ s₁ β t i a m+
        (1-t)*(β*(s₁.m i-s₀.m i))/2*‖m‖^2 := by
  let U : ℝ×ℝ→ℝ:=fun z=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i
    ((z.1,z.2,a.2.2),m)
  have hU : ContDiffAt ℝ ∞ U (a.1,a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×ℝ=>((z.1,z.2,a.2.2),m))
    (g := vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i) (a.1,a.2.1)
    (contDiffAt_vectorProfileCellEnergyLegendrePotential s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (by fun_prop)
  rw [show deriv (fun q=>vectorProfileCellFirstVariation s₀ s₁ β t i (q,a.2) m) a.1=
    deriv (fun θ=>deriv (fun q=>U (q,θ)) a.1) a.2.1 from
      deriv_real_parameters_commute U a.1 a.2.1 hU]
  let H : ℝ→Field n→L[ℝ]Field n:=
    fun θ=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (a.1,θ,a.2.2) m
  have hH:=hasDerivAt_vectorProfileCellPhysicalHessian_profile s₀ s₁ β t hβ ht i a hθ m hm
  have hT:=hasDerivAt_euclideanOperatorTrace hH
  have hMass : HasDerivAt (fun θ=>vectorProfileMass s₀ s₁ θ i) (s₁.m i-s₀.m i) a.2.1:=by
    convert ((hasDerivAt_id a.2.1).const_mul (s₁.m i-s₀.m i)).add_const (s₀.m i) using 1
    · funext θ
      unfold vectorProfileMass
      simp only [id_eq]
      ring
    · ring
  let R : ℝ→ℝ:=fun θ=>(1-t)/2*euclideanOperatorTrace (H θ)+
    (1-t)*(β*vectorProfileMass s₀ s₁ θ i)/2*‖m‖^2
  have hR : HasDerivAt R
      ((1-t)/2*euclideanOperatorTrace
        (-(vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)*
          vectorProfileCellB s₀ s₁ β t i a m*vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)+
        (1-t)*(β*(s₁.m i-s₀.m i))/2*‖m‖^2) a.2.1:=by
    convert ((hT.const_mul ((1-t)/2)).add
      ((((hMass.const_mul β).const_mul (1-t)).div_const 2).mul_const (‖m‖^2))) using 1 <;> rfl
  have he : (fun θ=>deriv (fun q=>U (q,θ)) a.1)=ᶠ[𝓝 a.2.1]R:=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    exact (hasDerivAt_vectorProfileCellEnergyLegendrePotential_time s₀ s₁ β t hβ ht i hi
      (a.1,θ,a.2.2) hq hθ' m hm).deriv
  rw [he.deriv_eq,hR.deriv]
  have hCycle : euclideanOperatorTrace
      (-(vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)*
        vectorProfileCellB s₀ s₁ β t i a m*vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)=
      -vectorProfileCellCurvaturePairing s₀ s₁ β t i a m:=by
    unfold euclideanOperatorTrace vectorProfileCellCurvaturePairing
    simp only [euclideanOperatorMatrix_mul,euclideanOperatorMatrix_neg,Matrix.neg_mul,
      Matrix.trace_neg]
    congr 1
    change Matrix.trace
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellBMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m)=
      Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
        vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
        vectorProfileCellBMatrix s₀ s₁ β t i a m)
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_cycle' (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (vectorProfileCellBMatrix s₀ s₁ β t i a m) (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
  rw [hCycle]
  ring

theorem contDiffAt_vectorProfileCellB (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellB s₀ s₁ β t i z.1 z.2) (a,m) :=
  contDiffAt_partial_hessian _ (a,m)
    (contDiffAt_vectorProfileCellFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ m hm)

theorem contDiffAt_vectorProfileCellCurvaturePairing (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellCurvaturePairing s₀ s₁ β t i z.1 z.2) (a,m) := by
  have hH:=contDiffAt_vectorProfileCellPhysicalHessian s₀ s₁ β t hβ ht i hi a hq hθ m hm
  have hB:=contDiffAt_vectorProfileCellB s₀ s₁ β t hβ ht i hi a hq hθ m hm
  have hh:=ContDiffAt.comp (f := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2*vectorProfileCellB s₀ s₁ β t i z.1 z.2)
    (g := euclideanOperatorTraceCLM (n:=n)) (a,m)
    euclideanOperatorTraceCLM.contDiff.contDiffAt ((hH.mul hH).mul hB)
  have he : (fun z : VectorProfileCellParameter n×Field n=>
      euclideanOperatorTraceCLM (vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2*vectorProfileCellB s₀ s₁ β t i z.1 z.2))=
      (fun z : VectorProfileCellParameter n×Field n=>vectorProfileCellCurvaturePairing s₀ s₁ β t i z.1 z.2):=by
    funext z
    change euclideanOperatorTrace (vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2*
      vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2*vectorProfileCellB s₀ s₁ β t i z.1 z.2)=_
    simp only [euclideanOperatorTrace,euclideanOperatorMatrix_mul,vectorProfileCellCurvaturePairing]
    rfl
  rw [←he]
  exact hh

theorem hasDerivAt_vectorProfileCellB_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun q=>vectorProfileCellB s₀ s₁ β t i (q,a.2) m)
      (-((1-t)/2) • hessianOperator (vectorProfileCellCurvaturePairing s₀ s₁ β t i a) m+
        ((1-t)*(β*(s₁.m i-s₀.m i))) • (1 : Field n→L[ℝ]Field n)) a.1 := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellFirstVariation s₀ s₁ β t i (z.1,a.2) z.2
  have hU : ContDiffAt ℝ ∞ U (a.1,m):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellFirstVariation s₀ s₁ β t i z.1 z.2) (a.1,m)
    (contDiffAt_vectorProfileCellFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ m hm) (by fun_prop)
  have hd:=hasDerivAt_partial_hessian U a.1 m hU
  have he : (fun y=>deriv (fun q=>U (q,y)) a.1)=ᶠ[𝓝 m]
      (fun y=>-(1-t)/2*vectorProfileCellCurvaturePairing s₀ s₁ β t i a y+
        (1-t)*(β*(s₁.m i-s₀.m i))/2*‖y‖^2):=by
    filter_upwards [(isOpen_vectorOpenSpinCube n).mem_nhds hm] with y hy
    exact vectorProfileCellFirstVariation_time s₀ s₁ β t hβ ht i hi a hq hθ y hy
  have hS : ContDiffAt ℝ 2 (vectorProfileCellCurvaturePairing s₀ s₁ β t i a) m:=
    ((contDiffAt_vectorProfileCellCurvaturePairing s₀ s₁ β t hβ ht i hi a hq hθ m hm).comp m
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  have hN : ContDiffAt ℝ 2 (fun y : Field n=>‖y‖^2) m:=(contDiff_norm_sq ℝ).contDiffAt
  apply hd.congr_deriv
  rw [hessianOperator_congr_of_eventuallyEq _ _ m he,
    hessianOperator_add_at _ _ m (contDiffAt_const.mul hS) (contDiffAt_const.mul hN),
    hessianOperator_const_mul_at _ m _ hS,hessianOperator_const_mul_at _ m _ hN,
    hessianOperator_norm_sq]
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_smul]
  module

theorem vectorProfileCellCurvaturePairing_generator (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun q=>vectorProfileCellCurvaturePairing s₀ s₁ β t i (q,a.2) m) a.1+
      (1-t)/2*responseMatrixPair
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (euclideanOperatorMatrix (hessianOperator (vectorProfileCellCurvaturePairing s₀ s₁ β t i a) m))=
      (1-t)*(β*(s₁.m i-s₀.m i))*Matrix.trace
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m)+
        2*Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*
          vectorProfileCellBMatrix s₀ s₁ β t i a m*
          euclideanOperatorMatrix (deriv (fun q=>vectorProfileCellPhysicalHessian
            s₀ s₁ β t i (q,a.2) m) a.1)) := by
  let h:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
  let B:=vectorProfileCellBMatrix s₀ s₁ β t i a m
  let Z:=euclideanOperatorMatrix (hessianOperator (vectorProfileCellCurvaturePairing s₀ s₁ β t i a) m)
  let Hdot:=deriv (fun q=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m) a.1
  let Bdot:=deriv (fun q=>vectorProfileCellB s₀ s₁ β t i (q,a.2) m) a.1
  have hdH : HasDerivAt (fun q=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m) Hdot a.1:=
    (hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).differentiableAt.hasDerivAt
  have hdB : HasDerivAt (fun q=>vectorProfileCellB s₀ s₁ β t i (q,a.2) m) Bdot a.1:=
    (hasDerivAt_vectorProfileCellB_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).differentiableAt.hasDerivAt
  have hBJet : euclideanOperatorMatrix Bdot+((1-t)/2) • Z=
      ((1-t)*(β*(s₁.m i-s₀.m i))) • (1 : Matrix (Fin n) (Fin n) ℝ):=by
    dsimp only [Bdot]
    rw [(hasDerivAt_vectorProfileCellB_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv]
    simp only [euclideanOperatorMatrix_add,euclideanOperatorMatrix_smul,euclideanOperatorMatrix_one]
    module
  have hSderiv:=hasDerivAt_euclideanOperatorTrace ((hdH.mul hdH).mul hdB)
  simp only [Pi.mul_apply] at hSderiv
  have hS : deriv (fun q=>vectorProfileCellCurvaturePairing s₀ s₁ β t i (q,a.2) m) a.1=
      Matrix.trace ((euclideanOperatorMatrix Hdot*h+h*euclideanOperatorMatrix Hdot)*B+
        (h*h)*euclideanOperatorMatrix Bdot):=by
    have he : (fun q=>vectorProfileCellCurvaturePairing s₀ s₁ β t i (q,a.2) m)=
        (fun q=>euclideanOperatorTrace (vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m*
          vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m*vectorProfileCellB s₀ s₁ β t i (q,a.2) m)):=by
      funext q
      simp only [vectorProfileCellCurvaturePairing,euclideanOperatorTrace,euclideanOperatorMatrix_mul]
      rfl
    rw [he,hSderiv.deriv]
    simp only [euclideanOperatorTrace,euclideanOperatorMatrix_add,euclideanOperatorMatrix_mul]
    rfl
  have hh:=vectorProfileCellHessianMatrix_symmetric s₀ s₁ β t hβ i a m hm
  have hb : B.IsSymm:=euclideanOperatorMatrix_hessian_symmetric _ m
    (((contDiffAt_vectorProfileCellFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ m hm).comp m
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num))
  have hdot : (euclideanOperatorMatrix Hdot).IsSymm:=by
    have he:= (hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv
    dsimp only [Hdot]
    rw [he]
    simp only [euclideanOperatorMatrix_smul,euclideanOperatorMatrix_mul,euclideanOperatorMatrix_add,
      euclideanOperatorMatrix_one]
    have hN:=euclideanOperatorMatrix_hessian_symmetric _ m
      (((contDiffAt_vectorProfileCellTrace s₀ s₁ β t hβ ht i hi a hq hθ m hm).comp m
        (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num))
    dsimp only [vectorProfileCellHessianMatrix] at hh
    change (euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m)).IsSymm at hN
    rw [Matrix.IsSymm,Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_mul,
      hh.eq,Matrix.transpose_add,hN.eq,Matrix.transpose_smul,Matrix.transpose_one]
    simp only [Matrix.mul_assoc]
  exact response_generator_curvature_pairing h B (euclideanOperatorMatrix Hdot)
    (euclideanOperatorMatrix Bdot) Z (1-t) (β*(s₁.m i-s₀.m i)) _ hh hb hdot hBJet hS

end QuantitativePaper
