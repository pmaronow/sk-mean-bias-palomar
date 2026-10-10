module
public import QuantitativePaper.VectorProfileCellExpectationIntegrable
public import QuantitativePaper.VectorProfileRawDerivativeEnvelopes
public import QuantitativePaper.VectorProfileRawTraceCheckpoint
public import FourPapersCommon.ExponentialPartialJets
public import FourPapersCommon.ExponentialBoundedLinear

@[expose] public section

/-! Actual smooth original-field generators have exponential retained
bounds on cropped cells. This proves every strict-time source expectation
is a genuine finite Bochner integral. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem exponentialSmoothOn_vectorProfileCellFieldGenerator
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (l u A B : ℝ) (hu : u<s₀.q (i+1)) (hA : 0<A) (hB : B<1)
    (F : VectorProfileCellParameter n×Field n→ℝ)
    (hF : ExponentialSmoothOn F (vectorProfileJointCylinder l u A B)) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellFieldGenerator s₀ s₁ β t i F z.1 z.2)
      (vectorProfileJointCylinder l u A B) := by
  let V:=vectorProfileJointCylinder (n:=n) l u A B
  have hV : IsOpen V:=isOpen_vectorProfileJointCylinder l u A B
  let L : (VectorProfileCellParameter n×Field n)→L[ℝ]ℝ:=
    (ContinuousLinearMap.fst ℝ ℝ (Couplings n×ℝ)).comp
      ((ContinuousLinearMap.snd ℝ ℝ (VectorProfileParameter n)).comp
        (ContinuousLinearMap.fst ℝ (VectorProfileCellParameter n) (Field n)))
  have hθ : ExponentialSmoothOn (L : (VectorProfileCellParameter n×Field n)→ℝ) V:=
    exponentialSmoothOn_bounded_linear L V 1 zero_le_one (fun z hz=>by
      change |z.1.2.1|≤1
      exact abs_le.mpr ⟨by linarith [hz.2.1],(hz.2.2.trans hB).le⟩)
  have hM : ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileMass s₀ s₁ z.1.2.1 i) V:=by
    apply ((ExponentialSmoothOn.const (s₀.m i) V).add
      (hθ.compCLM ((s₁.m i-s₀.m i) • ContinuousLinearMap.id ℝ ℝ))).congr
    intro z hz
    exact .of_forall fun w=>by
      simp only [Function.comp_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
        smul_eq_mul,vectorProfileMass,L,ContinuousLinearMap.comp_apply]
      change s₀.m i + (s₁.m i-s₀.m i)*w.1.2.1 = _
      ring
  have hU:=exponentialSmoothOn_vectorProfileCellJointPotential (n:=n)
    s₀ s₁ β t hβ ht i hi l u A B hu hA hB
  have hG:=hU.partialGradient hV
  have hDrift:=(hM.bilinear hG (ContinuousLinearMap.lsmul ℝ ℝ)).compCLM
    (((1-t)*β^2) • ContinuousLinearMap.id ℝ (Field n))
  have hPair:=(hF.partialFDeriv hV).bilinear hDrift (ContinuousLinearMap.apply ℝ ℝ).flip
  have hLap:=(hF.partialHessian hV).compCLM euclideanOperatorTraceCLM
  have hTime : ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      deriv (fun q=>F ((q,z.1.2),z.2)) z.1.1) V:=by
    apply (hF.directional (((1,(0,0)),0) : VectorProfileCellParameter n×Field n)).congr
    intro z hz
    filter_upwards [hV.mem_nhds hz] with w hw
    have hLine : HasDerivAt (fun q : ℝ=>((q,w.1.2),w.2)) ((1,(0,0)),0) w.1.1:=
      ((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
        (hasDerivAt_const w.1.1 w.2)
    exact (((hF.smooth w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt _ hLine).deriv.symm
  apply ((hTime.add hPair).add (hLap.compCLM ((((1-t)*β^2)/2) • ContinuousLinearMap.id ℝ ℝ))).congr
  intro z hz
  exact .of_forall fun w=>by
    simp only [Function.comp_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
      smul_eq_mul,ContinuousLinearMap.flip_apply,ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.lsmul_apply]
    have htrace (H : Field n→L[ℝ]Field n) : euclideanOperatorTraceCLM H=euclideanOperatorTrace H:=rfl
    simp only [htrace,euclideanOperatorTrace_hessian_eq_laplacian]
    unfold vectorProfileCellFieldGenerator vectorLaplacian
    simp only [smul_smul,mul_comm,vectorProfileCellJointGradient,directionalHessian]

end QuantitativePaper
