module
public import QuantitativePaper.VectorProfileClosedObservables
public import QuantitativePaper.VectorProfileTraceTimePullback

@[expose] public section

/-! A genuine retained-jet expression for the one-sided trace reaction,
continuous and exponentially bounded on the whole closed cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem retainedExponentialContinuousOn_vectorProfileMass
    (s₀ s₁ : RSBScheme k) (i : ℕ) (hi : i≤k+1)
    (Q : Set ℝ) (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (fun (_q : ℝ) (z : VectorProfileParameter n×Field n)=>
      vectorProfileMass s₀ s₁ z.1.1 i) Q (vectorProfileRetainedDomain n A B) := by
  refine ⟨(show Continuous (fun w : ℝ×(VectorProfileParameter n×Field n)=>
    vectorProfileMass s₀ s₁ w.2.1.1 i) by unfold vectorProfileMass;fun_prop).continuousOn,
    1,0,zero_le_one,le_rfl,?_⟩
  intro q hq z hz
  let S:=vectorProfileScheme s₀ s₁ z.1.1
    ⟨(hA.trans hz.1).le,(hz.2.trans hB).le⟩
  change ‖S.m i‖≤1*Real.exp (0*‖z‖)
  rw [Real.norm_of_nonneg (S.m_nonneg (by omega))]
  simpa using S.m_le_one (by omega)

theorem retainedExponentialContinuousOn_vectorProfileRetainedTraceReaction (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hL:=((retainedJetExponentialOn_vectorProfileCellRawTraceHessian (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).compCLM euclideanOperatorTraceCLM).values
  have hD:=(retainedJetExponentialOn_vectorProfileCellRawTraceFDeriv (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hG:=(retainedJetExponentialOn_vectorProfileCellRawTraceGradient (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hInv:=retainedExponentialContinuousOn_vectorProfileCellRawHessianInverse hn
    s₀ s₁ β t ht i hi A B hA hB
  have hIG:=hInv.bilinear hG (ContinuousLinearMap.apply ℝ (Field n)).flip
  have hQ:=hD.bilinear hIG (ContinuousLinearMap.apply ℝ ℝ).flip
  have hH:=(retainedJetExponentialOn_vectorProfileCellRawHessian (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hSquare:=(hH.bilinear hH
    (ContinuousLinearMap.mul ℝ (Field n→L[ℝ]Field n))).compCLM euclideanOperatorTraceCLM
  have hM:=retainedExponentialContinuousOn_vectorProfileMass (n:=n) s₀ s₁ i hi
    (Icc (s₀.q i) (s₀.q (i+1))) A B hA hB
  have hMS:=(hM.bilinear hSquare (ContinuousLinearMap.mul ℝ ℝ)).compCLM
    ((2:ℝ) • ContinuousLinearMap.id ℝ ℝ)
  apply ((hL.add hQ.neg).add hMS).compCLM
    ((-(1-t)*β^3/2) • ContinuousLinearMap.id ℝ ℝ) |>.congr
  intro q hq z hz
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
    ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,ContinuousLinearMap.apply_apply] 
  have htrace (L : Field n→L[ℝ]Field n) : euclideanOperatorTraceCLM L=euclideanOperatorTrace L:=rfl
  simp_rw [htrace]
  change -(1-t)*β^3/2*(_ + -_ + 2*(_*_))= -(1-t)*β^3/2*(_-_+2*_*_)
  ring

theorem vectorProfileRetainedTraceReaction_eq_field
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Ioo (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedTraceReaction s₀ s₁ β t i q z=
      vectorProfileCellFieldTraceTime s₀ s₁ β t i ((q,z.1),z.2) := by
  let U : Field n→ℝ:=fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)
  let T : Field n→ℝ:=vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)
  let H:=hessianOperator U z.2
  let G:=gradient U z.2
  have hUnit : IsUnit H:=by
    dsimp only [H,U]
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi (q,z.1)
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    exact vectorFieldHessian_isUnit _ β t z.1.2 (k+2) z.2
  have hHG : Ring.inverse H (H G)=G:=by
    have he:=congrArg (fun L : Field n→L[ℝ]Field n=>L G) (Ring.inverse_mul_cancel H hUnit)
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using he
  rw [vectorProfileCellFieldTraceTime_formula s₀ s₁ β t hβ ht i hi (q,z.1) hq hθ z.2,
    vectorProfileCellRawTrace_time_PDE s₀ s₁ β t hβ ht i (q,z.1) hq.2 ⟨hθ.1.le,hθ.2.le⟩ z.2,
    vectorProfileCellPotentialTime_gradient_formula s₀ s₁ β t hβ ht i (q,z.1) hq.2 ⟨hθ.1.le,hθ.2.le⟩ z.2]
  unfold vectorProfileRetainedTraceReaction
  rw [euclideanOperatorTrace_hessian_eq_laplacian]
  change _=β*(-((1-t)*β^2)/2*(vectorLaplacian T z.2+
    2*vectorProfileMass s₀ s₁ z.1.1 i*(euclideanOperatorTrace (H*H)+inner ℝ G (gradient T z.2)))-
    fderiv ℝ T z.2 (Ring.inverse H ((-((1-t)*β^2)/2) •
      (gradient T z.2+(2*vectorProfileMass s₀ s₁ z.1.1 i) •H G))))
  simp only [map_smul,map_add,smul_eq_mul,hHG,inner_gradient_left,real_inner_comm]
  ring

end QuantitativePaper
