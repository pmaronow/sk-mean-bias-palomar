module
public import QuantitativePaper.VectorProfileCellTestEnvelopes
public import QuantitativePaper.VectorFiniteCellBackward
public import QuantitativePaper.VectorExponentialCellIto

@[expose] public section

/-! The actual finite-profile diffusion generator equals the genuine
original-field Legendre generator; temperature and noise are literal. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileFiniteCellGenerator_eq
    (s₀ s₁ : RSBScheme k) (β t θ : ℝ) (ht : t<1)
    (hθ : θ∈Icc (0:ℝ) 1) (i : ℕ) (hi : i ≤ k+1)
    (F : VectorProfileCellParameter n×Field n→ℝ)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1)))
    (sample : VectorDisorderBrownianSample n)
    (hF : ContDiffAt ℝ ∞ F ((q,θ,sample.1),
      vectorFiniteState (vectorProfileScheme s₀ s₁ θ hθ) β t ht.le q sample)) :
    let s:=vectorProfileScheme s₀ s₁ θ hθ
    let X:=vectorFiniteState s β t ht.le
    let d:=vectorAdditiveDrift (vectorFiniteDriftData s β t ht.le)
      (Real.sqrt ((1-t)*β^2)) 0 1
    vectorExponentialGenerator (vectorProfileTestRestriction θ F) X d
      (Real.sqrt ((1-t)*β^2)) q sample=
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,sample.1) (X q sample) := by
  let s:=vectorProfileScheme s₀ s₁ θ hθ
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let x:=X q sample
  have hd:=vectorFinite_actual_cell_drift s β t ht.le i hi q hq sample
  have hCell : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,sample.1),y))=
      vectorColeHopfStep (((1-t)*β^2)*(s₀.q (i+1)-q)) (vectorProfileMass s₀ s₁ θ i)
        (vectorRecursion s β t sample.1 (k+1-i)):=by
    funext y
    exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i q θ hθ sample.1 y
  have hd' : vectorAdditiveDrift (vectorFiniteDriftData s β t ht.le)
      (Real.sqrt ((1-t)*β^2)) 0 1 q sample=
      (((1-t)*β^2*vectorProfileMass s₀ s₁ θ i) •
        vectorProfileCellJointGradient s₀ s₁ β t i ((q,θ,sample.1),x)):=by
    rw [hd]
    unfold vectorProfileCellJointGradient
    rw [hCell]
    simp only [smul_smul]
    rfl
  have hTest : ContDiffAt ℝ ∞ (vectorProfileTestRestriction θ F) (q,(sample.1,x)):=
    ContDiffAt.comp (f := fun z : VectorCompactTestParameter n=>((z.1,θ,z.2.1),z.2.2))
      (g := F) (q,(sample.1,x)) hF (by fun_prop)
  have hTestLine:=(hTest.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (q:ℝ)
    ((hasDerivAt_id (q:ℝ)).prodMk (hasDerivAt_const (q:ℝ) (sample.1,x)))
  have htEq : vectorCompactSmoothTimeField (vectorProfileTestRestriction θ F) (q,(sample.1,x))=
      deriv (fun r=>F ((r,θ,sample.1),x)) q:=hTestLine.deriv.symm
  change vectorExponentialGenerator (vectorProfileTestRestriction θ F) X
    (vectorAdditiveDrift (vectorFiniteDriftData s β t ht.le) (Real.sqrt ((1-t)*β^2)) 0 1)
    (Real.sqrt ((1-t)*β^2)) q sample=
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,sample.1) x
  unfold vectorExponentialGenerator vectorProfileCellFieldGenerator
  rw [hd',Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β)),htEq]
  change fderiv ℝ (fun y=>F ((q,θ,sample.1),y)) x
      (((1-t)*β^2*vectorProfileMass s₀ s₁ θ i) •
        vectorProfileCellJointGradient s₀ s₁ β t i ((q,θ,sample.1),x))+
    ((1-t)*β^2)/2*(∑j : Fin n,fderiv ℝ (fderiv ℝ (fun y=>F ((q,θ,sample.1),y))) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))+
    deriv (fun r=>F ((r,θ,sample.1),x)) q=_
  ring

end QuantitativePaper
