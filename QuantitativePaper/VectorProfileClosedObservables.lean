module
public import QuantitativePaper.VectorProfileClosedRawFields
public import QuantitativePaper.VectorProfileClosedInverseBounds
public import QuantitativePaper.VectorProfileCurvatureRetainedPullback

@[expose] public section

/-! Explicit retained-jet extensions of the literal Legendre observables.
Their values stay continuous and exponentially bounded at zero-variance
cell endpoints; no time derivative at a jump is introduced. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileRetainedSecondVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q : ℝ) (z : VectorProfileParameter n×Field n) : ℝ:=
  β⁻¹*(-vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,z.1) z.2+
    inner ℝ (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,z.1)) z.2)
      (Ring.inverse (hessianOperator
        (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2)
        (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,z.1)) z.2)))

def vectorProfileRetainedCurvaturePairing (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q : ℝ) (z : VectorProfileParameter n×Field n) : ℝ:=
  β*(-deriv (fun θ=>vectorProfileCellRawTrace s₀ s₁ β t i (q,θ,z.1.2) z.2) z.1.1+
    fderiv ℝ (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2
      (Ring.inverse (hessianOperator
        (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2)
        (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,z.1)) z.2)))

def vectorProfileRetainedTraceReaction (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q : ℝ) (z : VectorProfileParameter n×Field n) : ℝ:=
  -(1-t)*β^3/2*(euclideanOperatorTrace
      (hessianOperator (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2)-
    fderiv ℝ (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2
      (Ring.inverse (hessianOperator
        (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2)
        (gradient (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2))+
    2*vectorProfileMass s₀ s₁ z.1.1 i*euclideanOperatorTrace
      (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2*
       hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2))

theorem retainedExponentialContinuousOn_vectorProfileRetainedSecondVariation (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t i)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hU:=(retainedJetExponentialOn_vectorProfileCellPotentialSecondVariation (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hG:=(retainedJetExponentialOn_vectorProfileCellVariationGradient (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hH:=retainedExponentialContinuousOn_vectorProfileCellRawHessianInverse hn
    s₀ s₁ β t ht i hi A B hA hB
  have hHG:=hH.bilinear hG (ContinuousLinearMap.apply ℝ (Field n)).flip
  exact (hU.neg.add (hG.bilinear hHG (innerSL ℝ))).compCLM
    (β⁻¹ • ContinuousLinearMap.id ℝ ℝ)

theorem retainedExponentialContinuousOn_vectorProfileRetainedCurvaturePairing (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hT:=(retainedJetExponentialOn_vectorProfileCellRawTraceProfile (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hD:=(retainedJetExponentialOn_vectorProfileCellRawTraceFDeriv (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hG:=(retainedJetExponentialOn_vectorProfileCellVariationGradient (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  have hH:=retainedExponentialContinuousOn_vectorProfileCellRawHessianInverse hn
    s₀ s₁ β t ht i hi A B hA hB
  have hHG:=hH.bilinear hG (ContinuousLinearMap.apply ℝ (Field n)).flip
  exact (hT.neg.add (hD.bilinear hHG (ContinuousLinearMap.apply ℝ ℝ).flip)).compCLM
    (β • ContinuousLinearMap.id ℝ ℝ)

theorem vectorProfileRetainedSecondVariation_eq_field
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Ioo (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedSecondVariation s₀ s₁ β t i q z=
      vectorProfileCellFieldSecondVariation s₀ s₁ β t i ((q,z.1),z.2) :=
  (vectorProfileCellSecondVariation_pullback s₀ s₁ β t hβ ht i hi (q,z.1) hq hθ z.2).symm

theorem vectorProfileRetainedCurvaturePairing_eq_field
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Ioo (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedCurvaturePairing s₀ s₁ β t i q z=
      vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i ((q,z.1),z.2) :=
  (vectorProfileCellCurvaturePairing_retained_formula s₀ s₁ β t hβ ht i hi
    (q,z.1) hq hθ z.2).symm

end QuantitativePaper
