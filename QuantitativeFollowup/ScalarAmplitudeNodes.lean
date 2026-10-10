module
public import QuantitativeFollowup.ScalarAmplitudeIdentification
public import QuantitativeFollowup.ScalarGaussianPrefix
public import FourPapersCommon.ExponentialPartialJets

@[expose] public section

/-! Literal node potential and its spatial gradient as jointly smooth
functions of fixed Gaussian amplitudes and retained noise coordinates. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal BigOperators
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarAmplitudePrefixMask (n p : ℕ) : QuantitativePaper.Field n →L[ℝ] QuantitativePaper.Field n :=
  ∑ i : Fin n, if (i:ℕ)<p then scalarAmplitudeCoordinateProjection i else 0

def scalarAmplitudePrefixProjection (n p : ℕ) : ScalarAmplitudeState n →L[ℝ] ScalarAmplitudeState n :=
  (ContinuousLinearMap.fst ℝ (QuantitativePaper.Field n) (QuantitativePaper.Field n×ℝ)).prod
    (((scalarAmplitudePrefixMask n p).comp ((ContinuousLinearMap.fst ℝ (QuantitativePaper.Field n) ℝ).comp
      (ContinuousLinearMap.snd ℝ (QuantitativePaper.Field n) (QuantitativePaper.Field n×ℝ)))).prod
      ((ContinuousLinearMap.snd ℝ (QuantitativePaper.Field n) ℝ).comp
        (ContinuousLinearMap.snd ℝ (QuantitativePaper.Field n) (QuantitativePaper.Field n×ℝ))))

def scalarAmplitudeFieldDirection (n : ℕ) : ScalarAmplitudeState n := (0,0,1)

def scalarAmplitudeNodePotential (s : RSBScheme k) (p : ℕ) (w : ScalarAmplitudeState (k+2)) : ℝ :=
  scalarAmplitudeRecursion s (k+2-p) (scalarAmplitudePrefixProjection (k+2) p w)

def scalarAmplitudeNodeGradient (s : RSBScheme k) (p : ℕ) (w : ScalarAmplitudeState (k+2)) : ℝ :=
  fderiv ℝ (scalarAmplitudeRecursion s (k+2-p)) (scalarAmplitudePrefixProjection (k+2) p w)
    (scalarAmplitudeFieldDirection (k+2))

@[simp] theorem scalarAmplitudePrefixMask_apply (n p : ℕ) (z : QuantitativePaper.Field n) (i : Fin n) :
    scalarAmplitudePrefixMask n p z i=if (i:ℕ)<p then z i else 0 := by
  classical
  unfold scalarAmplitudePrefixMask
  simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i:ℕ)<p
    · simp [hi,scalarAmplitudeCoordinateProjection_apply]
    · simp [hi]
  · intro j _ hji
    by_cases hj : (j:ℕ)<p
    · simp [hj,scalarAmplitudeCoordinateProjection_apply,Ne.symm hji]
    · simp [hj]
  · simp

@[simp] theorem scalarAmplitudePrefixProjection_apply (n p : ℕ) (a z : QuantitativePaper.Field n) (x : ℝ) :
    scalarAmplitudePrefixProjection n p (a,z,x)=(a,scalarAmplitudePrefixMask n p z,x) := rfl

theorem scalarAmplitudePrefix_domain (n p : ℕ) (R : ℝ) :
    MapsTo (scalarAmplitudePrefixProjection n p) (scalarAmplitudeDomain n R) (scalarAmplitudeDomain n R) := by
  intro w hw
  exact hw

theorem exponentialSmoothOn_scalarAmplitudeNodePotential (s : RSBScheme k) (R : ℝ≥0) (p : ℕ) :
    ExponentialSmoothOn (scalarAmplitudeNodePotential s p) (scalarAmplitudeDomain (k+2) R) :=
  (exponentialSmoothOn_scalarAmplitudeRecursion s R (k+2-p)).precompCLM
    (scalarAmplitudePrefixProjection (k+2) p) (scalarAmplitudePrefix_domain _ _ _)

theorem exponentialSmoothOn_scalarAmplitudeNodeGradient (s : RSBScheme k) (R : ℝ≥0) (p : ℕ) :
    ExponentialSmoothOn (scalarAmplitudeNodeGradient s p) (scalarAmplitudeDomain (k+2) R) :=
  ((exponentialSmoothOn_scalarAmplitudeRecursion s R (k+2-p)).directional
    (scalarAmplitudeFieldDirection (k+2))).precompCLM
      (scalarAmplitudePrefixProjection (k+2) p) (scalarAmplitudePrefix_domain _ _ _)

theorem scalarAmplitudeNodePotential_value_bound (s : RSBScheme k) (R : ℝ≥0) (p : ℕ) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ w ∈ scalarAmplitudeDomain (k+2) R,
      |scalarAmplitudeNodePotential s p w| ≤ B+L*‖w‖ := by
  obtain ⟨B,hB,hv⟩ := scalarAmplitudeRecursion_value_bound s R (k+2-p)
  refine ⟨B,(1+(R:ℝ))*‖scalarAmplitudePrefixProjection (k+2) p‖,hB,by positivity,?_⟩
  intro w hw
  apply (hv _ (scalarAmplitudePrefix_domain _ _ _ hw)).trans
  have hh := mul_le_mul_of_nonneg_left ((scalarAmplitudePrefixProjection (k+2) p).le_opNorm w)
    (by positivity : 0 ≤ 1+(R:ℝ))
  linarith only [hh]

theorem scalarAmplitudeNodePotential_eq_potential (s r : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (hm : ∀ i, s.m i=r.m i)
    (a : QuantitativePaper.Field (k+2)) (ha : ∀ i : Fin (k+2), (a i)^2=β^2*(r.q (i+1)-r.q i))
    (p : ℕ) (hp : p≤k+2) (z : QuantitativePaper.Field (k+2)) (x : ℝ) :
    scalarAmplitudeNodePotential s p (a,z,x)=parisiPotential β (parisiSchemeMeasure r)
      (r.q p,scalarAmplitudeField (a,scalarAmplitudePrefixMask (k+2) p z,x)) := by
  rw [scalarAmplitudeNodePotential,scalarAmplitudePrefixProjection_apply,
    scalarAmplitudeRecursion_eq_potential s r β hβ hm a ha (k+2-p) (Nat.sub_le _ _)]
  rw [Nat.sub_sub_self hp]

theorem scalarAmplitudeRecursion_field_derivative (s r : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (hm : ∀ i, s.m i=r.m i)
    (a : QuantitativePaper.Field (k+2)) (ha : ∀ i : Fin (k+2), (a i)^2=β^2*(r.q (i+1)-r.q i))
    (j : ℕ) (hj : j≤k+2) (z : QuantitativePaper.Field (k+2)) (x : ℝ) :
    fderiv ℝ (scalarAmplitudeRecursion s j) (a,z,x) (scalarAmplitudeFieldDirection (k+2))=
      parisiGradient β (parisiSchemeMeasure r) (r.q (k+2-j),scalarAmplitudeField (a,z,x)) := by
  let R : ℝ≥0 := ⟨‖a‖+1,by positivity⟩
  have hw : (a,z,x) ∈ scalarAmplitudeDomain (k+2) R := by change ‖a‖<‖a‖+1;linarith
  have hf := ((exponentialSmoothOn_scalarAmplitudeRecursion s R j).smooth (a,z,x) hw).differentiableAt (by simp) |>.hasFDerivAt
  have hi : HasDerivAt (fun y : ℝ => (a,z,y)) (scalarAmplitudeFieldDirection (k+2)) x := by
    convert! (hasDerivAt_const x a).prodMk ((hasDerivAt_const x z).prodMk (hasDerivAt_id x)) using 1
  have hd := hf.comp_hasDerivAt (f := fun y : ℝ => (a,z,y)) x hi
  have he : (fun y : ℝ => scalarAmplitudeRecursion s j (a,z,y))=
      (fun y => parisiPotential β (parisiSchemeMeasure r) (r.q (k+2-j),scalarAmplitudeField (a,z,y))) :=
    funext fun y => scalarAmplitudeRecursion_eq_potential s r β hβ hm a ha j hj z y
  simp only [Function.comp_def] at hd
  rw [he] at hd
  have hp := (hasDerivAt_parisiPotential_spatial β hβ (parisiSchemeMeasure r) (r.q (k+2-j))
    (scalarAmplitudeField (a,z,x)) ⟨r.q_nonneg (by omega),r.q_le_one (by omega)⟩).comp x
      ((hasDerivAt_id x).add_const ⟪a,z⟫_ℝ)
  simpa only [Function.comp_def, scalarAmplitudeField, mul_one] using hd.unique hp

theorem scalarAmplitudeNodeGradient_eq_gradient (s r : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (hm : ∀ i, s.m i=r.m i)
    (a : QuantitativePaper.Field (k+2)) (ha : ∀ i : Fin (k+2), (a i)^2=β^2*(r.q (i+1)-r.q i))
    (p : ℕ) (hp : p≤k+2) (z : QuantitativePaper.Field (k+2)) (x : ℝ) :
    scalarAmplitudeNodeGradient s p (a,z,x)=parisiGradient β (parisiSchemeMeasure r)
      (r.q p,scalarAmplitudeField (a,scalarAmplitudePrefixMask (k+2) p z,x)) := by
  rw [scalarAmplitudeNodeGradient,scalarAmplitudePrefixProjection_apply,
    scalarAmplitudeRecursion_field_derivative s r β hβ hm a ha (k+2-p) (Nat.sub_le _ _),Nat.sub_sub_self hp]

end QuantitativeFollowup
