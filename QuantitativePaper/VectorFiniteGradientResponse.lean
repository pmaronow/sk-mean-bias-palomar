module
public import QuantitativePaper.VectorJointObservableRecursion
public import QuantitativePaper.VectorFiniteCellPDE

@[expose] public section

/-! Genuine backward response data for every coordinate of the actual
finite Parisi gradient, and its literal cell time derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorMagnetizationBoundedC3 (s : RSBScheme k) (β t : ℝ) (j : ℕ) (l : Fin n) :
    VectorBoundedC3 (fun z : VectorParameter n=>vectorMagnetization s β t z.1 j z.2 l) := by
  let h:=boundedJets_vectorMagnetization_component s β t j l
  let B:=fun r=>Classical.choose (h.2 r)
  exact {
    regularity := h.1.of_le (by simp)
    bounds := B
    bounds_nonneg := fun r=>(Classical.choose_spec (h.2 r)).1
    jets := fun r _=>(Classical.choose_spec (h.2 r)).2 }

def vectorFiniteGradientResponseData (s : RSBScheme k) (β t : ℝ) (i : ℕ) (l : Fin n) :
    VectorJointResponseTestData
      (fun z : VectorParameter n=>vectorRecursion s β t z.1 (k+1-i) z.2)
      (fun z : VectorParameter n=>vectorMagnetization s β t z.1 (k+1-i) z.2 l) :=
  vectorRecursionJointResponseData s β t (k+1-i)
    (vectorMagnetizationBoundedC3 s β t (k+1-i) l)

theorem vectorFiniteCellGradient_eq_response (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) (l : Fin n) :
    gradient (vectorFiniteCellPotential s β t p i q) x l=
      vectorStepResponse ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorMagnetization s β t p (k+1-i) y l) x := by
  rw [gradient_euclidean_coordinate]
  exact fderiv_vectorColeHopfStep_recursion_coordinate s β t _ _ p _ x l

theorem hasDerivAt_vectorFiniteCellGradient_time (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ)
    (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) (l : Fin n) :
    HasDerivAt (fun r=>gradient (vectorFiniteCellPotential s β t p i r) x l)
      (-((1-t)*β^2)*vectorLinearBackwardGenerator
        (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l)
        (vectorFiniteCellPotential s β t p i q) (s.m i) x) q := by
  let data:=(vectorFiniteGradientResponseData (n:=n) s β t i l).fieldData p
  have hv : 0<((1-t)*β^2)*(s.q (i+1)-q) :=
    mul_pos (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)) (sub_pos.mpr hq)
  have hd:=(hasDerivAt_vectorStepResponse_variance _ _ (s.m i)
    (data.weightedDatum (s.m i)) (data.expDatum (s.m i)) hv x).comp q
      (((hasDerivAt_id q).const_sub (s.q (i+1))).const_mul ((1-t)*β^2))
  have he : (fun r=>gradient (vectorFiniteCellPotential s β t p i r) x l)=
      (fun r=>vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorMagnetization s β t p (k+1-i) y l) x) :=
    funext fun r=>vectorFiniteCellGradient_eq_response s β t p i r x l
  rw [he]
  convert! hd using 1
  have hgrad : (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l)=
      vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-q)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorMagnetization s β t p (k+1-i) y l) :=
    funext fun y=>vectorFiniteCellGradient_eq_response s β t p i q y l
  rw [hgrad]
  unfold vectorLinearBackwardGenerator
  have hpot : vectorFiniteCellPotential s β t p i q=
      vectorColeHopfStep (((1-t)*β^2)*(s.q (i+1)-q)) (s.m i)
        (vectorRecursion s β t p (k+1-i)) := rfl
  rw [hpot]
  ring

end QuantitativePaper
