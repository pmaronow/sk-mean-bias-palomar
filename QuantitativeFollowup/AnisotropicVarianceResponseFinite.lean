module
public import QuantitativeFollowup.FollowupCavityNodeBStieltjes
public import QuantitativeFollowup.AnisotropicFiniteTailResponse
public import FourPapersCommon.FiniteStateCascadeConvexity

@[expose] public section

/-! Depth-independent bounds for the genuine diagonal-variance response.
The response is obtained by differentiating the actual Gaussian recursion;
binary terminal spins and normalized continuation laws give its bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

private theorem response_expectation_nonneg {E : Type*} [MeasurableSpace E]
    (Q : ℕ→ProbabilityTheory.Kernel E E) (f : E→ℝ) (hf : ∀x,0≤f x)
    (j : ℕ) (x : E) : 0≤OverlapPaper.sourceKernelExpectation Q j f x := by
  induction j generalizing x with
  | zero => exact hf x
  | succ j ih => exact integral_nonneg ih

theorem cavityFiniteBinaryGenerator_nonneg (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j J : ℕ) (H K : FiniteStateField (Configuration n)) :
    0≤cavityFiniteBinaryGenerator D s j J H K := by
  unfold cavityFiniteBinaryGenerator
  apply response_expectation_nonneg
  intro y
  exact add_nonneg (finiteStateCascadeHessian_nonneg _ _ (anisotropicSchemeMass_nonneg s) _ j y K)
    (mul_nonneg (anisotropicSchemeMass_nonneg s j) (sq_nonneg _))

theorem cavityFiniteBinaryGenerator_le_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j J : ℕ) (hj : j≤J) (H K : FiniteStateField (Configuration n))
    (hK : ∀σ,K σ*K σ=1) : cavityFiniteBinaryGenerator D s j J H K≤1 := by
  rw [cavityFiniteBinaryGenerator_eq_future_squares D s j J hj H K hK]
  have hs : (∑p∈Finset.range j,(anisotropicSchemeMass s (p+1)-anisotropicSchemeMass s p)*
      finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) (p+1) (J-(p+1)) H K K)≤0 := by
    apply Finset.sum_nonpos
    intro p _
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact sub_nonpos.mpr (anisotropicSchemeMass_antitone_step s p)
    · unfold finiteStateCascadePairMoment
      apply response_expectation_nonneg
      intro y
      exact mul_self_nonneg _
  linarith

private theorem response_cell_sum (s : RSBScheme k) (J : ℕ) :
    (∑j∈Finset.range J,(s.q (k+2-j)-s.q (k+1-j)))=1-s.q (k+2-J) := by
  induction J with
  | zero => simp [s.q_top]
  | succ J ih =>
    rw [Finset.sum_range_succ,ih]
    have hi : k+2-(J+1)=k+1-J:=by omega
    rw [hi]
    ring

theorem cavityFiniteNodeBResponse_mem_Icc (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : ℕ) (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) :
    cavityFiniteNodeBResponse D s J H K∈Icc 0 ((1-s.q (k+2-J))/2) := by
  constructor
  · unfold cavityFiniteNodeBResponse
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun j _=>mul_nonneg (cavityCellVariance_nonneg s j)
      (cavityFiniteBinaryGenerator_nonneg D s j J H K)
  · unfold cavityFiniteNodeBResponse
    have hs : (∑j∈Finset.range J,(s.q (k+2-j)-s.q (k+1-j))*
        cavityFiniteBinaryGenerator D s j J H K)≤
        ∑j∈Finset.range J,(s.q (k+2-j)-s.q (k+1-j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_of_le_one_right (cavityCellVariance_nonneg s j)
        (cavityFiniteBinaryGenerator_le_one D s j J (Finset.mem_range.mp hj).le H K hK)
    rw [response_cell_sum] at hs
    linarith

def anisotropicFiniteTailVarianceResponse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) : ℝ :=
  cavityFiniteNodeBResponse D (vectorClampedScheme s q q.property) (k+2)
    (anisotropicEnergyMap D P) (cavityCoordinateFeature i)

theorem anisotropicFiniteTailVarianceResponse_mem_Icc (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicFiniteTailVarianceResponse D s q P i∈Icc 0 ((1-(q:ℝ))/2) := by
  have he:=cavityFiniteNodeBResponse_mem_Icc D (vectorClampedScheme s q q.property) (k+2)
    (anisotropicEnergyMap D P) (cavityCoordinateFeature i) (cavityCoordinateFeature_binary i)
  have hi : k+1+2-(k+2)=1:=by omega
  rw [hi,vectorClampedScheme_overlap_succ s q q.property 0,s.q_zero,
    max_eq_left q.property.1] at he
  exact he

theorem hasDerivAt_anisotropicFiniteTailPotential_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n)
    (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>anisotropicFiniteTailPotential (anisotropicReplaceVariance D i u) s q P)
      (anisotropicFiniteTailVarianceResponse (anisotropicReplaceVariance D i b) s q P i) b := by
  have hd:=hasDerivAt_anisotropicFinitePotential_variance D
    (vectorClampedScheme s q q.property) i b hb (k+2) P
  rw [anisotropicFiniteTailVarianceResponse,anisotropicReplaceVariance_energyMap]
  apply hd.congr_of_eventuallyEq
  exact .of_forall fun u=>congrFun
    (anisotropicTailRecursion_eq_clamped (anisotropicReplaceVariance D i u) s q q.property le_rfl) P

end QuantitativeFollowup
