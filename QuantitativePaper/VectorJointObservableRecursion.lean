module
public import QuantitativePaper.VectorJointResponse

@[expose] public section

/-! Actual bounded C3 observables propagated through the literal finite
Parisi branching kernels. Full joint disorder/field bounds are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

structure VectorBoundedC3 (G : VectorParameter n→ℝ) where
  regularity : ContDiff ℝ 3 G
  bounds : ℕ→ℝ
  bounds_nonneg : ∀ j,0≤bounds j
  jets : ∀ j,j≤3 → ∀ p,‖iteratedFDeriv ℝ j G p‖≤bounds j

def vectorJointObservableRecursion (s : RSBScheme k) (β t : ℝ)
    (G : VectorParameter n→ℝ) : ℕ→VectorParameter n→ℝ
  | 0=>G
  | j+1=>vectorJointResponse (fun p=>vectorRecursion s β t p.1 j p.2)
      (vectorJointObservableRecursion s β t G j)
      ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))

theorem exists_vectorRecursion_jointResponseData (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) :
    Nonempty (VectorJointResponseTestData (fun p=>vectorRecursion s β t p.1 j p.2) G) := by
  obtain ⟨hF,K,hK,hFB⟩ := vectorRecursion_joint_smooth_bounded_jets (n:=n) s β t 3 j
  exact ⟨{
    potentialRegularity := hF
    observableRegularity := hG.regularity
    fieldLip := vectorJointLipschitzConstant n β t
    lipschitz := vectorRecursion_joint_lipschitz s β t j
    potentialPower := ⟨K,zero_le_one.trans hK⟩
    potentialPower_ge_one := hK
    potentialJets := hFB
    observableBounds := hG.bounds
    observableBounds_nonneg := hG.bounds_nonneg
    observableJets := hG.jets }⟩

def vectorRecursionJointResponseData (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) :
    VectorJointResponseTestData (fun p=>vectorRecursion s β t p.1 j p.2) G :=
  Classical.choice (exists_vectorRecursion_jointResponseData s β t j hG)

theorem boundedC3_vectorJointResponse {F G : VectorParameter n→ℝ}
    (data : VectorJointResponseTestData F G) (m v : ℝ) :
    Nonempty (VectorBoundedC3 (vectorJointResponse F G v m)) := by
  obtain ⟨B,hB,hJets⟩ := data.response_uniform_jets m
  exact ⟨{
    regularity := (hJets v).1
    bounds := B
    bounds_nonneg := hB
    jets := (hJets v).2 }⟩

theorem boundedC3_vectorJointObservableRecursion (s : RSBScheme k) (β t : ℝ)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) (j : ℕ) :
    Nonempty (VectorBoundedC3 (vectorJointObservableRecursion s β t G j)) := by
  induction j with
  | zero=>exact ⟨hG⟩
  | succ j ih=>
    obtain ⟨d⟩ := ih
    exact boundedC3_vectorJointResponse (vectorRecursionJointResponseData s β t j d) _ _

end QuantitativePaper
