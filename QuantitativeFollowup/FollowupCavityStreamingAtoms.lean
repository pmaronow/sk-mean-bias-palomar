module
public import QuantitativeFollowup.FollowupCavitySecondStreaming
public import QuantitativeFollowup.FollowupCavityMarkedDefectBounds

@[expose] public section

/-! Actual fixed-spin cavity atoms and their genuine enlarged-tree tests.
The bound stored in an atom is a bound on a finite terminal test, not a
derivative or response assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

structure CavityStreamingAtom (n k : ℕ) where
  tree : FiniteTerminalGenealogy (k+2)
  test : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy tree)→ℝ
  bound : ℝ
  bound_nonneg : 0≤bound
  test_le : ∀σ,|test σ|≤bound

def CavityStreamingAtom.complexity (A : CavityStreamingAtom n k) : ℕ :=
  FiniteCascadeGenealogy.leafCount (asGenealogy A.tree)

def CavityStreamingAtom.eval (A : CavityStreamingAtom n k)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) : ℝ→ℝ :=
  followupCavityPhysicalExpectation n β ρ hβ hρ s a A.tree A.test

theorem CavityStreamingAtom.complexity_pos (A : CavityStreamingAtom n k) :
    0<A.complexity := FiniteCascadeGenealogy.leafCount_pos _

theorem CavityStreamingAtom.eval_abs_le (A : CavityStreamingAtom n k)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |A.eval β ρ hβ hρ s a u|≤A.bound := by
  rw [CavityStreamingAtom.eval,
    followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq A.tree A.test u hu]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a A.tree)
      (f:=followupCavityPhysicalRecordObservable n A.tree A.test)
      (C:=A.bound) (.of_forall fun r=>by
        simpa only [Real.norm_eq_abs,followupCavityPhysicalRecordObservable] using A.test_le
          ((trimmedSpinEquiv (S:=Configuration (n+1)) A.tree) (spins (trimRoot A.tree) r.2)))

private theorem atoms_abs_list_sum {I : Type} (xs : List I) (f : I→ℝ) (C : ℝ)
    (h : ∀i∈xs,|f i|≤C) : |(xs.map f).sum|≤(xs.length:ℝ)*C := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      exact (abs_add_le _ _).trans ((add_le_add (h i (by simp))
        (ih (fun j hj=>h j (by simp [hj])))).trans_eq (by ring))

theorem cavityOriginalOriginalTerminalDefect_abs_le (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (τ : TerminalSpins (Configuration (n+1)) (trimRoot T)) :
    |cavityOriginalOriginalTerminalDefect n s T τ|≤
      2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2 := by
  classical
  let xs:=finiteCascadeTerminalVertices (trimRoot T) τ
  have hlen : xs.length=FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
    dsimp only [xs]
    rw [finiteCascadeTerminalVertices_length_eq_leafCount,leafCount_trimRoot]
  have hi (c : FiniteCascadeRecordVertex (trimRoot T)×Configuration (n+1)) :
      |(xs.map (fun d=>if c.1=d.1 then 0 else
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 d.1) c.2 d.2)).sum|
        ≤(xs.length:ℝ)*2 := by
    apply atoms_abs_list_sum
    intro d _
    split_ifs
    · norm_num
    · exact cavitySpinOverlapDefect_abs_le_two n _ (cavityPhysicalCommonOverlap_mem_Icc s _ _ _) _ _
  have hh:=atoms_abs_list_sum xs _ ((xs.length:ℝ)*2) (fun c _=>hi c)
  change |cavityOriginalOriginalTerminalDefect n s T τ|≤_ at hh
  rw [hlen] at hh
  exact hh.trans_eq (by ring)

def CavityStreamingAtom.originalOriginal (A : CavityStreamingAtom n k) (s : RSBScheme k) :
    CavityStreamingAtom n k where
  tree:=A.tree
  test:=cavityOriginalOriginalGraftSampleObservable s A.tree (cavityFullTestToTerminal A.tree A.test)
  bound:=2*(A.complexity:ℝ)^2*A.bound
  bound_nonneg:=mul_nonneg (by positivity) A.bound_nonneg
  test_le σ:=by
    dsimp only [cavityOriginalOriginalGraftSampleObservable,cavityFullTestToTerminal,cavityFullTestToTrim]
    rw [abs_mul]
    exact (mul_le_mul (A.test_le _)
      (cavityOriginalOriginalTerminalDefect_abs_le (n:=n) s A.tree _)
      (abs_nonneg _) A.bound_nonneg).trans_eq (by dsimp only [CavityStreamingAtom.complexity];ring)

def CavityStreamingAtom.originalFresh (A : CavityStreamingAtom n k) (s : RSBScheme k)
    (v : FiniteCascadeRecordVertex (trimRoot A.tree)) : CavityStreamingAtom n k where
  tree:=.advance (finiteCascadeVertexGraft v)
  test:=cavitySingleGraftSampleObservable A.tree v
    (cavityOriginalGraftPairObservable s A.tree v (cavityFullTestToTrim A.tree A.test))
  bound:=2*(A.complexity:ℝ)*A.bound
  bound_nonneg:=mul_nonneg (by positivity) A.bound_nonneg
  test_le σ:=by
    dsimp only [cavitySingleGraftSampleObservable,cavityOriginalGraftPairObservable,
      cavityFullTestToTrim]
    rw [abs_mul]
    exact (mul_le_mul (A.test_le _) (cavityOriginalVertexOverlapSum_abs_le n s A.tree v _ _)
      (abs_nonneg _) A.bound_nonneg).trans_eq (by dsimp only [CavityStreamingAtom.complexity];ring)

def CavityStreamingAtom.cross (A : CavityStreamingAtom n k)
    (v w : FiniteCascadeRecordVertex (trimRoot A.tree)) (q : Paper.Overlap) :
    CavityStreamingAtom n k where
  tree:=.advance (finiteCascadeCrossVertexGraft v w)
  test:=cavityCrossGraftSampleObservable A.tree v w q (cavityFullTestToTrim A.tree A.test)
  bound:=2*A.bound
  bound_nonneg:=mul_nonneg (by norm_num) A.bound_nonneg
  test_le σ:=by
    dsimp only [cavityCrossGraftSampleObservable,cavityFullTestToTrim]
    rw [abs_mul]
    exact (mul_le_mul (A.test_le _) (cavitySpinOverlapDefect_abs_le_two n q q.property _ _)
      (abs_nonneg _) A.bound_nonneg).trans_eq (by ring)

def CavityStreamingAtom.future (A : CavityStreamingAtom n k)
    (s : RSBScheme k) (v : FiniteCascadeRecordVertex (trimRoot A.tree)) (q : Paper.Overlap) :
    CavityStreamingAtom n k where
  tree:=.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))
  test:=cavityFutureResponseSampleObservable _
    (cavityFutureGraftResponseTerminalObservable A.tree v (cavityFiniteFutureDepth s v.depth q)
      q (cavityFullTestToTerminal A.tree A.test))
  bound:=2*A.bound
  bound_nonneg:=mul_nonneg (by norm_num) A.bound_nonneg
  test_le σ:=by
    dsimp only [cavityFutureResponseSampleObservable,cavityFutureGraftResponseTerminalObservable,
      cavityFullTestToTerminal,cavityFullTestToTrim]
    rw [abs_mul]
    exact (mul_le_mul (A.test_le _) (cavitySpinOverlapDefect_abs_le_two n q q.property _ _)
      (abs_nonneg _) A.bound_nonneg).trans_eq (by ring)

def cavityStreamingNormalizerAtom (n : ℕ) (s : RSBScheme k)
    (i : vectorPosteriorFeatureIndex k) : CavityStreamingAtom n k where
  tree:=cavityNormalizerGraftTree i
  test:=cavityFutureResponseSampleObservable _ (cavityNormalizerGraftTerminalTest s i)
  bound:=2
  bound_nonneg:=by norm_num
  test_le σ:=by
    dsimp only [cavityFutureResponseSampleObservable,cavityNormalizerGraftTerminalTest]
    exact cavitySpinOverlapDefect_abs_le_two n _ (vectorProfileAtom s i).property _ _

@[simp] theorem CavityStreamingAtom.originalOriginal_complexity (A : CavityStreamingAtom n k)
    (s : RSBScheme k) : (A.originalOriginal s).complexity=A.complexity := rfl

@[simp] theorem CavityStreamingAtom.originalFresh_complexity (A : CavityStreamingAtom n k)
    (s : RSBScheme k) (v : FiniteCascadeRecordVertex (trimRoot A.tree)) :
    (A.originalFresh s v).complexity=A.complexity+1 := by
  simp only [CavityStreamingAtom.complexity,CavityStreamingAtom.originalFresh,
    asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeVertexGraft_leafCount,leafCount_trimRoot]

@[simp] theorem CavityStreamingAtom.cross_complexity (A : CavityStreamingAtom n k)
    (v w : FiniteCascadeRecordVertex (trimRoot A.tree)) (q : Paper.Overlap) :
    (A.cross v w q).complexity=A.complexity+2 := by
  simp only [CavityStreamingAtom.complexity,CavityStreamingAtom.cross,
    asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeCrossVertexGraft_leafCount,leafCount_trimRoot]

@[simp] theorem CavityStreamingAtom.future_complexity (A : CavityStreamingAtom n k)
    (s : RSBScheme k) (v : FiniteCascadeRecordVertex (trimRoot A.tree)) (q : Paper.Overlap) :
    (A.future s v q).complexity=A.complexity+2 := by
  simp only [CavityStreamingAtom.complexity,CavityStreamingAtom.future,
    asGenealogy,FiniteCascadeGenealogy.leafCount,finiteCascadeFutureVertexGraft_leafCount,leafCount_trimRoot]

@[simp] theorem cavityStreamingNormalizerAtom_complexity (s : RSBScheme k)
    (i : vectorPosteriorFeatureIndex k) : (cavityStreamingNormalizerAtom n s i).complexity=2 := by
  simp only [CavityStreamingAtom.complexity,cavityStreamingNormalizerAtom,cavityNormalizerGraftTree,
    asGenealogy,FiniteCascadeGenealogy.leafCount,observationPairTree_leafCount]

end QuantitativeFollowup
