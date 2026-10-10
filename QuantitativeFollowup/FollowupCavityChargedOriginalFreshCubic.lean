module
public import QuantitativeFollowup.FollowupCavitySingleMarkedCubic
public import QuantitativeFollowup.FollowupCavityGraftCubicBudget
public import FourPapersCommon.FiniteObservationTerminalList

@[expose] public section

/-! Literal original/fresh cubic products retain every original leaf
index. Their actual single-mark laws obey the charged branch budget. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem sum_constant {A : Type*} (xs : List A) (B : ℝ) :
    (xs.map (fun _ => B)).sum=(xs.length:ℝ)*B := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one]; ring

def cavityChargedOriginalFreshTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c => c.1 *
    ((observationLeaves (trimRoot T)).map (fun j => ∫z,
      |cavityRecordedPairProduct s (trimRoot T) i l z.1 * cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) c.2))
        (observationLeafSpin (trimRoot T) j z.1.2) z.2|
          ∂anisotropicSingleVertexMarkedLaw D s a T c.2)).sum)).sum

theorem cavityChargedOriginalFreshTripleMoment_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    cavityChargedOriginalFreshTripleMoment D s a T i l ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2 *
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a +
          2*finiteCascadeUnweightedBranchSum
            (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  have hL : 0≤L := Nat.cast_nonneg _
  have hb : cavityChargedOriginalFreshTripleMoment D s a T i l ≤
      L*cavityChargedGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) := by
    unfold cavityChargedOriginalFreshTripleMoment cavityChargedGraftBranchBudget
    rw [←List.sum_map_mul_left]
    apply List.sum_le_sum
    intro c hc
    have hinner : ((observationLeaves (trimRoot T)).map (fun j => ∫z,
        |cavityRecordedPairProduct s (trimRoot T) i l z.1 * cavitySpinOverlapDefect n
          (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) c.2))
          (observationLeafSpin (trimRoot T) j z.1.2) z.2|
            ∂anisotropicSingleVertexMarkedLaw D s a T c.2)).sum ≤
        L*finiteCascadeUnweightedBranchSum
          (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2) := by
      calc
        _ ≤ ((observationLeaves (trimRoot T)).map (fun _ =>
            finiteCascadeUnweightedBranchSum
              (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2))).sum := by
          apply List.sum_le_sum
          intro j _
          rw [finiteCascadeVertexGraft_branchSum]
          exact cavitySingleVertex_leaf_triple_cubic hn D s a hq T c.2 i l j
        _ = _ := by
          rw [sum_constant,observationLeaves_length,leafCount_trimRoot]
    have hh := mul_le_mul_of_nonneg_left hinner (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    simpa only [mul_left_comm] using hh
  have hc := mul_le_mul_of_nonneg_left (cavityChargedGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q => (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1)) hL
  have hh := hb.trans hc
  simpa only [L,pow_two,mul_assoc,cavityThirdMoment] using hh

end QuantitativeFollowup
