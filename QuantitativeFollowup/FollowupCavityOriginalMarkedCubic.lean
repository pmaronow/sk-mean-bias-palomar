module
public import QuantitativeFollowup.FollowupCavitySingleMarkedCubic
public import FourPapersCommon.FiniteObservationTerminalList

@[expose] public section

/-! Every literal original-original streaming cubic product is dominated
under the unchanged recorded physical law, including repeated leaves. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem sum_constant {A : Type*} (xs : List A) (B : ℝ) :
    (xs.map (fun _ => B)).sum=(xs.length:ℝ)*B := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one]; ring

theorem cavityOriginalLeaf_leaf_triple_cubic (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (i l : Fin 2 → ObservationLeaf (trimRoot T)) (j h : ObservationLeaf (trimRoot T)) :
    (∫z, |cavityRecordedPairProduct s (trimRoot T) i l z *
      cavityRecordedLeafPairDefect s (trimRoot T) j h z.2|
        ∂anisotropicTrimmedRecordedTreeLaw D s a T) ≤
      finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) := by
  let ii : Fin 3 → ObservationLeaf (trimRoot T) := ![i 0,i 1,j]
  let ll : Fin 3 → ObservationLeaf (trimRoot T) := ![l 0,l 1,h]
  exact cavityTrimmedRecordedTripleDefectMoment_le_branch hn D s a hq T ii ll

def cavityOriginalLeafTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) : ℝ :=
  ((observationLeaves (trimRoot T)).map (fun j => ((observationLeaves (trimRoot T)).map (fun h =>
    ∫z, |cavityRecordedPairProduct s (trimRoot T) i l z * cavityRecordedLeafPairDefect s (trimRoot T) j h z.2|
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)).sum)).sum

theorem cavityOriginalLeafTripleMoment_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    cavityOriginalLeafTripleMoment D s a T i l ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2 *
        finiteCascadeUnweightedBranchSum
          (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) := by
  let B := finiteCascadeUnweightedBranchSum
    (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  calc
    _ ≤ ((observationLeaves (trimRoot T)).map (fun j =>
        ((observationLeaves (trimRoot T)).map (fun _ => B)).sum)).sum := by
      unfold cavityOriginalLeafTripleMoment
      apply List.sum_le_sum
      intro j _
      apply List.sum_le_sum
      intro h _
      exact cavityOriginalLeaf_leaf_triple_cubic hn D s a hq T i l j h
    _ = _ := by
      simp only [sum_constant,observationLeaves_length,leafCount_trimRoot,
        nsmul_eq_mul,pow_two,mul_assoc,B]

end QuantitativeFollowup
