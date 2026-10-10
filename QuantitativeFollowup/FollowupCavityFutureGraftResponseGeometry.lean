module
public import QuantitativeFollowup.FollowupCavityFutureVertexGraftLaw
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry
public import FourPapersCommon.FiniteCascadeFuturePairSpins
public import FourPapersCommon.FiniteObservationTerminalProjection

@[expose] public section

/-! Future-graft extraction is a fixed map of terminal spins. In particular,
the physical observable used in a second streaming passage has no hidden
dependence on the interpolation parameter through retained fields. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem response_continuationRecords_treeMap {E E' S : Type}
    (f : E→E') (U : (j : ℕ)→FiniteTerminalGenealogy j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeContinuationGraft U v)) :
    finiteCascadeContinuationRecords U v (observationTreeMap f _ z)=
      (observationTreeMap f T (finiteCascadeContinuationRecords U v z).1,
        observationTreeMap f (U v.depth) (finiteCascadeContinuationRecords U v z).2) := by
  induction v with
  | root T => rfl
  | child v ih =>
      simp only [finiteCascadeContinuationRecords,observationTreeMap,
        Prod.map_apply,Prod.map_fst,Prod.map_snd,FiniteCascadeRecordVertex.depth,ih]
  | left v ih =>
      simp only [finiteCascadeContinuationRecords,observationTreeMap,
        Prod.map_apply,Prod.map_fst,Prod.map_snd,FiniteCascadeRecordVertex.depth,ih]
  | right v ih =>
      simp only [finiteCascadeContinuationRecords,observationTreeMap,
        Prod.map_apply,Prod.map_fst,Prod.map_snd,FiniteCascadeRecordVertex.depth,ih]

private theorem response_pairSpins_treeMap {E E' S : Type} (f : E→E') {d : ℕ}
    (P : ObservationPairTree d) (z : Records E S P.tree) :
    P.spins (observationTreeMap f P.tree z)=P.spins z := by
  rw [observationPair_spins_eq_leaf_pair,observationPair_spins_eq_leaf_pair,
    observationLeafSpin_treeMap,observationLeafSpin_treeMap]

theorem cavityFutureGraftExtract_treeMap {E E' S : Type} (f : E→E')
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (z : Records E S (finiteCascadeFutureVertexGraft v p)) :
    finiteCascadeFutureGraftExtract v p (observationTreeMap f _ z)=
      (observationTreeMap f T (finiteCascadeFutureGraftExtract v p z).1,
        (finiteCascadeFutureGraftExtract v p z).2) := by
  simp only [finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records,
    response_continuationRecords_treeMap,response_pairSpins_treeMap]

def cavityFutureGraftTerminalExtract {S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (σ : TerminalSpins S (finiteCascadeFutureVertexGraft v p)) : TerminalSpins S T×(S×S) :=
  let e:=finiteCascadeFutureGraftExtract v p (observationUnitRecord _ σ)
  (finiteCascadeRecordTerminalSpins T e.1,e.2)

theorem cavityFutureGraftTerminalExtract_record {E S : Type} {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (z : Records E S (finiteCascadeFutureVertexGraft v p)) :
    cavityFutureGraftTerminalExtract v p (finiteCascadeRecordTerminalSpins _ z)=
      (finiteCascadeRecordTerminalSpins T (finiteCascadeFutureGraftExtract v p z).1,
        (finiteCascadeFutureGraftExtract v p z).2) := by
  unfold cavityFutureGraftTerminalExtract
  rw [←observationTreeMap_unit_eq_record,cavityFutureGraftExtract_treeMap]
  dsimp only
  rw [finiteCascadeRecordTerminalSpins_treeMap]

end QuantitativeFollowup
