module
public import FourPapersCommon.FiniteCascadeTerminalVertices
public import FourPapersCommon.FiniteCascadeReferenceTerminalProjection
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! The true terminal-vertex list has fixed leaf indices. This permits
finite streaming sums to be integrated without sample-dependent indices. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 900000

@[reducible] def observationLeaves : {j : ℕ} → (T : FiniteTerminalGenealogy j) → List (ObservationLeaf T)
  | _,.leaf => [()]
  | _,.advance T => observationLeaves T
  | _,.fork T U => (observationLeaves T).map Sum.inl ++ (observationLeaves U).map Sum.inr

theorem observationLeaves_length {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (observationLeaves T).length=FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      simp only [observationLeaves,List.length_append,List.length_map,asGenealogy,FiniteCascadeGenealogy.leafCount]
      rw [ihT,ihU]

theorem finiteCascadeTerminalVertices_eq_observationLeaves {E S : Type} [Fintype S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records E S T) :
    finiteCascadeTerminalVertices T (finiteCascadeRecordTerminalSpins T z)=
      (observationLeaves T).map (fun i => (observationLeafVertex T i,observationLeafSpin T i z)) := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      simpa only [finiteCascadeTerminalVertices,finiteCascadeRecordTerminalSpins,observationLeaves,
        List.map_map,Function.comp_def,observationLeafVertex,observationLeafSpin] using
        congrArg (List.map (fun c => (FiniteCascadeRecordVertex.child c.1,c.2))) (ih z.2)
  | fork T U ihT ihU =>
      simp only [finiteCascadeTerminalVertices,finiteCascadeRecordTerminalSpins,Prod.map_fst,Prod.map_snd,ihT,ihU,
        observationLeaves,List.map_append,List.map_map,Function.comp_def,observationLeafVertex,
        observationLeafSpin,Sum.elim_inl,Sum.elim_inr]

end FourPapersCommon
