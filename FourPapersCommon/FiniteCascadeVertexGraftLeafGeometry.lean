module
public import FourPapersCommon.FiniteCascadeGraftSpins
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! Actual old and fresh terminal leaves of vertex grafts preserve the
retained spins and their precise common-history levels. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

@[reducible] def finiteCascadeLinearLeaf : (j : ℕ)→ObservationLeaf (finiteCascadeLinearTerminalTree j)
  | 0=>PUnit.unit
  | j+1=>finiteCascadeLinearLeaf j

theorem finiteCascadeLinearLeaf_spin {E S : Type} (j : ℕ)
    (z : Records E S (finiteCascadeLinearTerminalTree j)) :
    observationLeafSpin _ (finiteCascadeLinearLeaf j) z=finiteCascadeLinearRecordSpin j z := by
  induction j with
  | zero=>rfl
  | succ j ih=>exact ih z.2

@[reducible] def finiteCascadeVertexGraftOldLeaf :
    {j : ℕ}→{T : FiniteTerminalGenealogy j}→(v : FiniteCascadeRecordVertex T)→
      ObservationLeaf T→ObservationLeaf (finiteCascadeVertexGraft v)
  | _,_,.root _=>Sum.inl
  | _,_,.child v=>finiteCascadeVertexGraftOldLeaf v
  | _,_,.left v=>Sum.map (finiteCascadeVertexGraftOldLeaf v) id
  | _,_,.right v=>Sum.map id (finiteCascadeVertexGraftOldLeaf v)

@[reducible] def finiteCascadeVertexGraftNewLeaf :
    {j : ℕ}→{T : FiniteTerminalGenealogy j}→(v : FiniteCascadeRecordVertex T)→
      ObservationLeaf (finiteCascadeVertexGraft v)
  | j,_,.root _=>Sum.inr (finiteCascadeLinearLeaf j)
  | _,_,.child v=>finiteCascadeVertexGraftNewLeaf v
  | _,_,.left v=>Sum.inl (finiteCascadeVertexGraftNewLeaf v)
  | _,_,.right v=>Sum.inr (finiteCascadeVertexGraftNewLeaf v)

theorem finiteCascadeVertexGraftOldLeaf_spin {E S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf T,
    ∀z : Records E S (finiteCascadeVertexGraft v),
      observationLeafSpin _ (finiteCascadeVertexGraftOldLeaf v i) z=
        observationLeafSpin T i (finiteCascadeGraftRecordExtract v z).1 := by
  induction v with
  | root T=>intros; rfl
  | child v ih=>intro i z; exact ih i z.2
  | left v ih=>intro i z; cases i with
    | inl i=>exact ih i z.1
    | inr i=>rfl
  | right v ih=>intro i z; cases i with
    | inl i=>rfl
    | inr i=>exact ih i z.2

theorem finiteCascadeVertexGraftNewLeaf_spin {E S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (z : Records E S (finiteCascadeVertexGraft v)) :
    observationLeafSpin _ (finiteCascadeVertexGraftNewLeaf v) z=
      (finiteCascadeGraftRecordExtract v z).2 := by
  induction v with
  | root T=>exact finiteCascadeLinearLeaf_spin _ z.2
  | child v ih=>exact ih z.2
  | left v ih=>exact ih z.1
  | right v ih=>exact ih z.2

theorem finiteCascadeVertexGraftOldLeaf_commonLevel {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i l : ObservationLeaf T,
    observationCommonLevel _ (finiteCascadeVertexGraftOldLeaf v i)
      (finiteCascadeVertexGraftOldLeaf v l)=observationCommonLevel T i l := by
  induction v with
  | root T=>intros; rfl
  | child v ih=>exact ih
  | left v ih=>intro i l; cases i with
    | inl i=>cases l with
      | inl l=>exact ih i l
      | inr l=>rfl
    | inr i=>cases l <;>rfl
  | right v ih=>intro i l; cases i with
    | inl i=>cases l <;>rfl
    | inr i=>cases l with
      | inl l=>rfl
      | inr l=>exact ih i l

theorem finiteCascadeVertexGraftOldNewLeaf_commonLevel {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf T,
    observationCommonLevel _ (finiteCascadeVertexGraftOldLeaf v i)
      (finiteCascadeVertexGraftNewLeaf v)=finiteCascadeCommonPathDepth T (observationLeafVertex T i) v := by
  induction v with
  | root T=>
      intro i
      cases T with
      | leaf=>rfl
      | advance T=>rfl
      | fork T U=>cases i <;>rfl
  | child v ih=>exact ih
  | left v ih=>intro i; cases i with
    | inl i=>exact ih i
    | inr i=>rfl
  | right v ih=>intro i; cases i with
    | inl i=>rfl
    | inr i=>exact ih i

theorem finiteCascadeVertexGraftNewLeaf_vertex_commonPathDepth {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀w : FiniteCascadeRecordVertex T,
    finiteCascadeCommonPathDepth (finiteCascadeVertexGraft v)
      (observationLeafVertex _ (finiteCascadeVertexGraftNewLeaf v)) (finiteCascadeGraftVertexEmbed v w)=
        finiteCascadeCommonPathDepth T v w := by
  induction v with
  | root T=>intro w; cases T <;>cases w <;>rfl
  | child v ih=>intro w; cases w with
    | root T=>rfl
    | child w=>exact ih w
  | left v ih=>intro w; cases w with
    | root T=>rfl
    | left w=>exact ih w
    | right w=>rfl
  | right v ih=>intro w; cases w with
    | root T=>rfl
    | left w=>rfl
    | right w=>exact ih w

@[reducible] def finiteCascadeCrossGraftOldLeaf {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (i : ObservationLeaf T) :
    ObservationLeaf (finiteCascadeCrossVertexGraft v w) :=
  finiteCascadeVertexGraftOldLeaf (finiteCascadeGraftVertexEmbed v w) (finiteCascadeVertexGraftOldLeaf v i)

@[reducible] def finiteCascadeCrossGraftFirstLeaf {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) : ObservationLeaf (finiteCascadeCrossVertexGraft v w) :=
  finiteCascadeVertexGraftOldLeaf (finiteCascadeGraftVertexEmbed v w) (finiteCascadeVertexGraftNewLeaf v)

@[reducible] def finiteCascadeCrossGraftSecondLeaf {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) : ObservationLeaf (finiteCascadeCrossVertexGraft v w) :=
  finiteCascadeVertexGraftNewLeaf (finiteCascadeGraftVertexEmbed v w)

theorem finiteCascadeCrossGraftOldLeaf_spin {E S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (i : ObservationLeaf T)
    (z : Records E S (finiteCascadeCrossVertexGraft v w)) :
    observationLeafSpin _ (finiteCascadeCrossGraftOldLeaf v w i) z=
      observationLeafSpin T i (finiteCascadeCrossGraftExtract v w z).1 := by
  simp only [finiteCascadeCrossGraftOldLeaf,finiteCascadeVertexGraftOldLeaf_spin,finiteCascadeCrossGraftExtract]

theorem finiteCascadeCrossGraftFirstLeaf_spin {E S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (z : Records E S (finiteCascadeCrossVertexGraft v w)) :
    observationLeafSpin _ (finiteCascadeCrossGraftFirstLeaf v w) z=(finiteCascadeCrossGraftExtract v w z).2.1 := by
  simp only [finiteCascadeCrossGraftFirstLeaf,finiteCascadeVertexGraftOldLeaf_spin,
    finiteCascadeVertexGraftNewLeaf_spin,finiteCascadeCrossGraftExtract]

theorem finiteCascadeCrossGraftSecondLeaf_spin {E S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (z : Records E S (finiteCascadeCrossVertexGraft v w)) :
    observationLeafSpin _ (finiteCascadeCrossGraftSecondLeaf v w) z=(finiteCascadeCrossGraftExtract v w z).2.2 := by
  simp only [finiteCascadeCrossGraftSecondLeaf,finiteCascadeVertexGraftNewLeaf_spin,finiteCascadeCrossGraftExtract]

theorem finiteCascadeCrossGraftOldLeaf_commonLevel {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (i l : ObservationLeaf T) :
    observationCommonLevel _ (finiteCascadeCrossGraftOldLeaf v w i) (finiteCascadeCrossGraftOldLeaf v w l)=
      observationCommonLevel T i l := by
  simp only [finiteCascadeCrossGraftOldLeaf,finiteCascadeVertexGraftOldLeaf_commonLevel]

theorem finiteCascadeCrossGraftFresh_commonLevel {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) :
    observationCommonLevel _ (finiteCascadeCrossGraftFirstLeaf v w) (finiteCascadeCrossGraftSecondLeaf v w)=
      finiteCascadeCommonPathDepth T v w := by
  rw [finiteCascadeCrossGraftFirstLeaf,finiteCascadeCrossGraftSecondLeaf,
    finiteCascadeVertexGraftOldNewLeaf_commonLevel]
  exact finiteCascadeVertexGraftNewLeaf_vertex_commonPathDepth v w

end FourPapersCommon
