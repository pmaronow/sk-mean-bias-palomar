module
public import FourPapersCommon.FiniteCascadeContinuationGraft
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! Literal old/new terminal leaves and full dependent record extraction
for continuation grafts, including their true ancestral split levels. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

@[reducible] def finiteCascadeContinuationOldLeaf (U : (j : ℕ)→FiniteTerminalGenealogy j) :
    {j : ℕ}→{T : FiniteTerminalGenealogy j}→(v : FiniteCascadeRecordVertex T)→
      ObservationLeaf T→ObservationLeaf (finiteCascadeContinuationGraft U v)
  | _, _, .root _ => Sum.inl
  | _, _, .child v => finiteCascadeContinuationOldLeaf U v
  | _, _, .left v => Sum.map (finiteCascadeContinuationOldLeaf U v) id
  | _, _, .right v => Sum.map id (finiteCascadeContinuationOldLeaf U v)

@[reducible] def finiteCascadeContinuationNewLeaf (U : (j : ℕ)→FiniteTerminalGenealogy j) :
    {j : ℕ}→{T : FiniteTerminalGenealogy j}→(v : FiniteCascadeRecordVertex T)→
      ObservationLeaf (U v.depth)→ObservationLeaf (finiteCascadeContinuationGraft U v)
  | _, _, .root _ => Sum.inr
  | _, _, .child v => finiteCascadeContinuationNewLeaf U v
  | _, _, .left v => fun i=>Sum.inl (finiteCascadeContinuationNewLeaf U v i)
  | _, _, .right v => fun i=>Sum.inr (finiteCascadeContinuationNewLeaf U v i)

@[reducible] def finiteCascadeContinuationRecords {E S : Type}
    (U : (j : ℕ)→FiniteTerminalGenealogy j) :
    {j : ℕ}→{T : FiniteTerminalGenealogy j}→(v : FiniteCascadeRecordVertex T)→
      Records E S (finiteCascadeContinuationGraft U v)→Records E S T×Records E S (U v.depth)
  | _, _, .root _ => fun z=>(z.1,z.2)
  | _, _, .child v => fun z=>((z.1,(finiteCascadeContinuationRecords U v z.2).1),
      (finiteCascadeContinuationRecords U v z.2).2)
  | _, _, .left v => fun z=>(((finiteCascadeContinuationRecords U v z.1).1,z.2),
      (finiteCascadeContinuationRecords U v z.1).2)
  | _, _, .right v => fun z=>((z.1,(finiteCascadeContinuationRecords U v z.2).1),
      (finiteCascadeContinuationRecords U v z.2).2)

theorem measurable_finiteCascadeContinuationRecords {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) :
    Measurable (finiteCascadeContinuationRecords (E:=E) (S:=S) U v) := by
  induction v with
  | root T => exact measurable_fst.prodMk measurable_snd
  | child v ih =>
      exact (measurable_fst.prodMk (ih.fst.comp measurable_snd)).prodMk
        (ih.snd.comp measurable_snd)
  | left v ih =>
      exact ((ih.fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (ih.snd.comp measurable_fst)
  | right v ih =>
      exact (measurable_fst.prodMk (ih.fst.comp measurable_snd)).prodMk
        (ih.snd.comp measurable_snd)

theorem finiteCascadeContinuationExtract_eq_records {E S A : Type}
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records E S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeContinuationGraft U v)) :
    finiteCascadeContinuationExtract U extract v z=
      ((finiteCascadeContinuationRecords U v z).1,
        extract v.depth (finiteCascadeContinuationRecords U v z).2) := by
  induction v with
  | root T => rfl
  | child v ih =>
      simp only [finiteCascadeContinuationExtract,finiteCascadeContinuationRecords,ih,
        FiniteCascadeRecordVertex.depth]
  | left v ih =>
      simp only [finiteCascadeContinuationExtract,finiteCascadeContinuationRecords,ih,
        FiniteCascadeRecordVertex.depth]
  | right v ih =>
      simp only [finiteCascadeContinuationExtract,finiteCascadeContinuationRecords,ih,
        FiniteCascadeRecordVertex.depth]

theorem finiteCascadeContinuationOldLeaf_spin {E S : Type}
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf T,
    ∀z : Records E S (finiteCascadeContinuationGraft U v),
      observationLeafSpin (finiteCascadeContinuationGraft U v) (finiteCascadeContinuationOldLeaf U v i) z=
        observationLeafSpin T i (finiteCascadeContinuationRecords U v z).1 := by
  induction v with
  | root T => intros; rfl
  | child v ih => intro i z; exact ih i z.2
  | left v ih =>
      intro i z
      cases i with
      | inl i => exact ih i z.1
      | inr i => rfl
  | right v ih =>
      intro i z
      cases i with
      | inl i => rfl
      | inr i => exact ih i z.2

theorem finiteCascadeContinuationNewLeaf_spin {E S : Type}
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf (U v.depth),
    ∀z : Records E S (finiteCascadeContinuationGraft U v),
      observationLeafSpin (finiteCascadeContinuationGraft U v) (finiteCascadeContinuationNewLeaf U v i) z=
        observationLeafSpin (U v.depth) i (finiteCascadeContinuationRecords U v z).2 := by
  induction v with
  | root T => intros; rfl
  | child v ih => intro i z; exact ih i z.2
  | left v ih => intro i z; exact ih i z.1
  | right v ih => intro i z; exact ih i z.2

theorem finiteCascadeContinuationOldLeaf_commonLevel
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i k : ObservationLeaf T,
    observationCommonLevel (finiteCascadeContinuationGraft U v)
      (finiteCascadeContinuationOldLeaf U v i) (finiteCascadeContinuationOldLeaf U v k)=
        observationCommonLevel T i k := by
  induction v with
  | root T => intros; rfl
  | child v ih => exact ih
  | left v ih =>
      intro i k
      cases i with
      | inl i => cases k with
        | inl k => exact ih i k
        | inr k => rfl
      | inr i => cases k with
        | inl k => rfl
        | inr k => rfl
  | right v ih =>
      intro i k
      cases i with
      | inl i => cases k with
        | inl k => rfl
        | inr k => rfl
      | inr i => cases k with
        | inl k => rfl
        | inr k => exact ih i k

theorem finiteCascadeCommonPathDepth_root_right {j : ℕ} (T : FiniteTerminalGenealogy j)
    (w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T w (.root T)=j := by
  cases T <;> cases w <;> rfl

theorem finiteCascadeContinuationOldNewLeaf_commonLevel
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf T,
    ∀k : ObservationLeaf (U v.depth),
    observationCommonLevel (finiteCascadeContinuationGraft U v)
      (finiteCascadeContinuationOldLeaf U v i) (finiteCascadeContinuationNewLeaf U v k)=
        finiteCascadeCommonPathDepth T (observationLeafVertex T i) v := by
  induction v with
  | root T =>
      intro i k
      exact (finiteCascadeCommonPathDepth_root_right T (observationLeafVertex T i)).symm
  | child v ih => exact ih
  | left v ih =>
      intro i k
      cases i with
      | inl i => exact ih i k
      | inr i => rfl
  | right v ih =>
      intro i k
      cases i with
      | inl i => rfl
      | inr i => exact ih i k

theorem finiteCascadeContinuationNewLeaf_commonLevel
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i k : ObservationLeaf (U v.depth),
    observationCommonLevel (finiteCascadeContinuationGraft U v)
      (finiteCascadeContinuationNewLeaf U v i) (finiteCascadeContinuationNewLeaf U v k)=
        observationCommonLevel (U v.depth) i k := by
  induction v with
  | root T => intros; rfl
  | child v ih => exact ih
  | left v ih => exact ih
  | right v ih => exact ih

theorem finiteCascadeContinuationOldLeaf_injective
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : Function.Injective (finiteCascadeContinuationOldLeaf U v) := by
  induction v with
  | root T => exact Sum.inl_injective
  | child v ih => exact ih
  | left v ih =>
      intro i k hik
      cases i <;> cases k <;> simp_all [finiteCascadeContinuationOldLeaf]
      all_goals exact ih hik
  | right v ih =>
      intro i k hik
      cases i <;> cases k <;> simp_all [finiteCascadeContinuationOldLeaf]
      all_goals exact ih hik

theorem finiteCascadeContinuationNewLeaf_injective
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : Function.Injective (finiteCascadeContinuationNewLeaf U v) := by
  induction v with
  | root T => exact Sum.inr_injective
  | child v ih => exact ih
  | left v ih => exact fun _ _ h=>ih (Sum.inl.inj h)
  | right v ih => exact fun _ _ h=>ih (Sum.inr.inj h)

theorem finiteCascadeContinuationOldNewLeaf_ne
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf T,
    ∀k : ObservationLeaf (U v.depth),
      finiteCascadeContinuationOldLeaf U v i≠finiteCascadeContinuationNewLeaf U v k := by
  induction v with
  | root T => intros; simp [finiteCascadeContinuationOldLeaf,finiteCascadeContinuationNewLeaf]
  | child v ih => exact ih
  | left v ih =>
      intro i k
      cases i with
      | inl i => exact fun h=>ih i k (Sum.inl.inj h)
      | inr i => simp [finiteCascadeContinuationOldLeaf,finiteCascadeContinuationNewLeaf]
  | right v ih =>
      intro i k
      cases i with
      | inl i => simp [finiteCascadeContinuationOldLeaf,finiteCascadeContinuationNewLeaf]
      | inr i => exact fun h=>ih i k (Sum.inr.inj h)

theorem finiteCascadeContinuationLeaf_partition
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) :
    ∀l : ObservationLeaf (finiteCascadeContinuationGraft U v),
      (∃i : ObservationLeaf T,finiteCascadeContinuationOldLeaf U v i=l) ∨
      (∃k : ObservationLeaf (U v.depth),finiteCascadeContinuationNewLeaf U v k=l) := by
  induction v with
  | root T =>
      intro l
      cases l with
      | inl i => exact Or.inl ⟨i,rfl⟩
      | inr k => exact Or.inr ⟨k,rfl⟩
  | child v ih => exact ih
  | left v ih =>
      intro l
      cases l with
      | inl l =>
          rcases ih l with ⟨i,hi⟩|⟨k,hk⟩
          · exact Or.inl ⟨Sum.inl i,congrArg Sum.inl hi⟩
          · exact Or.inr ⟨k,congrArg Sum.inl hk⟩
      | inr i => exact Or.inl ⟨Sum.inr i,rfl⟩
  | right v ih =>
      intro l
      cases l with
      | inl i => exact Or.inl ⟨Sum.inl i,rfl⟩
      | inr l =>
          rcases ih l with ⟨i,hi⟩|⟨k,hk⟩
          · exact Or.inl ⟨Sum.inr i,congrArg Sum.inr hi⟩
          · exact Or.inr ⟨k,congrArg Sum.inr hk⟩

end FourPapersCommon
