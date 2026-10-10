module
public import FourPapersCommon.FiniteCascadeVertexGraft

@[expose] public section

/-! An actual full continuation tree can be grafted at any retained
vertex. Its records are sampled conditionally on that vertex field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 800000

@[reducible] def finiteCascadeContinuationGraft (U : (j : ℕ) → FiniteTerminalGenealogy j) : {j : ℕ} → {T : FiniteTerminalGenealogy j} →
    FiniteCascadeRecordVertex T → FiniteTerminalGenealogy j
  | j, T, .root _ => .fork T (U j)
  | _, _, .child v => .advance (finiteCascadeContinuationGraft U v)
  | _, _, @FiniteCascadeRecordVertex.left j T R v => .fork (finiteCascadeContinuationGraft U v) R
  | _, _, @FiniteCascadeRecordVertex.right j T R v => .fork T (finiteCascadeContinuationGraft U v)

theorem finiteCascadeContinuationGraft_leafCount (U : (j : ℕ) → FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeContinuationGraft U v))=
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+
      FiniteCascadeGenealogy.leafCount (asGenealogy (U v.depth)) := by
  induction v with
  | root T =>
    simp only [finiteCascadeContinuationGraft, asGenealogy, FiniteCascadeGenealogy.leafCount,
      FiniteCascadeRecordVertex.depth]
  | child v ih => exact ih
  | left v ih =>
    simp only [finiteCascadeContinuationGraft, asGenealogy, FiniteCascadeGenealogy.leafCount,
      FiniteCascadeRecordVertex.depth] at *
    omega
  | right v ih =>
    simp only [finiteCascadeContinuationGraft, asGenealogy, FiniteCascadeGenealogy.leafCount,
      FiniteCascadeRecordVertex.depth] at *
    omega

theorem finiteCascadeContinuationGraft_branchSum (U : (j : ℕ) → FiniteTerminalGenealogy j) (χ : ℕ → ℝ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    finiteCascadeUnweightedBranchSum χ (finiteCascadeContinuationGraft U v)=
      finiteCascadeUnweightedBranchSum χ T+χ v.depth+finiteCascadeUnweightedBranchSum χ (U v.depth) := by
  induction v with
  | root T =>
    simp only [finiteCascadeContinuationGraft, finiteCascadeUnweightedBranchSum,
      FiniteCascadeRecordVertex.depth]
    ring
  | child v ih => exact ih
  | left v ih =>
    simp only [finiteCascadeContinuationGraft, finiteCascadeUnweightedBranchSum,
      FiniteCascadeRecordVertex.depth, ih]
    ring
  | right v ih =>
    simp only [finiteCascadeContinuationGraft, finiteCascadeUnweightedBranchSum,
      FiniteCascadeRecordVertex.depth, ih]
    ring

@[reducible] def finiteCascadeContinuationExtract {E S A : Type}
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records E S (U j) → A) :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → (v : FiniteCascadeRecordVertex T) →
      Records E S (finiteCascadeContinuationGraft U v) → Records E S T×A
  | j, _, .root _ => fun z=>(z.1, extract j z.2)
  | _, _, .child v => fun z=>((z.1, (finiteCascadeContinuationExtract U extract v z.2).1),
      (finiteCascadeContinuationExtract U extract v z.2).2)
  | _, _, .left v => fun z=>(((finiteCascadeContinuationExtract U extract v z.1).1, z.2),
      (finiteCascadeContinuationExtract U extract v z.1).2)
  | _, _, .right v => fun z=>((z.1, (finiteCascadeContinuationExtract U extract v z.2).1),
      (finiteCascadeContinuationExtract U extract v z.2).2)

theorem measurable_finiteCascadeContinuationExtract {E S A : Type}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records E S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    Measurable (finiteCascadeContinuationExtract (E:=E) (S:=S) U extract v) := by
  induction v with
  | root T =>
    exact measurable_fst.prodMk
      ((he _).comp measurable_snd)
  | child v ih =>
    exact (measurable_fst.prodMk (ih.fst.comp measurable_snd)).prodMk
      (ih.snd.comp measurable_snd)
  | left v ih =>
    exact ((ih.fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (ih.snd.comp measurable_fst)
  | right v ih =>
    exact (measurable_fst.prodMk (ih.fst.comp measurable_snd)).prodMk
      (ih.snd.comp measurable_snd)


end FourPapersCommon
