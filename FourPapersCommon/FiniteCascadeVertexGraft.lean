module
public import FourPapersCommon.FiniteCascadeChargeLevels
public import FourPapersCommon.FiniteCascadePruning

@[expose] public section

/-! Grafting a genuine full terminal continuation at a recorded vertex.
The old leaves and fields are retained; the only new branch level is the
level of that vertex. These are actual tree operations, not marginal-law
assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

@[reducible] def finiteCascadeLinearTerminalTree : (j : ℕ) → FiniteTerminalGenealogy j
  | 0 => .leaf
  | j+1 => .advance (finiteCascadeLinearTerminalTree j)

theorem finiteCascadeLinearTerminalTree_leafCount (j : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeLinearTerminalTree j))=1 := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem finiteCascadeLinearTerminalTree_branchSum (χ : ℕ → ℝ) (j : ℕ) :
    finiteCascadeUnweightedBranchSum χ (finiteCascadeLinearTerminalTree j)=0 := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

@[reducible] def finiteCascadeVertexGraft : {j : ℕ} → {T : FiniteTerminalGenealogy j} →
    FiniteCascadeRecordVertex T → FiniteTerminalGenealogy j
  | j, T, .root _ => .fork T (finiteCascadeLinearTerminalTree j)
  | _, _, .child v => .advance (finiteCascadeVertexGraft v)
  | _, _, @FiniteCascadeRecordVertex.left j T U v => .fork (finiteCascadeVertexGraft v) U
  | _, _, @FiniteCascadeRecordVertex.right j T U v => .fork T (finiteCascadeVertexGraft v)

def finiteCascadeVertexGraft_pruning {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) :
    FiniteCascadePruning (asGenealogy (finiteCascadeVertexGraft v)) (asGenealogy T) := by
  induction v with
  | root T => exact .left _ (.refl _)
  | child v ih => exact .advance ih
  | left v ih => exact .fork ih (.refl _)
  | right v ih => exact .fork (.refl _) ih

theorem finiteCascadeVertexGraft_leafCount {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeVertexGraft v))=
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+1 := by
  induction v with
  | root T =>
    simp only [finiteCascadeVertexGraft, asGenealogy, FiniteCascadeGenealogy.leafCount,
      finiteCascadeLinearTerminalTree_leafCount]
  | child v ih => exact ih
  | left v ih =>
    simp only [finiteCascadeVertexGraft, asGenealogy, FiniteCascadeGenealogy.leafCount]
    omega
  | right v ih =>
    simp only [finiteCascadeVertexGraft, asGenealogy, FiniteCascadeGenealogy.leafCount]
    omega

theorem finiteCascadeVertexGraft_branchSum (χ : ℕ → ℝ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    finiteCascadeUnweightedBranchSum χ (finiteCascadeVertexGraft v)=
      finiteCascadeUnweightedBranchSum χ T+χ v.depth := by
  induction v with
  | root T =>
    simp only [finiteCascadeVertexGraft, finiteCascadeUnweightedBranchSum,
      finiteCascadeLinearTerminalTree_branchSum, FiniteCascadeRecordVertex.depth, add_zero]
  | child v ih => exact ih
  | left v ih =>
    simp only [finiteCascadeVertexGraft, finiteCascadeUnweightedBranchSum,
      FiniteCascadeRecordVertex.depth, ih]
    ring
  | right v ih =>
    simp only [finiteCascadeVertexGraft, finiteCascadeUnweightedBranchSum,
      FiniteCascadeRecordVertex.depth, ih]
    ring

@[reducible] def finiteCascadeLinearRecordSpin {E S : Type} :
    (j : ℕ) → Records E S (finiteCascadeLinearTerminalTree j) → S
  | 0 => id
  | j+1 => finiteCascadeLinearRecordSpin j ∘ Prod.snd

theorem measurable_finiteCascadeLinearRecordSpin {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] (j : ℕ) :
    Measurable (finiteCascadeLinearRecordSpin (E:=E) (S:=S) j) := by
  induction j with
  | zero => exact measurable_id
  | succ j ih => exact ih.comp measurable_snd

@[reducible] def finiteCascadeGraftRecordExtract {E S : Type} :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → (v : FiniteCascadeRecordVertex T) →
      Records E S (finiteCascadeVertexGraft v) → Records E S T×S
  | j, _, .root _ => fun z=>(z.1, finiteCascadeLinearRecordSpin j z.2)
  | _, _, .child v => fun z=>((z.1, (finiteCascadeGraftRecordExtract v z.2).1),
      (finiteCascadeGraftRecordExtract v z.2).2)
  | _, _, .left v => fun z=>(((finiteCascadeGraftRecordExtract v z.1).1, z.2),
      (finiteCascadeGraftRecordExtract v z.1).2)
  | _, _, .right v => fun z=>((z.1, (finiteCascadeGraftRecordExtract v z.2).1),
      (finiteCascadeGraftRecordExtract v z.2).2)

theorem measurable_finiteCascadeGraftRecordExtract {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    Measurable (finiteCascadeGraftRecordExtract (E:=E) (S:=S) v) := by
  induction v with
  | root T =>
    exact measurable_fst.prodMk
      ((measurable_finiteCascadeLinearRecordSpin _).comp measurable_snd)
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
