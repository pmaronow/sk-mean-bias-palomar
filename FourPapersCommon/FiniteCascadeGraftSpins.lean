module
public import FourPapersCommon.FiniteCascadeCrossVertexGraft

@[expose] public section

/-! Extracting the retained and grafted spins depends only on terminal
spins. Thus a marked spin observable is still an actual bounded spin
observable of its enlarged genealogy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

@[reducible] def finiteCascadeLinearTerminalSpin {S : Type} :
    (j : ℕ) → FiniteCascadeGenealogy.Samples S
      (asGenealogy (finiteCascadeLinearTerminalTree j)) → S
  | 0 => id
  | j+1 => finiteCascadeLinearTerminalSpin j

@[reducible] def finiteCascadeGraftSpinExtract {S : Type} :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → (v : FiniteCascadeRecordVertex T) →
      FiniteCascadeGenealogy.Samples S (asGenealogy (finiteCascadeVertexGraft v)) →
        FiniteCascadeGenealogy.Samples S (asGenealogy T) × S
  | j, _, .root _ => Prod.map id (finiteCascadeLinearTerminalSpin j)
  | _, _, .child v => finiteCascadeGraftSpinExtract v
  | _, _, .left v => fun z => (((finiteCascadeGraftSpinExtract v z.1).1,z.2),
      (finiteCascadeGraftSpinExtract v z.1).2)
  | _, _, .right v => fun z => ((z.1,(finiteCascadeGraftSpinExtract v z.2).1),
      (finiteCascadeGraftSpinExtract v z.2).2)

private theorem linear_records_spin {E S : Type} (j : ℕ)
    (z : Records E S (finiteCascadeLinearTerminalTree j)) :
    finiteCascadeLinearRecordSpin j z =
      finiteCascadeLinearTerminalSpin j (spins (finiteCascadeLinearTerminalTree j) z) := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih z.2

theorem finiteCascadeGraftRecordExtract_spins {E S : Type}
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeVertexGraft v)) :
    finiteCascadeGraftSpinExtract v (spins (finiteCascadeVertexGraft v) z) =
      (spins T (finiteCascadeGraftRecordExtract v z).1,
        (finiteCascadeGraftRecordExtract v z).2) := by
  induction v with
  | root T => exact Prod.ext rfl (linear_records_spin _ z.2).symm
  | child v ih => exact ih z.2
  | @left j T U v ih =>
    simpa only [finiteCascadeGraftSpinExtract, finiteCascadeVertexGraft, spins,
      finiteCascadeGraftRecordExtract, Prod.map_apply', Prod.map_fst, Prod.map_snd] using
      congrArg (fun p : FiniteCascadeGenealogy.Samples S (asGenealogy T) × S =>
        ((p.1,spins U z.2),p.2)) (ih z.1)
  | @right j T U v ih =>
    simpa only [finiteCascadeGraftSpinExtract, finiteCascadeVertexGraft, spins,
      finiteCascadeGraftRecordExtract, Prod.map_apply', Prod.map_fst, Prod.map_snd] using
      congrArg (fun p : FiniteCascadeGenealogy.Samples S (asGenealogy U) × S =>
        ((spins T z.1,p.1),p.2)) (ih z.2)

@[reducible] def finiteCascadeCrossGraftSpinExtract {S : Type}
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : FiniteCascadeGenealogy.Samples S (asGenealogy (finiteCascadeCrossVertexGraft v w))) :
    FiniteCascadeGenealogy.Samples S (asGenealogy T) × (S × S) :=
  let z' := finiteCascadeGraftSpinExtract (finiteCascadeGraftVertexEmbed v w) z
  let z'' := finiteCascadeGraftSpinExtract v z'.1
  (z''.1,(z''.2,z'.2))

theorem finiteCascadeCrossGraftRecordExtract_spins {E S : Type}
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossVertexGraft v w)) :
    finiteCascadeCrossGraftSpinExtract v w (spins (finiteCascadeCrossVertexGraft v w) z) =
      (spins T (finiteCascadeCrossGraftExtract v w z).1,
        (finiteCascadeCrossGraftExtract v w z).2) := by
  unfold finiteCascadeCrossGraftSpinExtract finiteCascadeCrossGraftExtract
  rw [finiteCascadeGraftRecordExtract_spins]
  dsimp only
  rw [finiteCascadeGraftRecordExtract_spins]

end FourPapersCommon
