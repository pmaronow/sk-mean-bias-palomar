module
public import FourPapersCommon.FiniteCascadeContinuationGraftLaw
public import FourPapersCommon.FiniteCascadeFuturePairTree
public import FourPapersCommon.FiniteCascadeGaussianGraft

@[expose] public section

/-! A future conditional pair is realized by a genuine enlarged tree.
The old genealogy and the common future continuation are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def finiteCascadeFutureVertexGraft {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (p : ℕ) : FiniteTerminalGenealogy j :=
  finiteCascadeContinuationGraft (fun d=>(finiteCascadeFuturePairTree p d).tree) v

@[reducible] def finiteCascadeFutureGraftExtract {E S : Type} {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ) :
    Records E S (finiteCascadeFutureVertexGraft v p)→Records E S T×(S×S) :=
  finiteCascadeContinuationExtract (fun d=>(finiteCascadeFuturePairTree p d).tree)
    (fun d=>(finiteCascadeFuturePairTree p d).spins) v

theorem measurable_finiteCascadeFutureGraftExtract {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (p : ℕ) :
    Measurable (finiteCascadeFutureGraftExtract (E:=E) (S:=S) v p) :=
  measurable_finiteCascadeContinuationExtract _ _
    (fun d=>(finiteCascadeFuturePairTree p d).measurable_spins) v

theorem finiteCascadeFutureVertexGraft_leafCount {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (p : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeFutureVertexGraft v p))=
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  rw [finiteCascadeFutureVertexGraft,finiteCascadeContinuationGraft_leafCount,
    observationPairTree_leafCount]

theorem finiteCascadeFutureVertexGraft_branchSum (χ : ℕ→ℝ) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ) (hp : p≤v.depth) :
    finiteCascadeUnweightedBranchSum χ (finiteCascadeFutureVertexGraft v p)=
      finiteCascadeUnweightedBranchSum χ T+χ v.depth+χ p := by
  rw [finiteCascadeFutureVertexGraft,finiteCascadeContinuationGraft_branchSum,
    observationPairTree_branchSum,finiteCascadeFuturePairTree_split p v.depth hp]

variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeFutureVertexGraft_kernel (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (hp : p≤v.depth) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeFutureVertexGraft v p)).map
      (finiteCascadeFutureGraftExtract v p)=
      finiteCascadeTreeRecordKernel V a L T ⊗ₖ finiteCascadeFuturePairKernel V a L v p := by
  rw [finiteCascadeFutureGraftExtract,
    finiteCascadeContinuationGraft_kernel V a ha L _ _
      (fun d=>(finiteCascadeFuturePairTree p d).measurable_spins)]
  congr 1
  unfold finiteCascadeContinuationVertexKernel finiteCascadeContinuationKernel
  rw [finiteCascadeFuturePairTree_kernel V a ha L p v.depth hp]
  rfl

theorem finiteCascadeFutureVertexGraft_joint_law (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (hp : p≤v.depth) (μ : Measure (FiniteStateField S)) [SFinite μ] :
    (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L (finiteCascadeFutureVertexGraft v p)).map
      (fun z=>((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2))=
      finiteCascadeFutureMarkedLaw V a L v p (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L T) := by
  rw [finiteCascadeFutureGraftExtract,
    finiteCascadeContinuationGraft_joint_law V a ha L _ _
      (fun d=>(finiteCascadeFuturePairTree p d).measurable_spins)]
  unfold finiteCascadeContinuationMarkedLaw finiteCascadeFutureMarkedLaw
  congr 1
  unfold finiteCascadeContinuationVertexKernel finiteCascadeContinuationKernel
  rw [finiteCascadeFuturePairTree_kernel V a ha L p v.depth hp]
  rfl

variable {J : Type} [Fintype J]
theorem finiteCascadeGaussianJointLaw_future_graft (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀r,0≤a r) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (hp : p≤v.depth) (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s (finiteCascadeFutureVertexGraft v p) R H).map
      (fun z=>((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2))=
      finiteCascadeFutureMarkedLaw V a L v p (finiteCascadeTreeGaussianJointLaw V a L s T R H) := by
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  exact finiteCascadeFutureVertexGraft_joint_law V a ha L v p hp _

end FourPapersCommon
