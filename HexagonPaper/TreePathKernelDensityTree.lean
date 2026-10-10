module
public import HexagonPaper.TreePathKernelDensityReindex
public import FourPapersCommon.FiniteCascadeTreeRecords

@[expose] public section

/-! Finite genealogies carrying complete edge paths, with conditionally
independent branches. The construction is on arbitrary measurable path
spaces. Density identification is proved by structural recursion from
individual edge and leaf density identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HexagonPaper
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S]

@[reducible] def treePathRecordKernel (leaf : Kernel X S) (edge : ℕ → Kernel X Y)
    (endpoint : ℕ → Y → X) (he : ∀j, Measurable (endpoint j)) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Kernel X (Records Y S T)
  | _, .leaf => leaf
  | _, @FiniteTerminalGenealogy.advance j T =>
      edge j ⊗ₖ (treePathRecordKernel leaf edge endpoint he T).comap
        (fun p : X×Y => endpoint j p.2) ((he j).comp measurable_snd)
  | _, .fork T U => treePathRecordKernel leaf edge endpoint he T ×ₖ
      treePathRecordKernel leaf edge endpoint he U

 theorem isSFiniteKernel_treePathRecordKernel (leaf : Kernel X S) (edge : ℕ → Kernel X Y)
    (endpoint : ℕ → Y → X) (he : ∀j, Measurable (endpoint j))
    [hLeaf : IsSFiniteKernel leaf] [hEdge : ∀j, IsSFiniteKernel (edge j)]
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsSFiniteKernel (treePathRecordKernel leaf edge endpoint he T) := by
  induction T with
  | leaf => exact hLeaf
  | @advance j T ih =>
      haveI := ih
      haveI := hEdge j
      change IsSFiniteKernel (_ ⊗ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsSFiniteKernel (_ ×ₖ _)
      infer_instance

attribute [local instance] isSFiniteKernel_treePathRecordKernel

 theorem isMarkovKernel_treePathRecordKernel (leaf : Kernel X S) (edge : ℕ → Kernel X Y)
    (endpoint : ℕ → Y → X) (he : ∀j, Measurable (endpoint j))
    (hLeaf : IsMarkovKernel leaf) (hEdge : ∀j, IsMarkovKernel (edge j))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsMarkovKernel (treePathRecordKernel leaf edge endpoint he T) := by
  induction T with
  | leaf => exact hLeaf
  | @advance j T ih =>
      haveI := ih
      haveI := hEdge j
      change IsMarkovKernel (_ ⊗ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsMarkovKernel (_ ×ₖ _)
      infer_instance

@[reducible] def treePathLogDensity (leafLog : X → S → ℝ) (edgeLog : ℕ → X → Y → ℝ)
    (endpoint : ℕ → Y → X) : {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      X → Records Y S T → ℝ
  | _, .leaf => leafLog
  | _, @FiniteTerminalGenealogy.advance j T => fun x z =>
      edgeLog j x z.1 + treePathLogDensity leafLog edgeLog endpoint T (endpoint j z.1) z.2
  | _, .fork T U => fun x z => treePathLogDensity leafLog edgeLog endpoint T x z.1 +
      treePathLogDensity leafLog edgeLog endpoint U x z.2

 theorem measurable_treePathLogDensity (leafLog : X → S → ℝ) (edgeLog : ℕ → X → Y → ℝ)
    (endpoint : ℕ → Y → X) (he : ∀j, Measurable (endpoint j))
    (hl : Measurable (Function.uncurry leafLog))
    (hf : ∀j, Measurable (Function.uncurry (edgeLog j)))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (Function.uncurry (treePathLogDensity leafLog edgeLog endpoint T)) := by
  induction T with
  | leaf => exact hl
  | @advance j T ih =>
      exact ((hf j).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
        (ih.comp (((he j).comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)))
  | fork T U ihT ihU =>
      exact (ihT.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
        (ihU.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

 theorem treePathRecordKernel_exp_density
    (leaf leafRef : Kernel X S) (edge edgeRef : ℕ → Kernel X Y)
    (endpoint : ℕ → Y → X) (he : ∀j, Measurable (endpoint j))
    (leafLog : X → S → ℝ) (edgeLog : ℕ → X → Y → ℝ)
    (hl : Measurable (Function.uncurry leafLog))
    (hf : ∀j, Measurable (Function.uncurry (edgeLog j)))
    [hLeafRef : IsSFiniteKernel leafRef] [hEdgeRef : ∀j, IsSFiniteKernel (edgeRef j)]
    (hLeaf : leaf = leafRef.withDensity (fun x σ => ENNReal.ofReal (Real.exp (leafLog x σ))))
    (hEdge : ∀j, edge j = (edgeRef j).withDensity (fun x p => ENNReal.ofReal (Real.exp (edgeLog j x p))))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    treePathRecordKernel leaf edge endpoint he T =
      (treePathRecordKernel leafRef edgeRef endpoint he T).withDensity (fun x z =>
        ENNReal.ofReal (Real.exp (treePathLogDensity leafLog edgeLog endpoint T x z))) := by
  induction T with
  | leaf => exact hLeaf
  | @advance j T ih =>
      haveI := hEdgeRef j
      haveI := isSFiniteKernel_treePathRecordKernel leafRef edgeRef endpoint he T
      change edge j ⊗ₖ (treePathRecordKernel leaf edge endpoint he T).comap _ _ = _
      rw [ih,hEdge j]
      exact treePath_kernel_exp_density_endpoint_compProd (edgeRef j)
        (treePathRecordKernel leafRef edgeRef endpoint he T)
        (fun p : X×Y => endpoint j p.2) ((he j).comp measurable_snd)
        (edgeLog j) (treePathLogDensity leafLog edgeLog endpoint T) (hf j)
        (measurable_treePathLogDensity leafLog edgeLog endpoint he hl hf T)
  | fork T U ihT ihU =>
      haveI := isSFiniteKernel_treePathRecordKernel leafRef edgeRef endpoint he T
      haveI := isSFiniteKernel_treePathRecordKernel leafRef edgeRef endpoint he U
      change _ ×ₖ _ = _
      rw [ihT,ihU]
      exact treePath_kernel_exp_density_prod
        (treePathRecordKernel leafRef edgeRef endpoint he T)
        (treePathRecordKernel leafRef edgeRef endpoint he U)
        (treePathLogDensity leafLog edgeLog endpoint T)
        (treePathLogDensity leafLog edgeLog endpoint U)
        (measurable_treePathLogDensity leafLog edgeLog endpoint he hl hf T)
        (measurable_treePathLogDensity leafLog edgeLog endpoint he hl hf U)

end HexagonPaper
