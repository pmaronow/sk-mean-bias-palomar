module
public import FourPapersCommon.FiniteCascadeVertexGraftLaw
public import FourPapersCommon.FiniteCascadeFutureMarks
public import FourPapersCommon.FiniteObservationTreePairPruning

@[expose] public section

/-! An intermediate split is an actual finite continuation genealogy:
one common chain, followed by two independent terminal chains. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[reducible] def finiteCascadeFuturePairTree (p : ℕ) : (d : ℕ) → ObservationPairTree d
  | 0 => .split 0 false
  | d+1 => if p=d+1 then .split (d+1) false else .advance (finiteCascadeFuturePairTree p d)

theorem finiteCascadeFuturePairTree_split (p d : ℕ) (hp : p≤d) :
    (finiteCascadeFuturePairTree p d).splitLevel=p := by
  induction d with
  | zero =>
      have hp0 : p=0 := by omega
      subst p
      rfl
  | succ d ih =>
      by_cases h:p=d+1
      · subst p
        simp [finiteCascadeFuturePairTree,ObservationPairTree.splitLevel]
      · simp only [finiteCascadeFuturePairTree,if_neg h,ObservationPairTree.splitLevel]
        exact ih (by omega)

theorem observationLinearTree_leafCount (d : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationLinearTree d))=1 := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem observationLinearTree_branchSum (χ : ℕ→ℝ) (d : ℕ) :
    finiteCascadeUnweightedBranchSum χ (observationLinearTree d)=0 := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem observationPairTree_leafCount {d : ℕ} (P : ObservationPairTree d) :
    FiniteCascadeGenealogy.leafCount (asGenealogy P.tree)=2 := by
  induction P with
  | split d reverse =>
      change FiniteCascadeGenealogy.leafCount (asGenealogy (observationLinearTree d))+
        FiniteCascadeGenealogy.leafCount (asGenealogy (observationLinearTree d))=2
      rw [observationLinearTree_leafCount]
  | advance P ih => exact ih

theorem observationPairTree_branchSum (χ : ℕ→ℝ) {d : ℕ} (P : ObservationPairTree d) :
    finiteCascadeUnweightedBranchSum χ P.tree=χ P.splitLevel := by
  induction P with
  | split d reverse =>
      change finiteCascadeUnweightedBranchSum χ (observationLinearTree d)+
        finiteCascadeUnweightedBranchSum χ (observationLinearTree d)+χ d=χ d
      rw [observationLinearTree_branchSum]
      ring
  | advance P ih => exact ih

variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeObservationLinearKernel_spin (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    (finiteCascadeTreeRecordKernel V a L (observationLinearTree j)).map
      (observationLinearSpin j) = finiteStateCascadeGibbsKernel V a L j := by
  induction j with
  | zero =>
    simp only [observationLinearTree, finiteCascadeTreeRecordKernel,
      observationLinearSpin, Kernel.map_id, finiteStateCascadeGibbsKernel,
      finiteStateCascadeFieldKernel, sourceKernelLaw, Kernel.comp_id]
  | succ j ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree j)
    change ((_ ×ₖ _) ∘ₖ _).map (observationLinearSpin j ∘ Prod.snd) = _
    rw [Kernel.map_comp, Kernel.map_comp_right _ measurable_snd
      (measurable_observationLinearSpin j), ←Kernel.snd_eq, Kernel.snd_prod, ih,
      finiteStateCascadeGibbsKernel_succ]

theorem finiteCascadeObservationPairKernel (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {d : ℕ} (P : ObservationPairTree d) :
    (finiteCascadeTreeRecordKernel V a L P.tree).map P.spins=
      ((finiteStateCascadeGibbsKernel V a L P.splitLevel) ×ₖ
        finiteStateCascadeGibbsKernel V a L P.splitLevel) ∘ₖ
          sourceKernelLaw (fun r=>finiteStateGaussianCascadeKernel a L
            (gtStateLogPartition V) (P.splitLevel+r)) (d-P.splitLevel) := by
  induction P with
  | split d reverse =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree d)
      haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L d
      have hlin:=finiteCascadeObservationLinearKernel_spin V a ha L d
      cases reverse with
      | false =>
          change (_ ×ₖ _).map (Prod.map (observationLinearSpin (E:=FiniteStateField S) (S:=S) d)
            (observationLinearSpin (E:=FiniteStateField S) (S:=S) d))=_
          rw [←Kernel.map_prod_map _ _ (measurable_observationLinearSpin d)
            (measurable_observationLinearSpin d),hlin]
          simp only [Nat.sub_self,sourceKernelLaw,Kernel.comp_id]
      | true =>
          change (_ ×ₖ _).map (Prod.swap ∘ Prod.map (observationLinearSpin (E:=FiniteStateField S) (S:=S) d)
            (observationLinearSpin (E:=FiniteStateField S) (S:=S) d))=_
          rw [Kernel.map_comp_right _ ((measurable_observationLinearSpin d).prodMap
            (measurable_observationLinearSpin d)) measurable_swap,
            ←Kernel.map_prod_map _ _ (measurable_observationLinearSpin d)
              (measurable_observationLinearSpin d),hlin,Kernel.map_prod_swap]
          simp only [Nat.sub_self,sourceKernelLaw,Kernel.comp_id]
  | @advance d P ih =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L P.tree
      change (((Kernel.id ×ₖ finiteCascadeTreeRecordKernel V a L P.tree) ∘ₖ
        finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) d).map
        (P.spins ∘ Prod.snd))=_
      rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd P.measurable_spins,
        ←Kernel.snd_eq,Kernel.snd_prod,ih,Kernel.comp_assoc]
      simp only [ObservationPairTree.splitLevel]
      rw [Nat.succ_sub P.splitLevel_le,sourceKernelLaw,Nat.add_sub_of_le P.splitLevel_le]

theorem finiteCascadeFuturePairTree_kernel (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (p d : ℕ) (hp : p≤d) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeFuturePairTree p d).tree).map
      (finiteCascadeFuturePairTree p d).spins=
      ((finiteStateCascadeGibbsKernel V a L p) ×ₖ finiteStateCascadeGibbsKernel V a L p) ∘ₖ
        sourceKernelLaw (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r)) (d-p) := by
  rw [finiteCascadeObservationPairKernel V a ha L,finiteCascadeFuturePairTree_split p d hp]

end FourPapersCommon
