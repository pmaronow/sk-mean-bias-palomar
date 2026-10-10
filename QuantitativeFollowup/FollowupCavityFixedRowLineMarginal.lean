module
public import QuantitativeFollowup.FollowupCavityFixedRowDefinitions
public import FourPapersCommon.FiniteCascadeFuturePairTree

@[expose] public section

/-! Exact field marginal of the genuine full linear recorded path. The
normalized continuation below the selected field has total mass one. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon SpinGlass.AT OverlapPaper FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem measurable_cavityFixedRowLineField_marginal {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] (j d : ℕ) :
    Measurable (fun z : E×Records E S (observationLinearTree j)=>
      cavityFixedRowLineField j d z.1 z.2) := by
  induction j with
  | zero => exact measurable_fst
  | succ j ih =>
    by_cases h:d=j+1
    · simp only [cavityFixedRowLineField,if_pos h]
      exact measurable_fst
    · simp only [cavityFixedRowLineField,if_neg h]
      exact ih.comp measurable_snd

variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem cavityFixedRowLineField_kernel_marginal (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j d : ℕ) (hd : d≤j) :
    (Kernel.id ×ₖ finiteCascadeTreeRecordKernel V a L (observationLinearTree j)).map
      (fun z : FiniteStateField S×Records (FiniteStateField S) S (observationLinearTree j)=>
        cavityFixedRowLineField j d z.1 z.2)=
      sourceKernelLaw (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r)) (j-d) := by
  induction j generalizing d with
  | zero =>
    have hd0:d=0:=by omega
    subst d
    haveI:=isMarkovKernel_finiteStateGibbsKernel V
    change (Kernel.id ×ₖ finiteStateGibbsKernel V).map Prod.fst=Kernel.id
    rw [←Kernel.fst_eq,Kernel.fst_prod]
  | succ j ih =>
    haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree j)
    haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree (j+1))
    by_cases h:d=j+1
    · subst d
      simp only [cavityFixedRowLineField,if_pos rfl,Nat.sub_self,sourceKernelLaw,ite_true]
      rw [←Kernel.fst_eq,Kernel.fst_prod]
    · have hd':d≤j:=by omega
      simp only [cavityFixedRowLineField,if_neg h]
      change (Kernel.id ×ₖ ((Kernel.id ×ₖ finiteCascadeTreeRecordKernel V a L (observationLinearTree j)) ∘ₖ
        finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j)).map
          ((fun z : FiniteStateField S×Records (FiniteStateField S) S (observationLinearTree j)=>
            cavityFixedRowLineField j d z.1 z.2) ∘ Prod.snd)=_
      rw [Kernel.map_comp_right _ measurable_snd (measurable_cavityFixedRowLineField_marginal (E:=FiniteStateField S) (S:=S) j d),
        ←Kernel.snd_eq,Kernel.snd_prod,Kernel.map_comp,ih d hd']
      rw [Nat.succ_sub hd',sourceKernelLaw,Nat.add_sub_of_le hd']

theorem cavityFixedRowLineField_law (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j d : ℕ) (hd : d≤j) (H : FiniteStateField S) :
    (finiteCascadeTreeRecordKernel V a L (observationLinearTree j) H).map
      (cavityFixedRowLineField j d H)=
      sourceKernelLaw (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r)) (j-d) H := by
  haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree j)
  have hh:=congrArg (fun K : Kernel (FiniteStateField S) (FiniteStateField S)=>K H)
    (cavityFixedRowLineField_kernel_marginal V a ha L j d hd)
  rw [Kernel.map_apply _ (measurable_cavityFixedRowLineField_marginal (E:=FiniteStateField S) (S:=S) j d),Kernel.prod_apply,
    Kernel.id_apply,Measure.dirac_prod,Measure.map_map
      (measurable_cavityFixedRowLineField_marginal (E:=FiniteStateField S) (S:=S) j d) measurable_prodMk_left] at hh
  simpa only [Function.comp_def] using hh

theorem integral_cavityFixedRowLineField_eq_sourceKernelLaw (V : S→ℝ)
    (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j d : ℕ) (hd : d≤j) (H : FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : Measurable F) :
    (∫record,F (cavityFixedRowLineField j d H record)
      ∂finiteCascadeTreeRecordKernel V a L (observationLinearTree j) H)=
      ∫P,F P∂sourceKernelLaw
        (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r)) (j-d) H := by
  have hi : Measurable (fun r : Records (FiniteStateField S) S (observationLinearTree j)=>(H,r)):=
    measurable_const.prodMk measurable_id
  have hs : Measurable (fun r : Records (FiniteStateField S) S (observationLinearTree j)=>
      cavityFixedRowLineField j d H r):=by
    simpa only [Function.comp_def] using (measurable_cavityFixedRowLineField_marginal (E:=FiniteStateField S) (S:=S) j d).comp hi
  rw [←cavityFixedRowLineField_law V a ha L j d hd H,
    integral_map hs.aemeasurable hF.aestronglyMeasurable]

theorem integral_cavityFixedRowLineField_eq_sourceKernelExpectation (V : S→ℝ)
    (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j d : ℕ) (hd : d≤j) (H : FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀P,|F P|≤C) :
    (∫record,F (cavityFixedRowLineField j d H record)
      ∂finiteCascadeTreeRecordKernel V a L (observationLinearTree j) H)=
      sourceKernelExpectation
        (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r)) (j-d) F H := by
  rw [sourceKernelExpectation_eq_integral _
    (fun r=>isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (d+r)) F hF C hC,
    integral_cavityFixedRowLineField_eq_sourceKernelLaw V a ha L j d hd H F hF]

end QuantitativeFollowup
