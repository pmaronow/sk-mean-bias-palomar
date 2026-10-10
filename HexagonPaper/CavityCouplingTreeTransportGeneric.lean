module
public import HexagonPaper.TreeLikelihoodEndpointRecordsBasic

@[expose] public section

/-! Naturality of actual finite recorded path genealogies under a
measurable start/path change. The equality is derived from true edge and
leaf kernel equalities and endpoint commutation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon FiniteTerminalGenealogy
open scoped ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {X Y S Z W : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace Z] [MeasurableSpace W]

theorem cavityPathKernel_compProd_natural (κ κ' : Kernel X Y)
    (η η' : Kernel X Z) [IsFiniteKernel κ] [IsFiniteKernel κ']
    [IsFiniteKernel η] [IsFiniteKernel η']
    (s : X→X) (R : Y→Y) (V : Z→Z) (f f' : Y→X)
    (hs : Measurable s) (hR : Measurable R) (hV : Measurable V)
    (hf : Measurable f) (hf' : Measurable f')
    (hκ : κ.map R=κ'.comap s hs) (hη : η.map V=η'.comap s hs)
    (he : ∀y,f' (R y)=s (f y)):
    (κ ⊗ₖ η.comap (fun p:X×Y=>f p.2) (hf.comp measurable_snd)).map (Prod.map R V)=
      (κ' ⊗ₖ η'.comap (fun p:X×Y=>f' p.2) (hf'.comp measurable_snd)).comap s hs := by
  ext x : 1
  apply Measure.ext_prod
  intro A B hA hB
  rw [Kernel.map_apply' _ (hR.prodMap hV) _ (hA.prod hB),Kernel.comap_apply]
  change (κ ⊗ₖ η.comap (fun p:X×Y=>f p.2) (hf.comp measurable_snd)) x
    ((R ⁻¹' A) ×ˢ (V ⁻¹' B))=_
  rw [Kernel.compProd_apply_prod (hR hA) (hV hB),
    Kernel.compProd_apply_prod hA hB]
  simp only [Kernel.comap_apply]
  have hη' (y:Y):η (f y) (V ⁻¹' B)=η' (f' (R y)) B:=by
    have hh:=congrArg (fun k:Kernel X Z=>k (f y) B) hη
    rw [Kernel.map_apply' _ hV _ hB,Kernel.comap_apply] at hh
    simpa only [he] using hh
  simp_rw [hη']
  have hκ':κ' (s x)=(κ x).map R:=by
    have hh:=congrArg (fun k:Kernel X Y=>k x) hκ
    rw [Kernel.map_apply _ hR,Kernel.comap_apply] at hh
    exact hh.symm
  rw [hκ']
  exact (setLIntegral_map hA ((η'.measurable_coe hB).comp hf') hR).symm

@[reducible] def cavityTreeRecordPathMap (R : Y→Y):
    {j:ℕ}→(T:FiniteTerminalGenealogy j)→Records Y S T→Records Y S T
  | _,.leaf=>id
  | _,.advance T=>Prod.map R (cavityTreeRecordPathMap R T)
  | _,.fork T U=>Prod.map (cavityTreeRecordPathMap R T) (cavityTreeRecordPathMap R U)

theorem measurable_cavityTreeRecordPathMap (R:Y→Y) (hR:Measurable R)
    {j:ℕ} (T:FiniteTerminalGenealogy j):Measurable (cavityTreeRecordPathMap (S:=S) R T):=by
  induction T with
  | leaf=>exact measurable_id
  | advance T ih=>exact hR.prodMap ih
  | fork T U ihT ihU=>exact ihT.prodMap ihU

theorem isFiniteKernel_treePathRecordKernel (leaf:Kernel X S) (edge:ℕ→Kernel X Y)
    (endpoint:ℕ→Y→X) (he:∀j,Measurable (endpoint j))
    [IsFiniteKernel leaf] [∀j,IsFiniteKernel (edge j)]
    {j:ℕ} (T:FiniteTerminalGenealogy j):
    IsFiniteKernel (treePathRecordKernel leaf edge endpoint he T):=by
  induction T with
  | leaf=>infer_instance
  | @advance j T ih=>
    haveI:=ih
    change IsFiniteKernel (_ ⊗ₖ _)
    infer_instance
  | fork T U ihT ihU=>
    haveI:=ihT
    haveI:=ihU
    change IsFiniteKernel (_ ×ₖ _)
    infer_instance

attribute [local instance] isFiniteKernel_treePathRecordKernel

theorem cavityTreeRecordKernel_natural
    (leaf leaf':Kernel X S) (edge edge':ℕ→Kernel X Y)
    (endpoint endpoint':ℕ→Y→X) (he:∀j,Measurable (endpoint j))
    (he':∀j,Measurable (endpoint' j))
    [IsFiniteKernel leaf] [IsFiniteKernel leaf']
    [∀j,IsFiniteKernel (edge j)] [∀j,IsFiniteKernel (edge' j)]
    (s:X→X) (R:Y→Y) (hs:Measurable s) (hR:Measurable R)
    (hl:leaf=leaf'.comap s hs)
    (hEdge:∀j,(edge j).map R=(edge' j).comap s hs)
    (hEnd:∀j y,endpoint' j (R y)=s (endpoint j y))
    {j:ℕ} (T:FiniteTerminalGenealogy j):
    (treePathRecordKernel leaf edge endpoint he T).map (cavityTreeRecordPathMap R T)=
      (treePathRecordKernel leaf' edge' endpoint' he' T).comap s hs:=by
  induction T with
  | leaf=>simpa only [treePathRecordKernel,cavityTreeRecordPathMap,Kernel.map_id] using hl
  | @advance j T ih=>
    exact cavityPathKernel_compProd_natural (edge j) (edge' j)
      (treePathRecordKernel leaf edge endpoint he T)
      (treePathRecordKernel leaf' edge' endpoint' he' T) s R
      (cavityTreeRecordPathMap R T) (endpoint j) (endpoint' j) hs hR
      (measurable_cavityTreeRecordPathMap R hR T) (he j) (he' j)
      (hEdge j) ih (hEnd j)
  | fork T U ihT ihU=>
    change (_ ×ₖ _).map (Prod.map _ _) = (_ ×ₖ _).comap s hs
    rw [←Kernel.map_prod_map _ _ (measurable_cavityTreeRecordPathMap R hR T)
      (measurable_cavityTreeRecordPathMap R hR U),ihT,ihU,Kernel.comap_prod]

end HexagonPaper
