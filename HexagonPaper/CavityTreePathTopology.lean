module
public import HexagonPaper.TreeLikelihood

@[expose] public section

/-! The actual tagged tree space is a finite disjoint union of compact
interval edges and finite vertices. Its existing measurable structure
is its Borel structure, so arbitrary atomic profile charges are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true

instance treeSumBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] :
    BorelSpace (X⊕Y) := by
  constructor
  apply le_antisymm
  · intro s hs
    obtain ⟨hl,hr⟩ := measurableSet_sum_iff.mp hs
    letI : MeasurableSpace (X⊕Y) := borel (X⊕Y)
    letI : BorelSpace (X⊕Y) := ⟨rfl⟩
    have hli : MeasurableSet (Sum.inl '' (Sum.inl ⁻¹' s)) :=
      (Topology.IsOpenEmbedding.inl (X:=X) (Y:=Y)).measurableEmbedding.measurableSet_image' hl
    have hri : MeasurableSet (Sum.inr '' (Sum.inr ⁻¹' s)) :=
      (Topology.IsOpenEmbedding.inr (X:=X) (Y:=Y)).measurableEmbedding.measurableSet_image' hr
    have he : Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) = s := by
      ext z
      cases z <;> simp
    rw [←he]
    exact hli.union hri
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr
      ⟨(isOpen_sum_iff.mp hs).1.measurableSet,(isOpen_sum_iff.mp hs).2.measurableSet⟩

@[reducible] def treePathWeightPointTopology : {j : ℕ}→
    (T : FiniteTerminalGenealogy j)→TopologicalSpace (treePathWeightPoint T)
  | _,.leaf=>inferInstanceAs (TopologicalSpace Unit)
  | _,.advance T=>@instTopologicalSpaceSum _ _ inferInstance (treePathWeightPointTopology T)
  | _,.fork T U=>@instTopologicalSpaceSum _ _ inferInstance
      (@instTopologicalSpaceSum _ _ (treePathWeightPointTopology T) (treePathWeightPointTopology U))

instance {j : ℕ} (T : FiniteTerminalGenealogy j):TopologicalSpace (treePathWeightPoint T):=
  treePathWeightPointTopology T

instance {j : ℕ} (T : FiniteTerminalGenealogy j):CompactSpace (treePathWeightPoint T):=by
  induction T with
  | leaf=>exact inferInstanceAs (CompactSpace Unit)
  | advance T ih=>
    haveI:=ih
    change CompactSpace (Paper.Overlap⊕treePathWeightPoint T)
    infer_instance
  | fork T U ihT ihU=>
    haveI:=ihT
    haveI:=ihU
    change CompactSpace (Unit⊕(treePathWeightPoint T⊕treePathWeightPoint U))
    infer_instance

instance {j : ℕ} (T : FiniteTerminalGenealogy j):SecondCountableTopology (treePathWeightPoint T):=by
  induction T with
  | leaf=>exact inferInstanceAs (SecondCountableTopology Unit)
  | advance T ih=>
    haveI:=ih
    change SecondCountableTopology (Paper.Overlap⊕treePathWeightPoint T)
    infer_instance
  | fork T U ihT ihU=>
    haveI:=ihT
    haveI:=ihU
    change SecondCountableTopology (Unit⊕(treePathWeightPoint T⊕treePathWeightPoint U))
    infer_instance

instance {j : ℕ} (T : FiniteTerminalGenealogy j):BorelSpace (treePathWeightPoint T):=by
  induction T with
  | leaf=>exact inferInstanceAs (BorelSpace Unit)
  | advance T ih=>
    haveI:=ih
    change BorelSpace (Paper.Overlap⊕treePathWeightPoint T)
    infer_instance
  | fork T U ihT ihU=>
    haveI:=ihT
    haveI:=ihU
    change BorelSpace (Unit⊕(treePathWeightPoint T⊕treePathWeightPoint U))
    infer_instance

instance {j : ℕ} (T : FiniteTerminalGenealogy j):T2Space (treePathWeightPoint T):=by
  induction T with
  | leaf=>exact inferInstanceAs (T2Space Unit)
  | advance T ih=>
    haveI:=ih
    change T2Space (Paper.Overlap⊕treePathWeightPoint T)
    infer_instance
  | fork T U ihT ihU=>
    haveI:=ihT
    haveI:=ihU
    change T2Space (Unit⊕(treePathWeightPoint T⊕treePathWeightPoint U))
    infer_instance

@[reducible] def treeNativePointData {n : ℕ} (D : AnisotropicSpinModel n) (q : ℕ→Paper.Overlap):
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→AnisotropicObservationState n→
      Records (NativeTreePath n) (Configuration n) T→
        treePathWeightPoint T→Paper.Overlap×AnisotropicParameter n
  | _,.leaf=>fun x _ _=>(q 0,anisotropicObservationParameter D x)
  | _,@FiniteTerminalGenealogy.advance j T=>fun _ Z=>Sum.elim
      (fun r=>(r,Z.1 r)) (treeNativePointData D q T (edgePathEndpoint D (q j) Z.1) Z.2)
  | j,.fork T U=>fun x Z=>Sum.elim
      (fun _:Unit=>(q j,anisotropicObservationParameter D x))
      (Sum.elim (treeNativePointData D q T x Z.1) (treeNativePointData D q U x Z.2))

theorem continuous_treeNativePointData {n : ℕ} (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    Continuous (treeNativePointData D q T x Z):=by
  induction T generalizing x with
  | leaf=>exact continuous_const
  | @advance j T ih=>
    exact (continuous_id.prodMk Z.1.continuous).sumElim
      (ih (edgePathEndpoint D (q j) Z.1) Z.2)
  | fork T U ihT ihU=>exact continuous_const.sumElim ((ihT x Z.1).sumElim (ihU x Z.2))

def treeNativeFullPointData {n : ℕ} (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    C(Unit⊕treePathWeightPoint T,Paper.Overlap×AnisotropicParameter n):=
  ⟨Sum.elim (fun _:Unit=>(q j,anisotropicObservationParameter D x)) (treeNativePointData D q T x Z),
    continuous_const.sumElim (continuous_treeNativePointData D q T x Z)⟩

end HexagonPaper
