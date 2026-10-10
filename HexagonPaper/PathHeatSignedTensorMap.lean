module
public import HexagonPaper.PathHeatSignedTensor
public import HexagonPaper.PathHeatTreeBernsteinFiniteCoordinates

@[expose] public section

/-! True signed tensor pushforward under source index maps. -/
noncomputable section
open Set MeasureTheory
namespace HexagonPaper
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

 theorem pathHeatSignedTensor_map {X Y X' Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
    (S : SignedMeasure X) (T : SignedMeasure Y) (f : X → X') (g : Y → Y')
    (hf : Measurable f) (hg : Measurable g) :
    pathHeatSignedTensor (S.map f) (T.map g) =
      (pathHeatSignedTensor S T).map (Prod.map f g) := by
  change (S.map f).prod (T.map g) (ContinuousLinearMap.lsmul ℝ ℝ) = _
  apply VectorMeasure.prod_eq_of_forall_apply_prod
  intro s t hs ht
  rw [VectorMeasure.map_apply _ (hf.prodMap hg) (hs.prod ht)]
  change pathHeatSignedTensor S T ((f ⁻¹' s)×ˢ(g ⁻¹' t)) = _
  rw [pathHeatSignedTensor_apply,VectorMeasure.map_apply _ hf hs,
    VectorMeasure.map_apply _ hg ht]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]

 theorem pathHeatSignedTensor_indexPushforward {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] [CompactSpace X] [CompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (ι : C(X,Y)) (S T : SignedMeasure X) :
    pathHeatSignedTensor (S.map ι) (T.map ι) =
      (pathHeatSignedTensor S T).map (pathHeatIndexPairMap ι) :=
  pathHeatSignedTensor_map S T ι ι ι.continuous.measurable ι.continuous.measurable

end HexagonPaper
