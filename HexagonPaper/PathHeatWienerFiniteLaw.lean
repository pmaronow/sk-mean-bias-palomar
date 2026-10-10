module
public import HexagonPaper.PathHeatBrownianClockFactor
public import HexagonPaper.PathHeatTreeBernsteinMixedFlatten
public import HexagonPaper.PathHeatFlatClockCoupling

@[expose] public section

/-! The actual finite common-Wiener expectation equals the finite Gaussian
clock expectation. The same finite observations feed the actual fixed mixed
tree synthesis, including zero root coordinates. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {L n : ℕ}

def pathHeatWienerBernsteinClockMesh (c : ℝ→Fin L→C(I,I)) :
    ℝ→Fin L→Fin (n+1)→Paper.Overlap := fun z l i=>c z l (bernstein.z i)

theorem pathHeatWienerMixedBernstein_actual_mesh
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : ℝ) (w : Fin L→WienerPath) :
    pathHeatTreeMixedFlattenedSynthesis n L δ W
      (pathHeatWienerMeshReindex (pathHeatWienerMeshSample
        (pathHeatWienerBernsteinClockMesh (n:=n) c z) w))=
      pathHeatTreeMixedOperator δ W
        (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) w)) := by
  rw [pathHeatTreeMixedFlattenedSynthesis_actualReindex]
  change pathHeatTreeMixedOperator δ W
    (pathHeatTreeBernsteinSynthesis n L
      (WithLp.toLp 2 (fun p : Fin L×Fin (n+1)=>w p.1 (c z p.1 (bernstein.z p.2)))))=_
  rw [pathHeatFlatClockPath_Bernstein_actual_mesh]

theorem integral_pathHeatWienerMixedBernstein_eq_gaussian
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : ℝ)
    (hc : ∀l,Monotone (pathHeatWienerBernsteinClockMesh (n:=n) c z l))
    (h0 : ∀l,(pathHeatWienerBernsteinClockMesh (n:=n) c z l 0:ℝ)=0)
    (F : C(Fin L×I,ℝ)→ℝ) (hF : Measurable F) :
    (∫w,F (pathHeatTreeMixedOperator δ W
      (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) w)))
        ∂pathHeatWienerMeshBase (J:=Fin L))=
      gaussianLinearMean (fun y=>F (pathHeatTreeMixedFlattenedSynthesis n L δ W y))
        (pathHeatVarianceFactor (pathHeatBrownianClockVariance (pathHeatWienerBernsteinClockMesh (n:=n) c))
          pathHeatBrownianClockMask z) 0 := by
  let mesh := pathHeatWienerBernsteinClockMesh (n:=n) c
  let A := pathHeatTreeMixedFlattenedSynthesis n L δ W
  have hs : Measurable (fun w=>pathHeatWienerMeshReindex (pathHeatWienerMeshSample (mesh z) w)) :=
    pathHeatWienerMeshReindex.measurable.comp (measurable_pathHeatWienerMeshSample (mesh z))
  have hf : Measurable (fun y=>F (A y)) := hF.comp A.measurable
  have hlaw := pathHeatWienerMesh_eq_varianceLaw mesh z hc h0
  rw [pathHeatWienerMeshReindexedLaw_eq_actual_map] at hlaw
  calc
    _=(∫w,F (A (pathHeatWienerMeshReindex (pathHeatWienerMeshSample (mesh z) w)))
        ∂pathHeatWienerMeshBase (J:=Fin L)) := by
      apply integral_congr_ae
      exact .of_forall fun w=>congrArg F (pathHeatWienerMixedBernstein_actual_mesh c δ W z w).symm
    _=(∫y,F (A y) ∂(pathHeatWienerMeshBase (J:=Fin L)).map
        (fun w=>pathHeatWienerMeshReindex (pathHeatWienerMeshSample (mesh z) w))) :=
      (integral_map hs.aemeasurable hf.aestronglyMeasurable).symm
    _=(∫y,F (A y) ∂pathHeatVarianceLaw (pathHeatBrownianClockVariance mesh) pathHeatBrownianClockMask z) := by rw [hlaw]
    _=_ := by
      rw [pathHeatVarianceLaw,integral_map (by fun_prop) hf.aestronglyMeasurable]
      simp only [gaussianLinearMean,zero_add,A,mesh]

end HexagonPaper
