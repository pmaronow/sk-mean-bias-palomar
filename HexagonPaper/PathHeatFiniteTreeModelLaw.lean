module
public import HexagonPaper.PathHeatFiniteTreeModelEvaluation

@[expose] public section

/-! Actual joint law of the factory's finite Gaussian row under the full
independent finite-plus-tree canonical Wiener reference. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A J : ℕ} {Z : Type*}

def pathHeatFiniteTreeFiniteVector
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (z : Z)
    (w : Fin (A+J)→WienerPath) (a : Fin A) : ℝ :=
  pathHeatTreeMixedOperator (pathHeatFiniteTreeDiagonal δ) (pathHeatFiniteTreeAncestor V W)
    (pathHeatFlatClockPath (A+J) (pathHeatFiniteTreeClocks v V hV hv hvV c z) w)
    (finSumFinEquiv (Sum.inl a),1)

theorem pathHeatFiniteTreeFiniteVector_iIndepFun
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (z : Z) :
    iIndepFun (fun a w=>pathHeatFiniteTreeFiniteVector v V hV hv hvV c δ W z w a)
      (pathHeatWienerMeshBase (J:=Fin (A+J))) := by
  let rows : Fin A→Fin (A+J) := fun a=>finSumFinEquiv (Sum.inl a)
  have hr : Function.Injective rows := finSumFinEquiv.injective.comp Sum.inl_injective
  have hp : iIndepFun (fun l : Fin (A+J)=>fun w : Fin (A+J)→WienerPath=>w l)
      (pathHeatWienerMeshBase (J:=Fin (A+J))) :=
    iIndepFun_pi (μ:=fun _ : Fin (A+J)=>canonicalWienerMeasure)
      (X:=fun (_ : Fin (A+J)) (p : WienerPath)=>p) (fun _=>measurable_id.aemeasurable)
  have hi := hp.precomp hr
  let g : Fin A→WienerPath→ℝ := fun a p=>Real.sqrt V*
    p (pathHeatFiniteVarianceClock (v z a) V hV (hv z a) (hvV z a) 1)
  have hg : ∀a,Measurable (g a) := fun a=>
    measurable_const.mul (_root_.ContinuousMap.measurable_eval _)
  have ht := hi.comp g hg
  simpa only [Function.comp_def,pathHeatFiniteTreeFiniteVector,pathHeatFiniteTreeField_finite,
    pathHeatFlatClockPath_apply,pathHeatFiniteTreeClocks_finite,rows,g] using ht

theorem hasLaw_pathHeatFiniteTreeFiniteVector
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (z : Z) :
    HasLaw (pathHeatFiniteTreeFiniteVector v V hV hv hvV c δ W z)
      (Measure.pi (fun a=>gaussianReal 0 (v z a).toNNReal))
      (pathHeatWienerMeshBase (J:=Fin (A+J))) :=
  (pathHeatFiniteTreeFiniteVector_iIndepFun v V hV hv hvV c δ W z).hasLaw_pi
    (fun a=>hasLaw_pathHeatFiniteTreeFiniteCoordinate v V hV hv hvV c δ W z a)

theorem hasGaussianLaw_pathHeatFiniteTreeFiniteVector
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (z : Z) :
    HasGaussianLaw (pathHeatFiniteTreeFiniteVector v V hV hv hvV c δ W z)
      (pathHeatWienerMeshBase (J:=Fin (A+J))) :=
  (pathHeatFiniteTreeFiniteVector_iIndepFun v V hV hv hvV c δ W z).hasGaussianLaw
    (fun a=>(hasLaw_pathHeatFiniteTreeFiniteCoordinate v V hV hv hvV c δ W z a).hasGaussianLaw)

end HexagonPaper
