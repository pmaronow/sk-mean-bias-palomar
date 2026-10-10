module
public import HexagonPaper.PathHeatFiniteVarianceClock

@[expose] public section

/-! Genuine independent finite Gaussian coordinates are terminal rows of
the same product of canonical Wiener laws. Zero variances are retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : ℕ}

def pathHeatFiniteVarianceTerminal (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a)
    (w : Fin A→WienerPath) : Fin A→ℝ :=
  fun a => Real.sqrt (V a)*w a (pathHeatFiniteVarianceClock (v a) (V a) (hV a) (hv a) (hvV a) 1)

theorem measurable_pathHeatFiniteVarianceTerminal (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a) :
    Measurable (pathHeatFiniteVarianceTerminal v V hV hv hvV) := by
  apply Measurable.of_eval
  intro a
  exact measurable_const.mul ((_root_.ContinuousMap.measurable_eval _).comp (measurable_pi_apply a))

theorem hasLaw_pathHeatFiniteVarianceTerminal_coordinate (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a) (a : Fin A) :
    HasLaw (fun w => pathHeatFiniteVarianceTerminal v V hV hv hvV w a)
      (gaussianReal 0 (v a).toNNReal) (pathHeatWienerMeshBase (J:=Fin A)) :=
  (hasLaw_pathHeatFiniteVarianceTerminal (v a) (V a) (hV a) (hv a) (hvV a)).comp
    (measurePreserving_eval (fun _ : Fin A => canonicalWienerMeasure) a).hasLaw

theorem pathHeatFiniteVarianceTerminal_iIndepFun (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a) :
    iIndepFun (fun a w => pathHeatFiniteVarianceTerminal v V hV hv hvV w a)
      (pathHeatWienerMeshBase (J:=Fin A)) := by
  exact iIndepFun_pi (μ:=fun _ : Fin A=>canonicalWienerMeasure)
    (X:=fun (a : Fin A) (p : WienerPath) => Real.sqrt (V a)*
      p (pathHeatFiniteVarianceClock (v a) (V a) (hV a) (hv a) (hvV a) 1))
    (fun a => (measurable_const.mul (_root_.ContinuousMap.measurable_eval _)).aemeasurable)

theorem hasLaw_pathHeatFiniteVarianceTerminal_joint (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a) :
    HasLaw (pathHeatFiniteVarianceTerminal v V hV hv hvV)
      (Measure.pi (fun a => gaussianReal 0 (v a).toNNReal))
      (pathHeatWienerMeshBase (J:=Fin A)) := by
  refine ⟨(measurable_pathHeatFiniteVarianceTerminal v V hV hv hvV).aemeasurable,?_⟩
  change (Measure.pi (fun _ : Fin A => canonicalWienerMeasure)).map
    (fun w a => Real.sqrt (V a)*w a
      (pathHeatFiniteVarianceClock (v a) (V a) (hV a) (hv a) (hvV a) 1)) = _
  rw [Measure.pi_map_pi (f:=fun (a : Fin A) (p : WienerPath) => Real.sqrt (V a)*p
      (pathHeatFiniteVarianceClock (v a) (V a) (hV a) (hv a) (hvV a) 1)) (fun a =>
    (measurable_const.mul (_root_.ContinuousMap.measurable_eval _)).aemeasurable)]
  congr 1
  funext a
  exact (hasLaw_pathHeatFiniteVarianceTerminal (v a) (V a) (hV a) (hv a) (hvV a)).map_eq

theorem pathHeatFiniteVarianceTerminal_hasGaussianLaw (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a) :
    HasGaussianLaw (pathHeatFiniteVarianceTerminal v V hV hv hvV)
      (pathHeatWienerMeshBase (J:=Fin A)) :=
  (pathHeatFiniteVarianceTerminal_iIndepFun v V hV hv hvV).hasGaussianLaw
    (fun a => (hasLaw_pathHeatFiniteVarianceTerminal_coordinate v V hV hv hvV a).hasGaussianLaw)

theorem integral_pathHeatFiniteVarianceTerminal_coordinate (v V : Fin A→ℝ)
    (hV : ∀a,0<V a) (hv : ∀a,0≤v a) (hvV : ∀a,v a≤V a) (a : Fin A) :
    (∫w,pathHeatFiniteVarianceTerminal v V hV hv hvV w a
      ∂pathHeatWienerMeshBase (J:=Fin A))=0 := by
  rw [(hasLaw_pathHeatFiniteVarianceTerminal_coordinate v V hV hv hvV a).integral_eq,
    integral_id_gaussianReal]

end HexagonPaper
