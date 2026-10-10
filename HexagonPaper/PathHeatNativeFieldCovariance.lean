module
public import HexagonPaper.PathHeatMixedFieldCovariance
public import HexagonPaper.PathHeatClockKernelDifferentiation
public import HexagonPaper.PathHeatNativeWienerModel

@[expose] public section

/-! The original finite-coordinate/tree index kernel is the covariance of
actual native Wiener field values. Its derivative is the actual native
dot-kernel, with no covariance identification or differentiation premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology unitInterval BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X] {L : ℕ}

def pathHeatNativeClockField (ι : C(X,Fin L×I)) (c : Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (w : Fin L→WienerPath) : C(X,ℝ) :=
  pathHeatIndexRestriction ι (pathHeatTreeMixedOperator δ W (pathHeatFlatClockPath L c w))

def pathHeatNativeClockCovarianceKernel (ι : C(X,Fin L×I)) (c : Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) : X×X→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact
    ((pathHeatTreeMixedKernelOperator δ W
      (pathHeatClockRawKernel (pathHeatClockReal c))).uncurry.comp (pathHeatIndexPairMap ι))

theorem covariance_pathHeatNativeClockField (ι : C(X,Fin L×I))
    (c : Fin L→C(I,I)) (hc : ∀l,Monotone (c l))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (x y : X) :
    covariance (fun w=>pathHeatNativeClockField ι c δ W w x)
      (fun w=>pathHeatNativeClockField ι c δ W w y) (pathHeatWienerMeshBase (J:=Fin L)) =
        pathHeatNativeClockCovarianceKernel ι c δ W (x,y) :=
  covariance_pathHeatMixedClockEvaluation c hc δ W (ι x) (ι y)

theorem hasDerivAt_pathHeatNativeClockCovarianceKernel {a b : ℝ}
    (hab : a≤b) (ι : C(X,Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : ℝ)
    (hdc : ∀l t,HasDerivAt (fun u=>(c (projIcc a b hab u) l t:ℝ))
      (dc (projIcc a b hab z) l t) z) (x y : X) :
    HasDerivAt (fun u=>pathHeatNativeClockCovarianceKernel ι
      (c (projIcc a b hab u)) δ W (x,y))
      (pathHeatNativeWienerKernel ι dc δ W (projIcc a b hab z) (x,y)) z :=
  hasDerivAt_pathHeatMixedUnitClockKernel
    (fun u=>c (projIcc a b hab u)) (fun u=>dc (projIcc a b hab u)) δ W z hdc (ι x) (ι y)

theorem hasDerivAt_covariance_pathHeatNativeClockField {a b : ℝ}
    (hab : a≤b) (ι : C(X,Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (hc : ∀u l,Monotone (c u l)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : ℝ)
    (hdc : ∀l t,HasDerivAt (fun u=>(c (projIcc a b hab u) l t:ℝ))
      (dc (projIcc a b hab z) l t) z) (x y : X) :
    HasDerivAt (fun u=>covariance
      (fun w=>pathHeatNativeClockField ι (c (projIcc a b hab u)) δ W w x)
      (fun w=>pathHeatNativeClockField ι (c (projIcc a b hab u)) δ W w y)
      (pathHeatWienerMeshBase (J:=Fin L)))
      (pathHeatNativeWienerKernel ι dc δ W (projIcc a b hab z) (x,y)) z := by
  simp_rw [covariance_pathHeatNativeClockField ι _ (hc _) δ W]
  exact hasDerivAt_pathHeatNativeClockCovarianceKernel hab ι c dc δ W z hdc x y

end HexagonPaper
