module
public import HexagonPaper.PathHeatNativeSourceExtension
public import HexagonPaper.PathHeatSignedTensorMap

@[expose] public section

/-! Pair flat covariance kernels against actual pushforward derivative
measures by restricting the kernel to the native finite/tree index. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

def pathHeatNativeKernelRestriction (ι : C(X,Y)) (K : Y×Y→ᵇℝ) : X×X→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact (K.toContinuousMap.comp (pathHeatIndexPairMap ι))

@[simp] theorem pathHeatNativeKernelRestriction_apply (ι : C(X,Y)) (K : Y×Y→ᵇℝ) (x y : X) :
    pathHeatNativeKernelRestriction ι K (x,y)=K (ι x,ι y) := rfl

theorem signedContraction_pathHeatNativeKernelRestriction (ι : C(X,Y))
    (K : Y×Y→ᵇℝ) (M : SignedMeasure (X×X)) :
    signedContraction K (M.map (pathHeatIndexPairMap ι))=
      signedContraction (pathHeatNativeKernelRestriction ι K) M := by
  exact VectorMeasure.integral_map (pathHeatIndexPairMap ι).continuous.measurable
    K.continuous.aestronglyMeasurable
    (pathHeat_continuous_integrable (K.toContinuousMap.comp (pathHeatIndexPairMap ι)) M)


theorem pathHeatDensityGenerator_indexPushforward (ι : C(X,Y)) (K : Y×Y→ᵇℝ)
    (S : SignedMeasure X) (M : SignedMeasure (X×X)) (dotell : ℝ) :
    pathHeatDensityGenerator K (S.map ι) (M.map (pathHeatIndexPairMap ι)) dotell=
      pathHeatDensityGenerator (pathHeatNativeKernelRestriction ι K) S M dotell := by
  simp only [pathHeatDensityGenerator,pathHeatDensityDerivativeMeasure,signedContraction_add,
    pathHeatSignedTensor_indexPushforward,signedContraction_pathHeatNativeKernelRestriction]

theorem pathHeatObservableGenerator_indexPushforward (ι : C(X,Y)) (K : Y×Y→ᵇℝ)
    (S P : SignedMeasure X) (Q : SignedMeasure (X×X)) (dotphi : ℝ) :
    pathHeatObservableGenerator K (S.map ι) (P.map ι) (Q.map (pathHeatIndexPairMap ι)) dotphi=
      pathHeatObservableGenerator (pathHeatNativeKernelRestriction ι K) S P Q dotphi := by
  simp only [pathHeatObservableGenerator,pathHeatObservableDerivativeMeasure,signedContraction_add,
    pathHeatSignedTensor_indexPushforward,signedContraction_pathHeatNativeKernelRestriction]

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSingletonClass A]
variable {a b : ℝ}

theorem pathHeatNativeSourceExtension_densityGenerator (ι : C(X,Y))
    (d : PathHeatContinuousSignedSource (Icc a b×((E×A)×C(X,ℝ))) X)
    (K : Y×Y→ᵇℝ) (θ : Icc a b×((E×A)×C(Y,ℝ))) :
    (pathHeatNativeSourceExtension ι d).densityGenerator K θ=
      d.densityGenerator (pathHeatNativeKernelRestriction ι K)
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatDensityGenerator_indexPushforward ι K _ _ _

theorem pathHeatNativeSourceExtension_observableGenerator (ι : C(X,Y))
    (d : PathHeatContinuousSignedSource (Icc a b×((E×A)×C(X,ℝ))) X)
    (K : Y×Y→ᵇℝ) (θ : Icc a b×((E×A)×C(Y,ℝ))) :
    (pathHeatNativeSourceExtension ι d).observableGenerator K θ=
      d.observableGenerator (pathHeatNativeKernelRestriction ι K)
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatObservableGenerator_indexPushforward ι K _ _ _ _


theorem pathHeatNativeSourceExtension_densityGenerator_continuousKernel (ι : C(X,Y))
    (d : PathHeatContinuousSignedSource (Icc a b×((E×A)×C(X,ℝ))) X)
    (K : C(Y×Y,ℝ)) (θ : Icc a b×((E×A)×C(Y,ℝ))) :
    (pathHeatNativeSourceExtension ι d).densityGenerator (BoundedContinuousFunction.mkOfCompact K) θ=
      d.densityGenerator (BoundedContinuousFunction.mkOfCompact (K.comp (pathHeatIndexPairMap ι)))
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatNativeSourceExtension_densityGenerator ι d _ θ

theorem pathHeatNativeSourceExtension_observableGenerator_continuousKernel (ι : C(X,Y))
    (d : PathHeatContinuousSignedSource (Icc a b×((E×A)×C(X,ℝ))) X)
    (K : C(Y×Y,ℝ)) (θ : Icc a b×((E×A)×C(Y,ℝ))) :
    (pathHeatNativeSourceExtension ι d).observableGenerator (BoundedContinuousFunction.mkOfCompact K) θ=
      d.observableGenerator (BoundedContinuousFunction.mkOfCompact (K.comp (pathHeatIndexPairMap ι)))
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatNativeSourceExtension_observableGenerator ι d _ θ

end HexagonPaper
