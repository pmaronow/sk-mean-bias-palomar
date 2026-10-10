module
public import HexagonPaper.CavityVertexCancellationRestartVariance
public import HexagonPaper.CavityTreePathTopology

@[expose] public section

/-! The printed future square is the actual physical fresh-edge kernel
at every genuine tagged vertex of the complete native path tree. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

 theorem edgeParameter_disorder_field_decomposition (P : AnisotropicParameter n) :
    anisotropicDisorderInjection n (edgeParameterDisorderProjection n P)+
      anisotropicFieldInjection n (edgeParameterFieldProjection n P)=P := by
  ext i
  cases i <;> simp [edgeParameterDisorderProjection,edgeParameterFieldProjection,
    anisotropicDisorderInjection,anisotropicFieldInjection]

 def cavityTreePhysicalFutureSquare (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) : ℝ :=
  ∫Z,(anisotropicMeasureTailMagnetization D μ r (Z r) i)^2
    ∂edgePhysicalPathKernel D μ q r (edgeObservationParameterInverse D P)

 theorem cavityTreePhysicalFutureSquare_eq_restart (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    cavityTreePhysicalFutureSquare D μ q r P i=
      anisotropicRestartSpinSquare D μ (edgeParameterDisorderProjection n P) q
        (edgeParameterFieldProjection n P) i r := by
  have hm : Measurable (fun Z : NativeTreePath n=>
      (anisotropicMeasureTailMagnetization D μ r (Z r) i)^2) :=
    ((((EuclideanSpace.proj i).measurable.comp
      ((measurable_anisotropicMeasureTailMagnetization D μ).comp
        (measurable_const.prodMk (ContinuousMap.measurable_eval r)))).pow_const 2))
  unfold cavityTreePhysicalFutureSquare
  rw [edgePhysicalPathKernel_apply,integral_map
    (measurable_edgeStoppedDiffusionPath D μ _ q r _).aemeasurable hm.aestronglyMeasurable]
  unfold anisotropicRestartSpinSquare
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change (anisotropicMeasureTailMagnetization D μ r
      ((edgeStoppedDiffusionPath D μ (edgeParameterDisorderProjection n P) q r
        (anisotropicInverseNoiseMap D (edgeParameterFieldProjection n P)) sample) r) i)^2=
      (anisotropicRestartSpinResponse D μ (edgeParameterDisorderProjection n P) q
        (edgeParameterFieldProjection n P) i r sample)^2
    simp only [edgeStoppedDiffusionPath,edgeDiffusionPath,ContinuousMap.comp_apply,edgeStopMap,
      ContinuousMap.coe_mk,edgeStopOverlap,min_self,anisotropicRestartSpinResponse,
      anisotropicRestartPhysicalParameter]

 theorem anisotropic_full_field_vertex_variance_cancellation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    (q:ℝ)*fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
        (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)+
      2*deriv (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q P)
        (D.variance i)=
      1-(q:ℝ)*Paper.parisiCDF μ q*(anisotropicMeasureTailMagnetization D μ q P i)^2-
      ∫r : Paper.Overlap,if q<r then (r:ℝ)*cavityTreePhysicalFutureSquare D μ q r P i else 0
        ∂parisiFreeMeasure μ a := by
  have hh:=anisotropic_restart_vertex_variance_cancellation D μ a ha hμ
    (edgeParameterDisorderProjection n P) q (edgeParameterFieldProjection n P) i
  rw [edgeParameter_disorder_field_decomposition] at hh
  simpa only [cavityTreePhysicalFutureSquare_eq_restart] using hh

 theorem treeNativeFullPoint_vertex_variance_cancellation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T)
    (v : Unit⊕treePathWeightPoint T) (i : Fin n) :
    let qp:=treeNativeFullPointData D q T x Z v
    (qp.1:ℝ)*fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ qp.1)) qp.2
        (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)+
      2*deriv (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ qp.1 qp.2)
        (D.variance i)=
      1-(qp.1:ℝ)*Paper.parisiCDF μ qp.1*(anisotropicMeasureTailMagnetization D μ qp.1 qp.2 i)^2-
      ∫r : Paper.Overlap,if qp.1<r then (r:ℝ)*cavityTreePhysicalFutureSquare D μ qp.1 r qp.2 i else 0
        ∂parisiFreeMeasure μ a :=
  anisotropic_full_field_vertex_variance_cancellation D μ a ha hμ _ _ i

 theorem cavity_tree_native_vertex_cancellation (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (u : ℝ) (hu : u∈Icc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState (n+1))
    (Z : Records (NativeTreePath (n+1)) (Configuration (n+1)) T)
    (v : Unit⊕treePathWeightPoint T) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let qp:=treeNativeFullPointData D q T x Z v
    (qp.1:ℝ)*fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ qp.1)) qp.2
        (anisotropicCoordinateDirection (n+1) (Fin.last n))
        (anisotropicCoordinateDirection (n+1) (Fin.last n))+
      2*deriv (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D (Fin.last n) b) μ qp.1 qp.2)
        (followupCavityB n β ρ u)=
      1-(qp.1:ℝ)*Paper.parisiCDF μ qp.1*
        (anisotropicMeasureTailMagnetization D μ qp.1 qp.2 (Fin.last n))^2-
      ∫r : Paper.Overlap,if qp.1<r then (r:ℝ)*
        cavityTreePhysicalFutureSquare D μ qp.1 r qp.2 (Fin.last n) else 0 ∂parisiFreeMeasure μ a := by
  dsimp only
  simpa only [followupCavitySpinModel_variance_last] using
    treeNativeFullPoint_vertex_variance_cancellation (followupCavitySpinModel n β ρ hβ hρ u hu)
      μ a ha hμ q T x Z v (Fin.last n)

end HexagonPaper
