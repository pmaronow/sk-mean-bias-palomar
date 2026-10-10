module
public import HexagonPaper.EdgeLikelihoodPathKernelEndpoint
public import HexagonPaper.TreePathKernelDensityTree

@[expose] public section

/-! Complete native path genealogies for every Parisi profile. Each edge
is the actual restarted diffusion driven by fresh Wiener noise. The
reference genealogy uses the actual corresponding fresh Gaussian paths;
terminal spins use counting measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ENNReal
namespace HexagonPaper
open FiniteTerminalGenealogy SpinGlass.AT
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

abbrev NativeTreePath (n : ℕ):=C(Paper.Overlap,AnisotropicParameter n)

def treeNativeSpinKernel (D : AnisotropicSpinModel n) :
    Kernel (AnisotropicObservationState n) (Configuration n):=
  (anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D)

instance treeNativeSpinKernel_markov (D : AnisotropicSpinModel n):
    IsMarkovKernel (treeNativeSpinKernel D):=by
  unfold treeNativeSpinKernel
  infer_instance

def treeNativeSpinLog (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (x : AnisotropicObservationState n) (σ : Configuration n):ℝ:=
  anisotropicTerminalLinear D σ (anisotropicObservationParameter D x)-
    anisotropicMeasureTailPotential D μ 1 (anisotropicObservationParameter D x)

theorem measurable_treeNativeSpinLog (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure):
    Measurable (Function.uncurry (treeNativeSpinLog D μ)):=by
  apply measurable_from_prod_countable_left
  intro σ
  exact (((anisotropicTerminalLinear D σ).measurable.comp
    (measurable_anisotropicObservationParameter D)).sub
    (((continuous_anisotropicMeasureTailPotential_joint D μ).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
      (measurable_anisotropicObservationParameter D)))

theorem treeNativeSpinKernel_exp_density (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure):
    treeNativeSpinKernel D=(Kernel.const (AnisotropicObservationState n)
      (Measure.count:Measure (Configuration n))).withDensity
        (fun x σ=>ENNReal.ofReal (Real.exp (treeNativeSpinLog D μ x σ))) := by
  ext x : 1
  rw [Kernel.withDensity_apply _ ((measurable_treeNativeSpinLog D μ).exp.ennreal_ofReal),
    Kernel.const_apply]
  unfold treeNativeSpinKernel anisotropicTerminalSpinKernel
  rw [Kernel.comap_apply,Kernel.comap_apply,finiteStateGibbsKernel_apply]
  congr 1
  funext σ
  congr 1
  unfold treeNativeSpinLog
  have ht:=anisotropicMeasureTailPotential_one D μ (anisotropicObservationParameter D x)
  change anisotropicMeasureTailPotential D μ (1:Paper.Overlap) (anisotropicObservationParameter D x)=_ at ht
  rw [ht]
  unfold gtStateGibbs anisotropicGridTerminalPotential finiteLinearSoftmax
  rw [Real.exp_sub,Real.exp_log (finiteLinearPartition_pos _ _)]
  congr 1
  · simp only [anisotropicEnergyMap_apply,add_zero]
  · unfold gtStatePartition finiteLinearPartition
    congr 1
    funext σ
    simp only [anisotropicEnergyMap_apply,add_zero]

def treeNativePathKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    Kernel (AnisotropicObservationState n) (Records (NativeTreePath n) (Configuration n) T):=
  treePathRecordKernel (treeNativeSpinKernel D)
    (fun j=>edgePhysicalPathKernel D μ (q (j+1)) (q j))
    (fun j=>edgePathEndpoint D (q j)) (fun j=>measurable_edgePathEndpoint D (q j)) T

def treeReferencePathKernel (D : AnisotropicSpinModel n) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    Kernel (AnisotropicObservationState n) (Records (NativeTreePath n) (Configuration n) T):=
  treePathRecordKernel (Kernel.const _ (Measure.count:Measure (Configuration n)))
    (fun j=>edgeReferencePathKernel D (q (j+1)) (q j))
    (fun j=>edgePathEndpoint D (q j)) (fun j=>measurable_edgePathEndpoint D (q j)) T

def treeNativePathLog (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    AnisotropicObservationState n→Records (NativeTreePath n) (Configuration n) T→ℝ:=
  treePathLogDensity (treeNativeSpinLog D μ)
    (fun j _ Z=>edgePathLogDensity D μ (q (j+1)) (q j) Z)
    (fun j=>edgePathEndpoint D (q j)) T

instance treeNativePathKernel_markov (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    IsMarkovKernel (treeNativePathKernel D μ q T):=by
  exact isMarkovKernel_treePathRecordKernel _ _ _ _ inferInstance (fun _=>inferInstance) T

instance treeReferencePathKernel_sfinite (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    IsSFiniteKernel (treeReferencePathKernel D q T):=by
  exact isSFiniteKernel_treePathRecordKernel _ _ _ _ T

theorem treeNativePathKernel_exp_density (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    treeNativePathKernel D μ q T=(treeReferencePathKernel D q T).withDensity
      (fun x Z=>ENNReal.ofReal (Real.exp (treeNativePathLog D μ q T x Z))) := by
  exact treePathRecordKernel_exp_density _ _ _ _ _ _ _ _
    (measurable_treeNativeSpinLog D μ)
    (fun j=>by
      convert (continuous_edgePathLogDensity D μ (q (j+1)) (q j)).measurable.comp
        (measurable_snd : Measurable (fun p:AnisotropicObservationState n×NativeTreePath n=>p.2)) using 1
      rfl)
    (treeNativeSpinKernel_exp_density D μ)
    (fun j=>edgePhysicalPathKernel_exp_density D μ _ _ (hq j)) T

end HexagonPaper
