module
public import HexagonPaper.TreeLikelihoodCoalescing
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-! The normalized complete native tree law. Its root is the actual
Gaussian disorder tilt and its edges and spins are genuine normalized
native kernels. The positive full tree charge has mass k−a; its common
normalizer is the actual root disorder partition. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ENNReal
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def treeObservationGaussianLaw (n : ℕ):Measure (AnisotropicObservationState n):=
  (anisotropicDisorderLaw n).map (fun g=>(g,(0:Field n)))

instance treeObservationGaussianLaw_probability (n : ℕ):IsProbabilityMeasure (treeObservationGaussianLaw n):=by
  unfold treeObservationGaussianLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_id.prodMk measurable_const).aemeasurable).mpr inferInstance

def treeObservationRootDensity (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (x : AnisotropicObservationState n):ℝ≥0∞:=
  ENNReal.ofReal (Real.exp (a*anisotropicMeasurePotential D μ (anisotropicObservationParameter D x))/
    anisotropicMeasureOuterPartition D μ a)

theorem measurable_treeObservationRootDensity (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ):Measurable (treeObservationRootDensity D μ a):=by
  exact ((measurable_const.mul ((anisotropicMeasurePotential_lipschitz D μ).continuous.measurable.comp
    (measurable_anisotropicObservationParameter D))).exp.div_const _).ennreal_ofReal

theorem anisotropicObservationInitialLaw_tree_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ):
    anisotropicObservationInitialLaw D μ a=(treeObservationGaussianLaw n).withDensity
      (treeObservationRootDensity D μ a):=by
  have hm:Measurable (fun g:AnisotropicDisorder n=>(g,(0:Field n))):=
    measurable_id.prodMk measurable_const
  have hf:(fun g:AnisotropicDisorder n=>treeObservationRootDensity D μ a (g,(0:Field n)))=
      (fun g=>ENNReal.ofReal (Real.exp
        (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g))/
          anisotropicMeasureOuterPartition D μ a)):=by
    funext g
    unfold treeObservationRootDensity anisotropicObservationParameter
    simp only [map_zero,add_zero]
  have hd:=FRSB.map_withDensity_pullback (anisotropicDisorderLaw n)
    (fun g:AnisotropicDisorder n=>(g,(0:Field n))) hm
    (treeObservationRootDensity D μ a) (measurable_treeObservationRootDensity D μ a)
  rw [hf] at hd
  unfold anisotropicObservationInitialLaw treeObservationGaussianLaw
  rw [anisotropicMeasureOuterLaw_density]
  exact hd

def treeNativeFullLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    Measure (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T):=
  anisotropicObservationInitialLaw D μ a ⊗ₘ treeNativePathKernel D μ q T

instance treeNativeFullLaw_probability (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    IsProbabilityMeasure (treeNativeFullLaw D μ a q T):=by
  unfold treeNativeFullLaw
  infer_instance

def treeReferenceFullLaw (D : AnisotropicSpinModel n) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    Measure (AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T):=
  treeObservationGaussianLaw n ⊗ₘ treeReferencePathKernel D q T

def treePrintedFullDensity (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (p : AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T):ℝ≥0∞:=
  ENNReal.ofReal (Real.exp (treeNativeTerminalEnergy D q T p.1 p.2-
    ∫v,treeNativeFullPotential D μ q T p.1 p.2 v ∂treePathWeight μ a q T)/
      anisotropicMeasureOuterPartition D μ a)

theorem treeNativeFullLaw_printed_density (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (hμ : μ∈scalarFloor a) (q : ℕ→Paper.Overlap) (h0 : q 0=1)
    (hq : ∀j,q (j+1)≤q j) {j : ℕ} (T : FiniteTerminalGenealogy j) (hroot : q j=0):
    treeNativeFullLaw D μ a q T=(treeReferenceFullLaw D q T).withDensity
      (treePrintedFullDensity D μ a q T):=by
  have hm:Measurable (Function.uncurry (treeNativeSourceLog D μ q T)):=
    measurable_treePathLogDensity _ _ _ (fun j=>measurable_edgePathEndpoint D (q j))
      (measurable_treeNativeSpinLog D μ) (fun j=>measurable_edgePathSourceLog D μ (q (j+1)) (q j)) T
  have hk:=treeNativePathKernel_source_exp_density D μ q hq T
  haveI:IsSFiniteKernel ((treeReferencePathKernel D q T).withDensity
      (fun x Z=>ENNReal.ofReal (Real.exp (treeNativeSourceLog D μ q T x Z)))):=by
    rw [←hk]
    infer_instance
  unfold treeNativeFullLaw treeReferenceFullLaw
  rw [anisotropicObservationInitialLaw_tree_density,hk,
    Measure.withDensity_compProd_withDensity (measurable_treeObservationRootDensity D μ a)
      hm.exp.ennreal_ofReal]
  congr 1
  funext p
  unfold treeObservationRootDensity treePrintedFullDensity
  rw [←ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le
    (anisotropicMeasureOuterPartition_pos D μ a).le),div_mul_eq_mul_div,←Real.exp_add]
  congr 1
  congr 1
  have hu:anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D p.1)=
      anisotropicMeasurePotential D μ (anisotropicObservationParameter D p.1):=by
    rw [hroot]
    exact anisotropicMeasureTailPotential_zero D μ _
  rw [←hu]
  exact congrArg Real.exp (treeNativeSourceLog_full_weight D μ a hμ q h0 T p.1 p.2).2

end HexagonPaper
