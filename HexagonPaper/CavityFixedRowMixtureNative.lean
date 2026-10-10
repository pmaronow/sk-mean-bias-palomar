module
public import HexagonPaper.CavityFixedRowMixtureBasic
public import HexagonPaper.TreeLikelihoodNative
public import HexagonPaper.CavityTreeUnitCouplings
public import QuantitativeFollowup.FollowupCavityIncidentRow

@[expose] public section

/-! Actual arbitrary-profile fixed-row laws. The unit-coupling chart uses
the genuine restarted-diffusion path kernel, with the original positive
auxiliary variances. The deterministic incident row is added before the
actual Gaussian root tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped BigOperators NNReal
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def cavityNativeIncidentRow (n : ℕ) : Field n →L[ℝ] AnisotropicDisorder (n+1) :=
  ∑ i : Fin n, (EuclideanSpace.proj i).smulRight
    (EuclideanSpace.single (followupCavityIncidentIndex i) 1)

theorem cavityNativeIncidentRow_apply (θ : Field n) :
    cavityNativeIncidentRow n θ = ∑ i : Fin n,
      θ i • EuclideanSpace.single (followupCavityIncidentIndex i) 1 := by
  simp only [cavityNativeIncidentRow, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

def cavityNativeRestDisorder (D : AnisotropicSpinModel (n+1)) :
    AnisotropicDisorder (n+1) →L[ℝ] AnisotropicDisorder (n+1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => WithLp.toLp 2 (fun e => D.coupling e * g e)
      map_add' := by intro g h; ext e; simp [mul_add]
      map_smul' := by intro c g; ext e; simp [mul_left_comm] }

@[simp] theorem cavityNativeRestDisorder_apply (D : AnisotropicSpinModel (n+1))
    (g : AnisotropicDisorder (n+1)) (e : AnisotropicCouplingIndex (n+1)) :
    cavityNativeRestDisorder D g e = D.coupling e * g e := rfl

def cavityNativeFixedRowPotential (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder (n+1)) : ℝ :=
  anisotropicMeasurePotential (anisotropicUnitCouplings D) μ
    (anisotropicDisorderInjection (n+1) g)

theorem cavityNativeFixedRowPotential_lipschitz (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) :
    LipschitzWith (‖anisotropicEnergyMap (anisotropicUnitCouplings D)‖₊ *
      ‖anisotropicDisorderInjection (n+1)‖₊) (cavityNativeFixedRowPotential D μ) :=
  (anisotropicMeasurePotential_lipschitz (anisotropicUnitCouplings D) μ).comp
    (anisotropicDisorderInjection (n+1)).lipschitz

def cavityNativeFixedRowKernel (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) :
    Kernel (AnisotropicDisorder (n+1))
      (Records (NativeTreePath (n+1)) (Configuration (n+1)) T) :=
  (treeNativePathKernel (anisotropicUnitCouplings D) μ q T).comap
    (fun g => (g, (0 : QuantitativePaper.Field (n+1)))) (measurable_id.prodMk measurable_const)

instance cavityNativeFixedRowKernel_markov (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) : IsMarkovKernel (cavityNativeFixedRowKernel D μ q T) := by
  unfold cavityNativeFixedRowKernel
  infer_instance

def cavityNativeFixedRowNormalizer (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (θ : Field n) : ℝ :=
  cavityGaussianRootNormalizer (cavityNativeFixedRowPotential D μ) a
    (cavityNativeRestDisorder D) (cavityNativeIncidentRow n θ)

def cavityNativeFixedRowLaw (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (θ : Field n) :=
  cavityGaussianRootJoint (cavityNativeFixedRowPotential D μ) a
    (cavityNativeRestDisorder D) (cavityNativeIncidentRow n θ)
    (cavityNativeFixedRowKernel D μ q T)

theorem cavityNativeFixedRowNormalizer_pos (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (θ : Field n) :
    0 < cavityNativeFixedRowNormalizer D μ a θ :=
  cavityGaussianRootNormalizer_pos _ (cavityNativeFixedRowPotential_lipschitz D μ) a _ _

instance cavityNativeFixedRowLaw_probability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (θ : Field n) :
    IsProbabilityMeasure (cavityNativeFixedRowLaw D μ a q T θ) :=
  cavityGaussianRootJoint_probability _ (cavityNativeFixedRowPotential_lipschitz D μ) a _ _ _

def cavityNativeGaussianRowLaw (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : ℝ) :=
  cavityGaussianRootJoint (cavityNativeFixedRowPotential D μ) a
    (finiteStateGaussianSumMap (Real.sqrt v • cavityNativeIncidentRow n)
      (cavityNativeRestDisorder D)) 0 (cavityNativeFixedRowKernel D μ q T)

def cavityNativeIncidentGaussian (n : ℕ) (v : ℝ) : Measure (Field n) :=
  (stdGaussian (Field n)).map (fun g => Real.sqrt v • g)

theorem cavityNativeFixedRow_weighted_mixture_standard (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : ℝ)
    (F : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ)
    (hF : Measurable F) (B : ℝ) (hb : ∀ z, ‖F z‖ ≤ B) :
    (∫ z, F z ∂cavityNativeGaussianRowLaw D μ a q T v) =
      (∫ g, cavityNativeFixedRowNormalizer D μ a (Real.sqrt v • g) *
        (∫ z, F z ∂cavityNativeFixedRowLaw D μ a q T (Real.sqrt v • g))
        ∂stdGaussian (Field n)) /
      (∫ g, cavityNativeFixedRowNormalizer D μ a (Real.sqrt v • g)
        ∂stdGaussian (Field n)) := by
  simpa only [cavityNativeGaussianRowLaw, cavityNativeFixedRowNormalizer,
    cavityNativeFixedRowLaw, zero_add, ContinuousLinearMap.smul_apply, map_smul] using
    cavityGaussianRootJoint_weighted_mixture (cavityNativeFixedRowPotential D μ)
      (cavityNativeFixedRowPotential_lipschitz D μ) a
      (Real.sqrt v • cavityNativeIncidentRow n) (cavityNativeRestDisorder D) 0
      (cavityNativeFixedRowKernel D μ q T) F hF B hb

end HexagonPaper
