module
public import FourPapersCommon.FiniteCascadeTreeCoordinateScaling
public import QuantitativeFollowup.FollowupCavityNodeBModel
public import QuantitativeFollowup.FollowupCavityRootCharges

@[expose] public section

/-! A positive spatial variance is realized by scaling exactly its independent
edge coordinates, retaining the actual coupling disorder and every zero cell. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open FourPapersCommon FiniteTerminalGenealogy QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def cavityPathVarianceMultiplier (i : Fin n) (b : ℝ) (l : Fin n) : ℝ :=
  if l=i then Real.sqrt b else 1

theorem cavityPathVarianceInput_coordinate_scaling (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (b : ℝ) (hb : 0<b) (j : ℕ) :
    cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s j =
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s j).comp
        (finiteGaussianDiagonal (cavityPathVarianceMultiplier i b)) := by
  classical
  apply finiteStateCLM_eq_of_single
  intro l
  rw [ContinuousLinearMap.comp_apply,finiteGaussianDiagonal_single,map_smul]
  ext σ
  simp only [PiLp.smul_apply,smul_eq_mul,cavityFiniteEnergyInput_single]
  rw [anisotropicReplaceVariance_variance D i l b hb,
    anisotropicReplaceVariance_variance D i l 1 (by norm_num)]
  by_cases hl : l=i
  · simp only [hl,ite_true,cavityPathVarianceMultiplier,Real.sqrt_one]
    ring
  · simp only [hl,ite_false,cavityPathVarianceMultiplier,one_mul]

theorem anisotropicRootEnergyMap_replaceVariance (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) :
    anisotropicRootEnergyMap (anisotropicReplaceVariance D i b)=anisotropicRootEnergyMap D := by
  unfold anisotropicRootEnergyMap
  rw [anisotropicReplaceVariance_energyMap]

theorem cavityPathVariance_reference_record (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (b : ℝ) (hb : 0<b)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : FiniteStateGaussianInput (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T))
    (σ : TerminalSpins (Configuration n) T) :
    finiteCascadeTreeReferenceRootFlatRecord
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) T
        (anisotropicRootEnergyMap D) 0 (z,σ) =
      finiteCascadeTreeReferenceRootFlatRecord
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T
          (anisotropicRootEnergyMap D) 0
          (finiteGaussianDiagonal (Sum.elim (fun _ : AnisotropicCouplingIndex n => 1)
            (finiteCascadeEdgeMultiplier (cavityPathVarianceMultiplier i b) T)) z,σ) := by
  have he : cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s =
      fun p => (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s p).comp
        (finiteGaussianDiagonal (cavityPathVarianceMultiplier i b)) := by
    funext p
    exact cavityPathVarianceInput_coordinate_scaling D s i b hb p
  rw [he]
  exact finiteCascadeTreeReferenceRootFlatRecord_coordinate_scaling _ _ _ _ _ _ _

def cavityPathVarianceFixedRecordDensity (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) (b : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (p : FiniteStateGaussianInput (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T) ×
      TerminalSpins (Configuration n) T) : ℝ :=
  finiteCascadeTreeGaussianRecordDensity (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T
      (anisotropicRootEnergyMap D) 0
      (finiteCascadeTreeReferenceRootFlatRecord
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T
          (anisotropicRootEnergyMap D) 0
          (finiteGaussianDiagonal (Sum.elim (fun _ : AnisotropicCouplingIndex n => 1)
            (finiteCascadeEdgeMultiplier (cavityPathVarianceMultiplier i b) T)) p.1,p.2))

theorem cavityPathVariance_flat_density (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) (b : ℝ) (hb : 0<b) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T
        (anisotropicRootEnergyMap D) 0 = cavityPathVarianceFixedRecordDensity D s a i b T := by
  funext p
  simp only [finiteCascadeTreeGaussianFlatDensity,Function.comp_def,cavityPathVarianceFixedRecordDensity]
  rw [cavityPathVariance_reference_record D s i b hb]

theorem integrable_cavityPathVarianceFixedRecordDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) (b : ℝ) (hb : 0<b)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Integrable (cavityPathVarianceFixedRecordDensity D s a i b T)
      (finiteCascadeTreeGaussianFlatReferenceMeasure
        (S:=Configuration n) (I:=Fin n) (J:=AnisotropicCouplingIndex n) T) := by
  rw [←cavityPathVariance_flat_density D s a i b hb T]
  exact integrable_finiteCascadeTreeGaussianFlatDensity _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

theorem integral_cavityPathVarianceFixedRecordDensity_one (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) (b : ℝ) (hb : 0<b)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (∫p,cavityPathVarianceFixedRecordDensity D s a i b T p
      ∂finiteCascadeTreeGaussianFlatReferenceMeasure
        (S:=Configuration n) (I:=Fin n) (J:=AnisotropicCouplingIndex n) T)=1 := by
  rw [←cavityPathVariance_flat_density D s a i b hb T]
  exact integral_finiteCascadeTreeGaussianFlatDensity_one _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

end QuantitativeFollowup
