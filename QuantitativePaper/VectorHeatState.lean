module
public import QuantitativePaper.VectorItoTimeExpectation
public import QuantitativePaper.VectorBrownianMoments

@[expose] public section

/-! The actual zero-drift vector Wiener state and its literal Gaussian
averaging law, used in finite-cell Duhamel verification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 400000

def vectorHeatState {n : ℕ} (σ : ℝ) (x : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n := x+σ • disorderVectorBrownian r sample

theorem continuous_vectorHeatState {n : ℕ} (σ : ℝ) (x : Field n)
    (sample : VectorDisorderBrownianSample n) : Continuous (fun r => vectorHeatState σ x r sample) :=
  continuous_const.add ((continuous_disorderVectorBrownian sample).const_smul σ)

theorem measurable_uncurry_vectorHeatState {n : ℕ} (σ : ℝ) (x : Field n) :
    Measurable (Function.uncurry (vectorHeatState (n := n) σ x)) :=
  measurable_const.add ((measurable_uncurry_disorderVectorBrownian n).const_smul σ)

theorem stronglyAdapted_vectorHeatState {n : ℕ} (σ : ℝ) (x : Field n) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorHeatState (n := n) σ x) := by
  intro r
  exact stronglyMeasurable_const.add ((stronglyAdapted_disorderVectorBrownian n r).const_smul σ)

@[simp] theorem vectorHeatState_zero {n : ℕ} (σ : ℝ) (x : Field n)
    (sample : VectorDisorderBrownianSample n) : vectorHeatState σ x 0 sample=x := by
  simp [vectorHeatState,disorderVectorBrownian]

theorem vectorItoCharacteristics_vectorHeatState {n : ℕ} (σ : ℝ) (x : Field n) :
    VectorItoCharacteristics (vectorHeatState σ x) (fun _ _ => 0) σ where
  continuous_state := continuous_vectorHeatState σ x
  measurable_state := measurable_uncurry_vectorHeatState σ x
  adapted_state := stronglyAdapted_vectorHeatState σ x
  measurable_drift := measurable_const
  bounded_drift := ⟨0,by simp⟩
  decomposition := by intro r sample;simp [vectorHeatState,vectorIntegratedDrift,disorderVectorBrownian]

theorem hasLaw_disorderVectorBrownian {n : ℕ} (r : ℝ≥0) :
    HasLaw (disorderVectorBrownian (n := n) r) (fieldIncrementLaw n r)
      (vectorDisorderBrownianMeasure n) := by
  have hh := hasLaw_disorderVectorBrownianIncrement (n := n) 0 r (bot_le)
  convert hh using 1
  · funext sample
    simp [disorderVectorBrownianIncrement,disorderVectorBrownian]
  · simp

theorem integral_vectorHeatState_eq_heat {n : ℕ} (c : ℝ) (hc : 0≤c) (x : Field n)
    (r : ℝ≥0) (ψ : Field n→ℝ) (hψ : Measurable ψ) :
    (∫ sample,ψ (vectorHeatState (Real.sqrt c) x r sample) ∂vectorDisorderBrownianMeasure n)=
      ∫ z,ψ (fieldShift (c*(r : ℝ)) x z) ∂fieldGaussian n := by
  have hh := (hasLaw_disorderVectorBrownian (n := n) r).integral_comp
    ((hψ.comp (by fun_prop : Measurable (fun z : Field n => x+Real.sqrt c • z))).aestronglyMeasurable)
  change (∫ sample,ψ (x+Real.sqrt c • disorderVectorBrownian r sample)
    ∂vectorDisorderBrownianMeasure n)=∫ z,ψ (x+Real.sqrt c • z) ∂fieldIncrementLaw n r at hh
  have hmap : (∫ z,ψ (x+Real.sqrt c • z) ∂fieldIncrementLaw n r)=
      ∫ z,ψ (x+Real.sqrt c • (Real.sqrt (r : ℝ) • z)) ∂fieldGaussian n :=
    integral_map_of_stronglyMeasurable
      (by fun_prop : Measurable (fun z : Field n => Real.sqrt (r : ℝ) • z))
      (hψ.comp (by fun_prop : Measurable (fun z : Field n => x+Real.sqrt c • z))).stronglyMeasurable
  have hh := hh.trans hmap
  exact hh.trans (integral_congr_ae (Eventually.of_forall (fun z => by
    change ψ (x+Real.sqrt c • (Real.sqrt (r : ℝ) • z))=ψ (fieldShift (c*(r : ℝ)) x z)
    congr 1
    rw [smul_smul,←Real.sqrt_mul hc]
    rfl)))

end QuantitativePaper
