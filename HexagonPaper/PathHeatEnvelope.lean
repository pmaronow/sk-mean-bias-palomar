module
public import FourPapersCommon.WienerExponential
public import QuantitativePaper.VectorTerminal
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! A single actual integrable exponential envelope for a finite Gaussian row
and an arbitrary finite family of continuous Brownian edge/component paths.
The reciprocal envelope supplies a strictly positive lower bound for every
normalizer. This avoids division by a normalizer whose lower bound is merely
asserted, and does not require a Jensen premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper
open scoped BigOperators NNReal Topology
namespace HexagonPaper
set_option maxHeartbeats 1200000
variable {J : Type*} [Fintype J]

abbrev pathHeatBaseSample (n : ℕ) := Field n × (J → WienerPath)

def pathHeatBaseMeasure (n : ℕ) : Measure (pathHeatBaseSample (J:=J) n) :=
  (fieldGaussian n).prod (Measure.pi (fun _ : J => canonicalWienerMeasure))

instance pathHeatBaseMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (pathHeatBaseMeasure (J:=J) n) := by
  unfold pathHeatBaseMeasure
  infer_instance

def pathHeatRadius {n : ℕ} (p : pathHeatBaseSample (J:=J) n) : ℝ :=
  ‖p.1‖+∑j,‖p.2 j‖

def pathHeatEnvelope {n : ℕ} (C : ℝ) (p : pathHeatBaseSample (J:=J) n) : ℝ :=
  Real.exp (C*(1+pathHeatRadius p))

theorem pathHeatRadius_nonneg {n : ℕ} (p : pathHeatBaseSample (J:=J) n) :
    0 ≤ pathHeatRadius p := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem integrable_pathHeatEnvelope (n : ℕ) (C : ℝ) :
    Integrable (pathHeatEnvelope (J:=J) (n:=n) C) (pathHeatBaseMeasure n) := by
  have hw : Integrable (fun paths : J→WienerPath => ∏j,Real.exp (C*‖paths j‖))
      (Measure.pi (fun _ : J => canonicalWienerMeasure)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_norm_canonicalWienerMeasure C)
  have hg : Integrable (fun g : Field n => Real.exp (C*‖g‖)) (fieldGaussian n) :=
    SYK.integrable_exp_mul_norm C
  unfold pathHeatBaseMeasure
  convert (hg.mul_prod hw).const_mul (Real.exp C) using 1
  funext p
  simp only [pathHeatEnvelope,pathHeatRadius,←Real.exp_sum,Finset.mul_sum,
    ←Real.exp_add]
  congr 1;simp only [mul_add,mul_one,Finset.mul_sum]

theorem integrable_pathHeatEnvelope_power (n : ℕ) (C : ℝ) (k : ℕ) :
    Integrable (fun p : pathHeatBaseSample (J:=J) n => (pathHeatEnvelope C p)^k)
      (pathHeatBaseMeasure n) := by
  convert integrable_pathHeatEnvelope (J:=J) n ((k:ℝ)*C) using 1
  funext p
  simp only [pathHeatEnvelope,←Real.exp_nat_mul]
  congr 1;ring

/-- Uniform linear growth produces a positive normalizer and a common
positive lower bound, independently of the mesh and parameter. -/
theorem pathHeatNormalizer_common_lower_bound (n : ℕ) (C : ℝ) (hC : 0≤C)
    (ℓ : pathHeatBaseSample (J:=J) n →ℝ) (hℓ : Measurable ℓ)
    (hgrowth : ∀p,|ℓ p|≤C*(1+pathHeatRadius p)) :
    0 < (∫p,pathHeatEnvelope (J:=J) (-C) p ∂pathHeatBaseMeasure (J:=J) n) ∧
      (∫p,pathHeatEnvelope (J:=J) (-C) p ∂pathHeatBaseMeasure (J:=J) n) ≤
        (∫p,Real.exp (ℓ p) ∂pathHeatBaseMeasure (J:=J) n) := by
  have hi := integrable_pathHeatEnvelope (J:=J) n (-C)
  have hu := integrable_pathHeatEnvelope (J:=J) n C
  have hweight : Integrable (fun p=>Real.exp (ℓ p)) (pathHeatBaseMeasure n) := by
    apply hu.mono' hℓ.exp.aestronglyMeasurable
    exact .of_forall fun p => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgrowth p))
  refine ⟨integral_exp_pos hi,integral_mono hi hweight (fun p=>?_ )⟩
  apply Real.exp_le_exp.mpr
  have hh := (abs_le.mp (hgrowth p)).1
  simpa only [neg_mul] using hh

end HexagonPaper
