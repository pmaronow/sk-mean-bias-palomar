module
public import QuantitativePaper.VectorShiftedGaussianMoments
public import QuantitativePaper.VectorTaylorExpectation
public import QuantitativePaper.VectorDriftBounds
public import FourPapersCommon.VanishingPartitionErrors

@[expose] public section

/-! Actual spatial Taylor error sums vanish in expectation on a fixed time
interval. The field test may depend on the independent initial disorder and
on the deterministic left time. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal ContDiff Topology
namespace QuantitativePaper
variable {a : ℝ≥0}
open FourPapersCommon

def vectorSpatialTaylorApproxAt {n : ℕ}
    (f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ)
    (X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (σ : ℝ)
    (Z : VectorDisorderBrownianSample n → ℝ) (t : ℝ≥0) (N : ℕ)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑ j∈Finset.range N,Z sample*vectorSpatialTaylorError
    (f (uniformPartitionTime t N j)) (X (uniformPartitionTime t N j))
    (fun sample=>σ • disorderVectorBrownianIncrementAt a (uniformPartitionTime t N j)
      (uniformPartitionTime t N (j+1)) sample)
    (fun sample=>vectorIntegratedDrift (fun s=>d s sample) (uniformPartitionTime t N (j+1))-
      vectorIntegratedDrift (fun s=>d s sample) (uniformPartitionTime t N j)) sample

theorem tendsto_integral_vectorSpatialTaylorApproxAt {n : ℕ}
    (f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ)
    (hf : ∀ q sample,ContDiff ℝ 3 (f q sample)) (K₂ K₃ D : ℝ≥0)
    (h₂ : ∀ q sample x,‖iteratedFDeriv ℝ 2 (f q sample) x‖ ≤ K₂)
    (h₃ : ∀ q sample x,‖iteratedFDeriv ℝ 3 (f q sample) x‖ ≤ K₃)
    (X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hd : Measurable (Function.uncurry d)) (hD : ∀ s sample,‖d s sample‖ ≤ D)
    (σ : ℝ) (Z : VectorDisorderBrownianSample n → ℝ) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C)
    (hR : ∀ r s,r ≤ s → AEStronglyMeasurable (fun sample=>Z sample*vectorSpatialTaylorError
      (f r) (X r) (fun sample=>σ • disorderVectorBrownianIncrementAt a r s sample)
      (fun sample=>vectorIntegratedDrift (fun q=>d q sample) s-
        vectorIntegratedDrift (fun q=>d q sample) r) sample) (vectorDisorderBrownianMeasure n))
    (t : ℝ≥0) :
    Tendsto (fun N=>∫ sample,vectorSpatialTaylorApproxAt (a:=a) f X d σ Z t (N+1) sample
      ∂vectorDisorderBrownianMeasure n) atTop (𝓝 0) := by
  let e : ℕ → ℕ → VectorDisorderBrownianSample n → ℝ := fun N j sample=>
    Z sample*vectorSpatialTaylorError (f (uniformPartitionTime t (N+1) j))
      (X (uniformPartitionTime t (N+1) j))
      (fun sample=>σ • disorderVectorBrownianIncrementAt a (uniformPartitionTime t (N+1) j)
        (uniformPartitionTime t (N+1) (j+1)) sample)
      (fun sample=>vectorIntegratedDrift (fun q=>d q sample) (uniformPartitionTime t (N+1) (j+1))-
        vectorIntegratedDrift (fun q=>d q sample) (uniformPartitionTime t (N+1) j)) sample
  have hrt (N j : ℕ) : uniformPartitionTime t (N+1) j ≤ uniformPartitionTime t (N+1) (j+1) :=
    monotone_uniformPartitionTime t (N+1) (Nat.le_add_right j 1)
  have hlen (N j : ℕ) :
      ((uniformPartitionTime t (N+1) (j+1) : ℝ≥0) : ℝ)-
        ((uniformPartitionTime t (N+1) j : ℝ≥0) : ℝ) = (t : ℝ)/((N : ℝ)+1) := by
    have hh := dist_uniformPartitionTime_succ_eq t (Nat.succ_pos N) j
    rw [NNReal.dist_eq,abs_of_nonneg
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hrt N j)))] at hh
    simpa only [NNReal.coe_div,NNReal.coe_natCast,Nat.cast_add,Nat.cast_one,Nat.cast_succ,
      NNReal.coe_add,NNReal.coe_one] using hh
  have hcell (N j : ℕ) := integral_weighted_vectorSpatialTaylorError_boundAt a
    (uniformPartitionTime t (N+1) j) (uniformPartitionTime t (N+1) (j+1)) (hrt N j) σ
    (f (uniformPartitionTime t (N+1) j)) (hf _) K₂ K₃ D (h₂ _) (h₃ _)
    (X (uniformPartitionTime t (N+1) j))
    (fun sample=>vectorIntegratedDrift (fun q=>d q sample) (uniformPartitionTime t (N+1) (j+1))-
      vectorIntegratedDrift (fun q=>d q sample) (uniformPartitionTime t (N+1) j))
    (fun sample=>vectorIntegratedDrift_increment_bound (fun q=>d q sample)
      (hd.comp (measurable_id.prodMk measurable_const)) D (fun q=>hD q sample) (hrt N j))
    Z C hC (hR _ _ (hrt N j))
  have hi (N j : ℕ) (_ : j∈Finset.range (N+1)) : Integrable (e N j)
      (vectorDisorderBrownianMeasure n) := (hcell N j).1
  have hb (N j : ℕ) (_ : j∈Finset.range (N+1)) :
      ‖∫ sample,e N j sample ∂vectorDisorderBrownianMeasure n‖ ≤
        (C*(2*K₃*|σ|^3*vectorGaussianNormMoment n 3+
          K₂*|σ| *D*vectorGaussianNormMoment n 1))*((t : ℝ)/(N+1))*Real.sqrt ((t : ℝ)/(N+1))+
        (C*K₂/2*D^2)*((t : ℝ)/(N+1))^2+
        (2*C*K₃*D^3)*((t : ℝ)/(N+1))^3 := by
    have hh := (hcell N j).2
    rw [hlen] at hh
    rw [Real.norm_eq_abs]
    convert hh using 1 <;> ring
  exact tendsto_integral_partition_errors (vectorDisorderBrownianMeasure n) e t
    (C*(2*K₃*|σ|^3*vectorGaussianNormMoment n 3+K₂*|σ| *D*vectorGaussianNormMoment n 1))
    (C*K₂/2*D^2) (2*C*K₃*D^3) hi hb

end QuantitativePaper
