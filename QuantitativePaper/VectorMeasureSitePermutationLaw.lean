module
public import QuantitativePaper.VectorMeasureSitePermutationPotential
public import QuantitativePaper.VectorDyadicSpinMeanConvergence

@[expose] public section

/-! The actual arbitrary-profile Picard state and fractional disorder tilt
are covariant under site permutations, including their independent Wiener factor. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon StochasticCalculus
set_option maxHeartbeats 1500000
variable {n : ℕ}

theorem vectorMeasureDrift_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (r : ℝ≥0)
    (p : Couplings n × ℝ) (x : Field n) :
    vectorMeasureDrift μ β t ht r (siteDisorderPermutation π p) (siteFieldPermutation π x)=
      siteFieldPermutation π (vectorMeasureDrift μ β t ht r p x) := by
  simp only [vectorMeasureDrift,vectorMeasureGradient_site_permutation μ π β t ht,map_smul]

theorem vectorMeasureState_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (r : ℝ≥0) (hr : r≤1)
    (sample : VectorDisorderBrownianSample n) :
    vectorMeasureState μ β t ht r (siteSamplePermutation π sample)=
      siteFieldPermutation π (vectorMeasureState μ β t ht r sample) := by
  let P := siteFieldPermutation π
  let d := vectorMeasureDriftData (n:=n) μ β t ht
  have he (u : ℝ≥0) (hu : u≤1) :
      P (vectorMeasureState μ β t ht u sample)=
        0+Real.sqrt ((1-t)*β^2) • disorderVectorBrownian u (siteSamplePermutation π sample)+
        ∫s in Ioc (0 : ℝ≥0) u,
          d.drift s (siteSamplePermutation π sample).1
            (P (vectorMeasureState μ β t ht s sample)) ∂nonnegativeLebesgueMeasure := by
    have h := congrArg P (vectorAdditiveState_equation d (Real.sqrt ((1-t)*β^2)) 0 1 u hu sample)
    change P (vectorMeasureState μ β t ht u sample)=P (0+_+_) at h
    simp only [map_add,map_zero,map_smul] at h
    change P (vectorMeasureState μ β t ht u sample)=
      0+Real.sqrt ((1-t)*β^2) • P (disorderVectorBrownian u sample)+
      P (∫s in (0 : ℝ)..(u : ℝ),d.drift s.toNNReal sample.1
        (vectorMeasureState μ β t ht s.toNNReal sample)) at h
    rw [vectorIntegral_Ioc_eq_interval]
    have hc : P (∫s in (0 : ℝ)..(u : ℝ),d.drift s.toNNReal sample.1
        (vectorMeasureState μ β t ht s.toNNReal sample))=
      ∫s in (0 : ℝ)..(u : ℝ),P (d.drift s.toNNReal sample.1
        (vectorMeasureState μ β t ht s.toNNReal sample)) :=
      (P.toLinearIsometry.intervalIntegral_comp_comm _).symm
    rw [hc] at h
    rw [disorderVectorBrownian_site_permutation]
    refine h.trans ?_
    congr 2
    funext s
    change P (vectorMeasureDrift μ β t ht s.toNNReal sample.1
      (vectorMeasureState μ β t ht s.toNNReal sample))=
        vectorMeasureDrift μ β t ht s.toNNReal (siteDisorderPermutation π sample.1)
          (P (vectorMeasureState μ β t ht s.toNNReal sample))
    exact (vectorMeasureDrift_site_permutation μ π β t ht _ _ _).symm
  exact ((vectorAdditiveState_unique d (Real.sqrt ((1-t)*β^2)) 0 1
    (siteSamplePermutation π sample) (fun u=>P (vectorMeasureState μ β t ht u sample))
      (P.continuous.comp (continuous_vectorMeasureState μ β t ht sample)) he) r hr).symm

theorem vectorMeasureSpinMean_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    vectorMeasureSpinMean μ β t ht q (siteSamplePermutation π sample)=
      siteFieldPermutation π (vectorMeasureSpinMean μ β t ht q sample) := by
  unfold vectorMeasureSpinMean
  rw [vectorMeasureState_site_permutation μ π β t ht _
    (by apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal _ q.property.1]; exact q.property.2)]
  exact vectorMeasureGradient_site_permutation μ π β t ht q _ _

theorem vectorMeasureOuterWeight_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t a : ℝ) (ht : t≤1) (p : Couplings n × ℝ) :
    vectorMeasureOuterWeight μ β t a (siteDisorderPermutation π p)=
      vectorMeasureOuterWeight μ β t a p := by
  unfold vectorMeasureOuterWeight
  have h := vectorMeasurePotential_site_permutation μ π β t ht p 0
  simpa only [map_zero] using congrArg
    (fun u : ℝ=>Real.exp (a*u)/vectorMeasureOuterPartition (n:=n) μ β t a) h

theorem measurePreserving_siteSamplePermutation_tilt (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t a : ℝ) (ht : t≤1) :
    MeasurePreserving (siteSamplePermutation π)
      (vectorMeasureDisorderTilt (n:=n) μ β t a) (vectorMeasureDisorderTilt μ β t a) := by
  refine ⟨(siteSamplePermutation π).measurable,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (siteSamplePermutation π).measurable hS]
  unfold vectorMeasureDisorderTilt
  rw [withDensity_apply _ ((siteSamplePermutation π).measurable hS),withDensity_apply _ hS]
  have h := (measurePreserving_siteSamplePermutation π).setLIntegral_comp_preimage
    hS (((measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst).ennreal_ofReal)
  change (∫⁻z in (siteSamplePermutation π) ⁻¹' S,
    ENNReal.ofReal (vectorMeasureOuterWeight μ β t a (siteDisorderPermutation π z.1))
      ∂vectorDisorderBrownianMeasure n)=_ at h
  simpa only [Function.comp_def,vectorMeasureOuterWeight_site_permutation μ π β t a ht] using h

end QuantitativePaper
