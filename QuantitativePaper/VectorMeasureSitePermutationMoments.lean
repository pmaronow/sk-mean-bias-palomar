module
public import QuantitativePaper.VectorMeasureSitePermutationLaw
public import QuantitativePaper.VectorMeanOverlapNorm
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-! Exact site exchangeability consequences under the native tilted SK law.
The covariance with any one squared spin mean equals the self-overlap variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1500000
variable {n : ℕ}

def vectorMeasureSiteSquare (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (i : Fin n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  (vectorMeasureSpinMean μ β t ht q sample i)^2

def vectorMeasureSelfSquare (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ‖vectorMeasureSpinMean μ β t ht q sample‖^2/(n : ℝ)

theorem vectorMeasureSelfSquare_eq_average (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    vectorMeasureSelfSquare (n:=n) μ β t ht q =
      fun sample=>(∑i : Fin n,vectorMeasureSiteSquare μ β t ht q i sample)/(n : ℝ) := by
  funext sample
  simp [vectorMeasureSelfSquare,vectorMeasureSiteSquare,EuclideanSpace.real_norm_sq_eq]

theorem measurable_vectorMeasureSiteSquare (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (i : Fin n) :
    Measurable (vectorMeasureSiteSquare (n:=n) μ β t ht q i) := by
  have hm := (adapted_vectorMeasureSpinMean (n:=n) μ β t ht q).mono
    ((vectorBrownianFiltration n).le _) le_rfl
  exact ((EuclideanSpace.proj i).measurable.comp hm).pow_const 2

theorem vectorMeasureSiteSquare_bounds (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (i : Fin n) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureSiteSquare μ β t ht q i sample∈Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _,?_⟩
  exact (sq_le_one_iff_abs_le_one _).mpr (vectorMeasureSpinMean_component_bound μ β t ht q sample i)

theorem memLp_vectorMeasureSiteSquare (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (i : Fin n) :
    MemLp (vectorMeasureSiteSquare μ β t ht q i) 2 (vectorMeasureDisorderTilt μ β t a) := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply MemLp.of_bound (measurable_vectorMeasureSiteSquare μ β t ht q i).aestronglyMeasurable 1
  exact .of_forall fun sample=>by
    rw [Real.norm_of_nonneg (vectorMeasureSiteSquare_bounds μ β t ht q i sample).1]
    exact (vectorMeasureSiteSquare_bounds μ β t ht q i sample).2

theorem memLp_vectorMeasureSelfSquare (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    MemLp (vectorMeasureSelfSquare (n:=n) μ β t ht q) 2 (vectorMeasureDisorderTilt μ β t a) := by
  rw [vectorMeasureSelfSquare_eq_average]
  have h := (memLp_finsetSum (Finset.univ : Finset (Fin n))
    (fun i _=>memLp_vectorMeasureSiteSquare μ β t a ht q i)).const_mul (n : ℝ)⁻¹
  convert h using 1
  funext z
  ring

theorem vectorMeasureSiteSquare_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (i : Fin n) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureSiteSquare μ β t ht q i (siteSamplePermutation π sample)=
      vectorMeasureSiteSquare μ β t ht q (π i) sample := by
  simp only [vectorMeasureSiteSquare,vectorMeasureSpinMean_site_permutation,siteFieldPermutation_apply]

theorem vectorMeasureSelfSquare_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    vectorMeasureSelfSquare μ β t ht q (siteSamplePermutation π sample)=
      vectorMeasureSelfSquare μ β t ht q sample := by
  simp only [vectorMeasureSelfSquare,vectorMeasureSpinMean_site_permutation,
    LinearIsometryEquiv.norm_map]

theorem integral_vectorMeasureSiteSquare_eq (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i j : Fin n) :
    (∫z,vectorMeasureSiteSquare μ β t ht q i z ∂vectorMeasureDisorderTilt μ β t a)=
      ∫z,vectorMeasureSiteSquare μ β t ht q j z ∂vectorMeasureDisorderTilt μ β t a := by
  have h := (measurePreserving_siteSamplePermutation_tilt μ (Equiv.swap i j) β t a ht).integral_comp
    (siteSamplePermutation (Equiv.swap i j)).measurableEmbedding
    (vectorMeasureSiteSquare μ β t ht q i)
  simpa only [vectorMeasureSiteSquare_site_permutation,Equiv.swap_apply_left] using h.symm

theorem covariance_vectorMeasureSelfSquare_site_eq (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i j : Fin n) :
    covariance (vectorMeasureSelfSquare μ β t ht q) (vectorMeasureSiteSquare μ β t ht q i)
      (vectorMeasureDisorderTilt μ β t a)=
    covariance (vectorMeasureSelfSquare μ β t ht q) (vectorMeasureSiteSquare μ β t ht q j)
      (vectorMeasureDisorderTilt μ β t a) := by
  unfold covariance
  have h := (measurePreserving_siteSamplePermutation_tilt μ (Equiv.swap i j) β t a ht).integral_comp
    (siteSamplePermutation (Equiv.swap i j)).measurableEmbedding
    (fun z=>(vectorMeasureSelfSquare μ β t ht q z-
      ∫w : VectorDisorderBrownianSample n,vectorMeasureSelfSquare μ β t ht q w
        ∂vectorMeasureDisorderTilt μ β t a)*
      (vectorMeasureSiteSquare μ β t ht q i z-
        ∫w,vectorMeasureSiteSquare μ β t ht q i w ∂vectorMeasureDisorderTilt μ β t a))
  simpa only [vectorMeasureSelfSquare_site_permutation,vectorMeasureSiteSquare_site_permutation,
    Equiv.swap_apply_left,integral_vectorMeasureSiteSquare_eq μ β t a ht q i j] using h.symm

theorem integral_vectorMeasureSiteSquare_eq_self (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin n) :
    (∫z,vectorMeasureSiteSquare μ β t ht q i z ∂vectorMeasureDisorderTilt μ β t a)=
      ∫z,vectorMeasureSelfSquare (n:=n) μ β t ht q z ∂vectorMeasureDisorderTilt μ β t a := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  rw [vectorMeasureSelfSquare_eq_average,integral_div,integral_finset_sum]
  · have he (j : Fin n) := integral_vectorMeasureSiteSquare_eq μ β t a ht q j i
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  · intro j _
    exact (memLp_vectorMeasureSiteSquare μ β t a ht q j).integrable (by norm_num)

theorem covariance_vectorMeasureSelfSquare_site_eq_variance (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin n) :
    covariance (vectorMeasureSelfSquare μ β t ht q) (vectorMeasureSiteSquare μ β t ht q i)
      (vectorMeasureDisorderTilt μ β t a)=
      variance (vectorMeasureSelfSquare (n:=n) μ β t ht q) (vectorMeasureDisorderTilt μ β t a) := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  rw [←covariance_self (memLp_vectorMeasureSelfSquare μ β t a ht q).aemeasurable]
  conv_rhs => arg 2; rw [vectorMeasureSelfSquare_eq_average]
  rw [show (fun z=>(∑j : Fin n,vectorMeasureSiteSquare μ β t ht q j z)/(n : ℝ))=
      fun z=>(n : ℝ)⁻¹*(∑j : Fin n,vectorMeasureSiteSquare μ β t ht q j z) by
        funext z;ring,covariance_const_mul_right,covariance_fun_sum_right]
  · have he (j : Fin n) := covariance_vectorMeasureSelfSquare_site_eq μ β t a ht q j i
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn' : (n : ℝ)≠0 := by positivity
    field_simp
  · exact fun j=>memLp_vectorMeasureSiteSquare μ β t a ht q j
  · exact memLp_vectorMeasureSelfSquare μ β t a ht q

/-- The literal native expectation and covariance identities, with no supplied
exchangeability assumption and no minimizing-profile restriction. -/
theorem vectorMeasure_site_square_exchangeability (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin n) :
    ((∫z,(vectorMeasureSpinMean μ β t ht q z i)^2 ∂vectorMeasureDisorderTilt μ β t a)=
      ∫z,‖vectorMeasureSpinMean (n:=n) μ β t ht q z‖^2/(n : ℝ)
        ∂vectorMeasureDisorderTilt μ β t a) ∧
    covariance (fun z=>‖vectorMeasureSpinMean (n:=n) μ β t ht q z‖^2/(n : ℝ))
      (fun z=>(vectorMeasureSpinMean μ β t ht q z i)^2) (vectorMeasureDisorderTilt μ β t a)=
      variance (fun z=>‖vectorMeasureSpinMean (n:=n) μ β t ht q z‖^2/(n : ℝ))
        (vectorMeasureDisorderTilt μ β t a) :=
  ⟨integral_vectorMeasureSiteSquare_eq_self hn μ β t a ht q i,
    covariance_vectorMeasureSelfSquare_site_eq_variance hn μ β t a ht q i⟩

end QuantitativePaper
