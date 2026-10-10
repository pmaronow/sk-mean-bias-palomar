module
public import QuantitativeFollowup.FollowupCavityFourEndpointContact
public import QuantitativeFollowup.FollowupCavityCppFourDescendant
public import QuantitativeFollowup.FollowupCavityFourVarianceComparison

@[expose] public section

/-! Actual endpoint covariance transport and the source's exchangeable
one-site decomposition of the full self-overlap variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followup_cavity_one_covariance_spin_mean (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (q : Paper.Overlap) (H K : QuantitativePaper.Field (n+1) → ℝ) (hH : Continuous H) (hK : Continuous K)
    (CH CK : ℝ)
    (hHB : ∀ m : QuantitativePaper.Field (n+1), (∀ i, ‖m i‖ ≤ 1) → ‖H m‖ ≤ CH)
    (hKB : ∀ m : QuantitativePaper.Field (n+1), (∀ i, ‖m i‖ ≤ 1) → ‖K m‖ ≤ CK) :
    covariance (fun sample => H (anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one, le_rfl⟩) μ q sample))
      (fun sample => K (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one, le_rfl⟩) μ q sample))
      (anisotropicMeasureSampleLaw
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one, le_rfl⟩) μ a) =
    covariance (fun sample => H (vectorMeasureSpinMean μ β (1-ρ) (by linarith [hρ.1]) q sample))
      (fun sample => K (vectorMeasureSpinMean μ β (1-ρ) (by linarith [hρ.1]) q sample))
      (vectorMeasureDisorderTilt μ β (1-ρ) a) := by
  let D := followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one, le_rfl⟩
  let ht : 1-ρ ≤ 1 := by linarith [hρ.1]
  haveI := vectorMeasureDisorderTilt_probability (n:=n+1) μ β (1-ρ) a ht
  have hm : Measurable (anisotropicProcessMagnetization D μ q) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_uncurry_anisotropicProcessMagnetization D μ).comp
        ((measurable_const (a := q)).prodMk measurable_id)
  have hv : Measurable (vectorMeasureSpinMean (n:=n+1) μ β (1-ρ) ht q) :=
    (adapted_vectorMeasureSpinMean μ β (1-ρ) ht q).mono
      ((vectorBrownianFiltration (n+1)).le _) le_rfl
  have hPH : MemLp (fun sample => H (anisotropicProcessMagnetization D μ q sample)) 2
      (anisotropicMeasureSampleLaw D μ a) := MemLp.of_bound
    (hH.measurable.comp hm).aestronglyMeasurable CH
    (.of_forall fun sample => hHB _ (fun i => anisotropicProcessSpinResponse_bound D μ q i sample))
  have hPK : MemLp (fun sample => K (anisotropicProcessMagnetization D μ q sample)) 2
      (anisotropicMeasureSampleLaw D μ a) := MemLp.of_bound
    (hK.measurable.comp hm).aestronglyMeasurable CK
    (.of_forall fun sample => hKB _ (fun i => anisotropicProcessSpinResponse_bound D μ q i sample))
  have hVH : MemLp (fun sample => H (vectorMeasureSpinMean μ β (1-ρ) ht q sample)) 2
      (vectorMeasureDisorderTilt μ β (1-ρ) a) := MemLp.of_bound
    (hH.measurable.comp hv).aestronglyMeasurable CH
    (.of_forall fun sample => hHB _ (fun i => by
      simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β (1-ρ) ht q sample i))
  have hVK : MemLp (fun sample => K (vectorMeasureSpinMean μ β (1-ρ) ht q sample)) 2
      (vectorMeasureDisorderTilt μ β (1-ρ) a) := MemLp.of_bound
    (hK.measurable.comp hv).aestronglyMeasurable CK
    (.of_forall fun sample => hKB _ (fun i => by
      simpa only [Real.norm_eq_abs] using vectorMeasureSpinMean_component_bound μ β (1-ρ) ht q sample i))
  rw [covariance_eq_sub hPH hPK, covariance_eq_sub hVH hVK]
  change (∫sample, H (anisotropicProcessMagnetization D μ q sample) *
      K (anisotropicProcessMagnetization D μ q sample) ∂anisotropicMeasureSampleLaw D μ a) -
      (∫sample, H (anisotropicProcessMagnetization D μ q sample) ∂anisotropicMeasureSampleLaw D μ a) *
      (∫sample, K (anisotropicProcessMagnetization D μ q sample) ∂anisotropicMeasureSampleLaw D μ a) = _
  rw [followup_cavity_one_integral_spin_mean hn μ β ρ a hβ hρ q
      (fun m => H m * K m) (hH.mul hK),
    followup_cavity_one_integral_spin_mean hn μ β ρ a hβ hρ q H hH,
    followup_cavity_one_integral_spin_mean hn μ β ρ a hβ hρ q K hK]
  rfl

theorem vector_full_variance_one_site_decomposition (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) :
    variance (vectorMeasureSelfSquare (n:=n+1) μ β t ht q) (vectorMeasureDisorderTilt μ β t a) =
      variance (vectorMeasureSiteSquare μ β t ht q (Fin.last n)) (vectorMeasureDisorderTilt μ β t a) /
        (n+1 : ℕ) +
      (n : ℝ)/(n+1 : ℕ) * covariance
        (vectorMeasureSiteSquare μ β t ht q (Fin.last n))
        (cavityDeletedSiteSelfOverlap μ β t ht q (Fin.last n)) (vectorMeasureDisorderTilt μ β t a) := by
  let P := vectorMeasureDisorderTilt (n:=n+1) μ β t a
  let S := vectorMeasureSelfSquare (n:=n+1) μ β t ht q
  let f := vectorMeasureSiteSquare μ β t ht q (Fin.last n)
  haveI := vectorMeasureDisorderTilt_probability (n:=n+1) μ β t a ht
  have hS : MemLp S 2 P := memLp_vectorMeasureSelfSquare μ β t a ht q
  have hf : MemLp f 2 P := memLp_vectorMeasureSiteSquare μ β t a ht q (Fin.last n)
  have hc : covariance f S P = variance S P := by
    rw [covariance_comm]
    exact covariance_vectorMeasureSelfSquare_site_eq_variance (by omega) μ β t a ht q (Fin.last n)
  have he : cavityDeletedSiteSelfOverlap μ β t ht q (Fin.last n) =
      fun sample => (n : ℝ)⁻¹*((n+1 : ℕ)*S sample-f sample) := by
    rw [cavityDeletedSiteSelfOverlap_eq (by omega : 1 < n+1)]
    funext sample
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    dsimp only [S, f]
    ring
  rw [he, covariance_const_mul_right, covariance_fun_sub_right hf (hS.const_mul _) hf,
    covariance_const_mul_right, hc, covariance_self hf.aemeasurable]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN0 : (n+1 : ℕ) ≠ (0 : ℝ) := by positivity
  dsimp only [S, f, P] at *
  field_simp
  ring

theorem followupCavityCpp_one_eq_completed_covariance (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (q : Paper.Overlap) :
    followupCavityCpp n β ρ hβ hρ μ a 1 ⟨zero_le_one, le_rfl⟩ q =
      covariance (vectorMeasureSiteSquare μ β (1-ρ) (by linarith [hρ.1]) q (Fin.last n))
        (cavityDeletedSiteSelfOverlap μ β (1-ρ) (by linarith [hρ.1]) q (Fin.last n))
        (vectorMeasureDisorderTilt μ β (1-ρ) a) := by
  have hH : Continuous (fun m : QuantitativePaper.Field (n+1) => m (Fin.last n)^2) :=
    (EuclideanSpace.proj (Fin.last n)).continuous.pow 2
  have hHB (m : QuantitativePaper.Field (n+1)) (hm : ∀ i, ‖m i‖ ≤ 1) : ‖m (Fin.last n)^2‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hm (Fin.last n)) 2).trans_eq (by norm_num)
  have hh := followup_cavity_one_covariance_spin_mean hn μ β ρ a hβ hρ q
    (fun m => m (Fin.last n)^2) (anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n)))
    hH (continuous_anisotropicSelectedMeanSquare _) 1 1 hHB
    (fun m hm => anisotropicSelectedMeanSquare_bound _ m hm)
  unfold followupCavityCpp
  simp_rw [← cavitySelectedMeanSquare_erased_last_projection]
  rw [hh]
  congr 1
  funext sample
  simp [anisotropicSelectedMeanSquare, cavityDeletedSiteSelfOverlap, Nat.cast_add]

theorem followup_full_variance_trace_endpoint (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (q : Paper.Overlap) :
    variance (vectorMeasureSelfSquare (n:=n+1) μ β (1-ρ) (by linarith [hρ.1]) q)
      (vectorMeasureDisorderTilt μ β (1-ρ) a) =
      variance (vectorMeasureSiteSquare μ β (1-ρ) (by linarith [hρ.1]) q (Fin.last n))
        (vectorMeasureDisorderTilt μ β (1-ρ) a)/(n+1 : ℕ) +
      (n : ℝ)/(n+1 : ℕ)*followupCavityCpp n β ρ hβ hρ μ a 1 ⟨zero_le_one, le_rfl⟩ q := by
  rw [followupCavityCpp_one_eq_completed_covariance hn μ β ρ a hβ hρ q]
  exact vector_full_variance_one_site_decomposition hn μ β (1-ρ) a _ q

end QuantitativeFollowup
