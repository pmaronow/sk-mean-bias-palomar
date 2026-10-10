module
public import QuantitativeFollowup.FollowupCavityStandardEndpointMoments
public import QuantitativeFollowup.FourDescendantVarianceBounds
public import QuantitativePaper.VectorReplicaDefectDecomposition

@[expose] public section

/-! Actual minimizer contact at the completed SK endpoint fixes the deleted
rest mean. The centered four-descendant observable then has the sharp
coefficient-one variance bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followup_cavity_one_integral_spin_mean (hn:0<n) (μ:Paper.ParisiMeasure)
    (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (q:Paper.Overlap)
    (H:QuantitativePaper.Field (n+1)→ℝ) (hH:Continuous H) :
    (∫sample,H (anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ q sample)
      ∂anisotropicMeasureSampleLaw
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a)=
      ∫sample,H (vectorMeasureSpinMean μ β (1-ρ) (by linarith[hρ.1]) q sample)
        ∂vectorMeasureDisorderTilt μ β (1-ρ) a := by
  let ht:1-ρ<1:=by linarith[hρ.1]
  let F:=fun sample:VectorDisorderBrownianSample (n+1)=>H (vectorMeasureSpinMean μ β (1-ρ) ht.le q sample)
  have hm:Measurable (vectorMeasureSpinMean (n:=n+1) μ β (1-ρ) ht.le q):=
    (adapted_vectorMeasureSpinMean μ β (1-ρ) ht.le q).mono
      ((vectorBrownianFiltration (n+1)).le _) le_rfl
  have hF:Measurable F:=hH.measurable.comp hm
  have hFD (sample):F (vectorRemoveDiagonalSample sample)=F sample := by
    unfold F
    rw [←vectorMeasureSpinMean_diagonal_shift μ β (1-ρ) ht.le q sample]
  have he:=integral_standardSKOffDiagonalSampleLaw μ β (1-ρ) a hβ.ne' ht F hF hFD
  rw [followupCavitySpinModel_one_eq_offDiagonal n hn β ρ hβ hρ]
  convert! he using 1
  congr 1
  funext sample
  rw [standardSKOffDiagonalProcessMagnetization]
  rfl

theorem cavityDeletedSiteSelfOverlap_mean_eq_self (hN:1<n) (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (q:Paper.Overlap) (i:Fin n) :
    (∫sample,cavityDeletedSiteSelfOverlap μ β t ht q i sample
      ∂vectorMeasureDisorderTilt μ β t a)=
      ∫sample,vectorMeasureSelfSquare (n:=n) μ β t ht q sample
        ∂vectorMeasureDisorderTilt μ β t a := by
  haveI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  rw [cavityDeletedSiteSelfOverlap_eq hN,integral_div,
    integral_sub ((memLp_vectorMeasureSelfSquare μ β t a ht q).integrable (by norm_num) |>.const_mul (n:ℝ))
      ((memLp_vectorMeasureSiteSquare μ β t a ht q i).integrable (by norm_num)),integral_const_mul,
    integral_vectorMeasureSiteSquare_eq_self (by omega) μ β t a ht q i]
  have hnR:(n:ℝ)-1≠0:=by
    have hn':1<(n:ℝ):=by exact_mod_cast hN
    linarith
  field_simp

theorem followup_cavity_one_rest_mean_contact (hn:0<n) (μ:Paper.ParisiMeasure)
    (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (ha:a∈Ioo (0:ℝ) 1)
    (hμ:μ∈scalarFloor a)
    (hmin:∀ν∈scalarFloor a,vectorMeasureFunctional (n+1) μ β (1-ρ) a≤
      vectorMeasureFunctional (n+1) ν β (1-ρ) a)
    (q:Paper.Overlap) (hq:q∈(parisiFreeMeasure μ a).support) :
    (∫sample,anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ q sample)
      ∂anisotropicMeasureSampleLaw
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a)=(q:ℝ) := by
  let ht:1-ρ<1:=by linarith[hρ.1]
  rw [followup_cavity_one_integral_spin_mean hn μ β ρ a hβ hρ q
    (anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n)))
    (continuous_anisotropicSelectedMeanSquare _)]
  have he : (fun sample:VectorDisorderBrownianSample (n+1)=>anisotropicSelectedMeanSquare
      (Finset.univ.erase (Fin.last n)) (vectorMeasureSpinMean μ β (1-ρ) ht.le q sample))=
      cavityDeletedSiteSelfOverlap μ β (1-ρ) ht.le q (Fin.last n) := by
    funext sample
    simp [anisotropicSelectedMeanSquare,cavityDeletedSiteSelfOverlap,Nat.cast_add]
  rw [he,cavityDeletedSiteSelfOverlap_mean_eq_self (by omega)]
  have hc:=vectorSelfOverlap_mean_on_free_support (by omega : 0<n+1) μ a β (1-ρ)
    ha hμ hβ.ne' ht hmin q hq
  have hm:Measurable (vectorMeasureSelfSquare (n:=n+1) μ β (1-ρ) ht.le q):=
    (((adapted_vectorMeasureSpinMean μ β (1-ρ) ht.le q).mono
      ((vectorBrownianFiltration (n+1)).le _) le_rfl).norm.pow_const 2).div_const _
  change (∫z,vectorMeasureSelfSquare μ β (1-ρ) ht.le q z.1
    ∂vectorMeasureSpinPathLaw μ β (1-ρ) a ht.le)=(q:ℝ) at hc
  rwa [integral_vectorMeasureSpinPathLaw_sample μ β (1-ρ) a ht.le _ hm] at hc

theorem followup_cavity_one_four_centered_product_le (hn:0<n) (μ:Paper.ParisiMeasure)
    (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (ha:a∈Ioo (0:ℝ) 1)
    (hμ:μ∈scalarFloor a)
    (hmin:∀ν∈scalarFloor a,vectorMeasureFunctional (n+1) μ β (1-ρ) a≤
      vectorMeasureFunctional (n+1) ν β (1-ρ) a)
    (q:Paper.Overlap) (hq:q∈(parisiFreeMeasure μ a).support) :
    (∫z,(cavitySelectedSpinOverlap (Finset.univ.erase (Fin.last n)) z.2.1.1 z.2.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap (Finset.univ.erase (Fin.last n)) z.2.2.1 z.2.2.2-(q:ℝ))
      ∂cavityFourDescendantLaw
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a q)≤
      variance (vectorMeasureSelfSquare (n:=n+1) μ β (1-ρ) (by linarith[hρ.1]) q)
        (vectorMeasureDisorderTilt μ β (1-ρ) a)+1/(4*(n:ℝ)^2) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩
  let A:=fun sample:AnisotropicDisorderBrownianSample (n+1)=>
    anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n)) (anisotropicProcessMagnetization D μ q sample)
  have hAm:Measurable A:=measurable_cavitySelectedSelfOverlap D μ q _
  have hc:=followup_cavity_one_rest_mean_contact hn μ β ρ a hβ hρ ha hμ hmin q hq
  have hv:=variance_eq_integral (μ:=anisotropicMeasureSampleLaw D μ a) hAm.aemeasurable
  rw [hc] at hv
  rw [cavityFourDescendantLaw_centered_overlap_product,←hv]
  exact followup_cavity_one_rest_variance_le hn μ β ρ a hβ hρ q

end QuantitativeFollowup
