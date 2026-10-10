module
public import QuantitativeFollowup.FollowupCavityStandardEndpointModel
public import QuantitativeFollowup.StandardSKOffDiagonalLaw
public import QuantitativeFollowup.FourDescendantDeletedSiteVariance

@[expose] public section

/-! Physical u=1 cavity spin-mean observables have exactly their completed
SK moments. The coefficient-one deleted-site variance comparison follows
from the actual native site-permutation law, with no endpoint law premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem followup_cavity_one_variance_spin_mean (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β ρ a : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (q : Paper.Overlap) (H : QuantitativePaper.Field (n+1)→ℝ) (hH : Continuous H) :
    variance (fun sample => H (anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ q sample))
      (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 1
        ⟨zero_le_one,le_rfl⟩) μ a) =
    variance (fun sample => H (vectorMeasureSpinMean μ β (1-ρ)
      (by linarith [hρ.1]) q sample)) (vectorMeasureDisorderTilt μ β (1-ρ) a) := by
  let ht : 1-ρ<1 := by linarith [hρ.1]
  let F : VectorDisorderBrownianSample (n+1)→ℝ :=
    fun sample => H (vectorMeasureSpinMean μ β (1-ρ) ht.le q sample)
  have hm : Measurable (vectorMeasureSpinMean (n:=n+1) μ β (1-ρ) ht.le q) :=
    (adapted_vectorMeasureSpinMean μ β (1-ρ) ht.le q).mono
      ((vectorBrownianFiltration (n+1)).le _) le_rfl
  have hF : Measurable F := hH.measurable.comp hm
  have hFD (sample) : F (vectorRemoveDiagonalSample sample)=F sample := by
    unfold F
    rw [←vectorMeasureSpinMean_diagonal_shift μ β (1-ρ) ht.le q sample]
  have he := variance_standardSKOffDiagonalSampleLaw μ β (1-ρ) a hβ.ne' ht F hF hFD
  rw [followupCavitySpinModel_one_eq_offDiagonal n hn β ρ hβ hρ]
  convert! he using 1
  congr 1
  funext sample
  rw [standardSKOffDiagonalProcessMagnetization]
  rfl

theorem followup_cavity_one_rest_variance_le (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β ρ a : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap) :
    variance (fun sample => anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ q sample))
      (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 1
        ⟨zero_le_one,le_rfl⟩) μ a) ≤
    variance (vectorMeasureSelfSquare (n:=n+1) μ β (1-ρ) (by linarith [hρ.1]) q)
      (vectorMeasureDisorderTilt μ β (1-ρ) a) + 1/(4*(n:ℝ)^2) := by
  let ht : 1-ρ≤1 := by linarith [hρ.1]
  rw [followup_cavity_one_variance_spin_mean hn μ β ρ a hβ hρ q
    (anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n)))
    (continuous_anisotropicSelectedMeanSquare _)]
  have he : (fun sample : VectorDisorderBrownianSample (n+1) =>
      anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
        (vectorMeasureSpinMean μ β (1-ρ) ht q sample)) =
      cavityDeletedSiteSelfOverlap μ β (1-ρ) ht q (Fin.last n) := by
    funext sample
    simp [anisotropicSelectedMeanSquare,cavityDeletedSiteSelfOverlap,Nat.cast_add]
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using
    cavityDeletedSiteSelfOverlap_variance_le (by omega : 1<n+1) μ β (1-ρ) a ht q (Fin.last n)

end QuantitativeFollowup
