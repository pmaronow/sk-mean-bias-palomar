module
public import QuantitativeFollowup.FollowupCavityFourVarianceComparison
public import QuantitativeFollowup.FollowupCavityDecouplingCovariance
public import QuantitativeFollowup.FollowupCavityRestCovariance

@[expose] public section

/-! Literal coefficient-one comparison for the genuine independent rest
model, using the constructed zero-incident-coupling projection law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n:ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityRestSelectedMeanSquare_zero (μ:Paper.ParisiMeasure) (β ρ:ℝ)
    (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (q:Paper.Overlap)
    (sample:AnisotropicDisorderBrownianSample (n+1)) :
    anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample)=
      cavityRestSelfOverlap (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (cavityRestSampleProjection n sample) := by
  have he:(Finset.univ.erase (Fin.last n))=(Finset.univ:Finset (Fin n)).map Fin.castSuccEmb := by
    rw [Fin.univ_castSuccEmb]
    simp
  have hm (i:Fin n):
      anisotropicProcessMagnetization (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample i.castSucc=
        anisotropicProcessMagnetization (followupCavityRestSpinModel n β ρ hβ hρ) μ q
          (cavityRestSampleProjection n sample) i := by
    have h:=congrArg (fun x:QuantitativePaper.Field n=>x i)
      (cavityRestProcessMagnetization_zero μ n β ρ hβ hρ q sample)
    simpa only [cavityRestFieldProjection_apply] using h
  simp only [cavityRestSelfOverlap,anisotropicSelectedMeanSquare,he,Finset.sum_map,
    Finset.card_map,Finset.card_univ,Fintype.card_fin]
  change (∑i:Fin n,(anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample i.castSucc)^2)/(n:ℝ)=
    (∑i:Fin n,(anisotropicProcessMagnetization (followupCavityRestSpinModel n β ρ hβ hρ) μ q
      (cavityRestSampleProjection n sample) i)^2)/(n:ℝ)
  congr 1
  exact Finset.sum_congr rfl fun i _=>congrArg (fun x:ℝ=>x^2) (hm i)

theorem followup_cavity_zero_rest_variance (μ:Paper.ParisiMeasure) (β ρ a:ℝ)
    (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (q:Paper.Overlap) :
    variance (fun sample=>anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample))
      (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      variance (cavityRestSelfOverlap (followupCavityRestSpinModel n β ρ hβ hρ) μ q)
        (anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a) := by
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  have hL:=hasLaw_cavityRestSampleProjection μ n β ρ hβ hρ a
  have hm:=measurable_cavityRestSelfOverlap R μ q
  have h:=congrArg (variance (cavityRestSelfOverlap R μ q)) hL.map_eq
  rw [variance_map hm.aemeasurable hL.aemeasurable] at h
  simp_rw [cavityRestSelectedMeanSquare_zero]
  exact h

theorem followup_cavity_four_rest_variance_comparison (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Ioo (0:ℝ) 1) (hμ:μ∈scalarFloor a)
    (hmin:∀ν∈scalarFloor a,vectorMeasureFunctional (n+1) μ β (1-ρ) a≤
      vectorMeasureFunctional (n+1) ν β (1-ρ) a) :
    cavityRestVariance (followupCavityRestSpinModel n β ρ hβ hρ) μ a≤
      followupSourceMeanVarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
        720*β^2*Real.exp (21*β^2)*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ+
        1/(4*(n:ℝ)^2) := by
  have h:=followup_cavity_four_native_variance_comparison hn μ β ρ a hβ hρ ha hμ hmin
  simp_rw [followup_cavity_zero_rest_variance] at h
  exact h

end QuantitativeFollowup
