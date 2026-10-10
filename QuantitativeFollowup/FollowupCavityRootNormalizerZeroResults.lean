module
public import QuantitativeFollowup.FollowupCavityRootNormalizerZeroNormalized
public import QuantitativeFollowup.FollowupCavityRootNormalizerResults

@[expose] public section

/-! Literal arbitrary-profile root-normalizer identity at the zero-row
endpoint, and its closed physical interpolation interval. All fresh marks
are sampled from the actual full-past conditional terminal distribution. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem hasDerivWithinAt_log_followupCavityRootPartition_zero_future_squares
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    let E:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    HasDerivWithinAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
      (-a*followupCavityAlpha n β ρ/2*
        (∫r : Paper.Overlap,((∑i : Fin n,
          ∫p,(anisotropicProcessPairResponse E μ r (followupCavityIncidentIndex i) p)^2
            ∂anisotropicMeasureSampleLaw E μ a)/(n:ℝ)-
          (r:ℝ)*(∫p,(anisotropicProcessSpinResponse E μ r (Fin.last n) p)^2
            ∂anisotropicMeasureSampleLaw E μ a))∂parisiFreeMeasure μ a)) (Ici (0:ℝ)) 0 := by
  classical
  dsimp only
  let E:=followupCavitySpinModel n β ρ hβ hρ (0:ℝ) ⟨le_rfl,zero_le_one⟩
  let Q:=parisiFreeMeasure μ a
  let M:=fun (i : Fin n) (r : Paper.Overlap)=>
    ∫p,(anisotropicProcessPairResponse E μ r (followupCavityIncidentIndex i) p)^2
      ∂anisotropicMeasureSampleLaw E μ a
  let S:=fun r : Paper.Overlap=>(r:ℝ)*
    (∫p,(anisotropicProcessSpinResponse E μ r (Fin.last n) p)^2∂anisotropicMeasureSampleLaw E μ a)
  have hM (i : Fin n) : Integrable (M i) Q := by
    have hm : Measurable (M i) :=
      (((measurable_uncurry_anisotropicProcessPairResponse E μ (followupCavityIncidentIndex i)).pow_const 2).stronglyMeasurable.integral_prod_right' (ν:=anisotropicMeasureSampleLaw E μ a)).measurable
    apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    exact .of_forall fun r=>by
      have hb (p : AnisotropicDisorderBrownianSample (n+1)) :
          ‖(anisotropicProcessPairResponse E μ r (followupCavityIncidentIndex i) p)^2‖≤1 := by
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound E μ r _ p) 2).trans_eq (by norm_num)
      simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
        (μ:=anisotropicMeasureSampleLaw E μ a) (C:=1) (.of_forall hb)
  have hS : Integrable S Q := by
    have hm : Measurable S := measurable_subtype_coe.mul
      (((measurable_uncurry_anisotropicProcessSpinResponse E μ (Fin.last n)).pow_const 2).stronglyMeasurable.integral_prod_right' (ν:=anisotropicMeasureSampleLaw E μ a)).measurable
    apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    exact .of_forall fun r=>by
      dsimp only [S]
      rw [norm_mul,Real.norm_of_nonneg r.property.1]
      have hb : ‖∫p,(anisotropicProcessSpinResponse E μ r (Fin.last n) p)^2
          ∂anisotropicMeasureSampleLaw E μ a‖≤1:=by
        have hb (p : AnisotropicDisorderBrownianSample (n+1)) :
            ‖(anisotropicProcessSpinResponse E μ r (Fin.last n) p)^2‖≤1 := by
          rw [norm_pow]
          exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessSpinResponse_bound E μ r _ p) 2).trans_eq (by norm_num)
        simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
          (μ:=anisotropicMeasureSampleLaw E μ a) (C:=1) (.of_forall hb)
      exact (mul_le_mul_of_nonneg_left hb r.property.1).trans (by simpa only [mul_one] using r.property.2)
  have hα:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hb : 0<followupCavityD n β ρ-followupCavityAlpha n β ρ*(0:ℝ):=
    (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le (followupCavityB_window n β ρ (0:ℝ) hρ.2 ⟨le_rfl,zero_le_one⟩).1
  have hd:=hasDerivWithinAt_log_anisotropicCavityInterpolationPartition_zero_future_squares
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a ha hμ
    (cavityIncidentRootMask n) (Fin.last n) (followupCavityD n β ρ)
    (followupCavityAlpha n β ρ) (by simpa only [mul_zero,sub_zero] using hb)
  have he : anisotropicCavityInterpolationModel
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
      (cavityIncidentRootMask n) (Fin.last n) (followupCavityD n β ρ)
      (followupCavityAlpha n β ρ) (0:ℝ)=E :=
    (followupCavitySpinModel_eq_scaled_root_and_path n β ρ hβ hρ (0:ℝ) ⟨le_rfl,zero_le_one⟩).symm
  dsimp only at hd
  rw [he] at hd
  rw [followupCavity_incident_coupling_sum β ρ hβ hρ] at hd
  change HasDerivWithinAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
    (-a*followupCavityAlpha n β ρ/2*(1-∫r,S r∂Q)+
      a/2*(followupCavityAlpha n β ρ/(n:ℝ)*∑i : Fin n,(1-∫r,M i r∂Q))) (Ici (0:ℝ)) (0:ℝ) at hd
  have hN : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  have hi : (∫r,((∑i,M i r)/(n:ℝ)-S r)∂Q)=
      (∑i,∫r,M i r∂Q)/(n:ℝ)-(∫r,S r∂Q) := by
    rw [integral_sub ((integrable_finset_sum _ (fun i _=>hM i)).div_const _) hS,
      integral_div,integral_finset_sum _ (fun i _=>hM i)]
  change HasDerivWithinAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
    (-a*followupCavityAlpha n β ρ/2*(∫r,((∑i,M i r)/(n:ℝ)-S r)∂Q)) (Ici (0:ℝ)) (0:ℝ)
  rw [hi]
  have hs : (∑i : Fin n,(1-∫r,M i r∂Q))=(n:ℝ)-∑i : Fin n,∫r,M i r∂Q := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hs] at hd
  convert! hd using 1 <;> field_simp [hN] <;> ring


theorem hasDerivWithinAt_log_followupCavityRootPartition_zero
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    HasDerivWithinAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
      (-a*followupCavityAlpha n β ρ/2*
        (∫r : Paper.Overlap,∫z,cavitySpinOverlapDefect n r z.2.1 z.2.2
          ∂anisotropicFreshTerminalPairLaw D μ a r∂parisiFreeMeasure μ a)) (Ici (0:ℝ)) 0 := by
  dsimp only
  simpa only [anisotropicFreshTerminalPairLaw_overlapDefect] using
    hasDerivWithinAt_log_followupCavityRootPartition_zero_future_squares hn β ρ hβ hρ μ a ha hμ

theorem followup_cavity_root_normalizer_closed_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (u:ℝ)(hu:u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    HasDerivWithinAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
      (-a*followupCavityAlpha n β ρ/2*
        (∫r : Paper.Overlap,∫z,cavitySpinOverlapDefect n r z.2.1 z.2.2
          ∂anisotropicFreshTerminalPairLaw D μ a r∂parisiFreeMeasure μ a)) (Icc (0:ℝ) 1) u := by
  dsimp only
  by_cases hz:u=0
  · subst u
    exact (hasDerivWithinAt_log_followupCavityRootPartition_zero hn β ρ hβ hρ μ a ha hμ).mono
      (fun _ hx=>hx.1)
  · exact (hasDerivAt_log_followupCavityRootPartition hn β ρ hβ hρ μ a ha hμ u
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩).hasDerivWithinAt

end QuantitativeFollowup
