module
public import QuantitativeFollowup.FollowupCavityRootNormalizerNormalized
public import QuantitativeFollowup.FollowupCavityIncidentIndexSum

@[expose] public section

/-! Literal incident-row summation and the physical cavity normalizer.
The diagonal coordinate has zero coupling and is retained in the Gaussian
space; its contribution is proved to vanish. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem followupCavity_incident_coupling_sum (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (F : AnisotropicCouplingIndex (n+1)→ℝ) :
    (∑e,if cavityIncidentRootMask n e then
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩).coupling e^2*F e else 0)=
      followupCavityAlpha n β ρ/(n:ℝ)*∑i : Fin n,F (followupCavityIncidentIndex i) := by
  simpa only [followupCavityIncidentIndex,cavityIncidentEdge] using
    followupCavity_incident_hessian_sum n β ρ hβ hρ F

def followupCavityRootPartition (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a u : ℝ) : ℝ :=
  anisotropicMeasureOuterPartition
    (anisotropicCavityInterpolationModel
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
      (cavityIncidentRootMask n) (Fin.last n) (followupCavityD n β ρ)
      (followupCavityAlpha n β ρ) u) μ a

theorem followupCavityRootPartition_eq_actual (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityRootPartition n β ρ hβ hρ μ a u=
      anisotropicMeasureOuterPartition (followupCavitySpinModel n β ρ hβ hρ u hu) μ a := by
  exact congrArg (fun E : AnisotropicSpinModel (n+1)=>anisotropicMeasureOuterPartition E μ a)
    (followupCavitySpinModel_eq_scaled_root_and_path n β ρ hβ hρ u hu).symm

theorem hasDerivAt_log_followupCavityRootPartition_future_squares
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (u : ℝ) (hu : u∈Ioc (0:ℝ) 1) :
    let E:=followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩
    HasDerivAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
      (-a*followupCavityAlpha n β ρ/2*
        (∫r : Paper.Overlap,((∑i : Fin n,
          ∫p,(anisotropicProcessPairResponse E μ r (followupCavityIncidentIndex i) p)^2
            ∂anisotropicMeasureSampleLaw E μ a)/(n:ℝ)-
          (r:ℝ)*(∫p,(anisotropicProcessSpinResponse E μ r (Fin.last n) p)^2
            ∂anisotropicMeasureSampleLaw E μ a))∂parisiFreeMeasure μ a)) u := by
  classical
  dsimp only
  let E:=followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩
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
  have hb : 0<followupCavityD n β ρ-followupCavityAlpha n β ρ*u:=
    (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le (followupCavityB_window n β ρ u hρ.2 ⟨hu.1.le,hu.2⟩).1
  have hd:=hasDerivAt_log_anisotropicCavityInterpolationPartition_future_squares
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a ha hμ
    (cavityIncidentRootMask n) (Fin.last n) (followupCavityD n β ρ)
    (followupCavityAlpha n β ρ) u hα hu.1 hb
  have he : anisotropicCavityInterpolationModel
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
      (cavityIncidentRootMask n) (Fin.last n) (followupCavityD n β ρ)
      (followupCavityAlpha n β ρ) u=E :=
    (followupCavitySpinModel_eq_scaled_root_and_path n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩).symm
  dsimp only at hd
  rw [he] at hd
  rw [followupCavity_incident_coupling_sum β ρ hβ hρ] at hd
  change HasDerivAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
    (-a*followupCavityAlpha n β ρ/2*(1-∫r,S r∂Q)+
      a/2*(followupCavityAlpha n β ρ/(n:ℝ)*∑i : Fin n,(1-∫r,M i r∂Q))) u at hd
  have hN : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  have hi : (∫r,((∑i,M i r)/(n:ℝ)-S r)∂Q)=
      (∑i,∫r,M i r∂Q)/(n:ℝ)-(∫r,S r∂Q) := by
    rw [integral_sub ((integrable_finset_sum _ (fun i _=>hM i)).div_const _) hS,
      integral_div,integral_finset_sum _ (fun i _=>hM i)]
  change HasDerivAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
    (-a*followupCavityAlpha n β ρ/2*(∫r,((∑i,M i r)/(n:ℝ)-S r)∂Q)) u
  rw [hi]
  have hs : (∑i : Fin n,(1-∫r,M i r∂Q))=(n:ℝ)-∑i : Fin n,∫r,M i r∂Q := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hs] at hd
  convert hd using 1 <;> field_simp [hN] <;> ring

end QuantitativeFollowup
