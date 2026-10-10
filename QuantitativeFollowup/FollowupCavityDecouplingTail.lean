module
public import QuantitativeFollowup.FollowupCavityDecouplingFinite
public import QuantitativeFollowup.AnisotropicTailDerivative
public import QuantitativePaper.VectorScalarTail

@[expose] public section

/-! The cavity separation at zero incident coupling holds for the actual
arbitrary-profile tail potential, obtained from the constructed common-grid
limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem cavityScalarFinite_clamped (s : RSBScheme k) (β q x : ℝ)
    (hq : q∈Icc (0:ℝ) 1) :
    cavityScalarFinite (vectorClampedScheme s q hq) β (k+2) x=
      Real.log 2+Paper.parisiFinitePotential s β (q,x) := by
  let v : QuantitativePaper.Field 1:=WithLp.toLp 2 (fun _=>x)
  have hh:=vectorTailRecursion_zero_time s β q hq (0 : Couplings 1×ℝ) v
  rw [vectorTailRecursion_eq_clamped s β 0 q hq _ le_rfl,
    vectorRecursion_zero_time] at hh
  simpa only [Fin.sum_univ_one, v, PiLp.toLp_apply, cavityScalarFinite] using hh

theorem followupCavityTailRecursion_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicTailRecursion (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩)
      s q (k+2) (anisotropicParameterPoint g x)=
      anisotropicTailRecursion (followupCavityRestSpinModel n β ρ hβ hρ) s q (k+2)
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))+
      (Real.log 2+Paper.parisiFinitePotential s (followupCavityScalarBeta n β ρ)
        (q,x (Fin.last n))) := by
  rw [anisotropicTailRecursion_eq_clamped _ s q q.property le_rfl,
    anisotropicTailRecursion_eq_clamped _ s q q.property le_rfl,
    followupCavityFinitePotential_zero, cavityScalarFinite_clamped]

theorem followupCavityMeasureTailPotential_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicMeasureTailPotential (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩)
      μ q (anisotropicParameterPoint g x)=
      anisotropicMeasureTailPotential (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))+
      (Real.log 2+Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))) := by
  apply tendsto_nhds_unique (tendsto_anisotropicDyadicTailPotential _ μ q _)
  have hh:=(tendsto_anisotropicDyadicTailPotential (followupCavityRestSpinModel n β ρ hβ hρ) μ q
    (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))).add
    ((tendsto_const_nhds (x:=Real.log 2)).add ((Paper.tendsto_actual_finiteParisiPotential
      (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
      μ q (x (Fin.last n)) q.property).comp tendsto_vectorDyadicIndex))
  convert! hh using 1
  funext j
  exact followupCavityTailRecursion_zero _ n β ρ hβ hρ q g x

theorem followupCavityMeasurePotential_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicMeasurePotential (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩)
      μ (anisotropicParameterPoint g x)=
      anisotropicMeasurePotential (followupCavityRestSpinModel n β ρ hβ hρ) μ
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))+
      (Real.log 2+Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ (0,x (Fin.last n))) := by
  have hh:=followupCavityMeasureTailPotential_zero μ n β ρ hβ hρ ⟨0,by norm_num⟩ g x
  simpa only [anisotropicMeasureTailPotential_zero, Subtype.coe_mk] using hh

end QuantitativeFollowup
