module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseKernels

@[expose] public section

/-! The independent endpoint with only the last auxiliary variance varied.
All rest variances and every disorder coefficient remain literal constants.
The actual finite Gaussian recursion separates for every positive last variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityLastVarianceModel (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) : AnisotropicSpinModel (n+1) where
  variance i := if i = Fin.last n then b else
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩).variance i
  variance_pos i := by
    split_ifs
    · exact hb
    · exact (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩).variance_pos i
  coupling := (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩).coupling

@[simp] theorem cavityLastVarianceModel_last (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) :
    (cavityLastVarianceModel n β ρ hβ hρ b hb).variance (Fin.last n) = b := by
  simp only [cavityLastVarianceModel, ite_true]

@[simp] theorem cavityLastVarianceModel_rest (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) (i : Fin n) :
    (cavityLastVarianceModel n β ρ hβ hρ b hb).variance i.castSucc =
      (followupCavityRestSpinModel n β ρ hβ hρ).variance i := by
  simp only [cavityLastVarianceModel, Fin.castSucc_ne_last, if_false,
    followupCavitySpinModel_variance_rest, followupCavityRestSpinModel]

@[simp] theorem cavityLastVarianceModel_energy (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) :
    anisotropicEnergyMap (cavityLastVarianceModel n β ρ hβ hρ b hb) =
      anisotropicEnergyMap (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩) := rfl

 theorem cavityLastVariance_rest_noise (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) (z : QuantitativePaper.Field (n+1)) :
    cavityRestFieldProjection n (anisotropicNoiseMap (cavityLastVarianceModel n β ρ hβ hρ b hb) z) =
      anisotropicNoiseMap (followupCavityRestSpinModel n β ρ hβ hρ)
        (cavityRestFieldProjection n z) := by
  ext i
  simp only [cavityRestFieldProjection_apply, anisotropicNoiseMap_apply, cavityLastVarianceModel_rest]

 theorem cavityLastVariance_last_noise (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) (z : QuantitativePaper.Field (n+1)) :
    anisotropicNoiseMap (cavityLastVarianceModel n β ρ hβ hρ b hb) z (Fin.last n) =
      Real.sqrt b * z (Fin.last n) := by
  rw [anisotropicNoiseMap_apply, cavityLastVarianceModel_last]

theorem cavityLastVariance_finitePotential_product (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0 < b) (j : ℕ) (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicFinitePotential (cavityLastVarianceModel n β ρ hβ hρ b hb) s j
      (anisotropicParameterPoint g x)=
      anisotropicFinitePotential (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))+
      cavityScalarFinite s (Real.sqrt b) j (x (Fin.last n)) := by
  let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=Real.sqrt b
  induction j generalizing x with
  | zero =>
    rw [anisotropicFinitePotential_terminal_softmax,anisotropicFinitePotential_terminal_softmax,
      cavityScalarFinite_zero]
    change anisotropicGridTerminalPotential
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩)
      (anisotropicParameterPoint g x)=_
    exact followupCavityTerminal_zero n β ρ hβ hρ g x
  | succ j ih =>
    let δ:=s.q (k+2-j)-s.q (k+1-j)
    let Pr:=anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)
    let Lr:=Real.sqrt δ • anisotropicUnitInput R
    let Fr:=fun z : QuantitativePaper.Field n=>anisotropicFinitePotential R s j (Pr+Lr z)
    let Fs:=fun z : ℝ=>cavityScalarFinite s β0 j (x (Fin.last n)+Real.sqrt (β0^2*δ)*z)
    let F:=fun z : QuantitativePaper.Field n×ℝ=>Fr z.1+Fs z.2
    have hδ : 0≤δ:=sub_nonneg.mpr (s.q_mono' _ (Nat.sub_le _ _) _ (by omega))
    have hc : Real.sqrt (β0^2*δ)=Real.sqrt δ*Real.sqrt (b) := by
      dsimp only [β0]
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg (b))]
      exact mul_comm _ _
    have hm : Measurable F :=
      ((contDiff_anisotropicFinitePotential R s j).continuous.measurable.comp
        (measurable_const.add (Lr.measurable.comp measurable_fst))).add
        ((measurable_cavityScalarFinite s β0 j).comp (by fun_prop))
    have hi := integrable_finiteStateGaussian_lipschitz (anisotropicFinitePotential R s j)
      (anisotropicFinitePotential_lipschitz R s j) Lr Pr
    have he := integrable_exp_finiteStateGaussian_lipschitz (anisotropicFinitePotential R s j)
      (anisotropicFinitePotential_lipschitz R s j) Lr Pr (anisotropicSchemeMass s j)
    have hmap:=OverlapPaper.sourceLogAverage_map (stdGaussian (QuantitativePaper.Field (n+1))) (cavityFieldSplit n)
      (measurable_cavityFieldSplit n) (anisotropicSchemeMass s j) F hm
    rw [stdGaussian_map_cavityFieldSplit] at hmap
    have hid : (fun z : QuantitativePaper.Field (n+1)=>anisotropicFinitePotential D s j
        (anisotropicParameterPoint g x+anisotropicSchemeInput D s j z))=
        fun z=>F (cavityFieldSplit n z) := by
      funext z
      rw [anisotropicSchemeInput_apply,cavityAnisotropicPoint_add_field,ih]
      dsimp only [F,Fr,Fs,cavityFieldSplit,Lr,anisotropicUnitInput,Pr]
      rw [map_add,map_smul,cavityLastVariance_rest_noise]
      rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
        ←(anisotropicFieldInjection n).map_smul,cavityAnisotropicPoint_add_field]
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,D,cavityLastVariance_last_noise]
      rw [hc]
      apply congrArg₂ (·+·)
      · rfl
      · congr 1
        dsimp only [δ]
        ring
    rw [anisotropicFinitePotential_coleHopf,hid,←hmap,
      sourceLogAverage_prod_add _ _ _ Fr Fs hi
        (integrable_cavityScalarFinite_shift s β0 j _ _) he
        (integrable_exp_cavityScalarFinite_shift s β0 j _ _ _),cavityScalarFinite_coleHopf]
    congr 1
    exact (anisotropicFinitePotential_coleHopf R s j Pr).symm


end QuantitativeFollowup
