module
public import QuantitativeFollowup.FollowupCavityDecouplingScalar
public import QuantitativeFollowup.AnisotropicFiniteSmooth
public import OverlapPaper.ReplicaSourceGroupBaseline

@[expose] public section

/-! Actual finite u=0 cavity factorization, derived step by step from the
concrete Gaussian split and separated Hamiltonian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def followupCavityScalarBeta (n : ℕ) (β ρ : ℝ) : ℝ:=Real.sqrt (followupCavityD n β ρ)

theorem followupCavityD_pos (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    0<followupCavityD n β ρ :=
  (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le
    (le_add_of_nonneg_right (followupCavityAlpha_nonneg n β ρ hρ.2))

theorem followupCavityScalarBeta_pos (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    0<followupCavityScalarBeta n β ρ := Real.sqrt_pos.mpr (followupCavityD_pos n β ρ hβ hρ)

theorem cavityAnisotropicPoint_add_field (g : AnisotropicDisorder n) (x y : QuantitativePaper.Field n) :
    anisotropicParameterPoint g x+anisotropicFieldInjection n y=anisotropicParameterPoint g (x+y) := by
  ext i
  cases i <;> simp [anisotropicParameterPoint,anisotropicFieldInjection]

theorem followupCavityFinitePotential_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicFinitePotential (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) s j
      (anisotropicParameterPoint g x)=
      anisotropicFinitePotential (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))+
      cavityScalarFinite s (followupCavityScalarBeta n β ρ) j (x (Fin.last n)) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  induction j generalizing x with
  | zero =>
    rw [anisotropicFinitePotential_terminal_softmax,anisotropicFinitePotential_terminal_softmax,
      cavityScalarFinite_zero]
    exact followupCavityTerminal_zero n β ρ hβ hρ g x
  | succ j ih =>
    let δ:=s.q (k+2-j)-s.q (k+1-j)
    let Pr:=anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)
    let Lr:=Real.sqrt δ • anisotropicUnitInput R
    let Fr:=fun z : QuantitativePaper.Field n=>anisotropicFinitePotential R s j (Pr+Lr z)
    let Fs:=fun z : ℝ=>cavityScalarFinite s β0 j (x (Fin.last n)+Real.sqrt (β0^2*δ)*z)
    let F:=fun z : QuantitativePaper.Field n×ℝ=>Fr z.1+Fs z.2
    have hδ : 0≤δ:=sub_nonneg.mpr (s.q_mono' _ (Nat.sub_le _ _) _ (by omega))
    have hc : Real.sqrt (β0^2*δ)=Real.sqrt δ*Real.sqrt (followupCavityD n β ρ) := by
      dsimp only [β0, followupCavityScalarBeta]
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg (followupCavityD n β ρ))]
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
      rw [map_add,map_smul,cavityRestFieldProjection_noise_zero]
      rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
        ←(anisotropicFieldInjection n).map_smul,cavityAnisotropicPoint_add_field]
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,D,cavityLastNoise_zero]
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
