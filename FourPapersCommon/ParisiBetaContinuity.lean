module
public import FRSB.ParisiMinimizer

@[expose] public section

/-! Uniform inverse-temperature continuity of the actual Parisi PDE value.
The proof compares the same genuine bounded Brownian control in both models.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace FourPapersCommon
open Paper FRSB
set_option maxHeartbeats 600000

theorem parisiControlDrift_beta_sub_le {Ω : Type*} (β γ : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlDrift β μ A ω - parisiControlDrift γ μ A ω‖ ≤ |β ^ 2 - γ ^ 2| := by
  have hh := parisiControlDrift_norm_le 1 μ A hb ω
  simp only [parisiControlDrift, one_pow, one_mul] at hh
  unfold parisiControlDrift
  rw [← sub_mul, norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (mul_one _)

theorem parisiControlCost_beta_sub_le {Ω : Type*} (β γ : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlCost β μ A ω - parisiControlCost γ μ A ω‖ ≤ |β ^ 2 - γ ^ 2| / 2 := by
  have hh := parisiControlCost_norm_le 1 μ A hb ω
  simp only [parisiControlCost, one_pow] at hh
  have hi : ‖∫ s in (0 : ℝ)..1, parisiCDF μ s * A s ω ^ 2‖ ≤ 1 := by
    rw [norm_mul] at hh
    norm_num at hh
    simpa only [Real.norm_eq_abs] using hh
  unfold parisiControlCost
  rw [← sub_mul, ← sub_div, norm_mul, Real.norm_eq_abs, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (mul_one _)

theorem parisiControlPayoff_beta_sub_le {Ω : Type*} (β γ h : ℝ) (B : Ω → ℝ)
    (μ : ParisiMeasure) (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlPayoff β h B A μ ω - parisiControlPayoff γ h B A μ ω‖ ≤
      |β - γ| * ‖B ω‖ + (3 / 2 : ℝ) * |β ^ 2 - γ ^ 2| := by
  have hd := parisiControlDrift_beta_sub_le β γ μ A hb ω
  have hc := parisiControlCost_beta_sub_le β γ μ A hb ω
  have hl := lipschitzWith_logcosh.dist_le_mul
    (h + β * B ω + parisiControlDrift β μ A ω)
    (h + γ * B ω + parisiControlDrift γ μ A ω)
  simp only [dist_eq_norm, NNReal.coe_one, one_mul] at hl
  have he : (h + β * B ω + parisiControlDrift β μ A ω) -
      (h + γ * B ω + parisiControlDrift γ μ A ω) =
      (β - γ) * B ω + (parisiControlDrift β μ A ω - parisiControlDrift γ μ A ω) := by ring
  rw [he] at hl
  have hx := norm_add_le ((β - γ) * B ω)
    (parisiControlDrift β μ A ω - parisiControlDrift γ μ A ω)
  simp only [norm_mul, Real.norm_eq_abs] at hx hl hd hc
  unfold parisiControlPayoff
  rw [show (Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω)) -
      parisiControlCost β μ A ω) -
      (Real.log (Real.cosh (h + γ * B ω + parisiControlDrift γ μ A ω)) -
      parisiControlCost γ μ A ω) =
      (Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω)) -
       Real.log (Real.cosh (h + γ * B ω + parisiControlDrift γ μ A ω))) -
      (parisiControlCost β μ A ω - parisiControlCost γ μ A ω) by ring]
  exact (norm_sub_le _ _).trans (by simp only [Real.norm_eq_abs]; linarith)

def parisiBrownianAbsoluteMoment : ℝ :=
  ∫ ω, ‖canonicalBrownian 1 ω‖ ∂canonicalBrownianMeasure

theorem parisiBrownianAbsoluteMoment_nonneg : 0 ≤ parisiBrownianAbsoluteMoment :=
  integral_nonneg (fun _ => norm_nonneg _)

def parisiBetaError (β γ : ℝ) : ℝ :=
  |β - γ| * parisiBrownianAbsoluteMoment + (3 / 2 : ℝ) * |β ^ 2 - γ ^ 2|

theorem parisiControlObjective_beta_sub_le (β γ h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    ‖parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ -
      parisiControlObjective canonicalBrownianMeasure γ h (canonicalBrownian 1) A μ‖ ≤
      parisiBetaError β γ := by
  have hi (b : ℝ) := integrable_parisiControlPayoff canonicalBrownianMeasure b h
    (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one A hA.measurable hA.bounded μ
  unfold parisiControlObjective
  rw [← integral_sub (hi β) (hi γ)]
  have hb := norm_integral_le_of_norm_le
    ((integrable_hjb_canonicalBrownian_one.norm.const_mul |β - γ|).add
      (integrable_const ((3 / 2 : ℝ) * |β ^ 2 - γ ^ 2|)))
    (.of_forall fun ω => parisiControlPayoff_beta_sub_le β γ h (canonicalBrownian 1) μ A hA.bounded ω)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_hjb_canonicalBrownian_one.norm.const_mul |β - γ|)
    (integrable_const _), integral_const_mul] at hb
  simpa only [parisiBetaError, parisiBrownianAbsoluteMoment, integral_const, probReal_univ,
    smul_eq_mul, mul_one, one_mul] using hb

theorem parisiBetaError_symm (β γ : ℝ) : parisiBetaError β γ = parisiBetaError γ β := by
  simp only [parisiBetaError, abs_sub_comm]

theorem parisiPotential_initial_beta_sub_le (β γ h : ℝ) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (μ : ParisiMeasure) :
    ‖parisiPotential β μ (0, h) - parisiPotential γ μ (0, h)‖ ≤ parisiBetaError β γ := by
  have hup (b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
      parisiPotential b μ (0, h) - parisiPotential c μ (0, h) ≤ parisiBetaError b c := by
    let A := selectedParisiControl b h hb μ
    have hA := isParisiAdmissibleControl_selectedParisiControl b h hb μ
    have he := parisiControlObjective_selected_eq_potential b h hb μ
    have hl := parisiControlObjective_le_potential c h hc μ A hA
    have hh := parisiControlObjective_beta_sub_le b c h μ A hA
    have hr := (le_abs_self _).trans hh
    change parisiControlObjective canonicalBrownianMeasure b h (canonicalBrownian 1) A μ = _ at he
    linarith
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hh := hup γ β hγ hβ
    rw [parisiBetaError_symm γ β] at hh
    linarith
  · exact hup β γ hβ hγ

theorem tendsto_parisiBetaError {ι : Type*} {L : Filter ι} (γ : ℝ) (β : ι → ℝ)
    (hβ : Tendsto β L (𝓝 γ)) : Tendsto (fun i => parisiBetaError (β i) γ) L (𝓝 0) := by
  have h₁ := (hβ.sub_const γ).abs
  have h₂ := ((hβ.pow 2).sub_const (γ ^ 2)).abs
  simpa only [parisiBetaError, sub_self, abs_zero, zero_mul, mul_zero, zero_add] using
    (h₁.mul_const parisiBrownianAbsoluteMoment).add (h₂.const_mul (3 / 2 : ℝ))

end FourPapersCommon
