module
public import QuantitativePaper.ZeroTemperatureControlStability
public import Paper.ParisiHJB

@[expose] public section

/-! Exact energy normalization of the actual Parisi control objective and
its uniform comparison with the genuine |x|-terminal control value. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

def softAbsoluteTerminal (β x : ℝ) : ℝ :=
  (Real.log 2+Real.log (Real.cosh (β*x)))/β

theorem softAbsoluteTerminal_bounds (β x : ℝ) (hβ : 0<β) :
    |x| ≤ softAbsoluteTerminal β x ∧ softAbsoluteTerminal β x ≤ |x|+Real.log 2/β := by
  have hcosh : Real.exp |β*x|≤2*Real.cosh (β*x) := by
    rw [Real.cosh_eq]
    by_cases hx : 0≤β*x
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-(β*x))]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos (β*x)]
  have hlo:=Real.log_le_log (Real.exp_pos |β*x|) hcosh
  rw [Real.log_exp,Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.cosh_pos _).ne'] at hlo
  have hhi : Real.log (Real.cosh (β*x))≤|β*x| :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_logcosh_le_abs (β*x))
  have habs : |β*x|=β*|x| := by rw [abs_mul,abs_of_pos hβ]
  rw [habs] at hlo hhi
  constructor
  · exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hlo)
  · unfold softAbsoluteTerminal
    apply (div_le_iff₀ hβ).mpr
    have he : (|x|+Real.log 2/β)*β=β*|x|+Real.log 2 := by field_simp <;> ring
    rw [he]
    linarith

def softZeroControlPayoff (β : ℝ) (γ : ℝ→ℝ) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) : ℝ :=
  softAbsoluteTerminal β (zeroControlEndpoint γ x A ω)-zeroControlCost γ A ω

theorem softZeroControlPayoff_bounds (β : ℝ) (hβ : 0<β) (γ : ℝ→ℝ) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) :
    zeroControlPayoff γ x A ω ≤ softZeroControlPayoff β γ x A ω ∧
      softZeroControlPayoff β γ x A ω≤zeroControlPayoff γ x A ω+Real.log 2/β := by
  have hh:=softAbsoluteTerminal_bounds β (zeroControlEndpoint γ x A ω) hβ
  dsimp [softZeroControlPayoff,zeroControlPayoff]
  constructor <;> linarith

theorem scaled_parisiControlPayoff_eq (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    (x : ℝ) (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) :
    (parisiControlPayoff β (β*x) (canonicalBrownian 1) A μ ω+Real.log 2)/β=
      softZeroControlPayoff β (fun q=>β*parisiCDF μ q) x A ω := by
  have he : β*x+β*canonicalBrownian 1 ω+parisiControlDrift β μ A ω=
      β*zeroControlEndpoint (fun q=>β*parisiCDF μ q) x A ω := by
    unfold zeroControlEndpoint parisiControlDrift
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hc : parisiControlCost β μ A ω/β=
      zeroControlCost (fun q=>β*parisiCDF μ q) A ω := by
    unfold parisiControlCost zeroControlCost
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    field_simp
    <;> ring
  unfold parisiControlPayoff softZeroControlPayoff softAbsoluteTerminal
  rw [he,←hc]
  ring

theorem integrable_softZeroControlPayoff_parisi (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (x : ℝ) (A : ℝ→BrownianSample→ℝ)
    (hA : IsParisiAdmissibleControl A) :
    Integrable (softZeroControlPayoff β (fun q=>β*parisiCDF μ q) x A) canonicalBrownianMeasure := by
  have hp:=integrable_parisiControlPayoff canonicalBrownianMeasure β (β*x) (canonicalBrownian 1)
    (measurable_canonicalBrownian 1) integrable_hjb_canonicalBrownian_one A hA.measurable hA.bounded μ
  exact ((hp.add (integrable_const (Real.log 2))).div_const β).congr
    (.of_forall fun ω=>scaled_parisiControlPayoff_eq β hβ μ x A ω)

theorem integral_softZeroControlPayoff_parisi (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (x : ℝ) (A : ℝ→BrownianSample→ℝ)
    (hA : IsParisiAdmissibleControl A) :
    (∫ω,softZeroControlPayoff β (fun q=>β*parisiCDF μ q) x A ω ∂canonicalBrownianMeasure)=
      (parisiControlObjective canonicalBrownianMeasure β (β*x) (canonicalBrownian 1) A μ+Real.log 2)/β := by
  have hp:=integrable_parisiControlPayoff canonicalBrownianMeasure β (β*x) (canonicalBrownian 1)
    (measurable_canonicalBrownian 1) integrable_hjb_canonicalBrownian_one A hA.measurable hA.bounded μ
  calc
    _=(∫ω,(parisiControlPayoff β (β*x) (canonicalBrownian 1) A μ ω+Real.log 2)/β
        ∂canonicalBrownianMeasure) := integral_congr_ae (.of_forall fun ω=>
      (scaled_parisiControlPayoff_eq β hβ μ x A ω).symm)
    _=_ := by
      rw [integral_div,integral_add hp (integrable_const _),integral_const]
      simp only [probReal_univ,one_smul,parisiControlObjective]

theorem scaled_control_objective_sandwich (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (x : ℝ) (A : ℝ→BrownianSample→ℝ)
    (hA : IsParisiAdmissibleControl A) :
    zeroControlObjective (fun q=>β*parisiCDF μ q) x A≤
      (parisiControlObjective canonicalBrownianMeasure β (β*x) (canonicalBrownian 1) A μ+Real.log 2)/β ∧
    (parisiControlObjective canonicalBrownianMeasure β (β*x) (canonicalBrownian 1) A μ+Real.log 2)/β≤
      zeroControlObjective (fun q=>β*parisiCDF μ q) x A+Real.log 2/β := by
  have hm : Measurable (fun q=>β*parisiCDF μ q):=measurable_const.mul (parisiCDF_measurable μ)
  have hi : IntervalIntegrable (fun q=>β*parisiCDF μ q) volume (0:ℝ) 1:=
    (parisiCDF_monotone μ).intervalIntegrable.const_mul β
  have hz:=integrable_zeroControlPayoff _ hm hi x A hA
  have hs:=integrable_softZeroControlPayoff_parisi β hβ.ne' μ x A hA
  have h1:=integral_mono_ae hz hs (.of_forall fun ω=>(softZeroControlPayoff_bounds β hβ _ x A ω).1)
  have h2:=integral_mono_ae hs (hz.add (integrable_const (Real.log 2/β)))
    (.of_forall fun ω=>(softZeroControlPayoff_bounds β hβ _ x A ω).2)
  rw [integral_softZeroControlPayoff_parisi β hβ.ne' μ x A hA] at h1 h2
  dsimp only [Pi.add_apply] at h2
  rw [integral_add hz (integrable_const _),integral_const] at h2
  exact ⟨h1,by simpa only [one_smul,probReal_univ,zeroControlObjective] using h2⟩

/-- Uniform terminal comparison against the genuine actual Parisi PDE. -/
theorem zeroTemperatureValue_parisi_sandwich (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (x : ℝ) :
    zeroTemperatureValue (fun q=>β*parisiCDF μ q) x≤
      (Real.log 2+parisiPotential β μ (0,β*x))/β ∧
    (Real.log 2+parisiPotential β μ (0,β*x))/β≤
      zeroTemperatureValue (fun q=>β*parisiCDF μ q) x+Real.log 2/β := by
  have hm : Measurable (fun q=>β*parisiCDF μ q):=measurable_const.mul (parisiCDF_measurable μ)
  have hi : IntervalIntegrable (fun q=>β*parisiCDF μ q) volume (0:ℝ) 1:=
    (parisiCDF_monotone μ).intervalIntegrable.const_mul β
  constructor
  · apply csSup_le (zeroControlValues_nonempty _ x)
    rintro v ⟨A,hA,rfl⟩
    have hc:=(scaled_control_objective_sandwich β hβ μ x A hA).1
    have hp:=parisiControlObjective_le_potential β (β*x) hβ.ne' μ A hA
    have hh:=div_le_div_of_nonneg_right (add_le_add hp (le_refl (Real.log 2))) hβ.le
    exact hc.trans (by simpa only [add_comm] using hh)
  · let A:=selectedParisiControl β (β*x) hβ.ne' μ
    have hA:=isParisiAdmissibleControl_selectedParisiControl β (β*x) hβ.ne' μ
    have hc:=(scaled_control_objective_sandwich β hβ μ x A hA).2
    have he:=parisiControlObjective_selected_eq_potential β (β*x) hβ.ne' μ
    change parisiControlObjective canonicalBrownianMeasure β (β*x) (canonicalBrownian 1) A μ=_ at he
    rw [he] at hc
    have hv:=le_csSup (zeroControlValues_bddAbove _ hm hi x)
      (show zeroControlObjective (fun q=>β*parisiCDF μ q) x A∈zeroControlValues _ x from ⟨A,hA,rfl⟩)
    have hz : zeroControlObjective (fun q=>β*parisiCDF μ q) x A+Real.log 2/β≤
        zeroTemperatureValue (fun q=>β*parisiCDF μ q) x+Real.log 2/β := by
      dsimp [zeroTemperatureValue]
      linarith
    have hc' : (Real.log 2+parisiPotential β μ (0,β*x))/β≤
        zeroControlObjective (fun q=>β*parisiCDF μ q) x A+Real.log 2/β := by
      simpa only [add_comm] using hc
    exact hc'.trans hz

end QuantitativePaper
