module
public import QuantitativePaper.ZeroTemperatureControlStability
public import FRSB.BrownianMarkov

@[expose] public section

/-! The |x|-terminal scalar functional has a genuine lower bound, proved
with the constant adapted control and the actual Brownian mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper

def zeroTemperatureFunctional (γ : ℝ→ℝ) : ℝ :=
  zeroTemperatureValue γ 0-(1/2:ℝ)*∫q in (0:ℝ)..1,q*γ q

theorem admissible_oneControl : IsParisiAdmissibleControl (fun _ _=>1) where
  continuous_paths :=fun _=>continuous_const
  adapted :=stronglyAdapted_const _ 1
  measurable :=measurable_const
  bounded :=fun _ _=>by norm_num

theorem integral_zeroControlBrownian :
    (∫ω,canonicalBrownian 1 ω ∂canonicalBrownianMeasure)=0 := by
  have h:= (FRSB.hasLaw_scaledBrownian (1:ℝ) 1).integral_eq
  simpa only [one_mul,one_pow,NNReal.coe_one,Real.toNNReal_one,integral_id_gaussianReal] using h

theorem zeroTemperatureValue_ge_half_mass (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) :
    (1/2:ℝ)*(∫q in (0:ℝ)..1,γ q)≤zeroTemperatureValue γ 0 := by
  let A:ℝ→BrownianSample→ℝ:=fun _ _=>1
  have hA : IsParisiAdmissibleControl A:=admissible_oneControl
  have hz:=integrable_zeroControlEndpoint γ hγ hiγ 0 A hA
  have ha:=integral_mono_ae hz hz.abs (.of_forall fun ω=>le_abs_self (zeroControlEndpoint γ 0 A ω))
  have he : zeroControlEndpoint γ 0 A=(fun ω=>canonicalBrownian 1 ω+∫q in (0:ℝ)..1,γ q) := by
    funext ω
    simp [zeroControlEndpoint,A]
  rw [he,integral_add integrable_hjb_canonicalBrownian_one (integrable_const _),
    integral_zeroControlBrownian,integral_const] at ha
  simp only [probReal_univ,one_smul,zero_add] at ha
  have hiCost:=integrable_zeroControlCost γ hγ hiγ A hA
  have hv:=le_csSup (zeroControlValues_bddAbove γ hγ hiγ 0)
    (show zeroControlObjective γ 0 A∈zeroControlValues γ 0 from ⟨A,hA,rfl⟩)
  have ho : zeroControlObjective γ 0 A=
      (∫ω,|zeroControlEndpoint γ 0 A ω| ∂canonicalBrownianMeasure)-
      (1/2:ℝ)*(∫q in (0:ℝ)..1,γ q) := by
    unfold zeroControlObjective
    simp only [zeroControlPayoff]
    rw [integral_sub hz.abs hiCost]
    simp [zeroControlCost,A]
  rw [ho] at hv
  rw [he] at hv
  dsimp [zeroTemperatureValue]
  linarith

theorem intervalIntegrable_zeroTemperatureCorrection (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) :
    IntervalIntegrable (fun q=>q*γ q) volume (0:ℝ) 1 := by
  apply hiγ.norm.mono_fun' (measurable_id.mul hγ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with q hq
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hq
  change ‖q*γ q‖≤‖γ q‖
  rw [norm_mul,Real.norm_of_nonneg hq.1.le]
  exact (mul_le_mul_of_nonneg_right hq.2 (norm_nonneg _)).trans_eq (one_mul _)

theorem zeroTemperatureFunctional_nonneg (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hγ0 : ∀ᵐ q ∂volume,q∈Ioc (0:ℝ) 1→0≤γ q) :
    0≤zeroTemperatureFunctional γ := by
  have hj:=intervalIntegrable_zeroTemperatureCorrection γ hγ hiγ
  have hc : (∫q in (0:ℝ)..1,q*γ q)≤∫q in (0:ℝ)..1,γ q := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    apply integral_mono_ae hj.1 hiγ.1
    filter_upwards [hγ0.filter_mono (ae_restrict_le),ae_restrict_mem measurableSet_Ioc] with q hq hqi
    exact (mul_le_mul_of_nonneg_right hqi.2 (hq hqi)).trans_eq (one_mul _)
  have hv:=zeroTemperatureValue_ge_half_mass γ hγ hiγ
  unfold zeroTemperatureFunctional
  linarith

end QuantitativePaper
