module
public import QuantitativePaper.ZeroTemperatureControl

@[expose] public section

/-! Genuine L1 stability and finite supremum of the |x|-terminal Brownian
control value, including integrable unbounded coefficients. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

def zeroProfileDistance (γ η : ℝ→ℝ) : ℝ := ∫q in (0:ℝ)..1,‖γ q-η q‖

theorem zeroControlProduct_difference_bound (γ η : ℝ→ℝ)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hiη : IntervalIntegrable η volume (0:ℝ) 1)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A)
    (j : ℕ) (ω : BrownianSample) :
    ‖(∫q in (0:ℝ)..1,γ q*(A q ω)^j)-∫q in (0:ℝ)..1,η q*(A q ω)^j‖≤
      zeroProfileDistance γ η := by
  rw [←intervalIntegral.integral_sub
    (intervalIntegrable_zeroControlProduct γ hγ hiγ A hA j ω)
    (intervalIntegrable_zeroControlProduct η hη hiη A hA j ω)]
  have he : (fun q=>γ q*(A q ω)^j-η q*(A q ω)^j)=
      (fun q=>(γ q-η q)*(A q ω)^j) := by funext q;ring
  rw [he]
  exact norm_zeroControlProduct_integral_le (fun q=>γ q-η q) (hiγ.sub hiη) A hA j ω

theorem zeroControlPayoff_difference_bound (γ η : ℝ→ℝ)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hiη : IntervalIntegrable η volume (0:ℝ) 1) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A)
    (ω : BrownianSample) :
    ‖zeroControlPayoff γ x A ω-zeroControlPayoff η x A ω‖≤
      (3/2:ℝ)*zeroProfileDistance γ η := by
  have he : zeroControlEndpoint γ x A ω-zeroControlEndpoint η x A ω=
      (∫q in (0:ℝ)..1,γ q*A q ω)-∫q in (0:ℝ)..1,η q*A q ω := by
    unfold zeroControlEndpoint
    ring
  have hc : zeroControlCost γ A ω-zeroControlCost η A ω=
      (1/2:ℝ)*((∫q in (0:ℝ)..1,γ q*(A q ω)^2)-∫q in (0:ℝ)..1,η q*(A q ω)^2) := by
    unfold zeroControlCost
    ring
  have h1:=zeroControlProduct_difference_bound γ η hγ hη hiγ hiη A hA 1 ω
  simp only [pow_one] at h1
  have h2:=zeroControlProduct_difference_bound γ η hγ hη hiγ hiη A hA 2 ω
  have hcost : ‖zeroControlCost γ A ω-zeroControlCost η A ω‖≤
      (1/2:ℝ)*zeroProfileDistance γ η := by
    rw [hc,norm_mul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have haa:=norm_abs_sub_abs (zeroControlEndpoint γ x A ω) (zeroControlEndpoint η x A ω)
  rw [he] at haa
  have hh:=norm_sub_le (|zeroControlEndpoint γ x A ω|-|zeroControlEndpoint η x A ω|)
    (zeroControlCost γ A ω-zeroControlCost η A ω)
  have ht : zeroControlPayoff γ x A ω-zeroControlPayoff η x A ω=
      (|zeroControlEndpoint γ x A ω|-|zeroControlEndpoint η x A ω|)-
      (zeroControlCost γ A ω-zeroControlCost η A ω) := by unfold zeroControlPayoff;ring
  rw [ht]
  exact hh.trans (by linarith [haa.trans h1])

theorem zeroControlObjective_difference_bound (γ η : ℝ→ℝ)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hiη : IntervalIntegrable η volume (0:ℝ) 1) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) :
    ‖zeroControlObjective γ x A-zeroControlObjective η x A‖≤
      (3/2:ℝ)*zeroProfileDistance γ η := by
  rw [zeroControlObjective,zeroControlObjective,←integral_sub
    (integrable_zeroControlPayoff γ hγ hiγ x A hA)
    (integrable_zeroControlPayoff η hη hiη x A hA)]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=canonicalBrownianMeasure)
    (.of_forall fun ω=>zeroControlPayoff_difference_bound γ η hγ hη hiγ hiη x A hA ω)

theorem zeroControlPayoff_norm_bound (γ : ℝ→ℝ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A)
    (ω : BrownianSample) :
    ‖zeroControlPayoff γ x A ω‖≤ |x|+|canonicalBrownian 1 ω|+
      (3/2:ℝ)*(∫q in (0:ℝ)..1,‖γ q‖) := by
  have h1:=norm_zeroControlProduct_integral_le γ hiγ A hA 1 ω
  simp only [pow_one,Real.norm_eq_abs] at h1
  have h2:=norm_zeroControlProduct_integral_le γ hiγ A hA 2 ω
  have he:=abs_add_le (x+canonicalBrownian 1 ω) (∫q in (0:ℝ)..1,γ q*A q ω)
  have hx:=abs_add_le x (canonicalBrownian 1 ω)
  have hc : ‖zeroControlCost γ A ω‖≤(1/2:ℝ)*(∫q in (0:ℝ)..1,‖γ q‖) := by
    rw [zeroControlCost,norm_mul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hp:=norm_sub_le |zeroControlEndpoint γ x A ω| (zeroControlCost γ A ω)
  simp only [Real.norm_eq_abs,abs_abs] at hp hc
  unfold zeroControlPayoff
  simp only [Real.norm_eq_abs]
  exact hp.trans (by dsimp [zeroControlEndpoint] at *;linarith)

theorem zeroControlObjective_upper_bound (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) :
    zeroControlObjective γ x A≤ |x|+(∫ω,|canonicalBrownian 1 ω| ∂canonicalBrownianMeasure)+
      (3/2:ℝ)*(∫q in (0:ℝ)..1,‖γ q‖) := by
  have hbound:=integral_mono_ae (integrable_zeroControlPayoff γ hγ hiγ x A hA)
    (((integrable_const |x|).add integrable_hjb_canonicalBrownian_one.abs).add
      (integrable_const ((3/2:ℝ)*(∫q in (0:ℝ)..1,‖γ q‖))))
    (.of_forall fun ω=>(le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using zeroControlPayoff_norm_bound γ hiγ x A hA ω))
  dsimp only [Pi.add_apply] at hbound
  have hib : Integrable (fun ω=>|x|+|canonicalBrownian 1 ω|) canonicalBrownianMeasure := by
    convert! (integrable_const |x|).add integrable_hjb_canonicalBrownian_one.abs using 1
  rw [integral_add hib
    (integrable_const ((3/2:ℝ)*(∫q in (0:ℝ)..1,‖γ q‖))),
    integral_add (integrable_const |x|) integrable_hjb_canonicalBrownian_one.abs,
    integral_const,integral_const] at hbound
  simpa only [zeroControlObjective,probReal_univ,one_smul] using hbound

theorem zeroControlValues_bddAbove (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) (x : ℝ) :
    BddAbove (zeroControlValues γ x) := by
  refine ⟨|x|+(∫ω,|canonicalBrownian 1 ω| ∂canonicalBrownianMeasure)+
    (3/2:ℝ)*(∫q in (0:ℝ)..1,‖γ q‖),?_⟩
  rintro v ⟨A,hA,rfl⟩
  exact zeroControlObjective_upper_bound γ hγ hiγ x A hA

theorem zeroTemperatureValue_difference_bound (γ η : ℝ→ℝ)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hiη : IntervalIntegrable η volume (0:ℝ) 1) (x : ℝ) :
    ‖zeroTemperatureValue γ x-zeroTemperatureValue η x‖≤
      (3/2:ℝ)*zeroProfileDistance γ η := by
  have hbγ:=zeroControlValues_bddAbove γ hγ hiγ x
  have hbη:=zeroControlValues_bddAbove η hη hiη x
  have hforward : zeroTemperatureValue γ x≤zeroTemperatureValue η x+
      (3/2:ℝ)*zeroProfileDistance γ η := by
    apply csSup_le (zeroControlValues_nonempty γ x)
    rintro v ⟨A,hA,rfl⟩
    have hv:=le_csSup hbη (show zeroControlObjective η x A∈zeroControlValues η x from ⟨A,hA,rfl⟩)
    have hd:=zeroControlObjective_difference_bound γ η hγ hη hiγ hiη x A hA
    rw [Real.norm_eq_abs] at hd
    have ha:=le_abs_self (zeroControlObjective γ x A-zeroControlObjective η x A)
    have hh : zeroControlObjective γ x A≤zeroControlObjective η x A+
        (3/2:ℝ)*zeroProfileDistance γ η := by linarith
    have hz : zeroControlObjective η x A+(3/2:ℝ)*zeroProfileDistance γ η≤
        zeroTemperatureValue η x+(3/2:ℝ)*zeroProfileDistance γ η := by
      dsimp [zeroTemperatureValue]
      linarith
    exact hh.trans hz
  have hback : zeroTemperatureValue η x≤zeroTemperatureValue γ x+
      (3/2:ℝ)*zeroProfileDistance γ η := by
    apply csSup_le (zeroControlValues_nonempty η x)
    rintro v ⟨A,hA,rfl⟩
    have hv:=le_csSup hbγ (show zeroControlObjective γ x A∈zeroControlValues γ x from ⟨A,hA,rfl⟩)
    have hd:=zeroControlObjective_difference_bound γ η hγ hη hiγ hiη x A hA
    rw [Real.norm_eq_abs] at hd
    have ha:=neg_le_abs (zeroControlObjective γ x A-zeroControlObjective η x A)
    have hh : zeroControlObjective η x A≤zeroControlObjective γ x A+
        (3/2:ℝ)*zeroProfileDistance γ η := by linarith
    have hz : zeroControlObjective γ x A+(3/2:ℝ)*zeroProfileDistance γ η≤
        zeroTemperatureValue γ x+(3/2:ℝ)*zeroProfileDistance γ η := by
      dsimp [zeroTemperatureValue]
      linarith
    exact hh.trans hz
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end QuantitativePaper
