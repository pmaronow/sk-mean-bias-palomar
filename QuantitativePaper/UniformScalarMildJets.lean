module
public import QuantitativePaper.UniformScalarMild

@[expose] public section

/-! Every derivative of the actual scalar mild equation. Derivative
exchange uses the existing finite-temperature jet bounds only as dominating
functions; none of those bounds is claimed uniform in temperature. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 2500000

def scalarEnergyJetSource (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (q x s : ℝ) : ℝ :=
  (β*parisiCDF μ s)*heatGradient (s-q) (fun y=>scalarEnergySquareJet β μ j (s,y)) x

theorem measurable_scalarEnergyJetSource (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (q x : ℝ) : Measurable (scalarEnergyJetSource β μ j q x) := by
  have hm : Measurable (fun p : ℝ×ℝ=>p.2*
      scalarEnergySquareJet β μ j (p.1,x+Real.sqrt (p.1-q)*p.2)) := by
    exact measurable_snd.mul ((continuous_scalarEnergySquareJet β μ j).measurable.comp (by fun_prop))
  have hg := hm.stronglyMeasurable.integral_prod_right' (ν:=gaussianReal 0 1)
  unfold scalarEnergyJetSource heatGradient gaussianExpectation
  exact (measurable_const.mul (parisiCDF_measurable μ)).mul
    ((show Measurable (fun s : ℝ=>(Real.sqrt (s-q))⁻¹) by fun_prop).mul hg.measurable)

theorem scalarEnergyJetSource_norm_bound (β : ℝ) (hβ : 0≤β) (μ : ParisiMeasure)
    (j : ℕ) (M : ℝ) (hM : ∀p,‖scalarEnergySquareJet β μ j p‖≤M) (q x s : ℝ) :
    ‖scalarEnergyJetSource β μ j q x s‖≤
      (β*gaussianAbsMoment*M)*(Real.sqrt (s-q))⁻¹ := by
  have hm : ‖β*parisiCDF μ s‖≤β := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hβ (parisiCDF_nonneg μ s))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (parisiCDF_le_one μ s) hβ
  unfold scalarEnergyJetSource
  rw [norm_mul]
  exact (mul_le_mul hm (norm_heatGradient_le _ _ _ (fun y=>hM (s,y)) x)
    (norm_nonneg _) hβ).trans_eq (by ring)

theorem intervalIntegrable_scalarEnergyJetSource (β : ℝ) (hβ : 0≤β)
    (μ : ParisiMeasure) (j : ℕ) (q b x : ℝ) (hqb : q≤b) :
    IntervalIntegrable (scalarEnergyJetSource β μ j q x) volume q b := by
  obtain ⟨M,hM0,hM⟩:=scalarEnergySquareJet_bounded β μ j
  exact ((intervalIntegrable_inv_sqrt_sub q b hqb).const_mul (β*gaussianAbsMoment*M)).mono_fun'
    (measurable_scalarEnergyJetSource β μ j q x).aestronglyMeasurable
    (.of_forall (scalarEnergyJetSource_norm_bound β hβ μ j M hM q x))

theorem hasDerivAt_scalarEnergyJetSource (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (q s x : ℝ) :
    HasDerivAt (fun y=>scalarEnergyJetSource β μ j q y s)
      (scalarEnergyJetSource β μ (j+1) q x s) x := by
  obtain ⟨M,hM0,hM⟩:=scalarEnergySquareJet_bounded β μ j
  obtain ⟨K,hK0,hK⟩:=scalarEnergySquareJet_bounded β μ (j+1)
  exact (hasDerivAt_scalar_heatGradient_by_data (s-q)
    (fun y=>scalarEnergySquareJet β μ j (s,y))
    (fun y=>scalarEnergySquareJet β μ (j+1) (s,y)) M K x
    ((continuous_scalarEnergySquareJet β μ j).comp (by fun_prop))
    ((continuous_scalarEnergySquareJet β μ (j+1)).comp (by fun_prop))
    (hasDerivAt_scalarEnergySquareJet β μ j s) (fun y=>hM _) (fun y=>hK _)).const_mul _

theorem hasDerivAt_integral_scalarEnergyJetSource (β : ℝ) (hβ : 0≤β)
    (μ : ParisiMeasure) (j : ℕ) (q b x : ℝ) (hqb : q≤b) :
    HasDerivAt (fun y=>∫s in q..b,scalarEnergyJetSource β μ j q y s)
      (∫s in q..b,scalarEnergyJetSource β μ (j+1) q x s) x := by
  obtain ⟨K,hK0,hK⟩:=scalarEnergySquareJet_bounded β μ (j+1)
  let B : ℝ→ℝ:=fun s=>(β*gaussianAbsMoment*K)*(Real.sqrt (s-q))⁻¹
  have hB : Integrable B (volume.restrict (Ioc q b)) :=
    ((intervalIntegrable_inv_sqrt_sub q b hqb).const_mul _).1
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume.restrict (Ioc q b))
    (F:=fun y s=>scalarEnergyJetSource β μ j q y s)
    (F':=fun y s=>scalarEnergyJetSource β μ (j+1) q y s)
    (bound:=B) (s:=univ) (by simp)
    (.of_forall fun y=>(measurable_scalarEnergyJetSource β μ j q y).aestronglyMeasurable)
    (intervalIntegrable_scalarEnergyJetSource β hβ μ j q b x hqb).1
    (measurable_scalarEnergyJetSource β μ (j+1) q x).aestronglyMeasurable
    (.of_forall fun s y _=>scalarEnergyJetSource_norm_bound β hβ μ (j+1) K hK q y s)
    hB (.of_forall fun s y _=>hasDerivAt_scalarEnergyJetSource β μ j q s y)).2
  simpa only [intervalIntegral.integral_of_le hqb] using hD

theorem scalarEnergySpatialJet_mild_all (β : ℝ) (hβ : 0<β) (μ : ParisiMeasure)
    (j : ℕ) (b q x : ℝ) (hb : b∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) b) :
    scalarEnergySpatialJet β μ j (q,x)=
      heatSemigroup (b-q) (fun y=>scalarEnergySpatialJet β μ j (b,y)) x+
      (1/2:ℝ)*(∫s in q..b,scalarEnergyJetSource β μ j q x s) := by
  induction j generalizing x with
  | zero => simpa only [scalarEnergyJetSource,scalarEnergySquareJet_zero] using
      scalarEnergySpatialJet_mild β hβ μ b q x hb hq
  | succ j ih =>
    obtain ⟨M,hM0,hM⟩:=scalarEnergySpatialJet_bounded β μ j
    obtain ⟨K,hK0,hK⟩:=scalarEnergySpatialJet_bounded β μ (j+1)
    have hDt := hasDerivAt_scalar_heat_by_data (b-q)
      (fun y=>scalarEnergySpatialJet β μ j (b,y))
      (fun y=>scalarEnergySpatialJet β μ (j+1) (b,y)) M K x
      ((continuous_scalarEnergySpatialJet β μ j).comp (by fun_prop))
      ((continuous_scalarEnergySpatialJet β μ (j+1)).comp (by fun_prop))
      (hasDerivAt_scalarEnergySpatialJet β μ j b · hb) (fun y=>hM _) (fun y=>hK _)
    have hDi := (hasDerivAt_integral_scalarEnergyJetSource β hβ.le μ j q b x hq.2).const_mul (1/2:ℝ)
    have hD := hDt.add hDi
    have heq : (fun y=>scalarEnergySpatialJet β μ j (q,y))=
        (fun y=>heatSemigroup (b-q) (fun z=>scalarEnergySpatialJet β μ j (b,z)) y+
          (1/2:ℝ)*(∫s in q..b,scalarEnergyJetSource β μ j q y s)) := funext ih
    change HasDerivAt (fun y=>heatSemigroup (b-q)
      (fun z=>scalarEnergySpatialJet β μ j (b,z)) y+
        (1/2:ℝ)*(∫s in q..b,scalarEnergyJetSource β μ j q y s)) _ x at hD
    rw [←heq] at hD
    exact HasDerivAt.unique (hasDerivAt_scalarEnergySpatialJet β μ j q x ⟨hq.1,hq.2.trans hb.2⟩) hD

end QuantitativePaper
