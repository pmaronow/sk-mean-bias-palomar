module
public import FourPapersCommon.BoundedTimeIntegral

@[expose] public section

/-! Genuine deterministic time shifts of the analytic FTC data. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal Topology
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
set_option maxHeartbeats 1000000

def TimeFTCData.shiftStart {b : ℝ≥0} (d : TimeFTCData Ω E b)
    (a T : ℝ≥0) (hT : a+T≤b) : TimeFTCData Ω E T where
  f := fun r=>d.f ((a : ℝ)+r)
  ft := fun r=>d.ft ((a : ℝ)+r)
  bound := d.bound
  spatialLip := d.spatialLip
  f_measurable := d.f_measurable.comp
    (show Measurable (fun z : ℝ×(Ω×E)=>((a : ℝ)+z.1,z.2)) from by fun_prop)
  ft_measurable := d.ft_measurable.comp
    (show Measurable (fun z : ℝ×(Ω×E)=>((a : ℝ)+z.1,z.2)) from by fun_prop)
  f_continuous := by
    intro sample x
    apply (d.f_continuous sample x).comp (continuous_const.add continuous_id).continuousOn
    intro r hr
    have hh : (a : ℝ)+T≤b := by exact_mod_cast hT
    change 0≤(a : ℝ)+r ∧ (a : ℝ)+r≤b
    exact ⟨by linarith [a.coe_nonneg,hr.1],by linarith [hr.2]⟩
  derivative := by
    intro sample x r hr
    have hh : (a : ℝ)+T≤b := by exact_mod_cast hT
    have hd := d.derivative sample x ((a : ℝ)+r)
      ⟨by linarith [a.coe_nonneg,hr.1],by linarith [hr.2]⟩
    simpa only [Function.comp_def,mul_one] using hd.comp r ((hasDerivAt_id r).const_add (a : ℝ))
  ft_continuous := fun sample=>(d.ft_continuous sample).comp
    (show Continuous (fun z : ℝ×E=>((a : ℝ)+z.1,z.2)) from by fun_prop)
  ft_bound := by
    intro r hr sample x
    have hh : (a : ℝ)+T≤b := by exact_mod_cast hT
    exact d.ft_bound ((a : ℝ)+r)
      ⟨by linarith [a.coe_nonneg,hr.1],by linarith [hr.2]⟩ sample x
  ft_lipschitz := by
    intro r hr sample
    have hh : (a : ℝ)+T≤b := by exact_mod_cast hT
    exact d.ft_lipschitz ((a : ℝ)+r)
      ⟨by linarith [a.coe_nonneg,hr.1],by linarith [hr.2]⟩ sample

end FourPapersCommon
