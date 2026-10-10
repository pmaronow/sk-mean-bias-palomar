module
public import FourPapersCommon.TimePartitionFTC

@[expose] public section

/-! Squaring a genuine bounded time-FTC test preserves its actual time
derivative and uniform spatial controls. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ≥0}

def TimeFTCData.square (d : TimeFTCData Ω E T) (R L : ℝ≥0)
    (hR : ∀r sample x,‖d.f r sample x‖≤R)
    (hL : ∀r sample,LipschitzWith L (d.f r sample))
    (hc : ∀sample,Continuous (fun z : ℝ×E=>d.f z.1 sample z.2)) :
    TimeFTCData Ω E T where
  f := fun r sample x=>d.f r sample x^2
  ft := fun r sample x=>2*d.f r sample x*d.ft r sample x
  f_measurable := d.f_measurable.pow_const 2
  ft_measurable := (measurable_const.mul d.f_measurable).mul d.ft_measurable
  f_continuous := fun sample x=>(d.f_continuous sample x).pow 2
  derivative := by
    intro sample x r hr
    convert! (d.derivative sample x r hr).pow 2 using 1 <;> norm_num
  ft_continuous := fun sample=>((hc sample).const_mul 2).mul (d.ft_continuous sample)
  bound := 2*R*d.bound
  spatialLip := 2*(R*d.spatialLip+d.bound*L)
  ft_bound := by
    intro r hr sample x
    simp only [norm_mul,Real.norm_ofNat,NNReal.coe_mul,NNReal.coe_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hR r sample x) (by norm_num))
      (d.ft_bound r hr sample x) (norm_nonneg _) (by positivity)
  ft_lipschitz := by
    intro r hr sample
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hsplit : 2*d.f r sample x*d.ft r sample x-2*d.f r sample y*d.ft r sample y=
        2*(d.f r sample x*(d.ft r sample x-d.ft r sample y)+
          (d.f r sample x-d.f r sample y)*d.ft r sample y) := by ring
    rw [dist_eq_norm,hsplit,norm_mul,Real.norm_ofNat]
    have ha := norm_add_le (d.f r sample x*(d.ft r sample x-d.ft r sample y))
      ((d.f r sample x-d.f r sample y)*d.ft r sample y)
    have hb := (d.ft_lipschitz r hr sample).dist_le_mul x y
    have hf := (hL r sample).dist_le_mul x y
    rw [dist_eq_norm] at hb hf
    simp only [norm_mul] at ha
    have hx := hR r sample x
    have hy := d.ft_bound r hr sample y
    have h1 := mul_le_mul hx hb (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul hf hy (norm_nonneg _) (by positivity)
    simp only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_ofNat]
    nlinarith

end FourPapersCommon
