module
public import QuantitativeFollowup.ScalarRestartForcing
public import QuantitativeFollowup.IntegralFlowPerturbation
public import QuantitativeFollowup.ScalarRestartJacobian

@[expose] public section

/-! Joint continuity of the actual restart in weak measure, restart
level, initial field, and continuous Wiener path.  Only integrated
coefficient convergence is used, so atoms are allowed at every level. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem tendsto_scalarRestartNoiseStatePath {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μn L (𝓝 μ)) (an : ι → Paper.Overlap) (a : Paper.Overlap)
    (hA : Tendsto an L (𝓝 a)) (xn : ι → ℝ) (x : ℝ) (hx : Tendsto xn L (𝓝 x))
    (Wn : ι → C(Paper.Overlap,ℝ)) (W : C(Paper.Overlap,ℝ)) (hW : Tendsto Wn L (𝓝 W)) :
    Tendsto (fun i => parisiRestartNoiseStatePath β (xn i) (μn i) (an i) (an i).property.1 (Wn i))
      L (𝓝 (parisiRestartNoiseStatePath β x μ a a.property.1 W)) := by
  let X := scalarRestartFlow β μ a a.property.1 x W
  let Y := fun i => scalarRestartFlow β (μn i) (an i) (an i).property.1 (xn i) (Wn i)
  let E := fun i => |β| *‖Wn i-W‖
  let B := fun i => |xn i-x|+E i+∫ r in 0..1,
    ‖scalarRestartDriftField β (μn i) (an i) (an i).property.1 r (X r)-
      scalarRestartDriftField β μ a a.property.1 r (X r)‖
  have hX : Continuous X := continuous_scalarRestartFlow β μ a a.property.1 x W
  have hAn : Tendsto (fun i => (an i : ℝ)) L (𝓝 (a : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hA
  have hB : Tendsto B L (𝓝 0) := by
    have he := (tendsto_const_nhds (x := |β|)).mul (hW.sub_const W |>.norm)
    have hf := tendsto_scalarRestartDriftField_reference_gap β μn μ hμ
      (fun i => (an i : ℝ)) a (fun i => (an i).property.1) a.property.1 hAn X hX
    simpa only [B,E,sub_self,norm_zero,abs_zero,mul_zero,zero_add] using
      (hx.sub_const x |>.abs).add he |>.add hf
  have hn (i : ι) : 0 ≤ B i := by
    dsimp only [B,E]
    exact add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _)))
      (intervalIntegral.integral_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (fun _ _ => norm_nonneg _))
  have hb (i : ι) : dist (parisiRestartNoiseStatePath β (xn i) (μn i) (an i) (an i).property.1 (Wn i))
      (parisiRestartNoiseStatePath β x μ a a.property.1 W) ≤ B i*Real.exp (β^2) := by
    have hh := integral_state_perturbation_bound
      (scalarRestartDriftField β μ a a.property.1)
      (scalarRestartDriftField β (μn i) (an i) (an i).property.1)
      (parisiDriftConstant β) (parisiDriftConstant β)
      (scalarRestartDriftField_data β μ a a.property.1)
      (scalarRestartDriftField_data β (μn i) (an i) (an i).property.1)
      1 zero_le_one x (xn i) (E i) (by dsimp only [E]; positivity)
      (fun r => β*parisiNoiseExtension zero_le_one W r)
      (fun r => β*parisiNoiseExtension zero_le_one (Wn i) r) X (Y i)
      hX (continuous_scalarRestartFlow β (μn i) (an i) (an i).property.1 (xn i) (Wn i))
      (by
        intro r hr
        rw [←mul_sub,norm_mul,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
        have he := ContinuousMap.dist_apply_le_dist (f := Wn i) (g := W) (⟨r,hr⟩ : Paper.Overlap)
        simpa only [dist_eq_norm,parisiNoiseExtension,projIcc_of_mem zero_le_one hr] using he)
      (fun r hr => scalarRestartFlow_equation β μ a a.property.1 x W r hr)
      (fun r hr => scalarRestartFlow_equation β (μn i) (an i) (an i).property.1 (xn i) (Wn i) r hr)
    apply (ContinuousMap.dist_le (mul_nonneg (hn i) (Real.exp_pos _).le)).mpr
    intro r
    rw [dist_eq_norm]
    have hr := (hh r r.property).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by change β^2*(r : ℝ) ≤ β^2; nlinarith [sq_nonneg β,r.property.2])) (hn i))
    change ‖Y i r-X r‖ ≤ B i*Real.exp (β^2) at hr
    have heY : Y i r=parisiRestartNoiseStatePath β (xn i) (μn i) (an i) (an i).property.1 (Wn i) r := by
      simpa only [Y,projIcc_of_mem zero_le_one r.property] using
        scalarRestartFlow_eq_path β (μn i) (an i) (an i).property.1 (xn i) (Wn i) r
    have heX : X r=parisiRestartNoiseStatePath β x μ a a.property.1 W r := by
      simpa only [X,projIcc_of_mem zero_le_one r.property] using
        scalarRestartFlow_eq_path β μ a a.property.1 x W r
    rw [heY,heX] at hr
    exact hr
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) hb
  simpa only [zero_mul] using hB.mul (tendsto_const_nhds (x := Real.exp (β^2)))

theorem continuous_scalarRestartNoiseStatePath (β : ℝ) :
    Continuous (fun p : Paper.ParisiMeasure×(Paper.Overlap×(ℝ×C(Paper.Overlap,ℝ))) =>
      parisiRestartNoiseStatePath β p.2.2.1 p.1 p.2.1 p.2.1.property.1 p.2.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_scalarRestartNoiseStatePath (L := 𝓝 p) β
    (fun z : Paper.ParisiMeasure×(Paper.Overlap×(ℝ×C(Paper.Overlap,ℝ))) => z.1) p.1 continuous_fst.continuousAt
    (fun z => z.2.1) p.2.1 (continuous_fst.comp continuous_snd).continuousAt
    (fun z => z.2.2.1) p.2.2.1
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
    (fun z => z.2.2.2) p.2.2.2
      (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt

end QuantitativeFollowup
