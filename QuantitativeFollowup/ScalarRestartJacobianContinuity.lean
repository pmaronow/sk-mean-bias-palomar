module
public import QuantitativeFollowup.ScalarRestartContinuity
public import QuantitativeFollowup.ScalarRestartJacobian
public import QuantitativeFollowup.BoundedProductPrimitive

@[expose] public section

/-! The actual flow Jacobian is jointly continuous in weak measure,
restart level, initial field, driving path, and elapsed endpoint.
CDF convergence is used in L¹; no atom-free assumption is introduced. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem tendsto_scalarRestartFlowJacobian {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0)
    (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (an : ι → Paper.Overlap) (a : Paper.Overlap) (hA : Tendsto an L (𝓝 a))
    (xn : ι → ℝ) (x : ℝ) (hx : Tendsto xn L (𝓝 x))
    (Wn : ι → C(Paper.Overlap,ℝ)) (W : C(Paper.Overlap,ℝ)) (hW : Tendsto Wn L (𝓝 W))
    (tn : ι → Paper.Overlap) (t : Paper.Overlap) (hT : Tendsto tn L (𝓝 t)) :
    Tendsto (fun i => scalarRestartFlowJacobian β (μn i) (an i) (an i).property.1
      (xn i) (Wn i) (tn i)) L (𝓝 (scalarRestartFlowJacobian β μ a a.property.1 x W t)) := by
  let Xn := fun i => scalarRestartFlow β (μn i) (an i) (an i).property.1 (xn i) (Wn i)
  let X := scalarRestartFlow β μ a a.property.1 x W
  let Hn := fun i r => parisiHessian β (μn i) ((an i : ℝ)+r,Xn i r)
  let H := fun r => parisiHessian β μ ((a : ℝ)+r,X r)
  have hPath := tendsto_scalarRestartNoiseStatePath β μn μ hμ an a hA xn x hx Wn W hW
  have hAn : Tendsto (fun i => (an i : ℝ)) L (𝓝 (a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hA
  have hTn : Tendsto (fun i => (tn i : ℝ)) L (𝓝 (t : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hT
  have hHn (i : ι) : Measurable (Hn i) :=
    ((continuous_parisiHessian_all β (μn i)).comp
      ((continuous_const.add continuous_id).prodMk
        (continuous_scalarRestartFlow β (μn i) (an i) (an i).property.1 (xn i) (Wn i)))).measurable
  have hH : Measurable H := ((continuous_parisiHessian_all β μ).comp
    ((continuous_const.add continuous_id).prodMk (continuous_scalarRestartFlow β μ a a.property.1 x W))).measurable
  have hHp (r : ℝ) : Tendsto (fun i => Hn i r) L (𝓝 (H r)) := by
    have hXr : Tendsto (fun i => Xn i r) L (𝓝 (X r)) := by
      have he := (continuous_eval (X := Paper.Overlap) (Y := ℝ) (F := C(Paper.Overlap,ℝ))).continuousAt.tendsto.comp
        (hPath.prodMk_nhds (tendsto_const_nhds (x := projIcc 0 1 zero_le_one r)))
      simpa only [Xn,X,scalarRestartFlow_eq_path,Function.comp_def] using he
    have harg := hμ.prodMk_nhds ((hAn.add_const r).prodMk_nhds hXr)
    have hh := (continuous_parisiHessian_measure_joint β hβ).continuousAt.tendsto.comp harg
    simpa only [Hn,H,Function.comp_def] using hh
  have hC := tendsto_parisiRestartMeasure_CDFDistance μn μ hμ (fun i => (an i : ℝ)) a
    (fun i => (an i).property.1) a.property.1 hAn
  have hC' : Tendsto (fun i => ∫ s in 0..1,
      ‖parisiCDF (parisiRestartMeasure (μn i) (an i) (an i).property.1) s-
        parisiCDF (parisiRestartMeasure μ a a.property.1) s‖) L (𝓝 0) := by
    simpa only [Paper.parisiCDFDistance,Real.norm_eq_abs] using hC
  have hi := bounded_product_primitive_tendsto
    (fun i => parisiCDF (parisiRestartMeasure (μn i) (an i) (an i).property.1)) Hn
    (parisiCDF (parisiRestartMeasure μ a a.property.1)) H
    (fun i => parisiCDF_measurable _) hHn (parisiCDF_measurable _) hH
    (fun i s => by rw [Real.norm_of_nonneg (parisiCDF_nonneg _ _)]; exact parisiCDF_le_one _ _)
    (fun i r => norm_parisiHessian_le_one_all _ _ _)
    (fun s => by rw [Real.norm_of_nonneg (parisiCDF_nonneg _ _)]; exact parisiCDF_le_one _ _)
    (fun r => norm_parisiHessian_le_one_all _ _ _) hC' hHp
    (fun i => (tn i : ℝ)) t (fun i => (tn i).property) t.property hTn
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := β^2)).mul hi)
  simpa only [scalarRestartFlowJacobian,scalarRestartDriftDerivative,Xn,X,Hn,H,
    mul_assoc,intervalIntegral.integral_const_mul,Function.comp_def] using he

theorem continuous_scalarRestartFlowJacobian (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun p : Paper.ParisiMeasure×(Paper.Overlap×(ℝ×(C(Paper.Overlap,ℝ)×Paper.Overlap))) =>
      scalarRestartFlowJacobian β p.1 p.2.1 p.2.1.property.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_scalarRestartFlowJacobian (L := 𝓝 p) β hβ
    (fun z : Paper.ParisiMeasure×(Paper.Overlap×(ℝ×(C(Paper.Overlap,ℝ)×Paper.Overlap))) => z.1)
    p.1 continuous_fst.continuousAt
    (fun z => z.2.1) p.2.1 (continuous_fst.comp continuous_snd).continuousAt
    (fun z => z.2.2.1) p.2.2.1
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
    (fun z => z.2.2.2.1) p.2.2.2.1
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt
    (fun z => z.2.2.2.2) p.2.2.2.2
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt

end QuantitativeFollowup
