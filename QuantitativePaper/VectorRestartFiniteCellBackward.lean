module
public import QuantitativePaper.VectorRestartState
public import QuantitativePaper.VectorJointFixedParameter
public import QuantitativePaper.VectorFiniteCellBackward
public import QuantitativePaper.VectorDyadicGridJetAgreement

@[expose] public section

/-! Actual fixed-disorder restarted diffusions have the true backward Gaussian
response identity on every remaining finite-grid cell, including a partial
first cell and repeated partition nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorRestart_grid_cell_drift (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (r : ℝ≥0)
    (hr : (q:ℝ)+(r:ℝ)∈Ioo
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveDrift
      (vectorRestartDriftData (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht q p)
      (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q) r sample=
      ((1-t)*β^2) •
        ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m i • gradient
          (vectorColeHopfStep (((1-t)*β^2)*
            ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)-((q:ℝ)+r)))
            ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m i)
            (vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
              β t p (vectorDyadicIndex j+2-i)))
          (vectorRestartState (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht q p x r sample)) := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let ν:=Paper.parisiGridMeasure μ (vectorDyadicIndex j)
  have hr1 : (q:ℝ)+(r:ℝ)≤1:=hr.2.le.trans (s.q_le_one (by omega))
  have hrr : r≤vectorRestartHorizon q:=by
    rw [←NNReal.coe_le_coe,vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
    linarith
  rw [vectorAdditiveDrift,if_pos hrr]
  change vectorMeasureDrift ν β t ht ((q:ℝ).toNNReal+r) p
    (vectorRestartState ν β t ht q p x r sample)=_
  unfold vectorMeasureDrift
  rw [NNReal.coe_add,Real.coe_toNNReal (q:ℝ) q.property.1,
    vectorMeasureGradient_grid_eq_finite μ j β t ht]
  have hCDF : Paper.parisiCDF ν ((q:ℝ)+r)=s.m i:=by
    rw [show ν=Paper.parisiSchemeMeasure s from (FRSB.parisiSchemeMeasure_grid_eq μ (vectorDyadicIndex j)).symm]
    exact Paper.parisiCDF_scheme_cell s hi ⟨hr.1.le,hr.2⟩
  rw [hCDF]
  unfold vectorFiniteTailGradient
  rw [projIcc_of_mem _ ⟨add_nonneg q.property.1 r.coe_nonneg,hr1⟩,
    vectorTailRecursion_eq_finiteCell s β t ((q:ℝ)+r) p i hi ⟨hr.1.le,hr.2.le⟩]
  simp only [smul_smul]
  rfl

theorem vectorRestart_grid_cell_backward_identity (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (v : ℝ) (hv : v∈Icc
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (hqv : (q:ℝ)≤v) {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (v-(q:ℝ)).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(G (p,
        vectorRestartState (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q p x
          (((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)-(q:ℝ)).toNNReal) sample)-
      vectorStepResponse (((1-t)*β^2)*
        ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)-v))
        ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m i)
        (vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
          β t p (vectorDyadicIndex j+2-i)) (fun y=>G (p,y))
        (vectorRestartState (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q p x
          ((v-(q:ℝ)).toNNReal) sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(G (p,
        vectorRestartState (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q p x
          (((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)-(q:ℝ)).toNNReal) sample)-
      vectorStepResponse (((1-t)*β^2)*
        ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)-v))
        ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m i)
        (vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
          β t p (vectorDyadicIndex j+2-i)) (fun y=>G (p,y))
        (vectorRestartState (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q p x
          ((v-(q:ℝ)).toNNReal) sample)) ∂vectorDisorderBrownianMeasure n)=0 := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let ν:=Paper.parisiGridMeasure μ (vectorDyadicIndex j)
  let a:ℝ≥0:=(v-(q:ℝ)).toNNReal
  let Q:ℝ≥0:=(s.q (i+1)-(q:ℝ)).toNNReal
  have ha : (a:ℝ)=v-(q:ℝ):=Real.coe_toNNReal _ (sub_nonneg.mpr hqv)
  have hQ : (Q:ℝ)=s.q (i+1)-(q:ℝ):=Real.coe_toNNReal _
    (sub_nonneg.mpr (hqv.trans hv.2))
  have haQ : a≤Q:=by rw [←NNReal.coe_le_coe,ha,hQ];linarith [hv.2]
  have hcpos : 0<(1-t)*β^2:=mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  let data:=(vectorRecursionJointResponseData s β t (vectorDyadicIndex j+2-i) hG).fieldData p
  have hh:=vector_jointResponse_endpoint_martingale_past data.fixedParameter
    (vectorItoCharacteristics_vectorRestartState ν β t ht.le q p x)
    (Real.sq_sqrt hcpos.le) hcpos a Q haQ
    (fun r hr sample=>by
      have hphysical : (q:ℝ)+(r:ℝ)∈Ioo (s.q i) (s.q (i+1)):=by
        have hleft : (a:ℝ)<r:=hr.1
        have hright : (r:ℝ)<Q:=hr.2
        rw [ha] at hleft
        rw [hQ] at hright
        constructor <;> linarith [hv.1]
      have hd:=vectorRestart_grid_cell_drift μ j β t ht.le q p x i hi r hphysical sample
      have hvar : ((1-t)*β^2)*((Q:ℝ)-r)=
          ((1-t)*β^2)*(s.q (i+1)-((q:ℝ)+r)):=by rw [hQ];ring
      rw [hvar]
      exact hd)
    Z hZ C hC
  have hvariance : ((1-t)*β^2)*((Q:ℝ)-(a:ℝ))=
      ((1-t)*β^2)*(s.q (i+1)-v):=by rw [ha,hQ];ring
  simpa only [vectorJointResponse,hvariance,data,VectorResponseTestData.fixedParameter] using hh

end QuantitativePaper
