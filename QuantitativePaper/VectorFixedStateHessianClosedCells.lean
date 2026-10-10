module
public import QuantitativePaper.VectorFixedStateHessianExpectations
public import QuantitativePaper.VectorFixedStateGradientExpectations
public import FRSB.ClosedIntervalBounds

@[expose] public section

/-! Both actual cell endpoints and the depth-independent approximation
error for finite Hessian expectations on the fixed μ diffusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorCellHessianError (μ : Paper.ParisiMeasure) (β t m D r : ℝ) : ℝ :=
  ((1-t)*β^2)*vectorSpatialJetBound n 3*(Real.sqrt n*|Paper.parisiCDF μ r-m|+D)

theorem vectorCellHessianError_intervalIntegrable (μ : Paper.ParisiMeasure)
    (β t m D a b : ℝ) : IntervalIntegrable (vectorCellHessianError (n:=n) μ β t m D) volume a b :=
  (((((Paper.parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm.const_mul
    (Real.sqrt n)).add intervalIntegrable_const).const_mul (((1-t)*β^2)*vectorSpatialJetBound n 3)

theorem vectorFixedState_hessian_closed (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (hq : s.q i<s.q (i+1)) {a b : ℝ}
    (ha : s.q i≤a) (hab : a≤b) (hb : b≤ s.q (i+1)) :
    vectorFixedStateCellHessianMean s μ β t outer ht.le i l b-
      vectorFixedStateCellHessianMean s μ β t outer ht.le i l a=
      ∫r in a..b,vectorFixedStateCellHessianSourceMean s μ β t outer ht.le i l r := by
  have hbound : ‖vectorFixedStateCellHessianMean s μ β t outer ht.le i l b-
      vectorFixedStateCellHessianMean s μ β t outer ht.le i l a-
      ∫r in a..b,vectorFixedStateCellHessianSourceMean s μ β t outer ht.le i l r‖≤0 := by
    have hh:=FRSB.closed_interval_increment_bound
      (vectorFixedStateCellHessianMean s μ β t outer ht.le i l)
      (vectorFixedStateCellHessianSourceMean s μ β t outer ht.le i l) (fun _=>0)
      (continuous_vectorFixedStateCellHessianMean s μ β t outer ht.le i hi l)
      (vectorFixedStateCellHessianSourceMean_intervalIntegrable s μ β t outer ht.le i hi l)
      (fun _ _=>intervalIntegrable_const) hq
      (fun x y hx hxy hy=>by
        have hx0:0≤x:=(s.q_nonneg (by omega)).trans hx.le
        have hy0:0≤y:=hx0.trans hxy
        let xN:ℝ≥0:=⟨x,hx0⟩
        let yN:ℝ≥0:=⟨y,hy0⟩
        have he:=vectorFixedState_hessian_tilted_cropped s μ β t outer hβ ht i hi l
          xN yN (NNReal.coe_le_coe.mp hxy) hy
        change vectorFixedStateCellHessianMean s μ β t outer ht.le i l y-
          vectorFixedStateCellHessianMean s μ β t outer ht.le i l x=
          ∫r in x..y,vectorFixedStateCellHessianSourceMean s μ β t outer ht.le i l r at he
        rw [he]
        simp only [sub_self,norm_zero,intervalIntegral.integral_zero,le_refl]) ha hab hb
    simpa only [intervalIntegral.integral_zero] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

theorem vectorFixedStateCellHessianSourceMean_error (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (D : ℝ) (hD : 0≤D)
    (hgrad : ∀q p x,‖vectorMeasureGradient (n:=n) μ β t q p x-vectorFiniteTailGradient s β t q p x‖≤D)
    {r : ℝ} (hr : r∈Icc (s.q i) (s.q (i+1))) :
    ‖vectorFixedStateCellHessianSourceMean s μ β t outer ht i l r-
      (-(((1-t)*β^2)*(s.m i)))*vectorFixedStateCellEnergyMean s μ β t outer ht i l r‖≤
      vectorCellHessianError (n:=n) μ β t (s.m i) D r := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t outer
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  have hmap:Measurable (fun sample : VectorDisorderBrownianSample n=>(r.toNNReal,sample)):=
    measurable_const.prodMk measurable_id
  have hSm:=(measurable_uncurry_vectorFixedStateCellHessianSource s μ β t ht i l).comp hmap
  dsimp only [Function.comp_def] at hSm
  have hS : Integrable (fun sample=>vectorFixedStateCellHessianSource s μ β t ht i r.toNNReal sample l) P :=
    (integrable_const (((1-t)*β^2)*(2*vectorFiniteCellHessianDerivativeBound s β t i l*Real.sqrt n+
      (n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2))).mono'
      hSm.aestronglyMeasurable
      (.of_forall (norm_vectorFixedStateCellHessianSource_le s μ β t ht i hi l _))
  have hE : Integrable (fun sample=>vectorFixedStateCellGradientEnergy s μ β t ht i r.toNNReal sample l) P :=
    (integrable_const ((n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)).mono'
      (measurable_vectorFixedStateCellGradientEnergy s μ β t ht i l _).aestronglyMeasurable
      (.of_forall fun sample=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l _ sample).1]
        exact (vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l _ sample).2)
  unfold vectorFixedStateCellHessianSourceMean vectorFixedStateCellEnergyMean
  rw [←integral_const_mul,←integral_sub hS (hE.const_mul _)]
  have hr01 : r∈Icc (0:ℝ) 1:=⟨(s.q_nonneg (by omega)).trans hr.1,hr.2.trans (s.q_le_one (by omega))⟩
  let q:Paper.Overlap:=⟨r,hr01⟩
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=P)
    (.of_forall fun sample=>by
      simpa only [Real.norm_eq_abs,vectorCellHessianError,neg_mul,sub_neg_eq_add] using
        vectorFixedStateCellHessianSource_error s μ β t ht i hi D hD hgrad q hr sample l)

theorem vectorFixedState_hessian_cell_bound (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (hq : s.q i<s.q (i+1)) {a b : ℝ}
    (ha : s.q i≤a) (hab : a≤b) (hb : b≤ s.q (i+1))
    (D : ℝ) (hD : 0≤D)
    (hgrad : ∀q p x,‖vectorMeasureGradient (n:=n) μ β t q p x-vectorFiniteTailGradient s β t q p x‖≤D) :
    ‖vectorFixedStateCellHessianMean s μ β t outer ht.le i l b-
      vectorFixedStateCellHessianMean s μ β t outer ht.le i l a-
      ∫r in a..b,(-(((1-t)*β^2)*(s.m i)))*vectorFixedStateCellEnergyMean s μ β t outer ht.le i l r‖≤
      ∫r in a..b,vectorCellHessianError (n:=n) μ β t (s.m i) D r := by
  rw [vectorFixedState_hessian_closed s μ β t outer hβ ht i hi l hq ha hab hb]
  rw [←intervalIntegral.integral_sub
    (vectorFixedStateCellHessianSourceMean_intervalIntegrable s μ β t outer ht.le i hi l a b)
    ((continuous_vectorFixedStateCellEnergyMean s μ β t outer ht.le i l).intervalIntegrable a b |>.const_mul _)]
  apply intervalIntegral.norm_integral_le_of_norm_le hab _
    (vectorCellHessianError_intervalIntegrable μ β t (s.m i) D a b)
  filter_upwards with r
  intro hr
  exact vectorFixedStateCellHessianSourceMean_error s μ β t outer ht.le i hi l D hD hgrad
    ⟨ha.trans hr.1.le,hr.2.trans hb⟩

end QuantitativePaper
