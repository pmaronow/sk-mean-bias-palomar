module
public import QuantitativeFollowup.ScalarDynkinFields
public import FourPapersCommon.ParisiGradientL1State
public import FRSB.ParisiGridTopology

@[expose] public section

/-! Genuine weak-measure passage for polynomial Dynkin sources along a
fixed bounded-drift state. The CDF contribution is controlled by its actual
L¹ distance, so atoms do not require pointwise convergence at their levels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped NNReal Topology BoundedContinuousFunction
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem scalarDynkinMoment_sub_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν ρ : Paper.ParisiMeasure) (F : MomentPolynomial) (a r : ℝ) :
    ‖scalarDynkinMoment P X beta ν F a r-scalarDynkinMoment P X beta ρ F a r‖≤
      ‖polynomialJetBCF beta ν F-polynomialJetBCF beta ρ F‖ := by
  unfold scalarDynkinMoment
  rw [←integral_sub (integrable_scalarDynkinField hc beta ν F a r)
    (integrable_scalarDynkinField hc beta ρ F a r)]
  simpa only [scalarDynkinField,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=P)
    (.of_forall fun ω=>norm_polynomialJetField_sub_le beta ν ρ F _ _)

theorem tendsto_scalarDynkinMoment_of_weak {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {L : Filter ι}
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ρ : Paper.ParisiMeasure) (ν : ι→Paper.ParisiMeasure)
    (hν : Tendsto ν L (nhds ρ)) (F : MomentPolynomial) (a r : ℝ) :
    Tendsto (fun i=>scalarDynkinMoment P X beta (ν i) F a r) L
      (nhds (scalarDynkinMoment P X beta ρ F a r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i=>norm_nonneg _)
    (fun i=>scalarDynkinMoment_sub_norm_le hc beta (ν i) ρ F a r)
  simpa only [sub_self,norm_zero,Function.comp_def] using
    (((continuous_polynomialJetBCF beta F).tendsto ρ).comp hν).sub_const
      (polynomialJetBCF beta ρ F) |>.norm

def scalarDynkinJetGap (beta sigma D : ℝ) (ν ρ : Paper.ParisiMeasure)
    (F : MomentPolynomial) : ℝ :=
  beta^2*(‖polynomialJetBCF beta ν (momentDrift0 F)-polynomialJetBCF beta ρ (momentDrift0 F)‖+
    ‖polynomialJetBCF beta ν (dynkinTransportPolynomial F)-polynomialJetBCF beta ρ (dynkinTransportPolynomial F)‖)+
    D*‖polynomialJetBCF beta ν (polynomialSpatialDerivative F)-
      polynomialJetBCF beta ρ (polynomialSpatialDerivative F)‖+
    (|(sigma^2-beta^2)/2|)*‖polynomialJetBCF beta ν
      (polynomialSpatialDerivative (polynomialSpatialDerivative F))-
      polynomialJetBCF beta ρ (polynomialSpatialDerivative (polynomialSpatialDerivative F))‖

theorem scalarDynkinSource_sub_norm_le {Ω : Type*}
    (X d : ℝ≥0→Ω→ℝ) (beta sigma D : ℝ) (hD : 0≤D)
    (hd : ∀r ω,‖d r ω‖≤D) (ν ρ : Paper.ParisiMeasure)
    (F : MomentPolynomial) (a r : ℝ) (ω : Ω) :
    ‖scalarDynkinSource X d beta sigma ν F a r ω-
      scalarDynkinSource X d beta sigma ρ F a r ω‖≤
      scalarDynkinJetGap beta sigma D ν ρ F+
        beta^2*uniformPolynomialMomentBound beta (dynkinTransportPolynomial F)*
          |parisiCDF ν (a+r)-parisiCDF ρ (a+r)| := by
  have hg (G : MomentPolynomial) :
      ‖scalarDynkinField X beta ν G a r ω-scalarDynkinField X beta ρ G a r ω‖≤
        ‖polynomialJetBCF beta ν G-polynomialJetBCF beta ρ G‖ :=
    norm_polynomialJetField_sub_le beta ν ρ G _ _
  have hprod : ‖parisiCDF ν (a+r)*scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω-
      parisiCDF ρ (a+r)*scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω‖≤
      ‖polynomialJetBCF beta ν (dynkinTransportPolynomial F)-polynomialJetBCF beta ρ (dynkinTransportPolynomial F)‖+
      (|parisiCDF ν (a+r)-parisiCDF ρ (a+r)|)*uniformPolynomialMomentBound beta (dynkinTransportPolynomial F) := by
    rw [show parisiCDF ν (a+r)*scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω-
        parisiCDF ρ (a+r)*scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω=
        parisiCDF ν (a+r)*(scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω-
          scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω)+
        (parisiCDF ν (a+r)-parisiCDF ρ (a+r))*
          scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg ν _),Real.norm_eq_abs]
    apply add_le_add
    · exact (mul_le_mul (parisiCDF_le_one ν _) (hg _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · exact mul_le_mul_of_nonneg_left (norm_scalarDynkinField_le X beta ρ _ a r ω) (abs_nonneg _)
  have he : scalarDynkinSource X d beta sigma ν F a r ω-
      scalarDynkinSource X d beta sigma ρ F a r ω=
      beta^2*((scalarDynkinField X beta ν (momentDrift0 F) a r ω-
        scalarDynkinField X beta ρ (momentDrift0 F) a r ω)+
        (parisiCDF ν (a+r)*scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω-
          parisiCDF ρ (a+r)*scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω))+
      d r.toNNReal ω*(scalarDynkinField X beta ν (polynomialSpatialDerivative F) a r ω-
        scalarDynkinField X beta ρ (polynomialSpatialDerivative F) a r ω)+
      ((sigma^2-beta^2)/2)*(scalarDynkinField X beta ν
        (polynomialSpatialDerivative (polynomialSpatialDerivative F)) a r ω-
        scalarDynkinField X beta ρ (polynomialSpatialDerivative (polynomialSpatialDerivative F)) a r ω) := by
    unfold scalarDynkinSource
    ring
  rw [he]
  have hA := mul_le_mul_of_nonneg_left
    ((norm_add_le
      (scalarDynkinField X beta ν (momentDrift0 F) a r ω-
        scalarDynkinField X beta ρ (momentDrift0 F) a r ω)
      (parisiCDF ν (a+r)*scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω-
        parisiCDF ρ (a+r)*scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω)).trans
          (add_le_add (hg _) hprod)) (sq_nonneg beta)
  have hB := mul_le_mul (hd r.toNNReal ω) (hg (polynomialSpatialDerivative F)) (norm_nonneg _) hD
  have hC := mul_le_mul_of_nonneg_left
    (hg (polynomialSpatialDerivative (polynomialSpatialDerivative F)))
    (abs_nonneg ((sigma^2-beta^2)/2))
  have hn := (norm_add_le
    (beta^2*((scalarDynkinField X beta ν (momentDrift0 F) a r ω-
      scalarDynkinField X beta ρ (momentDrift0 F) a r ω)+
      (parisiCDF ν (a+r)*scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω-
        parisiCDF ρ (a+r)*scalarDynkinField X beta ρ (dynkinTransportPolynomial F) a r ω))+
      d r.toNNReal ω*(scalarDynkinField X beta ν (polynomialSpatialDerivative F) a r ω-
        scalarDynkinField X beta ρ (polynomialSpatialDerivative F) a r ω))
    (((sigma^2-beta^2)/2)*(scalarDynkinField X beta ν
      (polynomialSpatialDerivative (polynomialSpatialDerivative F)) a r ω-
      scalarDynkinField X beta ρ (polynomialSpatialDerivative (polynomialSpatialDerivative F)) a r ω))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  simp only [norm_mul,Real.norm_of_nonneg (sq_nonneg beta),Real.norm_eq_abs] at hn
  rw [Real.norm_eq_abs] at hA hB
  apply (hn.trans (add_le_add (add_le_add hA hB) hC)).trans_eq
  dsimp only [scalarDynkinJetGap]
  ring

theorem scalarDynkinSource_integral_sub_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta D : ℝ) (hD : 0≤D) (hd : ∀r ω,‖d r ω‖≤D)
    (ν ρ : Paper.ParisiMeasure) (F : MomentPolynomial)
    (a H : ℝ) (ha : a∈Icc (0 : ℝ) 1) (hH : H∈Icc (0 : ℝ) (1-a)) :
    ‖(∫r in (0 : ℝ)..H,∫ω,scalarDynkinSource X d beta sigma ν F a r ω ∂P)-
      (∫r in (0 : ℝ)..H,∫ω,scalarDynkinSource X d beta sigma ρ F a r ω ∂P)‖≤
      scalarDynkinJetGap beta sigma D ν ρ F*H+
        beta^2*uniformPolynomialMomentBound beta (dynkinTransportPolynomial F)*Paper.parisiCDFDistance ν ρ := by
  let E := scalarDynkinJetGap beta sigma D ν ρ F
  let K := beta^2*uniformPolynomialMomentBound beta (dynkinTransportPolynomial F)
  have hK : 0≤K := mul_nonneg (sq_nonneg beta) (uniformPolynomialMomentBound_nonneg beta _)
  have hm (τ : Paper.ParisiMeasure) : Monotone (fun r : ℝ=>parisiCDF τ (a+r)) :=
    fun _ _ h=>parisiCDF_monotone τ (by linarith only [h])
  have hCDFi : IntervalIntegrable (fun r : ℝ=>|parisiCDF ν (a+r)-parisiCDF ρ (a+r)|) volume 0 H := by
    simpa only [Real.norm_eq_abs] using ((hm ν).intervalIntegrable.sub (hm ρ).intervalIntegrable).norm
  have hEi : IntervalIntegrable (fun r=>E+K*|parisiCDF ν (a+r)-parisiCDF ρ (a+r)|) volume 0 H :=
    intervalIntegrable_const.add (hCDFi.const_mul K)
  rw [←intervalIntegral.integral_sub
    (scalarDynkinSource_expected_intervalIntegrable hc beta ν F a 0 H)
    (scalarDynkinSource_expected_intervalIntegrable hc beta ρ F a 0 H)]
  have hs (r : ℝ) : ‖(∫ω,scalarDynkinSource X d beta sigma ν F a r ω ∂P)-
      (∫ω,scalarDynkinSource X d beta sigma ρ F a r ω ∂P)‖≤
      E+K*|parisiCDF ν (a+r)-parisiCDF ρ (a+r)| := by
    have hint (τ : Paper.ParisiMeasure) : Integrable (scalarDynkinSource X d beta sigma τ F a r) P :=
      (integrable_const (scalarDynkinSourceBound beta sigma D F)).mono'
        ((measurable_scalarDynkinSource hc beta τ F a).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (.of_forall (norm_scalarDynkinSource_le X d beta sigma D hD hd τ F a r))
    rw [←integral_sub (hint ν) (hint ρ)]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=P)
      (.of_forall (scalarDynkinSource_sub_norm_le X d beta sigma D hD hd ν ρ F a r))
  apply (intervalIntegral.norm_integral_le_of_norm_le hH.1
    (.of_forall fun r _=>hs r) hEi).trans
  rw [intervalIntegral.integral_add intervalIntegrable_const (hCDFi.const_mul K),
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have hCDF := FourPapersCommon.integral_restart_CDF_difference_le ν ρ a H ha hH
  simpa only [E,K,FourPapersCommon.parisiCDFDistance,Paper.parisiCDFDistance,Real.norm_eq_abs,mul_comm]
    using add_le_add (le_refl (E*H)) (mul_le_mul_of_nonneg_left hCDF hK)

theorem tendsto_scalarDynkinSource_integral_of_weak {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {L : Filter ι} [L.IsCountablyGenerated]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ρ : Paper.ParisiMeasure) (ν : ι→Paper.ParisiMeasure)
    (hν : Tendsto ν L (nhds ρ)) (F : MomentPolynomial)
    (a H : ℝ) (ha : a∈Icc (0 : ℝ) 1) (hH : H∈Icc (0 : ℝ) (1-a)) :
    Tendsto (fun i=>∫r in (0 : ℝ)..H,∫ω,scalarDynkinSource X d beta sigma (ν i) F a r ω ∂P)
      L (nhds (∫r in (0 : ℝ)..H,∫ω,scalarDynkinSource X d beta sigma ρ F a r ω ∂P)) := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hj (G : MomentPolynomial) :
      Tendsto (fun i=>‖polynomialJetBCF beta (ν i) G-polynomialJetBCF beta ρ G‖) L (nhds 0) := by
    simpa only [sub_self,norm_zero,Function.comp_def] using
      (((continuous_polynomialJetBCF beta G).tendsto ρ).comp hν).sub_const
        (polynomialJetBCF beta ρ G) |>.norm
  have he : Tendsto (fun i=>scalarDynkinJetGap beta sigma D (ν i) ρ F) L (nhds 0) := by
    simpa only [scalarDynkinJetGap,mul_zero,zero_add] using
      (((hj _).add (hj _)).const_mul (beta^2)).add ((hj _).const_mul (D : ℝ)) |>.add
        ((hj _).const_mul (|(sigma^2-beta^2)/2|))
  have hCDF := tendsto_parisiCDFDistance_of_tendsto hν
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i=>norm_nonneg _)
    (fun i=>scalarDynkinSource_integral_sub_norm_le hc beta D D.coe_nonneg hD (ν i) ρ F a H ha hH)
  simpa only [mul_zero,zero_mul,zero_add] using (he.mul_const H).add
    (hCDF.const_mul (beta^2*uniformPolynomialMomentBound beta (dynkinTransportPolynomial F)))

end QuantitativeFollowup
