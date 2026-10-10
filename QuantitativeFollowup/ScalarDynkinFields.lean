module
public import FRSB.PolynomialMomentSources

@[expose] public section

/-! Actual polynomial jet tests along arbitrary bounded-drift Itô states.
The state and the tested Parisi measure can differ; the source includes
their true drift mismatch and the true variance mismatch. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def dynkinTransportPolynomial (F : MomentPolynomial) : MomentPolynomial :=
  momentDrift1 F-MvPolynomial.X 0*polynomialSpatialDerivative F

def scalarDynkinField {Ω : Type*} (X : ℝ≥0→Ω→ℝ) (beta : ℝ)
    (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a r : ℝ) (ω : Ω) : ℝ :=
  polynomialJetField beta ν F (a+r) (X r.toNNReal ω)

def scalarDynkinMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0→Ω→ℝ) (beta : ℝ) (ν : Paper.ParisiMeasure)
    (F : MomentPolynomial) (a r : ℝ) : ℝ :=
  ∫ω,scalarDynkinField X beta ν F a r ω ∂P

def scalarDynkinSource {Ω : Type*} (X d : ℝ≥0→Ω→ℝ) (beta sigma : ℝ)
    (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a r : ℝ) (ω : Ω) : ℝ :=
  beta^2*(scalarDynkinField X beta ν (momentDrift0 F) a r ω+
    parisiCDF ν (a+r)*scalarDynkinField X beta ν (dynkinTransportPolynomial F) a r ω)+
    d r.toNNReal ω*scalarDynkinField X beta ν (polynomialSpatialDerivative F) a r ω+
    ((sigma^2-beta^2)/2)*scalarDynkinField X beta ν
      (polynomialSpatialDerivative (polynomialSpatialDerivative F)) a r ω

theorem measurable_scalarDynkinField {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a : ℝ) :
    Measurable (Function.uncurry (scalarDynkinField X beta ν F a)) := by
  have hX : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable (u:=X) hc.continuous_state
      (fun r=>((hc.adapted_state r).mono (V.le r)).measurable)
  have hXR : Measurable (fun p : ℝ×Ω=>X p.1.toNNReal p.2) :=
    hX.comp (measurable_real_toNNReal.prodMap measurable_id)
  change Measurable (fun p : ℝ×Ω=>polynomialJetField beta ν F (a+p.1) (X p.1.toNNReal p.2))
  have harg : Measurable (fun p : ℝ×Ω=>(a+p.1,X p.1.toNNReal p.2)) :=
    (measurable_const.add measurable_fst).prodMk hXR
  convert! (continuous_polynomialJetField beta ν F).measurable.comp harg using 1

theorem norm_scalarDynkinField_le {Ω : Type*} (X : ℝ≥0→Ω→ℝ)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a r : ℝ) (ω : Ω) :
    ‖scalarDynkinField X beta ν F a r ω‖≤uniformPolynomialMomentBound beta F :=
  norm_polynomialJetField_le_uniform beta ν F _ _

theorem integrable_scalarDynkinField {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a r : ℝ) :
    Integrable (scalarDynkinField X beta ν F a r) P :=
  (integrable_const (uniformPolynomialMomentBound beta F)).mono'
    ((measurable_scalarDynkinField hc beta ν F a).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (.of_forall fun ω=>norm_scalarDynkinField_le X beta ν F a r ω)

theorem continuous_scalarDynkinMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a : ℝ) :
    Continuous (scalarDynkinMoment P X beta ν F a) := by
  unfold scalarDynkinMoment
  apply continuous_of_dominated (μ:=P) (bound:=fun _=>uniformPolynomialMomentBound beta F)
  · intro r
    exact (integrable_scalarDynkinField hc beta ν F a r).aestronglyMeasurable
  · intro r
    exact .of_forall fun ω=>norm_scalarDynkinField_le X beta ν F a r ω
  · exact integrable_const _
  · apply ae_of_all
    intro ω
    have hpath : Continuous (fun r : ℝ=>X r.toNNReal ω) :=
      (hc.continuous_state ω).comp continuous_real_toNNReal
    change Continuous (fun r : ℝ=>polynomialJetField beta ν F (a+r) (X r.toNNReal ω))
    have harg : Continuous (fun r : ℝ=>(a+r,X r.toNNReal ω)) :=
      (continuous_const.add continuous_id).prodMk hpath
    convert! (continuous_polynomialJetField beta ν F).comp harg using 1

theorem measurable_scalarDynkinSource {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a : ℝ) :
    Measurable (Function.uncurry (scalarDynkinSource X d beta sigma ν F a)) := by
  have hdm : Measurable (fun p : ℝ×Ω=>d p.1.toNNReal p.2) :=
    hc.measurable_drift.comp (measurable_real_toNNReal.prodMap measurable_id)
  exact (measurable_const.mul ((measurable_scalarDynkinField hc beta ν _ a).add
    (((parisiCDF_measurable ν).comp (measurable_const.add measurable_fst)).mul
      (measurable_scalarDynkinField hc beta ν _ a)))).add
      (hdm.mul (measurable_scalarDynkinField hc beta ν _ a)) |>.add
        (measurable_const.mul (measurable_scalarDynkinField hc beta ν _ a))

def scalarDynkinSourceBound (beta sigma D : ℝ) (F : MomentPolynomial) : ℝ :=
  beta^2*(uniformPolynomialMomentBound beta (momentDrift0 F)+
    uniformPolynomialMomentBound beta (dynkinTransportPolynomial F))+
    D*uniformPolynomialMomentBound beta (polynomialSpatialDerivative F)+
    (|(sigma^2-beta^2)/2|)*uniformPolynomialMomentBound beta
      (polynomialSpatialDerivative (polynomialSpatialDerivative F))

theorem norm_scalarDynkinSource_le {Ω : Type*}
    (X d : ℝ≥0→Ω→ℝ) (beta sigma D : ℝ) (hD : 0≤D)
    (hd : ∀r ω,‖d r ω‖≤D) (ν : Paper.ParisiMeasure)
    (F : MomentPolynomial) (a r : ℝ) (ω : Ω) :
    ‖scalarDynkinSource X d beta sigma ν F a r ω‖ ≤ scalarDynkinSourceBound beta sigma D F := by
  unfold scalarDynkinSource scalarDynkinSourceBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_mul,Real.norm_of_nonneg (sq_nonneg beta)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg beta)
      apply (norm_add_le _ _).trans
      apply add_le_add (norm_scalarDynkinField_le X beta ν _ a r ω)
      rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg ν _)]
      exact (mul_le_mul (parisiCDF_le_one ν _) (norm_scalarDynkinField_le X beta ν _ a r ω)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [norm_mul]
      exact mul_le_mul (hd _ ω) (norm_scalarDynkinField_le X beta ν _ a r ω)
        (norm_nonneg _) hD
  · rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_scalarDynkinField_le X beta ν _ a r ω) (abs_nonneg _)

theorem scalarDynkinSource_fubini {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a l r : ℝ) (hlr : l≤r) :
    Integrable (fun ω=>∫s in l..r,scalarDynkinSource X d beta sigma ν F a s ω) P ∧
      (∫ω,(∫s in l..r,scalarDynkinSource X d beta sigma ν F a s ω) ∂P)=
        ∫s in l..r,∫ω,scalarDynkinSource X d beta sigma ν F a s ω ∂P := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  exact bounded_source_fubini P _ (measurable_scalarDynkinSource hc beta ν F a)
    (scalarDynkinSourceBound beta sigma D F)
    (norm_scalarDynkinSource_le X d beta sigma D D.coe_nonneg hD ν F a) l r hlr

theorem scalarDynkinSource_expected_intervalIntegrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (F : MomentPolynomial) (a l r : ℝ) :
    IntervalIntegrable (fun s=>∫ω,scalarDynkinSource X d beta sigma ν F a s ω ∂P) volume l r := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hm := (measurable_scalarDynkinSource hc beta ν F a).stronglyMeasurable.integral_prod_right' (ν:=P)
  apply (intervalIntegrable_const (c:=scalarDynkinSourceBound beta sigma D F)).mono_fun'
    hm.aestronglyMeasurable
  exact .of_forall fun s=>by
    have hh := norm_integral_le_of_norm_le_const
      (μ:=P) (.of_forall (norm_scalarDynkinSource_le X d beta sigma D D.coe_nonneg hD ν F a s))
    simp only [probReal_univ,mul_one] at hh
    exact hh

end QuantitativeFollowup
