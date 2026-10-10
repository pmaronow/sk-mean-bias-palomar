module
public import QuantitativeFollowup.ScalarDynkinFields
public import FRSB.InteriorTimeCap
public import FRSB.ClosedIntervalBounds

@[expose] public section

/-! True finite-cell Dynkin identities for a polynomial of a tested Parisi
solution along an arbitrary bounded-drift state, with a fresh clock offset. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem scalarDynkin_finite_cell_cropped {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (hb : beta≠0) {k : ℕ} (s : RSBScheme k) {p : ℕ}
    (hp : p≤k+1) (hq : s.q p<s.q (p+1)) (F : MomentPolynomial)
    (a : ℝ) (l r : ℝ≥0) (hl : s.q p<a+l) (hlr : l≤r) (hr : a+r<s.q (p+1)) :
    scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a r-
      scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a l=
      ∫t in (l : ℝ)..(r : ℝ),∫ω,
        scalarDynkinSource X d beta sigma (parisiSchemeMeasure s) F a t ω ∂P := by
  let ν := parisiSchemeMeasure s
  let u := fun t x=>polynomialJetField beta ν F (a+t) x
  let ut := fun t x=>beta^2*polynomialJetField beta ν (polynomialTimeDerivative (s.m p) F) (a+t) x
  let ux := fun t x=>polynomialJetField beta ν (polynomialSpatialDerivative F) (a+t) x
  let uxx := fun t x=>polynomialJetField beta ν
    (polynomialSpatialDerivative (polynomialSpatialDerivative F)) (a+t) x
  let f := interiorCappedTest u (s.q p-a) l r (s.q (p+1)-a)
  have hl' : s.q p-a<(l : ℝ) := by linarith
  have hr' : (r : ℝ)<s.q (p+1)-a := by linarith
  have hut : ∀t∈Ioo (s.q p-a) (s.q (p+1)-a),∀x,
      HasDerivAt (fun t=>u t x) (ut t x) t := by
    intro t ht x
    have hd := (hasDerivAt_finiteCell_polynomialJetField_time beta hb s hp hq F
      (t:=a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩ x).comp t
        ((hasDerivAt_const t a).add (hasDerivAt_id t))
    simpa only [u,ut,Function.comp_def,Pi.add_apply,id_eq,zero_add,mul_one] using hd
  have hux : ∀t x,HasDerivAt (u t) (ux t x) x :=
    fun t x=>hasDerivAt_polynomialJetField_spatial beta ν F (a+t) x
  have huxx : ∀t x,HasDerivAt (ux t) (uxx t x) x :=
    fun t x=>hasDerivAt_polynomialJetField_spatial beta ν _ (a+t) x
  have hucont (G : MomentPolynomial) :
      Continuous (fun z : ℝ×ℝ=>polynomialJetField beta ν G (a+z.1) z.2) :=
      by
    have harg : Continuous (fun z : ℝ×ℝ=>(a+z.1,z.2)) :=
      (continuous_const.add continuous_fst).prodMk continuous_snd
    convert! (continuous_polynomialJetField beta ν G).comp harg using 1
  obtain ⟨hfc,hft,hfs,hfdt,hfx,hfxx⟩ := interiorCappedTest_regular u ut ux uxx
    (s.q p-a) l r (s.q (p+1)-a) hl' (NNReal.coe_le_coe.mpr hlr) hr'
    (hucont F) (continuous_const.mul (hucont _)) (hucont _) (hucont _)
    hut hux huxx (fun t=>(contDiff_polynomialJetField_spatial beta ν F (a+t)).of_le (by simp))
  let K := uniformPolynomialMomentBound beta (polynomialSpatialDerivative F)
  have hK : 0≤K := uniformPolynomialMomentBound_nonneg beta _
  have hfxB : ∀t x,‖itoSpaceDerivative f t x‖≤K := by
    intro t x
    rw [interiorCappedTest_spaceDerivative u ux hux]
    exact norm_polynomialJetField_le_uniform beta ν _ _ x
  have hgen : ∀ω,∀t∈Icc (l : ℝ) (r : ℝ),
      ‖hjbGenerator X d sigma f t ω-
        scalarDynkinSource X d beta sigma ν F a t ω‖≤0 := by
    intro ω t ht
    have ht' : a+t∈Ico (s.q p) (s.q (p+1)) :=
      ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hCDF : parisiCDF ν (a+t)=s.m p := parisiCDF_scheme_cell s hp ht'
    have hid := polynomialJetField_generator_identity beta ν (s.m p) F (a+t) (X t.toNNReal ω)
    have he : hjbGenerator X d sigma f t ω=
        scalarDynkinSource X d beta sigma ν F a t ω := by
      unfold hjbGenerator
      rw [interiorCappedTest_timeDerivative u ut (s.q p-a) l r (s.q (p+1)-a) hl'
        (NNReal.coe_le_coe.mpr hlr) hr' hut,
        interiorCappedTest_spaceDerivative u ux hux,
        interiorCappedTest_spaceSecondDerivative u ux uxx hux huxx,
        interiorTimeCap_eq _ _ _ _ _ ht,interiorTimeCapD_eq _ _ _ _ _ ht,mul_one]
      dsimp only [u,ut,ux,uxx,scalarDynkinSource,scalarDynkinField]
      rw [hCDF]
      simp only [polynomialJetField,dynkinTransportPolynomial,map_sub,map_mul,MvPolynomial.eval_X] at hid ⊢
      linear_combination hid
    rw [he,sub_self,norm_zero]
  have hfi (t : ℝ≥0) : Integrable (fun ω=>f t (X t ω)) P := by
    have hmeas : Measurable (X t) := ((hc.adapted_state t).mono (V.le t)).measurable
    exact (integrable_const (uniformPolynomialMomentBound beta F)).mono'
      (hfc.measurable.comp (measurable_const.prodMk hmeas)).aestronglyMeasurable
      (.of_forall fun ω=>norm_polynomialJetField_le_uniform beta ν F _ _)
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hh := ito_expectation_source_error hc f hfc hft hfs hfdt hfx hfxx l r hlr
    ⟨K,hK⟩ (fun t _ x=>hfxB t x) (scalarDynkinSource X d beta sigma ν F a)
    (measurable_scalarDynkinSource hc beta ν F a) (scalarDynkinSourceBound beta sigma D F)
    (norm_scalarDynkinSource_le X d beta sigma D D.coe_nonneg hD ν F a)
    (fun _=>0) intervalIntegrable_const hgen (hfi l) (hfi r)
  have heval (t : ℝ≥0) (ht : (t : ℝ)∈Icc (l : ℝ) (r : ℝ)) :
      (∫ω,f t (X t ω) ∂P)=scalarDynkinMoment P X beta ν F a t := by
    unfold f interiorCappedTest scalarDynkinMoment scalarDynkinField
    rw [interiorTimeCap_eq _ _ _ _ _ ht]
    simp only [Real.toNNReal_coe]
    rfl
  rw [heval r ⟨NNReal.coe_le_coe.mpr hlr,le_rfl⟩,
    heval l ⟨le_rfl,NNReal.coe_le_coe.mpr hlr⟩,intervalIntegral.integral_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem scalarDynkin_finite_cell_closed {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (hb : beta≠0) {k : ℕ} (s : RSBScheme k) {p : ℕ}
    (hp : p≤k+1) (hq : s.q p<s.q (p+1)) (F : MomentPolynomial)
    (a l r : ℝ) (hl0 : 0≤l) (hl : s.q p≤a+l) (hlr : l≤r) (hr : a+r ≤ s.q (p+1)) :
    scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a r-
      scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a l=
      ∫t in l..r,∫ω,scalarDynkinSource X d beta sigma (parisiSchemeMeasure s) F a t ω ∂P := by
  by_cases hlr' : l=r
  · subst r
    simp
  have hlrlt : l<r := lt_of_le_of_ne hlr hlr'
  have hbound := closed_interval_increment_bound
    (scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a)
    (fun t=>∫ω,scalarDynkinSource X d beta sigma (parisiSchemeMeasure s) F a t ω ∂P)
    (fun _=>0) (continuous_scalarDynkinMoment hc beta (parisiSchemeMeasure s) F a)
    (scalarDynkinSource_expected_intervalIntegrable hc beta (parisiSchemeMeasure s) F a)
    (fun _ _=>intervalIntegrable_const) hlrlt
    (fun x y hx hxy hy=>by
      have hx0 : 0≤x := hl0.trans hx.le
      have hy0 : 0≤y := hx0.trans hxy
      let xN : ℝ≥0 := ⟨x,hx0⟩
      let yN : ℝ≥0 := ⟨y,hy0⟩
      have hh := scalarDynkin_finite_cell_cropped hc beta hb s hp hq F a
        xN yN (by change s.q p<a+x;linarith) (by exact_mod_cast hxy)
          (by change a+y<s.q (p+1);linarith)
      change scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a y-
        scalarDynkinMoment P X beta (parisiSchemeMeasure s) F a x=
          ∫t in x..y,∫ω,scalarDynkinSource X d beta sigma (parisiSchemeMeasure s) F a t ω ∂P at hh
      rw [hh,sub_self,norm_zero,intervalIntegral.integral_zero])
    (l:=l) (r:=r) le_rfl hlr le_rfl
  rw [intervalIntegral.integral_zero] at hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

end QuantitativeFollowup
