module
public import QuantitativeFollowup.ReflectedFunctionalRegularization
public import QuantitativeFollowup.PartialReflectedRegularization
public import QuantitativeFollowup.LowerReflectedTaylor

@[expose] public section

/-! Actual partial regularization cost. Only free mass below T moves;
the prescribed root and untouched upper free mass cancel exactly. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem integral_lowerReflectedMeasure_potential (η : Measure Paper.Overlap) [IsFiniteMeasure η]
    (h : ℝ) (G : ℝ→ℝ) (hG : Continuous G) :
    (∫q : Paper.Overlap,G q∂lowerReflectedMeasure η h)=
      ∫q : Paper.Overlap,(∫u,G (lowerReflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h)∂η := by
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hi : Integrable (fun p : Paper.Overlap×ℝ=>G (lowerReflectedOverlap p:ℝ))
      (η.prod (symmetricUniformLaw h)):=
    (integrable_const K).mono'
      (hG.measurable.comp (measurable_subtype_coe.comp measurable_lowerReflectedOverlap)).aestronglyMeasurable
      (.of_forall fun p=>hK _ (lowerReflectedOverlap p).property)
  rw [lowerReflectedMeasure,integral_map_of_stronglyMeasurable (f:=fun q : Paper.Overlap=>G q)
    measurable_lowerReflectedOverlap (hG.comp continuous_subtype_val).stronglyMeasurable,integral_prod _ hi]

theorem partial_reflected_potential_increment_le (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T))
    (G : ℝ→ℝ) (hG : Continuous G)
    (hcost : ∀q∈Ico (0:ℝ) T,(∫u,G |q+u|∂symmetricUniformLaw h)-G q≤h^2/6) :
    (∫q : Paper.Overlap,G q∂(partialReflectedParisiMeasure μ s T h hs hh.1:Measure Paper.Overlap))-
      (∫q : Paper.Overlap,G q∂(μ:Measure Paper.Overlap))≤
      (parisiFreeMeasure μ s).real (overlapBelow T)*h^2/6 := by
  let η:=parisiFreeMeasure μ s
  let ηlo:=η.restrict (overlapBelow T)
  let ηhi:=η.restrict (overlapBelow T)ᶜ
  let ηh:=lowerReflectedMeasure ηlo h
  let g:=fun q : Paper.Overlap=>G q
  let F:=fun q : Paper.Overlap=>∫u,G (lowerReflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h
  have hlo:Integrable g ηlo:=integrable_overlap_potential ηlo G hG
  have hhi:Integrable g ηhi:=integrable_overlap_potential ηhi G hG
  have hgh:Integrable g ηh:=integrable_overlap_potential ηh G hG
  have hr:Integrable g (ENNReal.ofReal s • Measure.dirac zeroOverlap):=
    (integrable_dirac (by simp) : Integrable g (Measure.dirac zeroOverlap)).smul_measure ENNReal.ofReal_ne_top
  have hEq : (∫q,g q∂ηh)=(∫q,F q∂ηlo):=integral_lowerReflectedMeasure_potential ηlo h G hG
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hjoint:Integrable (fun p : Paper.Overlap×ℝ=>G (lowerReflectedOverlap p:ℝ))
      (ηlo.prod (symmetricUniformLaw h)):=
    (integrable_const K).mono'
      (hG.measurable.comp (measurable_subtype_coe.comp measurable_lowerReflectedOverlap)).aestronglyMeasurable
      (.of_forall fun p=>hK _ (lowerReflectedOverlap p).property)
  have hF:Integrable F ηlo:=hjoint.integral_prod_left
  have hpoint:∀ᵐq∂ηlo,F q-g q≤h^2/6 := by
    filter_upwards [ae_restrict_mem (measurableSet_overlapBelow T)] with q hq
    have he : (∫u,G (lowerReflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h)=
        ∫u,G |(q:ℝ)+u|∂symmetricUniformLaw h := by
      apply integral_congr_ae
      filter_upwards [symmetricUniformLaw_ae h] with u hu
      rw [lowerReflectedOverlap_coe T h hT hh q hq hu]
    change (∫u,G (lowerReflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h)-G q≤h^2/6
    rw [he]
    exact hcost q ⟨q.property.1,hq⟩
  have hb:=integral_mono_ae (hF.sub hlo) (integrable_const (h^2/6)) hpoint
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hF hlo,integral_const,Measure.real,show ηlo univ=η (overlapBelow T) from
    Measure.restrict_apply_univ _,smul_eq_mul] at hb
  have hη : ηlo+ηhi=η:=Measure.restrict_add_restrict_compl (measurableSet_overlapBelow T)
  have hμEq:(μ:Measure Paper.Overlap)=ENNReal.ofReal s • Measure.dirac zeroOverlap+(ηlo+ηhi):=by
    rw [hη]
    exact (root_add_parisiFreeMeasure μ s hs hμ).symm
  change (∫q,g q∂(ENNReal.ofReal s • Measure.dirac zeroOverlap+(ηh+ηhi)))-
    (∫q,g q∂(μ:Measure Paper.Overlap))≤_
  rw [hμEq,integral_add_measure hr (hgh.add_measure hhi),integral_add_measure hr (hlo.add_measure hhi),
    integral_add_measure hgh hhi,integral_add_measure hlo hhi,hEq]
  change _≤(η (overlapBelow T)).toReal*h^2/6
  linarith

theorem partial_reflected_vector_functional_cost_le {n : ℕ} (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s T h : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T))
    (β t a : ℝ) (hβ : β≠0) (ht : t≤1) (ha : 0≤a) :
    vectorMeasureFunctional n (partialReflectedParisiMeasure μ s T h hs hh.1) β t a-
      vectorMeasureFunctional n μ β t a≤((1-t)*β^2)*(parisiFreeMeasure μ s).real (overlapBelow T)*h^2/12 := by
  by_cases ht1:t=1
  · subst t
    simp only [vectorMeasureFunctional,sub_self,zero_mul,sub_zero]
    simp_rw [vectorMeasurePotential_one_zero]
    simp
  have htl:t<1:=lt_of_le_of_ne ht ht1
  let ν:=partialReflectedParisiMeasure μ s T h hs hh.1
  have hv:=vectorMeasureFunctional_convex_deficit_bound hn ν μ β t a hβ htl ha
  have hg:=partial_reflected_potential_increment_le μ s T h hs hμ hT hh
    (vectorOverlapDeficit (n:=n) ν β t a ht)
    (continuous_vectorOverlapDeficit ν β t a ht)
    (fun q hq=>transportDeficit_lower_reflected_uniform_bound _
      (continuous_vectorMeanOverlapReal ν β t a ht)
      (vectorMeanOverlapReal_monotoneOn ν β t a hβ htl)
      (fun r _=>vectorMeanOverlapReal_nonneg_le_one ν β t a ht r) T h hT hh q hq)
  have hc:0≤((1-t)*β^2)/2:=by positivity
  have hhg:=mul_le_mul_of_nonneg_left hg hc
  change _≤vectorMeasureFunctional n μ β t a-vectorMeasureFunctional n ν β t a at hv
  change vectorMeasureFunctional n ν β t a-vectorMeasureFunctional n μ β t a≤_
  nlinarith

end QuantitativeFollowup
