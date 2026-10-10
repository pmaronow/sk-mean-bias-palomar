module
public import QuantitativeFollowup.ReflectedMeasure
public import QuantitativeFollowup.VectorDeficitFirstVariation

@[expose] public section

/-! The actual reflected measure incurs at most the proved integrated
Taylor cost. The constructed root atom cancels exactly, and genuine
product-measure Fubini handles the free perturbations. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem integrable_overlap_potential (P : Measure Paper.Overlap) [IsFiniteMeasure P]
    (G : ℝ→ℝ) (hG : Continuous G) : Integrable (fun q : Paper.Overlap=>G q) P := by
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  exact (integrable_const K).mono' (hG.measurable.comp measurable_subtype_coe).aestronglyMeasurable
    (.of_forall fun q=>hK q q.property)

theorem integral_reflectedFreeMeasure_potential (μ : Paper.ParisiMeasure) (s h : ℝ)
    (G : ℝ→ℝ) (hG : Continuous G) :
    (∫q : Paper.Overlap,G q∂reflectedFreeMeasure μ s h)=
      ∫q : Paper.Overlap,(∫u,G (reflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h)∂parisiFreeMeasure μ s := by
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hm:=hG.measurable.comp (measurable_subtype_coe.comp measurable_reflectedOverlap)
  have hi : Integrable (fun p : Paper.Overlap×ℝ=>G (reflectedOverlap p:ℝ))
      ((parisiFreeMeasure μ s).prod (symmetricUniformLaw h)):=
    (integrable_const K).mono' hm.aestronglyMeasurable (.of_forall fun p=>hK _ (reflectedOverlap p).property)
  rw [reflectedFreeMeasure,integral_map_of_stronglyMeasurable (f:=fun q : Paper.Overlap=>G q) measurable_reflectedOverlap
    (hG.comp continuous_subtype_val).stronglyMeasurable,integral_prod _ hi]

theorem reflected_potential_increment_le (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hh : h∈Ioc (0:ℝ) (1/2))
    (G : ℝ→ℝ) (hG : Continuous G)
    (hcost : ∀q∈Icc (0:ℝ) 1,(∫u,G (overlapReflection (q+u))∂symmetricUniformLaw h)-G q≤h^2/6) :
    (∫q : Paper.Overlap,G q∂(reflectedParisiMeasure μ s h hs hh.1:Measure Paper.Overlap))-
      (∫q : Paper.Overlap,G q∂(μ:Measure Paper.Overlap))≤(1-s)*h^2/6 := by
  let η:=parisiFreeMeasure μ s
  let ηh:=reflectedFreeMeasure μ s h
  let g:=fun q : Paper.Overlap=>G q
  let F:=fun q : Paper.Overlap=>∫u,G (reflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h
  have hg:Integrable g η:=integrable_overlap_potential η G hG
  have hgh:Integrable g ηh:=integrable_overlap_potential ηh G hG
  have hr:Integrable g (ENNReal.ofReal s • Measure.dirac zeroOverlap):=
    (integrable_dirac (by simp) : Integrable g (Measure.dirac zeroOverlap)).smul_measure ENNReal.ofReal_ne_top
  have hEq : (∫q,g q∂ηh)=(∫q,F q∂η):=integral_reflectedFreeMeasure_potential μ s h G hG
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hjoint:Integrable (fun p : Paper.Overlap×ℝ=>G (reflectedOverlap p:ℝ))
      (η.prod (symmetricUniformLaw h)) :=
    (integrable_const K).mono'
      (hG.measurable.comp (measurable_subtype_coe.comp measurable_reflectedOverlap)).aestronglyMeasurable
      (.of_forall fun p=>hK _ (reflectedOverlap p).property)
  have hF:Integrable F η:=hjoint.integral_prod_left
  have hpoint (q : Paper.Overlap) : F q-g q≤h^2/6 := by
    have he : (∫u,G (reflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h)=
        ∫u,G (overlapReflection ((q:ℝ)+u))∂symmetricUniformLaw h := by
      apply integral_congr_ae
      filter_upwards [symmetricUniformLaw_ae h] with u hu
      rw [reflectedOverlap_coe hh q hu]
    change (∫u,G (reflectedOverlap (q,u):ℝ)∂symmetricUniformLaw h)-G q≤h^2/6
    rw [he]
    exact hcost q q.property
  have hb:=integral_mono (hF.sub hg) (integrable_const (h^2/6)) hpoint
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hF hg,integral_const,Measure.real,show η univ=ENNReal.ofReal (1-s) from parisiFreeMeasure_univ μ s,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2),smul_eq_mul] at hb
  change (∫q,g q∂(ENNReal.ofReal s • Measure.dirac zeroOverlap+ηh))-
    (∫q,g q∂(μ:Measure Paper.Overlap))≤_
  rw [←root_add_parisiFreeMeasure μ s hs hμ,integral_add_measure hr hgh,integral_add_measure hr hg,hEq]
  linarith

theorem reflected_vector_functional_cost_le {n : ℕ} (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hh : h∈Ioc (0:ℝ) (1/2))
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a) :
    vectorMeasureFunctional n (reflectedParisiMeasure μ s h hs hh.1) β t a-
      vectorMeasureFunctional n μ β t a≤((1-t)*β^2)*(1-s)*h^2/12 := by
  let ν:=reflectedParisiMeasure μ s h hs hh.1
  have hv:=vectorMeasureFunctional_convex_deficit_bound hn ν μ β t a hβ ht ha
  have hg:=reflected_potential_increment_le μ s h hs hμ hh
    (vectorOverlapDeficit (n:=n) ν β t a ht.le)
    (continuous_vectorOverlapDeficit ν β t a ht.le)
    (fun q hq=>vectorOverlapDeficit_reflected_uniform_bound ν β t a hβ ht h hh q hq)
  have hc : 0≤((1-t)*β^2)/2:=by positivity
  have hhg:=mul_le_mul_of_nonneg_left hg hc
  change _≤vectorMeasureFunctional n μ β t a-vectorMeasureFunctional n ν β t a at hv
  change vectorMeasureFunctional n ν β t a-vectorMeasureFunctional n μ β t a≤_
  nlinarith

end QuantitativeFollowup
