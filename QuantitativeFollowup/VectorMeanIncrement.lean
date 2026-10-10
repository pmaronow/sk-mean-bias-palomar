module
public import QuantitativeFollowup.MeanIncrementGeometry
public import QuantitativeFollowup.VectorSupportContact
public import FourPapersCommon.SquareIncrementIdentity

@[expose] public section

/-! The literal factor-two mean-increment estimate towards any contact
level of an actual minimizing profile, and its actual L² state-mean form. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped Topology BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 900000
variable {n : ℕ}

theorem vector_mean_increment_towards_support (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) (r : Paper.Overlap) :
    |vectorMeanOverlap (n:=n) μ β t a ht.le r-vectorMeanOverlap (n:=n) μ β t a ht.le q|≤
      2*|(r:ℝ)-q| := by
  have hcontact:=vector_free_support_contact hn μ s hs hμ β t a hβ ht ha hmin q hq
  have hargmin:=(vector_minimum_iff_free_support_argmin hn μ s ⟨hs.1,hs.2.le⟩ hs.2
    hμ β t a hβ ht ha).mp hmin hq
  have hh:=mean_increment_towards_deficit_minimum
    (vectorMeanOverlapReal (n:=n) μ β t a ht.le)
    (continuous_vectorMeanOverlapReal μ β t a ht.le)
    (vectorMeanOverlapReal_monotoneOn μ β t a hβ ht)
    (fun u _=>vectorMeanOverlapReal_nonneg_le_one μ β t a ht.le u)
    q r q.property r.property (by
      unfold vectorMeanOverlapReal
      rw [projIcc_of_mem zero_le_one q.property]
      exact hcontact.2)
    (fun y hy=>hargmin ⟨y,hy⟩)
  simpa only [vectorMeanOverlapReal,projIcc_of_mem zero_le_one r.property,
    projIcc_of_mem zero_le_one q.property] using hh

theorem vector_mean_increment_ordered_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) (r : Paper.Overlap) (hrq : r≤q) :
    0≤vectorMeanOverlap (n:=n) μ β t a ht.le q-vectorMeanOverlap (n:=n) μ β t a ht.le r ∧
      vectorMeanOverlap (n:=n) μ β t a ht.le q-vectorMeanOverlap (n:=n) μ β t a ht.le r≤2*((q:ℝ)-r) := by
  have hmono:=vectorMeanOverlap_monotone (n:=n) μ β t a hβ ht hrq
  have hb:=vector_mean_increment_towards_support hn μ s hs hμ β t a hβ ht ha hmin q hq r
  have hrq' : (r:ℝ)≤(q:ℝ):=hrq
  rw [abs_of_nonpos (sub_nonpos.mpr hmono),abs_of_nonpos (sub_nonpos.mpr hrq')] at hb
  exact ⟨sub_nonneg.mpr hmono,by linarith⟩

theorem vector_spinMean_increment_second_moment (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) :
    (∫sample,‖vectorMeasureSpinMean μ β t ht.le q sample-
        vectorMeasureSpinMean μ β t ht.le r sample‖^2∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
      (n:ℝ)*(vectorMeanOverlap (n:=n) μ β t a ht.le q-
        vectorMeanOverlap (n:=n) μ β t a ht.le r) := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let f:=fun (sample : VectorDisorderBrownianSample n) (l : Fin n)=>vectorMeasureSpinMean μ β t ht.le q sample l
  let g:=fun (sample : VectorDisorderBrownianSample n) (l : Fin n)=>vectorMeasureSpinMean μ β t ht.le r sample l
  have hii (l : Fin n) : Integrable (fun sample=>(f sample l-g sample l)^2) P := by
    have hff : Integrable (fun sample=>(f sample l)^2) P:=by
      simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le q q l
    have hgg : Integrable (fun sample=>(g sample l)^2) P:=by
      simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le r r l
    have hfg : Integrable (fun sample=>g sample l*f sample l) P:=
      integrable_vectorMeanOverlap_mul μ β t a ht.le r q l
    exact FourPapersCommon.integrable_square_sub hff hgg hfg
  have he (l : Fin n) : (∫sample,(f sample l-g sample l)^2∂P)=
      (∫sample,(f sample l)^2∂P)-(∫sample,(g sample l)^2∂P) := by
    have hff : Integrable (fun sample=>(f sample l)^2) P:=by
      simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le q q l
    have hgg : Integrable (fun sample=>(g sample l)^2) P:=by
      simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le r r l
    have hfg : Integrable (fun sample=>g sample l*f sample l) P:=
      integrable_vectorMeanOverlap_mul μ β t a ht.le r q l
    have hc:=vectorMeanOverlap_cross μ β t a hβ ht r q hrq l
    change (∫sample,g sample l*f sample l∂P)=∫sample,(g sample l)^2∂P at hc
    exact FourPapersCommon.integral_square_sub_of_cross hff hgg hfg hc
  simp_rw [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply]
  rw [integral_finsetSum _ (fun l _=>hii l)]
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  unfold vectorMeanOverlap
  have hn' : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  rw [mul_sub,mul_div_cancel₀ _ hn',mul_div_cancel₀ _ hn']

theorem vector_spinMean_increment_towards_support_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) (r : Paper.Overlap) (hrq : r≤q) :
    (∫sample,‖vectorMeasureSpinMean μ β t ht.le q sample-
        vectorMeasureSpinMean μ β t ht.le r sample‖^2∂vectorMeasureDisorderTilt (n:=n) μ β t a)≤
      2*(n:ℝ)*((q:ℝ)-r) := by
  rw [vector_spinMean_increment_second_moment hn μ β t a hβ ht r q hrq]
  have hh:=mul_le_mul_of_nonneg_left
    (vector_mean_increment_ordered_bound hn μ s hs hμ β t a hβ ht ha hmin q hq r hrq).2
    (Nat.cast_nonneg n : (0:ℝ)≤n)
  nlinarith

end QuantitativeFollowup
