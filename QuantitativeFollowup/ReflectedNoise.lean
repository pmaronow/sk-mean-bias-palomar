module
public import QuantitativeFollowup.ParisiFreeMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! The actual uniform perturbation and reflected overlap map used by
the follow-up's regularization. No regularity of the input measure is
required; in particular the input may have atoms at either endpoint. -/
noncomputable section
open Set MeasureTheory Paper
open scoped ENNReal Topology
namespace QuantitativeFollowup

def symmetricUniformLaw (h : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/(2*h)) • volume.restrict (Icc (-h) h)

theorem symmetricUniformLaw_probability (h : ℝ) (hh : 0<h) :
    IsProbabilityMeasure (symmetricUniformLaw h) := by
  constructor
  rw [symmetricUniformLaw,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Icc]
  simp only [smul_eq_mul]
  rw [←ENNReal.ofReal_mul (by positivity),show h-(-h)=2*h by ring]
  field_simp
  simp

instance symmetricUniformLaw_finite (h : ℝ) : IsFiniteMeasure (symmetricUniformLaw h) := by
  constructor
  simp only [symmetricUniformLaw,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Icc,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem symmetricUniformLaw_ae (h : ℝ) :
    ∀ᵐu∂symmetricUniformLaw h,u∈Icc (-h) h := by
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

def overlapReflection (z : ℝ) : ℝ := if z≤1 then |z| else 2-z

theorem measurable_overlapReflection : Measurable overlapReflection := by
  exact measurable_abs.ite (measurableSet_le measurable_id measurable_const)
    (measurable_const.sub measurable_id)

theorem overlapReflection_mem {q h u : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (hh : h∈Ioc (0:ℝ) (1/2)) (hu : u∈Icc (-h) h) :
    overlapReflection (q+u)∈Icc (0:ℝ) 1 := by
  unfold overlapReflection
  split_ifs with hz
  · constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor
      · linarith [hq.1,hu.1,hh.2]
      · exact hz
  · constructor <;> linarith [hq.1,hq.2,hu.1,hu.2,hh.2]

theorem overlapReflection_displacement {q h u : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (_hh : h∈Ioc (0:ℝ) (1/2)) (hu : u∈Icc (-h) h) :
    |overlapReflection (q+u)-q|≤h := by
  unfold overlapReflection
  split_ifs with hz
  · by_cases hz0 : 0≤q+u
    · rw [abs_of_nonneg hz0]
      simpa only [add_sub_cancel_left,abs_le] using (show -h≤u ∧ u≤h from hu)
    · rw [abs_of_neg (lt_of_not_ge hz0),abs_le]
      constructor <;> linarith [hq.1,hu.1,hu.2]
  · rw [abs_le]
    constructor <;> linarith [hq.1,hq.2,hu.1,hu.2]

def reflectedOverlap (p : Paper.Overlap×ℝ) : Paper.Overlap :=
  projIcc (0 : ℝ) 1 zero_le_one (overlapReflection ((p.1:ℝ)+p.2))

theorem measurable_reflectedOverlap : Measurable reflectedOverlap :=
  (continuous_projIcc.measurable).comp
    (measurable_overlapReflection.comp ((measurable_subtype_coe.comp measurable_fst).add measurable_snd))

theorem reflectedOverlap_coe {h : ℝ} (hh : h∈Ioc (0:ℝ) (1/2))
    (q : Paper.Overlap) {u : ℝ} (hu : u∈Icc (-h) h) :
    (reflectedOverlap (q,u):ℝ)=overlapReflection ((q:ℝ)+u) := by
  exact congrArg Subtype.val (projIcc_of_mem _ (overlapReflection_mem q.property hh hu))

theorem reflectedOverlap_displacement {h : ℝ} (hh : h∈Ioc (0:ℝ) (1/2))
    (q : Paper.Overlap) {u : ℝ} (hu : u∈Icc (-h) h) :
    |(reflectedOverlap (q,u):ℝ)-(q:ℝ)|≤h := by
  rw [reflectedOverlap_coe hh q hu]
  exact overlapReflection_displacement q.property hh hu

end QuantitativeFollowup
