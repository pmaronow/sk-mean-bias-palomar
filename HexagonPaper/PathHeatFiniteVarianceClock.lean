module
public import HexagonPaper.PathHeatClockKernelDifferentiation
public import HexagonPaper.PathHeatBrownianMesh

@[expose] public section

/-! An actual finite centered Gaussian coordinate of variance `v` is
represented by a scaled terminal observation of a canonical Wiener row.
The clock is linear in level, including variance zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pathHeatFiniteVarianceClock (v V : ℝ) (hV : 0<V) (hv : 0≤v) (hvV : v≤V) : C(I,I) :=
  ⟨fun q => ⟨(q:ℝ)*v/V, by
      constructor
      · exact div_nonneg (mul_nonneg q.property.1 hv) hV.le
      · apply (div_le_one hV).mpr
        exact (mul_le_of_le_one_left hv q.property.2).trans hvV⟩,
    Continuous.subtype_mk ((continuous_subtype_val.mul_const v).div_const V) _⟩

@[simp] theorem pathHeatFiniteVarianceClock_apply (v V : ℝ)
    (hV : 0<V) (hv : 0≤v) (hvV : v≤V) (q : I) :
    (pathHeatFiniteVarianceClock v V hV hv hvV q : ℝ)=(q:ℝ)*v/V := rfl

@[simp] theorem pathHeatFiniteVarianceClock_root (v V : ℝ)
    (hV : 0<V) (hv : 0≤v) (hvV : v≤V) :
    pathHeatFiniteVarianceClock v V hV hv hvV 0=0 := by
  apply Subtype.ext
  simp

@[simp] theorem pathHeatFiniteVarianceClock_terminal (v V : ℝ)
    (hV : 0<V) (hv : 0≤v) (hvV : v≤V) :
    (pathHeatFiniteVarianceClock v V hV hv hvV 1 : ℝ)=v/V := by
  simp

theorem pathHeatFiniteVarianceClock_monotone (v V : ℝ)
    (hV : 0<V) (hv : 0≤v) (hvV : v≤V) :
    Monotone (pathHeatFiniteVarianceClock v V hV hv hvV) := by
  intro q r hqr
  change (q:ℝ)*v/V ≤ (r:ℝ)*v/V
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqr hv) hV.le

theorem pathHeatFiniteVarianceClock_strictMono (v V : ℝ)
    (hV : 0<V) (hv : 0<v) (hvV : v≤V) :
    StrictMono (pathHeatFiniteVarianceClock v V hV hv.le hvV) := by
  intro q r hqr
  change (q:ℝ)*v/V < (r:ℝ)*v/V
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hqr hv) hV

def pathHeatFiniteVarianceClockDerivative (dv V : ℝ) : C(I,ℝ) :=
  ⟨fun q => (q:ℝ)*dv/V, (continuous_subtype_val.mul_const dv).div_const V⟩

@[simp] theorem pathHeatFiniteVarianceClockDerivative_apply (dv V : ℝ) (q : I) :
    pathHeatFiniteVarianceClockDerivative dv V q=(q:ℝ)*dv/V := rfl

theorem continuous_pathHeatFiniteVarianceClock_family {Z : Type*} [TopologicalSpace Z]
    (v : Z→ℝ) (V : ℝ) (hV : 0<V) (hv : ∀z,0≤v z) (hvV : ∀z,v z≤V)
    (hc : Continuous v) :
    Continuous (fun z => pathHeatFiniteVarianceClock (v z) V hV (hv z) (hvV z)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.subtype_mk
  exact (continuous_snd.subtype_val.mul (hc.comp continuous_fst)).div_const V

theorem hasDerivAt_pathHeatFiniteVarianceClock (v : ℝ→ℝ) (dv V z : ℝ)
    (hV : 0<V) (hv : ∀w,0≤v w) (hvV : ∀w,v w≤V)
    (hdv : HasDerivAt v dv z) (q : I) :
    HasDerivAt (fun w => (pathHeatFiniteVarianceClock (v w) V hV (hv w) (hvV w) q : ℝ))
      (pathHeatFiniteVarianceClockDerivative dv V q) z :=
  (hdv.const_mul (q:ℝ)).div_const V

theorem pathHeatFiniteVarianceClock_terminal_variance (v V : ℝ)
    (hV : 0<V) (hv : 0≤v) (hvV : v≤V) :
    (Real.sqrt V)^2*(pathHeatFiniteVarianceClock v V hV hv hvV 1 : ℝ)=v := by
  rw [Real.sq_sqrt hV.le,pathHeatFiniteVarianceClock_terminal]
  field_simp

theorem pathHeatFiniteVarianceClock_terminal_derivative (dv V : ℝ) (hV : 0<V) :
    (Real.sqrt V)^2*pathHeatFiniteVarianceClockDerivative dv V 1=dv := by
  rw [Real.sq_sqrt hV.le,pathHeatFiniteVarianceClockDerivative_apply]
  change V*(1*dv/V)=dv
  rw [one_mul]
  field_simp

theorem hasLaw_pathHeatFiniteVarianceTerminal (v V : ℝ)
    (hV : 0<V) (hv : 0≤v) (hvV : v≤V) :
    HasLaw (fun p : WienerPath => Real.sqrt V *
      p (pathHeatFiniteVarianceClock v V hV hv hvV 1))
      (gaussianReal 0 v.toNNReal) canonicalWienerMeasure := by
  have h := gaussianReal_const_mul
    (hasLaw_pathHeatWiener_eval (pathHeatFiniteVarianceClock v V hV hv hvV 1)) (Real.sqrt V)
  have he : NNReal.mk ((Real.sqrt V)^2) (sq_nonneg _) *
      (pathHeatFiniteVarianceClock v V hV hv hvV 1).1.toNNReal = v.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _
      (pathHeatFiniteVarianceClock v V hV hv hvV 1).property.1,Real.coe_toNNReal _ hv]
    exact pathHeatFiniteVarianceClock_terminal_variance v V hV hv hvV
  simpa only [mul_zero,he] using h

end HexagonPaper
