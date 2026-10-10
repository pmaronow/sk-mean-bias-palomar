module
public import FRSB.ConstantMassKernel
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! The actual normalized Gaussian Cole--Hopf kernel is Feller, and its
positive-variance transitions charge every nonempty open set. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
open scoped NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem continuous_constantMassKernel_bounded_integral (m : ℝ) (v : ℝ≥0)
    (A : ℝ→ℝ) (hA : Continuous A) (hg : HasLinearGrowth A)
    (F : ℝ→ℝ) (hF : Continuous F) (C : ℝ) (hb : ∀x,‖F x‖≤C) :
    Continuous (fun x=>∫y,F y ∂FRSB.constantMassKernel m v A x) := by
  have he (x : ℝ) : (∫y,F y ∂FRSB.constantMassKernel m v A x)=
      ∫z,F (x+z)*coleHopfQ m v A x z ∂gaussianReal 0 v := by
    rw [FRSB.integral_constantMassKernel m v A hA hg]
    have hs : (gaussianReal 0 v).map (fun z=>x+z)=gaussianReal x v := by
      simpa using gaussianReal_map_const_add (μ:=0) (v:=v) x
    rw [←hs]
    rw [integral_map (μ:=gaussianReal 0 v) (φ:=fun z : ℝ=>x+z)
      (f:=fun y=>F y*FRSB.constantMassWeight m v A x y)
      (measurable_const.add measurable_id).aemeasurable
      (hF.mul ((FRSB.continuous_constantMassWeight m v A hA hg).comp
        ((continuous_const : Continuous (fun _ : ℝ=>x)).prodMk continuous_id))).aestronglyMeasurable]
    rfl
  simp_rw [he]
  exact continuous_integral_mul_coleHopfQ' hA hg m hF
    (HasExpGrowth.of_bounded (fun x=>by simpa only [Real.norm_eq_abs] using hb x)) v

theorem isOpenPosMeasure_constantMassKernel (m : ℝ) (v : ℝ≥0) (hv : v≠0)
    (A : ℝ→ℝ) (hA : Continuous A) (hg : HasLinearGrowth A) (x : ℝ) :
    Measure.IsOpenPosMeasure (FRSB.constantMassKernel m v A x) := by
  rw [FRSB.constantMassKernel_apply m v A hA hg]
  letI : Measure.IsOpenPosMeasure (gaussianReal x v):=
    (gaussianReal_absolutelyContinuous' x hv).isOpenPosMeasure
  exact (withDensity_absolutelyContinuous'
    ((FRSB.continuous_constantMassWeight m v A hA hg).comp
      (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun y=>(ENNReal.ofReal_pos.mpr (FRSB.constantMassWeight_pos m v A x y)).ne')).isOpenPosMeasure

theorem isOpenPosMeasure_comp_of_transition (K : Kernel ℝ ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hK : ∀x,Measure.IsOpenPosMeasure (K x)) :
    Measure.IsOpenPosMeasure (K ∘ₘ μ) := by
  constructor
  intro U hU hn
  rw [Measure.bind_apply hU.measurableSet K.aemeasurable]
  intro he
  have ha := (lintegral_eq_zero_iff (K.measurable_coe hU.measurableSet)).mp he
  have hnz : ∀x,K x U≠0:=fun x=>by
    letI:=hK x
    exact hU.measure_ne_zero (K x) hn
  have : ∀ᵐx ∂μ,False := ha.mono (fun x hx=>hnz x hx)
  have hz : μ=0:=by simpa using this
  have hh:=congrArg (fun ν : Measure ℝ=>ν univ) hz
  simpa using hh

end FourPapersCommon
