module
public import FourPapersCommon.BoundedLayercake
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

/-! The genuine weighted layer-cake and truncated square-tail identity for
an arbitrary bounded scalar random variable on a finite measure space. -/
noncomputable section
open Set MeasureTheory intervalIntegral
open scoped NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 2200000

theorem integral_abs_cube_eq_square_layercake {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω→ℝ) (hf : Measurable f)
    (hb : ∀ω,|f ω|≤1) :
    (∫ω,|f ω|^3 ∂P)=
      ∫θ in Ioo (0:ℝ) 1,∫ω,{ω | θ < |f ω| }.indicator (fun ω=>f ω^2) ω ∂P :=by
  let w : Ω→ℝ≥0∞:=fun ω=>ENNReal.ofReal (f ω^2)
  let R:=P.withDensity w
  have hw : Measurable w:=(hf.pow_const 2).ennreal_ofReal
  have hwle : w≤ᵐ[P]fun _=>1:=.of_forall fun ω=>by
    dsimp only [w]
    rw [ENNReal.ofReal_le_one]
    simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hb ω)
  have hRP : R≤P:=by
    change P.withDensity w≤P
    calc
      _≤P.withDensity 1:=withDensity_mono hwle
      _=P:=withDensity_one
  let : IsFiniteMeasure R:=isFiniteMeasure_of_le P hRP
  have hia : Integrable (fun ω=>|f ω|) R:=
    Integrable.of_bound hf.abs.aestronglyMeasurable 1 (.of_forall fun ω=>by simpa only [Real.norm_eq_abs,abs_abs] using hb ω)
  have hc:=integral_layercake_unit_interval R (fun ω=>|f ω|) hia
    (.of_forall fun ω=>abs_nonneg _) (.of_forall hb)
  have he : (∫ω,|f ω| ∂R)=(∫ω,|f ω|^3 ∂P):=by
    rw [integral_withDensity_eq_integral_toReal_smul hw (.of_forall fun ω=>ENNReal.ofReal_lt_top)]
    apply MeasureTheory.integral_congr_ae
    exact .of_forall fun ω=>by
      simp only [w,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
      rw [←sq_abs]
      ring
  rw [he] at hc
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  dsimp only
  have hs : MeasurableSet {ω | θ < |f ω| }:=measurableSet_lt measurable_const hf.abs
  rw [←setIntegral_one_eq_measureReal (μ:=R),
    setIntegral_withDensity_eq_setIntegral_toReal_smul hw (.of_forall fun ω=>ENNReal.ofReal_lt_top) _ hs]
  simp only [w,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,mul_one]
  exact (MeasureTheory.integral_indicator hs).symm

theorem cubic_moment_truncated_square_layercake {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω→ℝ) (hf : Measurable f)
    (hb : ∀ω,|f ω|≤1) (z : ℝ) (hz : z∈Ioc (0:ℝ) (1/4)) :
    (∫ω,|f ω|^3 ∂P)≤z*(∫ω,f ω^2 ∂P)+
      (∫θ in Ioo z (1/4),∫ω,{ω | θ < |f ω| }.indicator (fun ω=>f ω^2) ω ∂P)+
      (3/4)*(∫ω,{ω | (1/4:ℝ) < |f ω| }.indicator (fun ω=>f ω^2) ω ∂P) :=by
  let T : ℝ→ℝ:=fun θ=>∫ω,{ω | θ < |f ω| }.indicator (fun ω=>f ω^2) ω ∂P
  let K:=∫ω,f ω^2 ∂P
  have hiF : Integrable (fun ω=>f ω^2) P:=Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1
    (.of_forall fun ω=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hb ω))
  have hTbound (θ : ℝ) : 0≤T θ ∧ T θ≤K:=by
    refine ⟨integral_nonneg (fun ω=>Set.indicator_nonneg (fun _ _=>sq_nonneg _) _),?_⟩
    exact MeasureTheory.integral_mono (hiF.indicator (measurableSet_lt (measurable_const (a:=θ)) hf.abs)) hiF
      (fun ω=>by simp only [Set.indicator,mem_setOf_eq];split_ifs <;> first | exact le_rfl | positivity)
  have hTanti : Antitone T:=by
    intro θ η hθη
    apply MeasureTheory.integral_mono (hiF.indicator (measurableSet_lt (measurable_const (a:=η)) hf.abs))
      (hiF.indicator (measurableSet_lt (measurable_const (a:=θ)) hf.abs))
    intro ω
    simp only [Set.indicator,mem_setOf_eq]
    split_ifs <;> first | exact le_rfl | positivity | exfalso; linarith
  have hTm : Measurable T:=hTanti.measurable
  have hiT (a b : ℝ) (hab : a≤b) : IntervalIntegrable T volume a b:=by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
    apply Integrable.of_bound hTm.aestronglyMeasurable K
    exact .of_forall fun θ=>by rw [Real.norm_of_nonneg (hTbound θ).1];exact (hTbound θ).2
  have hz1 : z≤1:=by linarith [hz.2]
  have hi0z:=hiT 0 z hz.1.le
  have hizq:=hiT z (1/4) hz.2
  have hiq1:=hiT (1/4) 1 (by norm_num)
  have hi01:=hiT 0 1 zero_le_one
  have h0:=intervalIntegral.integral_mono hz.1.le hi0z intervalIntegrable_const
    (fun θ=>(hTbound θ).2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at h0
  have h1:=intervalIntegral.integral_mono_on (by norm_num : (1/4:ℝ)≤1) hiq1 intervalIntegrable_const
    (fun θ hθ=>hTanti hθ.1)
  norm_num [intervalIntegral.integral_const,smul_eq_mul] at h1
  rw [integral_abs_cube_eq_square_layercake P f hf hb,
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le zero_le_one,
    ←integral_add_adjacent_intervals hi0z (hizq.trans hiq1),
    ←integral_add_adjacent_intervals hizq hiq1]
  change (∫θ in 0..z,T θ)+((∫θ in z..(1/4),T θ)+(∫θ in (1/4)..1,T θ))≤_
  rw [intervalIntegral.integral_of_le hz.2,integral_Ioc_eq_integral_Ioo]
  change _≤z*K+(∫θ in Ioo z (1/4),T θ)+(3/4)*T (1/4)
  linarith

end FourPapersCommon
