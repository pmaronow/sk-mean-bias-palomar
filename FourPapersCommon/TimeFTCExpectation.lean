module
public import FourPapersCommon.TimePartitionFTC

@[expose] public section

/-! Quantitative expectation error for replacing a time-dependent test by its
right-endpoint spatial state. The stochastic input is only a proved L1
increment bound, independent of any target partition convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 1500000
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ≥0} (P : Measure Ω) [IsProbabilityMeasure P]

def timeFTCCellError (d : TimeFTCData Ω E T) (X : ℝ≥0 → Ω → E)
    (Z : Ω → ℝ) (a b : ℝ≥0) (sample : Ω) : ℝ :=
  ∫ s in Ioc a b,Z sample*(d.ft s sample (X b sample)-d.ft s sample (X s sample))
    ∂nonnegativeLebesgueMeasure

theorem timeFTCCellError_expectation_bound (d : TimeFTCData Ω E T)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖ ≤ C)
    (A D : ℝ≥0)
    (hi : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      Integrable (fun sample => ‖X t sample-X r sample‖) P)
    (hinc : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      (∫ sample,‖X t sample-X r sample‖ ∂P) ≤ A*Real.sqrt ((t : ℝ)-r)+D*((t : ℝ)-r))
    (a b : ℝ≥0) (hab : a ≤ b) (hb : b ≤ T) :
    Integrable (timeFTCCellError d X Z a b) P ∧
    |∫ sample,timeFTCCellError d X Z a b sample ∂P| ≤
      C*d.spatialLip*((b : ℝ)-a)*(A*Real.sqrt ((b : ℝ)-a)+D*((b : ℝ)-a)) := by
  let F : ℝ≥0 → Ω → ℝ := fun s sample =>
    Z sample*(d.ft s sample (X b sample)-d.ft s sample (X s sample))
  let μ : Measure ℝ≥0 := nonnegativeLebesgueMeasure.restrict (Ioc a b)
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ,Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b)⟩
  have hF : Measurable (Function.uncurry F) := by
    have hright : Measurable (fun p : ℝ≥0 × Ω =>
        d.ft p.1 p.2 (X b p.2)) := d.ft_measurable.comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk
        (measurable_snd.prodMk (hX.of_uncurry_left.comp measurable_snd)))
    have hpath : Measurable (fun p : ℝ≥0 × Ω =>
        d.ft p.1 p.2 (X p.1 p.2)) := d.ft_measurable.comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk
        (measurable_snd.prodMk hX))
    exact (hZ.comp measurable_snd).mul (hright.sub hpath)
  have hbounded : ∀ᵐ p ∂μ.prod P,‖F p.1 p.2‖ ≤ 2*C*d.bound := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hF.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply Eventually.of_forall
    intro sample
    have hsT : (s : ℝ) ∈ Icc (0 : ℝ) T :=
      ⟨s.coe_nonneg,(show (s : ℝ) ≤ b from hs.2).trans (show (b : ℝ) ≤ T from hb)⟩
    have hh := norm_sub_le (d.ft s sample (X b sample)) (d.ft s sample (X s sample))
    have hdiff : ‖d.ft s sample (X b sample)-d.ft s sample (X s sample)‖ ≤ 2*d.bound :=
      hh.trans (by nlinarith [d.ft_bound s hsT sample (X b sample),d.ft_bound s hsT sample (X s sample)])
    have hmul := mul_le_mul (hC sample) hdiff (norm_nonneg _) C.coe_nonneg
    change ‖Z sample*(d.ft s sample (X b sample)-d.ft s sample (X s sample))‖ ≤
      2*C*d.bound
    rw [norm_mul]
    convert hmul using 1 <;> ring
  have hprod : Integrable (Function.uncurry F) (μ.prod P) :=
    (integrable_const (2*(C : ℝ)*(d.bound : ℝ))).mono' hF.aestronglyMeasurable hbounded
  have hinterr : Integrable (timeFTCCellError d X Z a b) P := by
    exact hprod.integral_prod_right
  have hinner : ∀ s ∈ Ioc a b,‖∫ sample,F s sample ∂P‖ ≤
      C*d.spatialLip*(A*Real.sqrt ((b : ℝ)-a)+D*((b : ℝ)-a)) := by
    intro s hs
    have hsT : (s : ℝ) ∈ Icc (0 : ℝ) T :=
      ⟨s.coe_nonneg,(show (s : ℝ) ≤ b from hs.2).trans (show (b : ℝ) ≤ T from hb)⟩
    have hpoint (sample : Ω) : ‖F s sample‖ ≤ C*d.spatialLip*‖X b sample-X s sample‖ := by
      have hLip := (d.ft_lipschitz s hsT sample).dist_le_mul (X b sample) (X s sample)
      simp only [dist_eq_norm] at hLip
      have hh := mul_le_mul (hC sample) hLip (norm_nonneg _) C.coe_nonneg
      simpa only [F,norm_mul,mul_assoc] using hh
    have hnorm : Integrable (fun sample => ‖F s sample‖) P :=
      ((hi s b hs.2 hb).const_mul (C*d.spatialLip)).mono'
        (hF.of_uncurry_left.norm.aestronglyMeasurable) (.of_forall (by simpa only [Real.norm_eq_abs,abs_abs] using hpoint))
    have him := integral_mono hnorm ((hi s b hs.2 hb).const_mul (C*d.spatialLip)) hpoint
    rw [integral_const_mul] at him
    have hdt : 0 ≤ (b : ℝ)-s := sub_nonneg.mpr (show (s : ℝ) ≤ b from hs.2)
    have hsa : (a : ℝ) ≤ s := (show (a : ℝ) < s from hs.1).le
    have hmono : A*Real.sqrt ((b : ℝ)-s)+D*((b : ℝ)-s) ≤
        A*Real.sqrt ((b : ℝ)-a)+D*((b : ℝ)-a) := by
      gcongr
    exact (norm_integral_le_integral_norm _).trans (him.trans
      ((mul_le_mul_of_nonneg_left (hinc s b hs.2 hb) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hmono (by positivity))))
  refine ⟨hinterr,?_⟩
  have hswap := integral_integral_swap hprod
  change (∫ s,∫ sample,F s sample ∂P ∂μ) =
    ∫ sample,timeFTCCellError d X Z a b sample ∂P at hswap
  rw [← hswap,← Real.norm_eq_abs]
  have hbnd : ‖∫ s,∫ sample,F s sample ∂P ∂μ‖ ≤
      (C*d.spatialLip*(A*Real.sqrt ((b : ℝ)-a)+D*((b : ℝ)-a)))*μ.real univ :=
    norm_integral_le_of_norm_le_const
      ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hinner s hs))
  have hm : μ.real univ = (b : ℝ)-a := by
    simp only [μ,Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))]
  rw [hm] at hbnd
  convert hbnd using 1 <;> ring

end FourPapersCommon
