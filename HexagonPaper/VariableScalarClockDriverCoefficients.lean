module
public import HexagonPaper.VariableScalarClockDriverContinuous
public import HexagonPaper.VariableScalarClockPrimitive
public import FourPapersCommon.DeterministicBrownianProcess
public import StochasticCalculus.QuadraticVariationDensity

@[expose] public section

/-! The source coefficient itself supplies an actual deterministic L²
Itô integrand. Its stopped Gram matrix is the integral primitive, including
all real times in the unit interval. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus FourPapersCommon
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def scalarCoefficientVolatility (c : ℝ→ℝ) : ℝ≥0→ℝ :=
  (Ioc (0:ℝ≥0) 1).indicator (fun t=>Real.sqrt (c (t:ℝ)))

theorem scalarCoefficientVolatility_memLp (c : ℝ→ℝ) (hc : Measurable c)
    (M : ℝ) (hM : ∀q∈Icc (0:ℝ) 1, ‖c q‖≤M) :
    MemLp (scalarCoefficientVolatility c) 2 nonnegativeLebesgueMeasure := by
  unfold scalarCoefficientVolatility
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0:ℝ≥0) 1)) :=
    ⟨by simpa using (nonnegativeLebesgueMeasure_Ioc_ne_top (0:ℝ≥0) 1).lt_top⟩
  apply MemLp.of_bound
    ((Real.continuous_sqrt.measurable.comp (hc.comp NNReal.continuous_coe.measurable)).aestronglyMeasurable)
    (Real.sqrt M)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
  change ‖Real.sqrt (c (q:ℝ))‖≤Real.sqrt M
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt ((le_abs_self _).trans
    (hM q ⟨q.property,hq.2⟩))

def scalarCoefficientLp (c : ℝ→ℝ) (hc : Measurable c)
    (M : ℝ) (hM : ∀q∈Icc (0:ℝ) 1, ‖c q‖≤M) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  (scalarCoefficientVolatility_memLp c hc M hM).toLp (scalarCoefficientVolatility c)

theorem scalarCoefficientLp_coeFn (c : ℝ→ℝ) (hc : Measurable c)
    (M : ℝ) (hM : ∀q∈Icc (0:ℝ) 1, ‖c q‖≤M) :
    (scalarCoefficientLp c hc M hM : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure]
      scalarCoefficientVolatility c :=
  (scalarCoefficientVolatility_memLp c hc M hM).coeFn_toLp

theorem scalarCoefficientLp_stopped_gram (c : ℝ→ℝ) (hc : Measurable c)
    (M : ℝ) (hM : ∀q∈Icc (0:ℝ) 1, ‖c q‖≤M)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q) (q r : Paper.Overlap) :
    inner ℝ
      (deterministicTimeCut (scalarCoefficientLp c hc M hM) (q:ℝ).toNNReal)
      (deterministicTimeCut (scalarCoefficientLp c hc M hM) (r:ℝ).toNNReal)=
      scalarCoefficientPrimitive c (min (q:ℝ) (r:ℝ)) := by
  let f:=scalarCoefficientLp c hc M hM
  let T:ℝ≥0:=(min (q:ℝ) (r:ℝ)).toNNReal
  have hT : (T:ℝ)=min (q:ℝ) (r:ℝ) := Real.coe_toNNReal _ (le_min q.property.1 r.property.1)
  have he : (fun t:ℝ≥0=>inner ℝ
      (deterministicTimeCut f (q:ℝ).toNNReal t)
      (deterministicTimeCut f (r:ℝ).toNNReal t))=ᵐ[nonnegativeLebesgueMeasure]
        (Ioc (0:ℝ≥0) T).indicator (fun t=>c (t:ℝ)) := by
    filter_upwards [deterministicTimeCut_coeFn f (q:ℝ).toNNReal,
      deterministicTimeCut_coeFn f (r:ℝ).toNNReal,
      scalarCoefficientLp_coeFn c hc M hM,
      (show ∀ᵐ t∂nonnegativeLebesgueMeasure,t≠(1:ℝ≥0) by
        simpa only [mem_singleton_iff] using
          (countable_singleton (1:ℝ≥0)).ae_notMem nonnegativeLebesgueMeasure)] with t hq hr hf ht
    change (f:ℝ≥0→ℝ) t=scalarCoefficientVolatility c t at hf
    rw [hq,hr]
    have hqt : t≤(q:ℝ).toNNReal ↔ (t:ℝ)≤q := by
      rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ q.property.1]
    have hrt : t≤(r:ℝ).toNNReal ↔ (t:ℝ)≤r := by
      rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ r.property.1]
    have hmt : t≤T ↔ t≤(q:ℝ).toNNReal ∧ t≤(r:ℝ).toNNReal := by
      rw [←NNReal.coe_le_coe,hT,le_min_iff,←hqt,←hrt]
    by_cases hti : t∈Ioc (0:ℝ≥0) T
    · have hboth:=(hmt.mp hti.2)
      have htq:t∈Ioc (0:ℝ≥0) (q:ℝ).toNNReal:=⟨hti.1,hboth.1⟩
      have htr:t∈Ioc (0:ℝ≥0) (r:ℝ).toNNReal:=⟨hti.1,hboth.2⟩
      have hq1:(q:ℝ).toNNReal≤1:=by
        simpa only [Real.toNNReal_one] using Real.toNNReal_le_toNNReal q.property.2
      have ht1:t≤1:=hboth.1.trans hq1
      have htc:t∈Ioc (0:ℝ≥0) 1:=⟨hti.1,ht1⟩
      have htlt:(t:ℝ)<1:=by exact_mod_cast lt_of_le_of_ne ht1 ht
      have htpos:(0:ℝ)<t:=by exact_mod_cast hti.1
      rw [indicator_of_mem htq,indicator_of_mem htr,indicator_of_mem hti]
      rw [hf]
      unfold scalarCoefficientVolatility
      rw [indicator_of_mem htc,real_inner_self_eq_norm_sq,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hpos t ⟨htpos,htlt⟩).le]
    · rw [indicator_of_notMem hti]
      by_cases htq:t∈Ioc (0:ℝ≥0) (q:ℝ).toNNReal
      · have htr:t∉Ioc (0:ℝ≥0) (r:ℝ).toNNReal:=by
          intro htr
          exact hti ⟨htq.1,hmt.mpr ⟨htq.2,htr.2⟩⟩
        rw [indicator_of_notMem htr,inner_zero_right]
      · rw [indicator_of_notMem htq,inner_zero_left]
  rw [L2.inner_def,integral_congr_ae he,integral_indicator measurableSet_Ioc,
    integral_nonnegative_Ioc_eq_real_Icc (fun t (_:Unit)=>c (t:ℝ)) T (),hT]
  rw [scalarCoefficientPrimitive,intervalIntegral.integral_of_le
    (le_min q.property.1 r.property.1),←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change c (t.toNNReal:ℝ)=c t
  rw [Real.coe_toNNReal _ ht.1]

theorem scalarCoefficientLp_clock_gram (c : ℝ→ℝ) (hc : Measurable c)
    (M : ℝ) (hM : ∀q∈Icc (0:ℝ) 1, ‖c q‖≤M)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q)
    (hint : IntervalIntegrable c volume 0 1) (q r : Paper.Overlap) :
    inner ℝ
      (deterministicTimeCut (scalarCoefficientLp c hc M hM) (q:ℝ).toNNReal)
      (deterministicTimeCut (scalarCoefficientLp c hc M hM) (r:ℝ).toNNReal)=
      (Real.sqrt (scalarCoefficientPrimitive c 1))^2*
        min (scalarCoefficientClock c hint hpos q:ℝ)
          (scalarCoefficientClock c hint hpos r:ℝ) := by
  rw [scalarCoefficientLp_stopped_gram c hc M hM hpos,
    (scalarCoefficientClock_temperature c hint hpos).2]
  have hC:scalarCoefficientPrimitive c 1≠0:=(scalarCoefficient_total_pos c hint hpos).ne'
  have he:=scalarCoefficientClock_apply c hint hpos (min q r)
  change (scalarCoefficientClock c hint hpos (min q r):ℝ)=
    scalarCoefficientPrimitive c (min (q:ℝ) (r:ℝ))/scalarCoefficientPrimitive c 1 at he
  have he':= (div_eq_iff hC).mp he.symm
  rw [(scalarCoefficientClock c hint hpos).monotone.map_min] at he'
  refine he'.trans ?_
  change min (scalarCoefficientClock c hint hpos q:ℝ)
    (scalarCoefficientClock c hint hpos r:ℝ)*scalarCoefficientPrimitive c 1=_
  ring

end HexagonPaper
