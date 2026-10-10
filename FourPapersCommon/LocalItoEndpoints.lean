module
public import FourPapersCommon.LocalItoTest
public import FRSB.StochasticCrops

@[expose] public section

/-! Endpoint passage for actual local Itô expectations. Strict interior
time crops converge to both closed endpoints; the source integral is a
continuous primitive of an actual bounded measurable expectation. -/
noncomputable section
open Set MeasureTheory Filter StochasticCalculus Paper FRSB
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem continuous_ito_bounded_observable_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0→Ω→ℝ}
    (hXc : ∀ω,Continuous (fun t=>X t ω)) (hXm : StronglyAdapted V X)
    (f : ℝ→ℝ→ℝ) (hf : Continuous (fun p : ℝ×ℝ=>f p.1 p.2))
    (M : ℝ) (hM : ∀ (t x : ℝ),‖f t x‖≤M) :
    Continuous (fun t : ℝ≥0=>∫ω,f t (X t ω)∂P) := by
  apply continuous_of_dominated (μ:=P) (bound:=fun _=>M)
  · intro t
    exact (hf.measurable.comp (measurable_const.prodMk
      ((hXm t).mono (V.le t)).measurable)).aestronglyMeasurable
  · intro t
    exact .of_forall fun ω=>hM t (X t ω)
  · exact integrable_const _
  · exact .of_forall fun ω=>hf.comp (NNReal.continuous_coe.prodMk (hXc ω))

theorem intervalIntegrable_bounded_source_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (g : ℝ→Ω→ℝ) (hg : Measurable (Function.uncurry g))
    (B : ℝ) (hB : ∀ (t : ℝ) (ω : Ω),‖g t ω‖≤B) (a b : ℝ) :
    IntervalIntegrable (fun t=>∫ω,g t ω∂P) volume a b := by
  apply (intervalIntegrable_const (c:=B)).mono_fun'
    (hg.stronglyMeasurable.integral_prod_right (ν:=P)).aestronglyMeasurable
  exact .of_forall fun t=>by
    simpa using norm_integral_le_of_norm_le_const (μ:=P) (.of_forall (hB t))

theorem ito_expectation_local_source_closed {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0→Ω→ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f ft fx fxx : ℝ→ℝ→ℝ) (b : ℝ)
    (hf : Continuous (fun p : ℝ×ℝ=>f p.1 p.2))
    (hft : ContinuousOn (fun p : ℝ×ℝ=>ft p.1 p.2) (Ioo (0:ℝ) b×ˢuniv))
    (hfx : Continuous (fun p : ℝ×ℝ=>fx p.1 p.2))
    (hfxx : Continuous (fun p : ℝ×ℝ=>fxx p.1 p.2))
    (ht : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (fun s=>f s x) (ft t x) t)
    (hx : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (f t) (fx t x) x)
    (hxx : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (fx t) (fxx t x) x)
    (hC2 : ∀t∈Ioo (0:ℝ) b,ContDiff ℝ 2 (f t))
    (K M : ℝ≥0) (hK : ∀t∈Ioo (0:ℝ) b,∀x,‖fx t x‖≤K)
    (hM : ∀ (t x : ℝ),‖f t x‖≤M)
    (source : ℝ→Ω→ℝ) (hsm : Measurable (Function.uncurry source))
    (B : ℝ) (hB : ∀ (t : ℝ) (ω : Ω),‖source t ω‖≤B)
    (hsource : ∀ω,∀t∈Ioo (0:ℝ) b,
      ft t (X t.toNNReal ω)+fx t (X t.toNNReal ω)*d t.toNNReal ω+
        (1/2:ℝ)*fxx t (X t.toNNReal ω)*β^2=source t ω)
    (l r : ℝ≥0) (hlr : l≤r) (hrb : (r:ℝ)<b) :
    (∫ω,f r (X r ω)∂P)-(∫ω,f l (X l ω)∂P)=
      ∫t in (l:ℝ)..(r:ℝ),∫ω,source t ω∂P := by
  by_cases heq : l=r
  · subst r
    simp only [sub_self,intervalIntegral.integral_same]
  have hlr' : (l:ℝ)<(r:ℝ) := NNReal.coe_lt_coe.mpr (lt_of_le_of_ne hlr heq)
  let L:=leftCellCrop (l:ℝ) (r:ℝ)
  let R:=rightCellCrop (l:ℝ) (r:ℝ)
  let m : ℝ→ℝ:=fun t=>∫ω,source t ω∂P
  have hi (a c : ℝ) : IntervalIntegrable m volume a c :=
    intervalIntegrable_bounded_source_expectation source hsm B hB a c
  have hmC : Continuous (fun t : ℝ=>∫s in (0:ℝ)..t,m s) :=
    intervalIntegral.continuous_primitive hi 0
  have hF := continuous_ito_bounded_observable_expectation (P:=P) (V:=V) hc.continuous_state hc.adapted_state
    f hf M hM
  have hL : Tendsto L atTop (𝓝 l) := by
    simpa only [Real.toNNReal_coe] using tendsto_leftCellCrop l.coe_nonneg hlr'
  have hR : Tendsto R atTop (𝓝 r) := by
    simpa only [Real.toNNReal_coe] using tendsto_rightCellCrop l.coe_nonneg hlr'
  have hI : Tendsto (fun n=>∫t in (L n:ℝ)..(R n:ℝ),m t) atTop
      (𝓝 (∫t in (l:ℝ)..(r:ℝ),m t)) := by
    have hr := hmC.tendsto r |>.comp (NNReal.continuous_coe.tendsto r |>.comp hR)
    have hl := hmC.tendsto l |>.comp (NNReal.continuous_coe.tendsto l |>.comp hL)
    have he (a c : ℝ) : (∫t in a..c,m t)=
        (∫t in (0:ℝ)..c,m t)-(∫t in (0:ℝ)..a,m t) := by
      linarith [intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a c)]
    rw [he]
    exact (hr.sub hl).congr (fun n=>(he (L n) (R n)).symm)
  have he (n : ℕ) : (∫ω,f (R n) (X (R n) ω)∂P)-
      (∫ω,f (L n) (X (L n) ω)∂P)=∫t in (L n:ℝ)..(R n:ℝ),m t := by
    obtain ⟨hLr,hLR,hRr⟩:=cellCrop_bounds l.coe_nonneg hlr' n
    apply ito_expectation_local_source hc f ft fx fxx 0 b hf hft hfx hfxx ht hx hxx hC2
      K M hK (fun t _ x=>hM t x) source hsm B hB (L n) (R n)
      (l.coe_nonneg.trans_lt hLr) hLR (hRr.trans hrb)
    intro ω t htt
    exact hsource ω t ⟨(l.coe_nonneg.trans_lt hLr).trans_le htt.1,
      htt.2.trans_lt (hRr.trans hrb)⟩
  exact tendsto_nhds_unique ((hF.tendsto r |>.comp hR).sub
    (hF.tendsto l |>.comp hL)) (hI.congr (fun n=>(he n).symm))

end FourPapersCommon
