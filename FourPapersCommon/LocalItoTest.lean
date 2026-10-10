module
public import FRSB.InteriorTimeCap
public import FRSB.ItoExpectationSource

@[expose] public section

/-! Genuine interior-capped Itô tests require spatial regularity only on
their actual open strip. This allows the local continuous-CDF PDE to be
used without asserting regularity across unrelated CDF jumps. -/
noncomputable section
open Set MeasureTheory Filter StochasticCalculus Paper FRSB
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 500000

theorem interiorCappedTest_regular_local (f ft fx fxx : ℝ→ℝ→ℝ)
    (a l r b : ℝ) (hal : a<l) (hlr : l≤r) (hrb : r<b)
    (hf : Continuous (fun p : ℝ×ℝ=>f p.1 p.2))
    (hft : ContinuousOn (fun p : ℝ×ℝ=>ft p.1 p.2) (Ioo a b×ˢuniv))
    (hfx : Continuous (fun p : ℝ×ℝ=>fx p.1 p.2))
    (hfxx : Continuous (fun p : ℝ×ℝ=>fxx p.1 p.2))
    (ht : ∀t∈Ioo a b,∀x,HasDerivAt (fun s=>f s x) (ft t x) t)
    (hx : ∀t∈Ioo a b,∀x,HasDerivAt (f t) (fx t x) x)
    (hxx : ∀t∈Ioo a b,∀x,HasDerivAt (fx t) (fxx t x) x)
    (hC2 : ∀t∈Ioo a b,ContDiff ℝ 2 (f t)) :
    Continuous (fun p : ℝ×ℝ=>interiorCappedTest f a l r b p.1 p.2) ∧
    (∀x,Differentiable ℝ (fun t=>interiorCappedTest f a l r b t x)) ∧
    (∀t,ContDiff ℝ 2 (interiorCappedTest f a l r b t)) ∧
    Continuous (fun p : ℝ×ℝ=>itoTimeDerivative (interiorCappedTest f a l r b) p.1 p.2) ∧
    Continuous (fun p : ℝ×ℝ=>itoSpaceDerivative (interiorCappedTest f a l r b) p.1 p.2) ∧
    Continuous (fun p : ℝ×ℝ=>itoSpaceSecondDerivative (interiorCappedTest f a l r b) p.1 p.2) := by
  have hm : Continuous (fun p : ℝ×ℝ=>(interiorTimeCap a l r b p.1,p.2)) := by fun_prop
  have hmem (t : ℝ) := interiorTimeCap_mem a l r b hal hlr hrb t
  have he (t x : ℝ) : itoSpaceDerivative (interiorCappedTest f a l r b) t x=
      fx (interiorTimeCap a l r b t) x := (hx _ (hmem t) x).deriv
  have he2 (t x : ℝ) : itoSpaceSecondDerivative (interiorCappedTest f a l r b) t x=
      fxx (interiorTimeCap a l r b t) x := by
    unfold itoSpaceSecondDerivative
    have hfun : deriv (interiorCappedTest f a l r b t)=fx (interiorTimeCap a l r b t) :=
      funext (fun y=>he t y)
    rw [hfun]
    exact (hxx _ (hmem t) x).deriv
  refine ⟨hf.comp hm,interiorCappedTest_differentiable_time f ft a l r b hal hlr hrb ht,
    fun t=>hC2 _ (hmem t),?_,?_,?_⟩
  · simp_rw [interiorCappedTest_timeDerivative f ft a l r b hal hlr hrb ht]
    apply (hft.comp_continuous hm (fun p=>⟨hmem p.1,mem_univ _⟩)).mul
    exact (continuous_interiorTimeCapD a l r b).comp continuous_fst
  · simp_rw [he]
    exact hfx.comp hm
  · simp_rw [he2]
    exact hfxx.comp hm

theorem ito_expectation_local_source {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0→Ω→ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f ft fx fxx : ℝ→ℝ→ℝ) (a b : ℝ)
    (hf : Continuous (fun p : ℝ×ℝ=>f p.1 p.2))
    (hft : ContinuousOn (fun p : ℝ×ℝ=>ft p.1 p.2) (Ioo a b×ˢuniv))
    (hfx : Continuous (fun p : ℝ×ℝ=>fx p.1 p.2))
    (hfxx : Continuous (fun p : ℝ×ℝ=>fxx p.1 p.2))
    (ht : ∀t∈Ioo a b,∀x,HasDerivAt (fun s=>f s x) (ft t x) t)
    (hx : ∀t∈Ioo a b,∀x,HasDerivAt (f t) (fx t x) x)
    (hxx : ∀t∈Ioo a b,∀x,HasDerivAt (fx t) (fxx t x) x)
    (hC2 : ∀t∈Ioo a b,ContDiff ℝ 2 (f t))
    (K M : ℝ≥0) (hK : ∀t∈Ioo a b,∀x,‖fx t x‖≤K)
    (hM : ∀t∈Ioo a b,∀x,‖f t x‖≤M)
    (source : ℝ→Ω→ℝ) (hsm : Measurable (Function.uncurry source))
    (B : ℝ) (hB : ∀ (t : ℝ) (ω : Ω),‖source t ω‖≤B)
    (l r : ℝ≥0) (hal : a<(l:ℝ)) (hlr : l≤r) (hrb : (r:ℝ)<b)
    (hsource : ∀ω,∀t∈Icc (l:ℝ) (r:ℝ),
      ft t (X t.toNNReal ω)+fx t (X t.toNNReal ω)*d t.toNNReal ω+
        (1/2:ℝ)*fxx t (X t.toNNReal ω)*β^2=source t ω) :
    (∫ω,f r (X r ω)∂P)-(∫ω,f l (X l ω)∂P)=
      ∫t in (l:ℝ)..(r:ℝ),∫ω,source t ω∂P := by
  let g:=interiorCappedTest f a l r b
  have hlrR:=NNReal.coe_le_coe.mpr hlr
  obtain ⟨hgc,hgt,hgs,hgdt,hgx,hgxx⟩:=interiorCappedTest_regular_local
    f ft fx fxx a l r b hal hlrR hrb hf hft hfx hfxx ht hx hxx hC2
  have hmem (t : ℝ):=interiorTimeCap_mem a l r b hal hlrR hrb t
  have hge (t x : ℝ) : itoSpaceDerivative g t x=fx (interiorTimeCap a l r b t) x :=
    (hx _ (hmem t) x).deriv
  have hge2 (t x : ℝ) : itoSpaceSecondDerivative g t x=fxx (interiorTimeCap a l r b t) x := by
    unfold itoSpaceSecondDerivative
    rw [show deriv (g t)=fx (interiorTimeCap a l r b t) from funext fun y=>hge t y]
    exact (hxx _ (hmem t) x).deriv
  have hgi (t : ℝ≥0) : Integrable (fun ω=>g t (X t ω)) P := by
    have hXm : Measurable (X t) := ((hc.adapted_state t).mono (V.le t)).measurable
    apply (integrable_const (M:ℝ)).mono' (hgc.measurable.comp
      (measurable_const.prodMk hXm)).aestronglyMeasurable
    exact .of_forall fun ω=>hM _ (hmem t) _
  have hh:=ito_expectation_source_error hc g hgc hgt hgs hgdt hgx hgxx l r hlr K
    (fun t _ x=>by rw [hge];exact hK _ (hmem t) x)
    source hsm B hB (fun _=>0) intervalIntegrable_const (by
      intro ω t htr
      unfold hjbGenerator
      rw [interiorCappedTest_timeDerivative f ft a l r b hal hlrR hrb ht,hge,hge2,
        interiorTimeCap_eq _ _ _ _ _ htr,interiorTimeCapD_eq _ _ _ _ _ htr,mul_one,
        hsource ω t htr,sub_self,norm_zero]) (hgi l) (hgi r)
  simp only [intervalIntegral.integral_zero] at hh
  have heval (t : ℝ≥0) (htt : (t:ℝ)∈Icc (l:ℝ) (r:ℝ)) :
      (fun ω=>g t (X t ω))=(fun ω=>f t (X t ω)) := by
    funext ω
    simp only [g,interiorCappedTest,interiorTimeCap_eq _ _ _ _ _ htt]
  rw [heval l ⟨le_rfl,hlrR⟩,heval r ⟨hlrR,le_rfl⟩] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

end FourPapersCommon
