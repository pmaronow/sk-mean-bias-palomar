module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! True Fubini for the recursive Stieltjes attachment weight.  The
hypotheses are ordinary integrability of each actual vertex section and
joint edge section, rather than an integral interchange conclusion.
This is used for cross and future source terms, retaining all atoms. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

 theorem nativeStreamingOriginWeightIntegral_parameter_fubini
    {X : Type*} [MeasurableSpace X] (m : Measure X) [SFinite m]
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (Φ : X → NativeStreamingOrigin T → ℝ)
    (hvertex : ∀v : FiniteCascadeRecordVertex T,
      Integrable (fun x => Φ x (.vertex v)) m)
    (hedge : ∀e : NativeStreamingEdge T,
      Integrable (fun z : X × Paper.Overlap => Φ z.1 (.edge e z.2))
        (m.prod ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))) :
    Integrable (fun x => nativeStreamingOriginWeightIntegral μ a q T s (Φ x)) m ∧
      (∫x, nativeStreamingOriginWeightIntegral μ a q T s (Φ x) ∂m) =
        nativeStreamingOriginWeightIntegral μ a q T s (fun o => ∫x, Φ x o ∂m) := by
  induction T generalizing s with
  | leaf =>
      refine ⟨(hvertex (.root .leaf)).const_mul _, ?_⟩
      exact integral_const_mul _ _
  | @advance j T ih =>
      have ht := ih (Paper.parisiCDF μ (q j))
        (fun x o => Φ x (nativeStreamingOriginChild o))
        (fun v => hvertex (.child v)) (fun e => hedge (.child e))
      have he := hedge (.here T)
      have hv := (hvertex (.root T.advance)).const_mul (Paper.parisiCDF μ (q (j+1))-s)
      refine ⟨(ht.1.add he.integral_prod_left).add hv, ?_⟩
      change (∫x, nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Φ x (nativeStreamingOriginChild o)) +
        (∫r in Ioc (q (j+1)) (q j), Φ x (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-s)*Φ x (.vertex (.root T.advance)) ∂m) = _
      rw [integral_add, integral_add, ht.2,
        integral_integral_swap he, integral_const_mul]
      · exact ht.1
      · exact he.integral_prod_left
      · exact ht.1.add he.integral_prod_left
      · exact hv
  | @fork j T U ihT ihU =>
      have ht := ihT (Paper.parisiCDF μ (q j))
        (fun x o => Φ x (nativeStreamingOriginLeft o))
        (fun v => hvertex (.left v)) (fun e => hedge (.left e))
      have hu := ihU (Paper.parisiCDF μ (q j))
        (fun x o => Φ x (nativeStreamingOriginRight o))
        (fun v => hvertex (.right v)) (fun e => hedge (.right e))
      have hv := (hvertex (.root (.fork T U))).const_mul (2*Paper.parisiCDF μ (q j)-s)
      refine ⟨(ht.1.add hu.1).add hv, ?_⟩
      change (∫x, nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Φ x (nativeStreamingOriginLeft o)) +
        nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
        (fun o => Φ x (nativeStreamingOriginRight o)) +
        (2*Paper.parisiCDF μ (q j)-s)*Φ x (.vertex (.root (.fork T U))) ∂m) = _
      rw [integral_add, integral_add, ht.2, hu.2, integral_const_mul]
      · exact ht.1
      · exact hu.1
      · exact ht.1.add hu.1
      · exact hv

end QuantitativeFollowup
