module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFubini
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! Structural parameter differentiation of the genuine Stieltjes
attachment functional. Actual vertex and edge-integral derivatives are
inputs to this supporting reducer; model consumers discharge them using
the true marked laws and endpoint dominated convergence. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_nativeStreamingOriginWeightIntegral_of_components
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (incoming : ℝ)
    (Φ : ℝ→NativeStreamingOrigin T→ℝ) (Ψ : NativeStreamingOrigin T→ℝ)
    (s : Set ℝ) (u : ℝ)
    (hV : ∀v : FiniteCascadeRecordVertex T,
      HasDerivWithinAt (fun t=>Φ t (.vertex v)) (Ψ (.vertex v)) s u)
    (hE : ∀e : NativeStreamingEdge T,
      HasDerivWithinAt (fun t=>∫r in Ioc (q (e.depth+1)) (q e.depth),
        Φ t (.edge e r) ∂parisiFreeMeasure μ a)
      (∫r in Ioc (q (e.depth+1)) (q e.depth), Ψ (.edge e r) ∂parisiFreeMeasure μ a) s u) :
    HasDerivWithinAt (fun t=>nativeStreamingOriginWeightIntegral μ a q T incoming (Φ t))
      (nativeStreamingOriginWeightIntegral μ a q T incoming Ψ) s u := by
  induction T generalizing incoming with
  | leaf => exact (hV (.root .leaf)).const_mul (1-incoming)
  | @advance j T ih =>
      have ht := ih (Paper.parisiCDF μ (q j))
        (fun t o=>Φ t (nativeStreamingOriginChild o))
        (fun o=>Ψ (nativeStreamingOriginChild o))
        (fun v=>hV (.child v)) (fun e=>hE (.child e))
      exact (ht.add (hE (.here T))).add
        ((hV (.root T.advance)).const_mul (Paper.parisiCDF μ (q (j+1))-incoming))
  | @fork j T U ihT ihU =>
      have ht := ihT (Paper.parisiCDF μ (q j))
        (fun t o=>Φ t (nativeStreamingOriginLeft o))
        (fun o=>Ψ (nativeStreamingOriginLeft o))
        (fun v=>hV (.left v)) (fun e=>hE (.left e))
      have hu := ihU (Paper.parisiCDF μ (q j))
        (fun t o=>Φ t (nativeStreamingOriginRight o))
        (fun o=>Ψ (nativeStreamingOriginRight o))
        (fun v=>hV (.right v)) (fun e=>hE (.right e))
      exact (ht.add hu).add
        ((hV (.root (.fork T U))).const_mul (2*Paper.parisiCDF μ (q j)-incoming))

theorem hasDerivWithinAt_nativeStreamingOriginPairWeightIntegral_of_components
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j k : ℕ} (T : FiniteTerminalGenealogy j) (U : FiniteTerminalGenealogy k)
    (incoming otherIncoming : ℝ)
    (Φ : ℝ→NativeStreamingOrigin T→NativeStreamingOrigin U→ℝ)
    (Ψ : NativeStreamingOrigin T→NativeStreamingOrigin U→ℝ)
    (s : Set ℝ) (u : ℝ) (hu : u∈s)
    (hVV : ∀v : FiniteCascadeRecordVertex T,∀w : FiniteCascadeRecordVertex U,
      HasDerivWithinAt (fun t=>Φ t (.vertex v) (.vertex w)) (Ψ (.vertex v) (.vertex w)) s u)
    (hVE : ∀v : FiniteCascadeRecordVertex T,∀f : NativeStreamingEdge U,
      HasDerivWithinAt (fun t=>∫l in Ioc (q (f.depth+1)) (q f.depth),
        Φ t (.vertex v) (.edge f l) ∂parisiFreeMeasure μ a)
      (∫l in Ioc (q (f.depth+1)) (q f.depth),Ψ (.vertex v) (.edge f l)
        ∂parisiFreeMeasure μ a) s u)
    (hEV : ∀e : NativeStreamingEdge T,∀w : FiniteCascadeRecordVertex U,
      HasDerivWithinAt (fun t=>∫r in Ioc (q (e.depth+1)) (q e.depth),
        Φ t (.edge e r) (.vertex w) ∂parisiFreeMeasure μ a)
      (∫r in Ioc (q (e.depth+1)) (q e.depth),Ψ (.edge e r) (.vertex w)
        ∂parisiFreeMeasure μ a) s u)
    (hEE : ∀e : NativeStreamingEdge T,∀f : NativeStreamingEdge U,
      HasDerivWithinAt (fun t=>∫l in Ioc (q (f.depth+1)) (q f.depth),
        ∫r in Ioc (q (e.depth+1)) (q e.depth),Φ t (.edge e r) (.edge f l)
          ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)
      (∫l in Ioc (q (f.depth+1)) (q f.depth),∫r in Ioc (q (e.depth+1)) (q e.depth),
        Ψ (.edge e r) (.edge f l) ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a) s u)
    (hiEV : ∀t∈s,∀e : NativeStreamingEdge T,∀w : FiniteCascadeRecordVertex U,
      Integrable (fun r=>Φ t (.edge e r) (.vertex w))
        ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
    (hiEE : ∀t∈s,∀e : NativeStreamingEdge T,∀f : NativeStreamingEdge U,
      Integrable (fun z : Paper.Overlap×Paper.Overlap=>Φ t (.edge e z.1) (.edge f z.2))
        (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))))
    (hΨEV : ∀e : NativeStreamingEdge T,∀w : FiniteCascadeRecordVertex U,
      Integrable (fun r=>Ψ (.edge e r) (.vertex w))
        ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
    (hΨEE : ∀e : NativeStreamingEdge T,∀f : NativeStreamingEdge U,
      Integrable (fun z : Paper.Overlap×Paper.Overlap=>Ψ (.edge e z.1) (.edge f z.2))
        (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth))))) :
    HasDerivWithinAt (fun t=>nativeStreamingOriginWeightIntegral μ a q T incoming
      (fun o=>nativeStreamingOriginWeightIntegral μ a q U otherIncoming (Φ t o)))
      (nativeStreamingOriginWeightIntegral μ a q T incoming
        (fun o=>nativeStreamingOriginWeightIntegral μ a q U otherIncoming (Ψ o))) s u := by
  apply hasDerivWithinAt_nativeStreamingOriginWeightIntegral_of_components μ a q T incoming
  · intro v
    exact hasDerivWithinAt_nativeStreamingOriginWeightIntegral_of_components μ a q U otherIncoming
      _ _ s u (hVV v) (hVE v)
  · intro e
    have hd := hasDerivWithinAt_nativeStreamingOriginWeightIntegral_of_components μ a q U otherIncoming
      (fun t o=>∫r in Ioc (q (e.depth+1)) (q e.depth),Φ t (.edge e r) o ∂parisiFreeMeasure μ a)
      (fun o=>∫r in Ioc (q (e.depth+1)) (q e.depth),Ψ (.edge e r) o ∂parisiFreeMeasure μ a)
      s u (hEV e) (hEE e)
    have he := nativeStreamingOriginWeightIntegral_parameter_fubini
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))
      μ a q U otherIncoming (fun r o=>Ψ (.edge e r) o) (hΨEV e) (hΨEE e)
    rw [←he.2] at hd
    apply hd.congr_of_mem ?_ hu
    intro t ht
    exact (nativeStreamingOriginWeightIntegral_parameter_fubini
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))
      μ a q U otherIncoming (fun r o=>Φ t (.edge e r) o) (hiEV t ht e) (hiEE t ht e)).2

end QuantitativeFollowup
