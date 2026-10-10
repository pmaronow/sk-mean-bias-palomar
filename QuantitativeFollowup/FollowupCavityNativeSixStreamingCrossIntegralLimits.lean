module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginIntegralLimits
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFubini

@[expose] public section

/-! Passage for two recursive genuine Stieltjes attachment weights.
The four kinds of actual vertex/edge sections are retained individually;
joint edge integrability discharges every Fubini interchange internally. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

 theorem tendsto_nativeStreamingOriginPairWeightIntegral
    {L : Type*} {l : Filter L}
    (μN : L → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j k : ℕ}
    (T : FiniteTerminalGenealogy j) (U : FiniteTerminalGenealogy k)
    (sN tN : L → ℝ) (s t : ℝ) (hs : Tendsto sN l (𝓝 s))
    (ht : Tendsto tN l (𝓝 t))
    (ΦN : L → NativeStreamingOrigin T → NativeStreamingOrigin U → ℝ)
    (Φ : NativeStreamingOrigin T → NativeStreamingOrigin U → ℝ)
    (hCDFT : ∀i, i≤j → Tendsto (fun N => Paper.parisiCDF (μN N) (q i)) l
      (𝓝 (Paper.parisiCDF μ (q i))))
    (hCDFU : ∀i, i≤k → Tendsto (fun N => Paper.parisiCDF (μN N) (q i)) l
      (𝓝 (Paper.parisiCDF μ (q i))))
    (hVV : ∀v : FiniteCascadeRecordVertex T, ∀w : FiniteCascadeRecordVertex U,
      Tendsto (fun N => ΦN N (.vertex v) (.vertex w)) l
        (𝓝 (Φ (.vertex v) (.vertex w))))
    (hVE : ∀v : FiniteCascadeRecordVertex T, ∀f : NativeStreamingEdge U,
      Tendsto (fun N => ∫r in Ioc (q (f.depth+1)) (q f.depth),
        ΦN N (.vertex v) (.edge f r) ∂parisiFreeMeasure (μN N) a) l
      (𝓝 (∫r in Ioc (q (f.depth+1)) (q f.depth),
        Φ (.vertex v) (.edge f r) ∂parisiFreeMeasure μ a)))
    (hEV : ∀e : NativeStreamingEdge T, ∀w : FiniteCascadeRecordVertex U,
      Tendsto (fun N => ∫r in Ioc (q (e.depth+1)) (q e.depth),
        ΦN N (.edge e r) (.vertex w) ∂parisiFreeMeasure (μN N) a) l
      (𝓝 (∫r in Ioc (q (e.depth+1)) (q e.depth),
        Φ (.edge e r) (.vertex w) ∂parisiFreeMeasure μ a)))
    (hEE : ∀e : NativeStreamingEdge T, ∀f : NativeStreamingEdge U,
      Tendsto (fun N => ∫l' in Ioc (q (f.depth+1)) (q f.depth),
        ∫r in Ioc (q (e.depth+1)) (q e.depth), ΦN N (.edge e r) (.edge f l')
          ∂parisiFreeMeasure (μN N) a ∂parisiFreeMeasure (μN N) a) l
      (𝓝 (∫l' in Ioc (q (f.depth+1)) (q f.depth),
        ∫r in Ioc (q (e.depth+1)) (q e.depth), Φ (.edge e r) (.edge f l')
          ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)))
    (hiEVN : ∀N, ∀e : NativeStreamingEdge T, ∀w : FiniteCascadeRecordVertex U,
      Integrable (fun r => ΦN N (.edge e r) (.vertex w))
        ((parisiFreeMeasure (μN N) a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
    (hiEEN : ∀N, ∀e : NativeStreamingEdge T, ∀f : NativeStreamingEdge U,
      Integrable (fun z : Paper.Overlap × Paper.Overlap => ΦN N (.edge e z.1) (.edge f z.2))
        (((parisiFreeMeasure (μN N) a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure (μN N) a).restrict (Ioc (q (f.depth+1)) (q f.depth)))))
    (hiEV : ∀e : NativeStreamingEdge T, ∀w : FiniteCascadeRecordVertex U,
      Integrable (fun r => Φ (.edge e r) (.vertex w))
        ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
    (hiEE : ∀e : NativeStreamingEdge T, ∀f : NativeStreamingEdge U,
      Integrable (fun z : Paper.Overlap × Paper.Overlap => Φ (.edge e z.1) (.edge f z.2))
        (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth))))) :
    Tendsto (fun N => nativeStreamingOriginWeightIntegral (μN N) a q T (sN N)
      (fun o => nativeStreamingOriginWeightIntegral (μN N) a q U (tN N) (ΦN N o))) l
      (𝓝 (nativeStreamingOriginWeightIntegral μ a q T s
        (fun o => nativeStreamingOriginWeightIntegral μ a q U t (Φ o)))) := by
  apply tendsto_nativeStreamingOriginWeightIntegral μN μ a q T sN s hs _ _ hCDFT
  · intro v
    exact tendsto_nativeStreamingOriginWeightIntegral μN μ a q U tN t ht _ _ hCDFU
      (hVV v) (hVE v)
  · intro e
    have H := tendsto_nativeStreamingOriginWeightIntegral μN μ a q U tN t ht
      (fun N o => ∫r in Ioc (q (e.depth+1)) (q e.depth),
        ΦN N (.edge e r) o ∂parisiFreeMeasure (μN N) a)
      (fun o => ∫r in Ioc (q (e.depth+1)) (q e.depth),
        Φ (.edge e r) o ∂parisiFreeMeasure μ a) hCDFU (hEV e) (hEE e)
    have hlim := nativeStreamingOriginWeightIntegral_parameter_fubini
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))
      μ a q U t (fun r o => Φ (.edge e r) o) (hiEV e) (hiEE e)
    rw [←hlim.2] at H
    apply H.congr'
    exact .of_forall fun N =>
      (nativeStreamingOriginWeightIntegral_parameter_fubini
        ((parisiFreeMeasure (μN N) a).restrict (Ioc (q (e.depth+1)) (q e.depth)))
        (μN N) a q U (tN N) (fun r o => ΦN N (.edge e r) o)
        (hiEVN N e) (hiEEN N e)).2.symm

end QuantitativeFollowup
