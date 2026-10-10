module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral

@[expose] public section

/-! Passage through the actual recursive attachment weight. Every
retained vertex coefficient and every halfclosed Stieltjes edge integral
is retained explicitly. Concrete marked-law limits supply these inputs
in the subsequent source-term applications. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem tendsto_nativeStreamingOriginWeightIntegral
    {L : Type*} {l : Filter L}
    (μN : L → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (sN : L → ℝ) (s : ℝ) (hs : Tendsto sN l (𝓝 s))
    (ΦN : L → NativeStreamingOrigin T → ℝ) (Φ : NativeStreamingOrigin T → ℝ)
    (hCDF : ∀i, i ≤ j → Tendsto (fun N => Paper.parisiCDF (μN N) (q i)) l
      (𝓝 (Paper.parisiCDF μ (q i))))
    (hvertex : ∀v : FiniteCascadeRecordVertex T,
      Tendsto (fun N => ΦN N (.vertex v)) l (𝓝 (Φ (.vertex v))))
    (hedge : ∀e : NativeStreamingEdge T,
      Tendsto (fun N => ∫r in Ioc (q (e.depth+1)) (q e.depth),
        ΦN N (.edge e r) ∂parisiFreeMeasure (μN N) a) l
      (𝓝 (∫r in Ioc (q (e.depth+1)) (q e.depth),
        Φ (.edge e r) ∂parisiFreeMeasure μ a))) :
    Tendsto (fun N => nativeStreamingOriginWeightIntegral (μN N) a q T (sN N) (ΦN N)) l
      (𝓝 (nativeStreamingOriginWeightIntegral μ a q T s Φ)) := by
  induction T generalizing sN s with
  | leaf =>
      exact (tendsto_const_nhds.sub hs).mul (hvertex (.root .leaf))
  | @advance j T ih =>
      have hT := ih (fun N => Paper.parisiCDF (μN N) (q j))
        (Paper.parisiCDF μ (q j)) (hCDF j (Nat.le_succ j))
        (fun N o => ΦN N (nativeStreamingOriginChild o))
        (fun o => Φ (nativeStreamingOriginChild o))
        (fun i hi => hCDF i (hi.trans (Nat.le_succ j)))
        (fun v => hvertex (.child v)) (fun e => hedge (.child e))
      exact (hT.add (hedge (.here T))).add
        ((hCDF (j+1) le_rfl |>.sub hs).mul (hvertex (.root T.advance)))
  | @fork j T U ihT ihU =>
      have hT := ihT (fun N => Paper.parisiCDF (μN N) (q j))
        (Paper.parisiCDF μ (q j)) (hCDF j le_rfl)
        (fun N o => ΦN N (nativeStreamingOriginLeft o))
        (fun o => Φ (nativeStreamingOriginLeft o)) hCDF
        (fun v => hvertex (.left v)) (fun e => hedge (.left e))
      have hU := ihU (fun N => Paper.parisiCDF (μN N) (q j))
        (Paper.parisiCDF μ (q j)) (hCDF j le_rfl)
        (fun N o => ΦN N (nativeStreamingOriginRight o))
        (fun o => Φ (nativeStreamingOriginRight o)) hCDF
        (fun v => hvertex (.right v)) (fun e => hedge (.right e))
      exact (hT.add hU).add
        (((hCDF j le_rfl).const_mul 2 |>.sub hs).mul
          (hvertex (.root (.fork T U))))

end QuantitativeFollowup
