module
public import QuantitativeFollowup.SupportingPrintedCoalescedOriginWeights
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket

@[expose] public section

/-! The literal origin functional with open edge cells and actual physical
cluster charges. The generic identity below records callback coherence;
a separate physical consumer discharges it from the actual marked laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def printedNativeOriginWeight (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Φ : NativeStreamingOrigin T → ℝ) : ℝ :=
  nativeCoalescedOriginResidual μ a q T Φ +
    ((parisiFreeMeasure μ a).real {q j} +
      ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j))*
      Φ (.vertex (.root T))

theorem printedNativeOriginWeight_eq_true (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hqj : q j=zeroOverlap)
    (Φ : NativeStreamingOrigin T → ℝ)
    (hΦ : nativeCoalescedOriginCoherent μ a q T Φ) :
    nativeStreamingOriginWeightIntegral μ a q T a Φ =
      printedNativeOriginWeight μ a q T Φ :=
  nativeOriginWeightIntegral_initial_eq_printed_coalesced μ a ha hμ q hq hq0 T hqj Φ hΦ

theorem nativeCoalescedOriginResidual_congr (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Φ Ψ : NativeStreamingOrigin T → ℝ)
    (hV : ∀v, Φ (.vertex v)=Ψ (.vertex v))
    (hE : ∀e r, r∈Ioo (q (e.depth+1)) (q e.depth) →
      Φ (.edge e r)=Ψ (.edge e r)) :
    nativeCoalescedOriginResidual μ a q T Φ =
      nativeCoalescedOriginResidual μ a q T Ψ := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      have hc := ih (fun o => Φ (nativeStreamingOriginChild o))
        (fun o => Ψ (nativeStreamingOriginChild o))
        (fun v => hV (.child v)) (fun e r hr => hE (.child e) r hr)
      simp only [nativeCoalescedOriginResidual]
      rw [hc]
      split_ifs with hz
      · rfl
      · rw [hV (.child (.root T))]
        congr 2
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hE (.here T) r hr
  | @fork j T U ihT ihU =>
      simp only [nativeCoalescedOriginResidual]
      rw [ihT (fun o => Φ (nativeStreamingOriginLeft o))
          (fun o => Ψ (nativeStreamingOriginLeft o))
          (fun v => hV (.left v)) (fun e r hr => hE (.left e) r hr),
        ihU (fun o => Φ (nativeStreamingOriginRight o))
          (fun o => Ψ (nativeStreamingOriginRight o))
          (fun v => hV (.right v)) (fun e r hr => hE (.right e) r hr)]

theorem printedNativeOriginWeight_congr (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Φ Ψ : NativeStreamingOrigin T → ℝ)
    (hV : ∀v, Φ (.vertex v)=Ψ (.vertex v))
    (hE : ∀e r, r∈Ioo (q (e.depth+1)) (q e.depth) →
      Φ (.edge e r)=Ψ (.edge e r)) :
    printedNativeOriginWeight μ a q T Φ = printedNativeOriginWeight μ a q T Ψ := by
  unfold printedNativeOriginWeight
  rw [nativeCoalescedOriginResidual_congr μ a q T Φ Ψ hV hE,hV (.root T)]

def printedNativeSourceSixBracket (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  nativeStreamingSourceOriginalTerm D μ a q T F +
    (-2*∑i : ObservationLeaf T, printedNativeOriginWeight μ a q T
      (fun o => nativeStreamingPatternMoment D μ a q T F (.originalFresh i o))) +
    printedNativeOriginWeight μ a q T (fun o => printedNativeOriginWeight μ a q T
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p))) +
    printedNativeOriginWeight μ a q T (fun o =>
      Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
        nativeStreamingPatternMoment D μ a q T F (.current o)) +
    printedNativeOriginWeight μ a q T (nativeStreamingPatternFutureIntegral D μ a q T F) +
    nativeStreamingSourceNormalizerTerm D μ a q T F

theorem nativeStreamingSourceSixBracket_eq_printed_of_coherence
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1)
    (T : FiniteTerminalGenealogy J) (hqJ : q J=zeroOverlap)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (hf : ∀i, nativeCoalescedOriginCoherent μ a q T
      (fun o => nativeStreamingPatternMoment D μ a q T F (.originalFresh i o)))
    (hv : ∀v, nativeCoalescedOriginCoherent μ a q T
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) p)))
    (he : ∀e r, r∈Ioo (q (e.depth+1)) (q e.depth) →
      nativeCoalescedOriginCoherent μ a q T
        (fun p => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) p)))
    (hcross : nativeCoalescedOriginCoherent μ a q T (fun o =>
      nativeStreamingOriginWeightIntegral μ a q T a
        (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p))))
    (hc : nativeCoalescedOriginCoherent μ a q T (fun o =>
      Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
        nativeStreamingPatternMoment D μ a q T F (.current o)))
    (hfuture : nativeCoalescedOriginCoherent μ a q T
      (nativeStreamingPatternFutureIntegral D μ a q T F)) :
    nativeStreamingSourceSixBracket D μ a q T F =
      printedNativeSourceSixBracket D μ a q T F := by
  have hx : nativeStreamingSourceCrossTerm D μ a q T F =
      printedNativeOriginWeight μ a q T (fun o => printedNativeOriginWeight μ a q T
        (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p))) := by
    unfold nativeStreamingSourceCrossTerm
    rw [printedNativeOriginWeight_eq_true μ a ha hμ q hq hq0 T hqJ _ hcross]
    apply printedNativeOriginWeight_congr
    · intro v
      exact printedNativeOriginWeight_eq_true μ a ha hμ q hq hq0 T hqJ _ (hv v)
    · intro e r hr
      exact printedNativeOriginWeight_eq_true μ a ha hμ q hq hq0 T hqJ _ (he e r hr)
  unfold nativeStreamingSourceSixBracket printedNativeSourceSixBracket
  rw [hx]
  simp only [nativeStreamingSourceOriginalFreshTerm,nativeStreamingSourceCurrentTerm,
    nativeStreamingSourceFutureTerm]
  rw [printedNativeOriginWeight_eq_true μ a ha hμ q hq hq0 T hqJ _ hc,
    printedNativeOriginWeight_eq_true μ a ha hμ q hq hq0 T hqJ _ hfuture]
  congr 5
  apply congrArg (fun x : ℝ => -2*x)
  apply Finset.sum_congr rfl
  intro i hi
  exact printedNativeOriginWeight_eq_true μ a ha hμ q hq hq0 T hqJ _ (hf i)

end QuantitativeFollowup
