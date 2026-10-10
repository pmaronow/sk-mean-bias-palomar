module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternSourceResponse

@[expose] public section

/-! The literal second bracket applies the genuine first source response
to each pattern in the unchanged six-term attachment functional. The mark
measures, original-tree weights, strict future masks and independent
normalizer component remain fixed when the physical parameter varies. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingPatternFutureFunctional
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (Φ : NativeStreamingAttachmentPattern T→ℝ)
    (o : NativeStreamingOrigin T) : ℝ :=
  ∑j∈Finset.range J, ∫l in Ioc (q (j+1)) (q j),
    if nativeStreamingOriginLevel q o<l then Φ (.future o j l) else 0
    ∂parisiFreeMeasure μ a

def nativeStreamingSourceSixFunctional
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (Φ : NativeStreamingAttachmentPattern T→ℝ) : ℝ :=
  (∑i : ObservationLeaf T, ∑k : ObservationLeaf T, Φ (.original i k)) +
  (-2*∑i : ObservationLeaf T, nativeStreamingOriginWeightIntegral μ a q T a
    (fun o=>Φ (.originalFresh i o))) +
  nativeStreamingOriginWeightIntegral μ a q T a (fun o=>
    nativeStreamingOriginWeightIntegral μ a q T a (fun p=>Φ (.cross o p))) +
  nativeStreamingOriginWeightIntegral μ a q T a (fun o=>
    Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*Φ (.current o)) +
  nativeStreamingOriginWeightIntegral μ a q T a
    (nativeStreamingPatternFutureFunctional μ a q T Φ) +
  a*∫l,Φ (.normalizer l) ∂parisiFreeMeasure μ a

def nativeStreamingSourceTermwiseSecondBracket
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) : ℝ :=
  nativeStreamingSourceSixFunctional μ a q T
    (nativeStreamingPatternSourceResponse D μ a q T F)

theorem nativeStreamingSourceSixBracket_eq_pattern_functional
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    nativeStreamingSourceSixBracket D μ a q T F =
      nativeStreamingSourceSixFunctional μ a q T
        (nativeStreamingPatternMoment D μ a q T F) := rfl

theorem nativeStreamingOriginWeightIntegral_const_mul
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (incoming c : ℝ)
    (Φ : NativeStreamingOrigin T→ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T incoming (fun o=>c*Φ o) =
      c*nativeStreamingOriginWeightIntegral μ a q T incoming Φ := by
  induction T generalizing incoming with
  | leaf => simp only [nativeStreamingOriginWeightIntegral]; ring
  | @advance j T ih =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>c*Φ (nativeStreamingOriginChild o)) +
        (∫r in Ioc (q (j+1)) (q j),c*Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-incoming)*(c*Φ (.vertex (.root T.advance))) = _
      rw [ih,integral_const_mul]
      change _=c*(nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>Φ (nativeStreamingOriginChild o)) +
        (∫r in Ioc (q (j+1)) (q j),Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-incoming)*Φ (.vertex (.root T.advance)))
      ring
  | @fork j T U ihT ihU =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>c*Φ (nativeStreamingOriginLeft o)) +
        nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
        (fun o=>c*Φ (nativeStreamingOriginRight o)) +
        (2*Paper.parisiCDF μ (q j)-incoming)*(c*Φ (.vertex (.root (.fork T U)))) = _
      rw [ihT,ihU]
      change _=c*(nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>Φ (nativeStreamingOriginLeft o)) +
        nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
        (fun o=>Φ (nativeStreamingOriginRight o)) +
        (2*Paper.parisiCDF μ (q j)-incoming)*Φ (.vertex (.root (.fork T U))))
      ring

theorem nativeStreamingSourceSixFunctional_const_mul
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (c : ℝ)
    (Φ : NativeStreamingAttachmentPattern T→ℝ) :
    nativeStreamingSourceSixFunctional μ a q T (fun P=>c*Φ P) =
      c*nativeStreamingSourceSixFunctional μ a q T Φ := by
  have hf : nativeStreamingPatternFutureFunctional μ a q T (fun P=>c*Φ P)=
      fun o=>c*nativeStreamingPatternFutureFunctional μ a q T Φ o := by
    funext o
    simp only [nativeStreamingPatternFutureFunctional]
    simp_rw [show ∀j l, (if nativeStreamingOriginLevel q o<l then c*Φ (.future o j l) else 0)=
      c*(if nativeStreamingOriginLevel q o<l then Φ (.future o j l) else 0) by
      intro j l; split_ifs <;> simp]
    simp only [integral_const_mul,Finset.mul_sum]
  simp only [nativeStreamingSourceSixFunctional]
  rw [hf]
  simp_rw [show ∀o, Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*(c*Φ (.current o))=
    c*(Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*Φ (.current o)) by intro o; ring]
  simp_rw [nativeStreamingOriginWeightIntegral_const_mul,integral_const_mul]
  simp_rw [←Finset.mul_sum]
  ring

end QuantitativeFollowup
