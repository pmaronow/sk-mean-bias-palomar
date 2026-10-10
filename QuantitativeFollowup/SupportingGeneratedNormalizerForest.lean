module
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponents
public import QuantitativeFollowup.FollowupCavityGeneratedForestReindex
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternNormalizerTerminalRepresentation

@[expose] public section

/-! A true independent binary normalizer component is added to the whole
old native forest. Its observable retains every old terminal spin and
mark coordinate jointly, without a per-component factorization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {I : Type*} [Fintype I] {n m : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def printedGeneratedNormalizerDepth (J : I → ℕ) : I ⊕ Unit → ℕ
  | .inl i => J i
  | .inr _ => 2

def printedGeneratedNormalizerTree (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :
    (k : I ⊕ Unit) → FiniteTerminalGenealogy (printedGeneratedNormalizerDepth J k)
  | .inl i => T i
  | .inr _ => anisotropicBinaryObservationTree

def printedGeneratedNormalizerClock (q : I → ℕ → Paper.Overlap) (r : Paper.Overlap) :
    I ⊕ Unit → ℕ → Paper.Overlap
  | .inl i => q i
  | .inr _ => anisotropicBinaryObservationSchedule r

def printedGeneratedNormalizerOldRecord (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i))
    (z : CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerDepth J)
      (printedGeneratedNormalizerTree J T)) : CavityGeneratedForestRecord (n:=n) J T :=
  fun i => z (.inl i)

def printedGeneratedNormalizerNewRecord (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i))
    (z : CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerDepth J)
      (printedGeneratedNormalizerTree J T)) :
    AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
        anisotropicBinaryObservationTree := z (.inr ())

theorem printedGeneratedNormalizerForest_product_expectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap) (r : Paper.Overlap)
    (F : CavityGeneratedForestRecord (n:=n) J T → ℝ) :
    (∫z, F (printedGeneratedNormalizerOldRecord J T z)*
        nativeStreamingNormalizerBinaryTerminalTest n r
          (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
            (printedGeneratedNormalizerNewRecord J T z).2)
      ∂cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerDepth J)
        (printedGeneratedNormalizerTree J T) (printedGeneratedNormalizerClock q r)) =
      (∫z, F z ∂cavityGeneratedNativeForestLaw D μ a J T q)*
        nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule r)
          anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n r) := by
  let η : (k : I ⊕ Unit) → Measure
      (AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
          (printedGeneratedNormalizerTree J T k)) := fun k =>
    anisotropicRecordedProfileTreeLaw D μ a (printedGeneratedNormalizerClock q r k)
      (printedGeneratedNormalizerTree J T k)
  let K := fun z : AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
        anisotropicBinaryObservationTree =>
    nativeStreamingNormalizerBinaryTerminalTest n r
      (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2)
  have hp := measurePreserving_sumPiEquivProdPi η
  calc
    _ = ∫z : CavityGeneratedForestRecord (n:=n) J T ×
        (Unit → AnisotropicObservationState (n+1) ×
          Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
            anisotropicBinaryObservationTree), F z.1*K (z.2 ())
        ∂(cavityGeneratedNativeForestLaw D μ a J T q).prod
          (Measure.pi (fun _ : Unit => η (.inr ()))) := by
      change (∫z, F (fun i => z (.inl i))*K (z (.inr ())) ∂Measure.pi η) = _
      rw [←hp.symm.integral_comp']
      rfl
    _ = (∫z, F z ∂cavityGeneratedNativeForestLaw D μ a J T q)*
        (∫z, K (z ()) ∂Measure.pi (fun _ : Unit => η (.inr ()))) :=
      integral_prod_mul
        (μ := cavityGeneratedNativeForestLaw D μ a J T q)
        (ν := Measure.pi (fun _ : Unit => η (.inr ()))) F
        (fun z : Unit → AnisotropicObservationState (n+1) ×
            Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
              anisotropicBinaryObservationTree => K (z ()))
    _ = _ := by
      have h := (measurePreserving_funUnique (η (.inr ())) Unit).integral_comp' K
      exact congrArg (fun x : ℝ => (∫z, F z ∂cavityGeneratedNativeForestLaw D μ a J T q)*x) h

theorem printedGeneratedNormalizerForest_terminal_expectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap) (r : Paper.Overlap)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) :
    (∫z, F h (cavityGeneratedForestTerminalProjection J T
          (printedGeneratedNormalizerOldRecord J T z))*
        nativeStreamingNormalizerBinaryTerminalTest n r
          (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
            (printedGeneratedNormalizerNewRecord J T z).2)
      ∂cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerDepth J)
        (printedGeneratedNormalizerTree J T) (printedGeneratedNormalizerClock q r)) =
      (∫σ, F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _))*
        (∫z, cavitySpinOverlapDefect n r z.2.1 z.2.2 ∂anisotropicFreshTerminalPairLaw D μ a r) := by
  rw [printedGeneratedNormalizerForest_product_expectation D μ a J T q r
      (fun z => F h (cavityGeneratedForestTerminalProjection J T z)),
    cavityGeneratedNativeForest_integral_terminal,
    nativeStreamingNormalizer_binary_terminal_expectation]

def printedGeneratedNormalizerAppendedForest (W : CavityGeneratedConstructedForest m) :
    CavityGeneratedConstructedForest (m+1) :=
  (W.reindex Fin.castSucc).appendComponent
    (cavityGeneratedSiblingComponent (Fin.last m) (.fork .single .single))

theorem printedGeneratedNormalizerAppendedForest_old_component
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    (printedGeneratedNormalizerAppendedForest W).component c.castSucc =
      (W.reindex Fin.castSucc).component c :=
  (W.reindex Fin.castSucc).appendComponent_old _ c

theorem printedGeneratedNormalizerAppendedForest_new_component
    (W : CavityGeneratedConstructedForest m) :
    (printedGeneratedNormalizerAppendedForest W).component (Fin.last W.componentCount) =
      cavityGeneratedSiblingComponent (Fin.last m) (.fork .single .single) :=
  (W.reindex Fin.castSucc).appendComponent_new _

theorem printedGeneratedNormalizerAppendedForest_old_clock
    (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (c : Fin W.componentCount) :
    (W.reindex Fin.castSucc).clockTemplate.clock (Fin.snoc h r) c =
      W.clockTemplate.clock h c :=
  W.reindex_clock Fin.castSucc h (Fin.snoc h r) (fun i => by simp only [Fin.snoc_castSucc]) c

end QuantitativeFollowup
