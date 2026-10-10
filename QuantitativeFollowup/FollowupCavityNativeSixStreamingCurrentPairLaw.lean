module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingContinuationLaw

@[expose] public section

/-! Two current fresh marks are conditionally independent draws from the
true terminal continuation at the actual ancestral state. The enlarged
genealogy retains the complete old record and realizes that product law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingCurrentPairTree (j : ℕ) : FiniteTerminalGenealogy j :=
  .fork (observationLinearTree j) (observationLinearTree j)

def nativeStreamingCurrentPairExtract {E S : Type} (j : ℕ) :
    Records E S (nativeStreamingCurrentPairTree j)→S×S :=
  Prod.map (observationLinearSpin j) (observationLinearSpin j)

theorem nativeStreamingCurrentPairExtract_measurable {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] (j : ℕ) :
    Measurable (nativeStreamingCurrentPairExtract (E:=E) (S:=S) j) :=
  (measurable_observationLinearSpin j).prodMap (measurable_observationLinearSpin j)

theorem nativeStreamingCurrentPairExtract_continuous {E S : Type}
    [TopologicalSpace E] [TopologicalSpace S] (j : ℕ) :
    Continuous (nativeStreamingCurrentPairExtract (E:=E) (S:=S) j) :=
  (nativeStreamingLinearSpin_continuous j).prodMap (nativeStreamingLinearSpin_continuous j)

def nativeStreamingCurrentPairKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    Kernel (AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)
      (Configuration n×Configuration n) :=
  (anisotropicObservationTerminalSpinKernel D μ (q v.depth) ×ₖ
    anisotropicObservationTerminalSpinKernel D μ (q v.depth)).comap
      (Function.uncurry (nativeStreamingVertexState v)) (nativeStreamingVertexState_measurable v)

instance nativeStreamingCurrentPairKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (nativeStreamingCurrentPairKernel D μ q T v) := by
  unfold nativeStreamingCurrentPairKernel
  infer_instance

def nativeStreamingCurrentPairLaw (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :=
  anisotropicRecordedProfileTreeLaw D μ a q T ⊗ₘ nativeStreamingCurrentPairKernel D μ q T v

theorem nativeStreamingActualContinuationKernel_current_pair (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (hzero : q 0=1) (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingActualContinuationKernel D μ q nativeStreamingCurrentPairTree
      nativeStreamingCurrentPairExtract T v=nativeStreamingCurrentPairKernel D μ q T v := by
  have hl:=anisotropicRecordedLinearSpinKernel D μ q hzero v.depth
    (fun i _=>hq (Nat.le_succ i))
  unfold nativeStreamingActualContinuationKernel nativeStreamingCurrentPairKernel
  have hp : (anisotropicRecordedProfileTreeKernel D μ q (nativeStreamingCurrentPairTree v.depth)).map
      (nativeStreamingCurrentPairExtract v.depth)=
      anisotropicObservationTerminalSpinKernel D μ (q v.depth) ×ₖ
        anisotropicObservationTerminalSpinKernel D μ (q v.depth) := by
    change (_ ×ₖ _).map (Prod.map _ _)=_
    rw [←Kernel.map_prod_map _ _ (measurable_observationLinearSpin v.depth)
      (measurable_observationLinearSpin v.depth),hl]
  rw [hp]

theorem nativeStreamingCurrentPairLaw_eq_graft (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (hzero : q 0=1) (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    (anisotropicRecordedProfileTreeLaw D μ a q
      (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)).map
        (fun z=>((z.1,(finiteCascadeContinuationExtract nativeStreamingCurrentPairTree
          nativeStreamingCurrentPairExtract v z.2).1),
          (finiteCascadeContinuationExtract nativeStreamingCurrentPairTree
            nativeStreamingCurrentPairExtract v z.2).2))=
      nativeStreamingCurrentPairLaw D μ a q T v := by
  have hg:=nativeStreamingActualContinuationLaw_eq_graft D μ a q nativeStreamingCurrentPairTree
    nativeStreamingCurrentPairExtract (fun j=>nativeStreamingCurrentPairExtract_measurable j) T v
  unfold nativeStreamingActualContinuationLaw at hg
  rw [nativeStreamingActualContinuationKernel_current_pair D μ q hq hzero T v] at hg
  exact hg

end QuantitativeFollowup
