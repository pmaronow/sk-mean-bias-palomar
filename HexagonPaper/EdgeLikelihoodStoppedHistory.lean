module
public import HexagonPaper.EdgeLikelihoodGaussianHistory

@[expose] public section

/-! Deterministic stopping of the genuine finite chronological edge law.
The density on the enlarged stopped history is the actual prefix density,
pulled back along restriction. No new transition-law premise is introduced.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def edgeHistoryStopExtend {A : Type*} (H N : ℕ) (hHN : H ≤ N) :
    FiniteHistory A H → FiniteHistory A N :=
  fun p i => p ⟨min (i : ℕ) H, by omega⟩

def edgeHistoryStopRestrict {A : Type*} (H N : ℕ) (hHN : H ≤ N) :
    FiniteHistory A N → FiniteHistory A H :=
  fun p i => p ⟨(i : ℕ), by omega⟩

theorem measurable_edgeHistoryStopExtend {A : Type*} [MeasurableSpace A]
    (H N : ℕ) (hHN : H ≤ N) : Measurable (edgeHistoryStopExtend (A:=A) H N hHN) :=
  Measurable.of_eval fun i => measurable_pi_apply _

theorem measurable_edgeHistoryStopRestrict {A : Type*} [MeasurableSpace A]
    (H N : ℕ) (hHN : H ≤ N) : Measurable (edgeHistoryStopRestrict (A:=A) H N hHN) :=
  Measurable.of_eval fun i => measurable_pi_apply _

theorem edgeHistoryStopRestrict_extend {A : Type*} (H N : ℕ) (hHN : H ≤ N)
    (p : FiniteHistory A H) :
    edgeHistoryStopRestrict H N hHN (edgeHistoryStopExtend H N hHN p) = p := by
  funext i
  change p ⟨min (i : ℕ) H, _⟩ = p i
  congr 1
  apply Fin.ext
  exact min_eq_left (by omega)

theorem stopped_history_map_withDensity {A : Type*} [MeasurableSpace A]
    (H N : ℕ) (hHN : H ≤ N) (ν : Measure (FiniteHistory A H))
    (w : FiniteHistory A H → ℝ≥0∞) (hw : Measurable w) :
    (ν.withDensity w).map (edgeHistoryStopExtend H N hHN) =
      (ν.map (edgeHistoryStopExtend H N hHN)).withDensity
        (w ∘ edgeHistoryStopRestrict H N hHN) := by
  have he : (w ∘ edgeHistoryStopRestrict H N hHN) ∘
      edgeHistoryStopExtend H N hHN = w := by
    funext p
    simp only [Function.comp_def, edgeHistoryStopRestrict_extend]
  rw [← map_withDensity_pullback ν (edgeHistoryStopExtend H N hHN)
    (measurable_edgeHistoryStopExtend H N hHN)
    (w ∘ edgeHistoryStopRestrict H N hHN)
    (hw.comp (measurable_edgeHistoryStopRestrict H N hHN))]
  change (ν.withDensity w).map (edgeHistoryStopExtend H N hHN) =
    (ν.withDensity ((w ∘ edgeHistoryStopRestrict H N hHN) ∘
      edgeHistoryStopExtend H N hHN)).map (edgeHistoryStopExtend H N hHN)
  rw [he]

def edgeStoppedPhysicalHistory {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (H N : ℕ) (hHN : H ≤ N) :
    VectorDisorderBrownianSample n → FiniteHistory (AnisotropicParameter n) N :=
  edgeHistoryStopExtend H N hHN ∘ anisotropicFiniteRestartPhysicalHistory D s g q x H

def edgeStoppedReferenceHistory {n k : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (H N : ℕ) (hHN : H ≤ N) :
    VectorDisorderBrownianSample n → FiniteHistory (AnisotropicParameter n) N :=
  edgeHistoryStopExtend H N hHN ∘ edgeReferenceBrownianHistory D s g q x H

theorem edge_stopped_finite_history_likelihood {n k : ℕ}
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (H N : ℕ) (hHN : H ≤ N) (hH : H ≤ k+2) :
    (vectorDisorderBrownianMeasure n).map (edgeStoppedPhysicalHistory D s g q x H N hHN) =
      ((vectorDisorderBrownianMeasure n).map
        (edgeStoppedReferenceHistory D s g q x H N hHN)).withDensity
          (finiteHistoryDensity (edgeRestartFiniteWeight D s q) H ∘
            edgeHistoryStopRestrict H N hHN) := by
  have hw : Measurable (finiteHistoryDensity (edgeRestartFiniteWeight D s q) H) :=
    measurable_finiteHistoryDensity _
      (fun i => measurable_anisotropicFiniteTransitionWeight D
        (vectorClampedScheme s q q.property) (i+1)) H
  rw [edgeStoppedPhysicalHistory, edgeStoppedReferenceHistory,
    ← Measure.map_map (measurable_edgeHistoryStopExtend H N hHN)
      (measurable_anisotropicFiniteRestartPhysicalHistory D s g q x H),
    ← Measure.map_map (measurable_edgeHistoryStopExtend H N hHN)
      (measurable_edgeReferenceBrownianHistory D s g q x H),
    edge_restart_finite_brownian_likelihood D s g q x H hH,
    stopped_history_map_withDensity H N hHN _ _ hw]

end HexagonPaper
