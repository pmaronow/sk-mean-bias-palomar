module
public import OverlapPaper.ReplicaSourceBranchingEstimate

@[expose] public section

/-! Actual expectation transport through intertwining measurable kernels.
No law or normalized expectation is supplied as a desired conclusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open OverlapPaper

 theorem sourceKernelExpectation_map_intertwining {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (Q : ℕ→Kernel A A) (R : ℕ→Kernel B B) (T : A→B) (hT : Measurable T)
    (n : ℕ) (hmap : ∀i<n,∀x,(Q i x).map T=R i (T x))
    (f : B→ℝ) (hf : Measurable f) (x : A) :
    sourceKernelExpectation Q n (fun y=>f (T y)) x=sourceKernelExpectation R n f (T x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [sourceKernelExpectation]
    have he : (fun y=>sourceKernelExpectation Q n (fun y=>f (T y)) y)=
        fun y=>sourceKernelExpectation R n f (T y) :=
      funext (fun y=>ih (fun i hi=>hmap i (by omega)) y)
    rw [he,←hmap n (by omega) x,
      integral_map hT.aemeasurable (sourceKernelExpectation_measurable R f hf n).aestronglyMeasurable]

end FourPapersCommon
