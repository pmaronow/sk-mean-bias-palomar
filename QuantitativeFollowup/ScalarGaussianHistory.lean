module
public import QuantitativePaper.VectorHistoryLinear
public import FRSB.FiniteForwardLaw

@[expose] public section

/-! The actual scalar Brownian finite tuple is the pushforward of one
standard Euclidean Gaussian by an explicit continuous linear history map.
This includes repeated times and zero variances, without inverting a
covariance matrix or assuming a finite-dimensional Gaussian law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def scalarGaussianHistoryUpdate (β : ℝ) (T : ℕ → ℝ≥0) (i : ℕ) :
    (ℝ×ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ+
    Real.sqrt (β^2*((T (i+1):ℝ)-T i)) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem scalarGaussianHistoryUpdate_apply (β : ℝ) (T : ℕ → ℝ≥0) (i : ℕ) (x z : ℝ) :
    scalarGaussianHistoryUpdate β T i (x,z)=x+Real.sqrt (β^2*((T (i+1):ℝ)-T i))*z := rfl

def scalarGaussianHistoryInput (n : ℕ) : Field n →L[ℝ] (ℝ×(Fin n→ℝ)) :=
  (0 : Field n →L[ℝ] ℝ).prod
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).toContinuousLinearMap

def scalarGaussianHistoryLinear (β : ℝ) (T : ℕ → ℝ≥0) (n : ℕ) :
    Field n →L[ℝ] (Fin (n+1)→ℝ) :=
  (independentHistoryLinear (scalarGaussianHistoryUpdate β T) n).comp (scalarGaussianHistoryInput n)

theorem scalarGaussianHistoryLinear_apply (β : ℝ) (T : ℕ → ℝ≥0) (n : ℕ) (z : Field n) :
    scalarGaussianHistoryLinear β T n z=
      independentHistory (fun i x w => x+Real.sqrt (β^2*((T (i+1):ℝ)-T i))*w) n
        (0,WithLp.ofLp z) := by
  rw [scalarGaussianHistoryLinear,ContinuousLinearMap.comp_apply,independentHistoryLinear_apply]
  rfl

theorem scalarGaussianHistoryInput_map (n : ℕ) :
    (fieldGaussian n).map (scalarGaussianHistoryInput n)=
      (Measure.dirac (0 : ℝ)).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  rw [Measure.dirac_prod]
  have he : (scalarGaussianHistoryInput n : Field n → ℝ×(Fin n→ℝ))=
      (Prod.mk (0 : ℝ)) ∘ WithLp.ofLp := rfl
  rw [he,←Measure.map_map measurable_prodMk_left (by fun_prop)]
  congr 1
  rw [fieldGaussian,SYK.standardGaussianMeasureOnEuclidean,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

theorem scalarGaussianHistoryUpdate_map (β : ℝ) (T : ℕ → ℝ≥0) (hT : Monotone T)
    (i : ℕ) (x : ℝ) :
    (gaussianReal 0 1).map (fun z => scalarGaussianHistoryUpdate β T i (x,z))=
      Paper.gaussianStateKernel (β^2*((T (i+1):ℝ)-T i)).toNNReal x := by
  have hv : 0≤β^2*((T (i+1):ℝ)-T i) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hT (Nat.le_succ i)))
  have hs : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (β^2*((T (i+1):ℝ)-T i))*z)=
      gaussianReal 0 (β^2*((T (i+1):ℝ)-T i)).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.coe_injective
      simp only [NNReal.coe_mk,mul_one,
        Real.coe_toNNReal _ hv,Real.sq_sqrt hv]
  have he : (fun z => scalarGaussianHistoryUpdate β T i (x,z))=
      (fun z : ℝ => x+z) ∘ (fun z : ℝ => Real.sqrt (β^2*((T (i+1):ℝ)-T i))*z) := rfl
  rw [he,←Measure.map_map (by fun_prop) (by fun_prop),hs,gaussianReal_map_const_add]
  simp only [zero_add,Paper.gaussianStateKernel_apply]

theorem scalarGaussianHistoryLinear_law (β : ℝ) (T : ℕ → ℝ≥0) (hT : Monotone T) (n : ℕ) :
    (fieldGaussian n).map (scalarGaussianHistoryLinear β T n)=
      FourPapersCommon.finiteHistoryLaw (Measure.dirac 0)
        (fun i => Paper.gaussianStateKernel (β^2*((T (i+1):ℝ)-T i)).toNNReal) n := by
  rw [scalarGaussianHistoryLinear,ContinuousLinearMap.coe_comp,
    ←Measure.map_map (independentHistoryLinear _ _).measurable
    (scalarGaussianHistoryInput n).measurable,scalarGaussianHistoryInput_map]
  have he : independentHistoryLinear (scalarGaussianHistoryUpdate β T) n=
      independentHistory (fun i x z => scalarGaussianHistoryUpdate β T i (x,z)) n :=
    funext (independentHistoryLinear_apply _ _)
  rw [he]
  exact independentHistory_law (Measure.dirac 0) (gaussianReal 0 1)
    (fun i x z => scalarGaussianHistoryUpdate β T i (x,z))
    (fun i => (scalarGaussianHistoryUpdate β T i).measurable)
    (fun i => Paper.gaussianStateKernel (β^2*((T (i+1):ℝ)-T i)).toNNReal)
    (fun _ => inferInstance) (fun i x => (scalarGaussianHistoryUpdate_map β T hT i x).symm) n

theorem scalar_finiteHistoryLaw_eq_frsb (ν : Measure ℝ) (κ : ℕ → Kernel ℝ ℝ) (n : ℕ) :
    FourPapersCommon.finiteHistoryLaw ν κ n=FRSB.finiteHistoryLaw ν κ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FourPapersCommon.finiteHistoryLaw,FRSB.finiteHistoryLaw,ih]
    rfl

/-- An actual map-of-probability-laws identity for the full scalar Brownian
record, including the deterministic initial coordinate. -/
theorem scaledBrownian_history_eq_gaussianLinear (β : ℝ) (T : ℕ → ℝ≥0)
    (hT : Monotone T) (h0 : T 0=0) (n : ℕ) :
    Paper.canonicalBrownianMeasure.map
      (FRSB.historySample (fun r ω => β*Paper.canonicalBrownian r ω) T n)=
      (fieldGaussian n).map (scalarGaussianHistoryLinear β T n) := by
  rw [FRSB.scaledBrownian_historyLaw β T hT,scalarGaussianHistoryLinear_law β T hT,
    scalar_finiteHistoryLaw_eq_frsb]
  congr 1
  simp only [h0,Paper.canonicalBrownian_zero,mul_zero,Measure.map_const,measure_univ,one_smul]

end QuantitativeFollowup
