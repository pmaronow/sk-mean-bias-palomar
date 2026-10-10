module
public import QuantitativePaper.VectorGradientSquareIdentity
public import QuantitativePaper.VectorMeanOverlapPrimitive

@[expose] public section

/-! Genuine closed-time derivatives of the actual self-overlap. The
literal candidate is identified by the proved finite-cell/measure-limit
integral law, including one-sided derivatives at zero and one. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem vectorMeanOverlapPrimitive_eq (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) {q : ℝ} (hq : q∈Icc (0 : ℝ) 1) :
    vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le q=vectorMeanOverlapReal (n:=n) μ β t a ht.le q := by
  have he:=vectorMeanOverlapReal_interval_integral (n:=n) μ β t a hβ ht
    (r:=0) ⟨le_rfl,zero_le_one⟩ hq
  unfold vectorMeanOverlapPrimitive
  linarith

theorem hasDerivWithinAt_vectorMeanOverlapReal (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) {q : ℝ} (hq : q∈Icc (0 : ℝ) 1) :
    HasDerivWithinAt (vectorMeanOverlapReal (n:=n) μ β t a ht.le)
      (vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc (0 : ℝ) 1 zero_le_one q))
      (Icc (0 : ℝ) 1) q :=
  (hasDerivAt_vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le q).hasDerivWithinAt.congr_of_mem
    (fun r hr=>(vectorMeanOverlapPrimitive_eq (n:=n) μ β t a hβ ht hr).symm) hq

theorem hasDerivAt_vectorMeanOverlapReal (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) {q : ℝ} (hq : q∈Ioo (0 : ℝ) 1) :
    HasDerivAt (vectorMeanOverlapReal (n:=n) μ β t a ht.le)
      (vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc (0 : ℝ) 1 zero_le_one q)) q :=
  (hasDerivWithinAt_vectorMeanOverlapReal (n:=n) μ β t a hβ ht ⟨hq.1.le,hq.2.le⟩).hasDerivAt
    (Icc_mem_nhds hq.1 hq.2)

theorem vectorOverlapPotentialPrimitive_eq_deficit (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) {q : ℝ} (hq : q∈Icc (0 : ℝ) 1) :
    vectorOverlapPotentialPrimitive (n:=n) μ β t a ht.le q=vectorOverlapDeficit (n:=n) μ β t a ht.le q := by
  unfold vectorOverlapPotentialPrimitive vectorOverlapDeficit transportDeficit
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hq.2] at hr
  dsimp only
  rw [vectorMeanOverlapPrimitive_eq μ β t a hβ ht ⟨hq.1.trans hr.1,hr.2⟩]

end QuantitativePaper
