module
public import QuantitativePaper.VectorConditionalPairMovingTime
public import QuantitativePaper.VectorTemperatureDefectContinuity

@[expose] public section

/-! The literal raw conditional-pair moment expansion transports the
conditional replica defect. The moving mean moment is an explicit input
to this algebraic continuity leaf. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ} {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
variable {ν : J→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure}
variable {qj : J→Paper.Overlap} {q : Paper.Overlap}
set_option maxHeartbeats 1800000

theorem tendsto_vectorConditionalReplicaDefect_of_weak_and_time_of_mean_limits
    (hn : 0<n) (β t s : ℝ) (hβ : β≠0) (ht : t<1)
    (hν : Tendsto ν l (𝓝 μ)) (hq : Tendsto qj l (𝓝 q))
    (hMean : ∀i : Fin n,Tendsto (fun j=>∫sample,
      vectorBaseMeanProduct (ν j) β t ht.le (qj j) i i sample
        ∂vectorMeasureDisorderTilt (n:=n) (ν j) β t s) l
      (𝓝 (∫sample,vectorBaseMeanProduct μ β t ht.le q i i sample
        ∂vectorMeasureDisorderTilt (n:=n) μ β t s))) :
    Tendsto (fun j=>vectorConditionalReplicaDefect (n:=n) (ν j) β t s ht.le (qj j)) l
      (𝓝 (vectorConditionalReplicaDefect (n:=n) μ β t s ht.le q)) := by
  have hP:=tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _=>tendsto_finsetSum (Finset.univ : Finset (Fin n))
    fun k _=>tendsto_vectorMeasureRawPair_square_of_weak_and_time β t s ht hν hq i k
  have hM:=tendsto_finsetSum Finset.univ fun i _=>hMean i
  have hqr : Tendsto (fun j=>(qj j:ℝ)) l (𝓝 (q:ℝ)):=
    (continuous_subtype_val.tendsto q).comp hq
  have hR:=((hP.const_mul ((1/(n:ℝ))^2)).sub
    ((hqr.const_mul 2).mul (hM.const_mul (1/(n:ℝ))))).add (hqr.pow 2)
  simpa only [vectorConditionalReplicaDefect_eq_second_moment_integrals hn _ β t s hβ ht] using hR

end QuantitativePaper
