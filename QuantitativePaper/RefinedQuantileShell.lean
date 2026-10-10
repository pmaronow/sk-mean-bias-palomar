module
public import QuantitativeFollowup.VectorQuantileIntervalVariance
public import FourPapersCommon.RefinedShellBound

@[expose] public section

/-! Full original Lemma 3.1. The already proved, stronger follow-up
interval variance theorem implies the source refined shell bound with a
universal numerical constant, for the literal physical law and essential
image diameter, including arbitrary overlap atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem parisiQuantileImageDiameter_nonneg_of_positive_interval
    (μ : Paper.ParisiMeasure) (s : ℝ) (I : Set ℝ) (hI : I.OrdConnected)
    (hDom : I⊆Ioo (0:ℝ) (1-s)) (hv : 0<volume.real I) :
    0≤parisiQuantileImageDiameter μ s I := by
  exact (monotone_essential_diameter_range (fun v=>(parisiFreeQuantile μ s v:ℝ))
    (fun _ _ h=>parisiFreeQuantile_monotone μ s h)
    (fun v=>(parisiFreeQuantile μ s v).property) I hI
    ⟨0,fun v hv=>(hDom hv).1.le⟩
    ⟨1-s,fun v hv=>(hDom hv).2.le⟩ hv).1

theorem vector_refined_quantile_shell (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (J : Set ℝ) (hJ : J.OrdConnected) (hDom : J⊆Ioo (0:ℝ) (1-s))
    (m u : ℝ) (hm : 0 < m) (hlen : volume.real J = m) (hmu : m ≤ u)
    (hThreshold : ∀ᵐv ∂volume.restrict J,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s v)) :
    (∫v in J,variance (vectorSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
      (vectorMeasureSpinPathLaw μ β t s ht.le))≤
      2560*((((n:ℝ)*((1-t)*β^2))^(-(3/4:ℝ)))*u^(-(1/2:ℝ))+
        (((n:ℝ)*((1-t)*β^2))^(-(2/3:ℝ)))*u^(-(1/3:ℝ))*
          (parisiQuantileImageDiameter μ s J)^(2/3:ℝ)) := by
  have hM : 0<(n:ℝ)*((1-t)*β^2):=
    mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hell:=parisiQuantileImageDiameter_nonneg_of_positive_interval μ s J hJ hDom
    (hlen.symm ▸ hm)
  exact (vector_quantile_interval_variance hn μ s β t hβ ht hs hμ hmin J hJ hDom
    m u hm hlen (hm.trans_le hmu) hThreshold).trans
      (refined_shell_bound_from_log_window ((n:ℝ)*((1-t)*β^2)) m u
        (parisiQuantileImageDiameter μ s J) hM hm hmu hell)

end QuantitativePaper
