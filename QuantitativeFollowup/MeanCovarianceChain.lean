module
public import QuantitativeFollowup.VectorMeanIncrementEndpoints
public import QuantitativePaper.VectorDirectionalDenominator
public import QuantitativePaper.VectorCovarianceQuadraticBounds

@[expose] public section

/-! The literal covariance costs of an earlier-known mean increment and of
the terminal short piece, for an actual minimizing profile. -/
noncomputable section
open MeasureTheory Set QuantitativePaper
open scoped NNReal ENNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vector_covariance_mean_chain_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support)
    (p r u : Paper.Overlap) (hpu : p≤u) (hru : r≤u) (huq : u<q)
    (hgap : (q:ℝ)-r≤2*((q:ℝ)-u)) (hp : 0<Paper.parisiCDF μ p) :
    vectorDirectionCovariance (n:=n) μ β t a ht.le
      (fun sample=>vectorMeasureSpinMean μ β t ht.le u sample-
        vectorMeasureSpinMean μ β t ht.le r sample) q≤
      4*(n:ℝ)/(((1-t)*β^2)*(Paper.parisiCDF μ p)^2) := by
  let b : VectorDisorderBrownianSample n→Field n := fun sample=>vectorMeasureSpinMean μ β t ht.le u sample-vectorMeasureSpinMean μ β t ht.le r sample
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  let c := (1-t)*β^2
  let A := Paper.parisiCDF μ p
  let I := c*∫v in (u:ℝ)..(q:ℝ),(Paper.parisiCDF μ v)^2
  have hc : 0<c := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hca : 0<c*A^2 := mul_pos hc (sq_pos_of_pos hp)
  have hd : 0<(q:ℝ)-u := sub_pos.mpr huq
  have hIl : c*A^2*((q:ℝ)-u)≤I := vectorDirectionDenominator_lower_at μ β t ht.le p u q hpu huq.le
  have hIp : 0<I := (mul_pos hca hd).trans_le hIl
  have hbm : Measurable[vectorBrownianFiltration n (u:ℝ).toNNReal] b :=
    (adapted_vectorMeasureSpinMean μ β t ht.le u).sub
      ((adapted_vectorMeasureSpinMean μ β t ht.le r).mono
        ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hru)) le_rfl)
  have hb2 : MemLp b 2 P :=
    (memLp_vectorMeasureSpinMean μ β t a ht.le u).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r)
  have hdec := vectorDirectionCovariance_decay hn μ β t a hβ ht u q huq.le b hbm hb2 hIp
  have hinc : (∫sample,‖b sample‖^2∂P)≤4*(n:ℝ)*((q:ℝ)-u) := by
    have hmono := vectorMeanOverlap_monotone (n:=n) μ β t a hβ ht huq.le
    have hfull := vector_spinMean_increment_towards_support_full hn μ s hs hμ β t a hβ ht ha hmin q hq r (hru.trans huq.le)
    have hur := vector_spinMean_increment_second_moment hn μ β t a hβ ht r u hru
    have hqr := vector_spinMean_increment_second_moment hn μ β t a hβ ht r q (hru.trans huq.le)
    have hh := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n : (0:ℝ)≤n)
    have hgap' := mul_le_mul_of_nonneg_left hgap (by positivity : 0≤2*(n:ℝ))
    change (∫sample,‖b sample‖^2∂P)=_ at hur
    change (∫sample,‖vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample‖^2∂P)=_ at hqr
    rw [hur]
    linarith
  apply hdec.trans
  apply (div_le_iff₀ hIp).mpr
  calc
    _ ≤ 4*(n:ℝ)*((q:ℝ)-u) := hinc
    _ = (4*(n:ℝ)/(c*A^2))*(c*A^2*((q:ℝ)-u)) := by
      rw [←mul_assoc,div_mul_cancel₀ _ hca.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hIl (div_nonneg (by positivity) hca.le)

theorem vector_covariance_mean_terminal_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support)
    (r : Paper.Overlap) (hrq : r≤q) :
    vectorDirectionCovariance (n:=n) μ β t a ht.le
      (fun sample=>vectorMeasureSpinMean μ β t ht.le q sample-
        vectorMeasureSpinMean μ β t ht.le r sample) q≤2*(n:ℝ)^2*((q:ℝ)-r) := by
  have hdim := vectorDirectionCovariance_le_dimension_moment (n:=n) μ β t a hβ ht q _
    ((memLp_vectorMeasureSpinMean μ β t a ht.le q).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r))
  have hinc := vector_spinMean_increment_towards_support_full hn μ s hs hμ β t a hβ ht ha hmin q hq r hrq
  have hh := mul_le_mul_of_nonneg_left hinc (Nat.cast_nonneg n : (0:ℝ)≤n)
  exact hdim.trans (hh.trans_eq (by ring))

end QuantitativeFollowup
