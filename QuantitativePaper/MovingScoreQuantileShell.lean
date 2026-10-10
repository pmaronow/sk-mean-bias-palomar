module
public import QuantitativePaper.QuantileDiameterBounds
public import QuantitativePaper.ScoreRefinedQuantileShell
public import FourPapersCommon.DyadicQuantileShells
public import FourPapersCommon.MovingCutoffPowers

@[expose] public section

/-! The literal terminal-spin score variance on each actual moving dyadic quantile shell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_moving_score_quantile_shell (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (u : ℝ) (hu : 0<u) (hMu : 1≤((n:ℝ)*((1-t)*β^2))*u^2) (j : ℕ) :
    (∫v in dyadicQuantileShell s u j,
      variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
        (vectorMeasureSpinPathLaw μ β t s ht.le))≤
      16384*(((n:ℝ)*((1-t)*β^2))^(-(2/3:ℝ))*u^(-(1/3:ℝ)))*
        ((2:ℝ)^(-(1/3:ℝ)))^j := by
  let M:=(n:ℝ)*((1-t)*β^2)
  let U:=(2:ℝ)^j*u
  let J:=dyadicQuantileShell s u j
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hU : 0<U:=by dsimp only [U];positivity
  have huU : u≤U:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hu.le
  have hMU : 1≤M*U^2:=hMu.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le huU 2) hM.le)
  have hDom : J⊆Ioo (0:ℝ) (1-s):=dyadicQuantileShell_subset s u j
  by_cases hpos : 0<volume.real J
  · have hell:=parisiQuantileImageDiameter_nonneg_of_positive_interval μ s J
      (dyadicQuantileShell_ordConnected s u j) hDom hpos
    have hell1:=parisiQuantileImageDiameter_le_one μ s J hpos
    have hThreshold : ∀ᵐv ∂volume.restrict J,U≤Paper.parisiCDF μ (parisiFreeQuantile μ s v):=by
      filter_upwards [ae_restrict_mem (dyadicQuantileShell_ordConnected s u j).measurableSet] with v hv
      have hL : U-s≤v:=hv.2.1
      exact (by linarith : U ≤ s+v).trans
        (parisiCDF_freeQuantile_lower μ s ⟨hs.1.le,hs.2.le⟩ (Ioo_subset_Ioc_self (hDom hv)))
    have hb:=vector_refined_score_quantile_shell hn μ s β t hβ ht hs hμ hmin J
      (dyadicQuantileShell_ordConnected s u j) hDom (volume.real J) U hpos rfl
      (dyadicQuantileShell_length_le s u hu.le j) hThreshold
    have hpell : (parisiQuantileImageDiameter μ s J)^(2/3:ℝ)≤1:=
      Real.rpow_le_one hell hell1 (by norm_num)
    have hdom:=moving_shell_quarter_dominance M U hM hU hMU
    have hc : 0≤M^(-(2/3:ℝ))*U^(-(1/3:ℝ)):=by positivity
    have hsecond:=mul_le_mul_of_nonneg_left hpell hc
    calc
      _≤8192*(M^(-(3/4:ℝ))*U^(-(1/2:ℝ))+
          M^(-(2/3:ℝ))*U^(-(1/3:ℝ))*(parisiQuantileImageDiameter μ s J)^(2/3:ℝ)):=hb
      _≤16384*(M^(-(2/3:ℝ))*U^(-(1/3:ℝ))):=by linarith
      _=16384*(M^(-(2/3:ℝ))*u^(-(1/3:ℝ)))*((2:ℝ)^(-(1/3:ℝ)))^j:=by
        rw [dyadic_shell_power_identity M u hM hu j]
        ring
  · have hfinite : volume J≠∞:=by
      apply ne_of_lt
      exact (measure_mono hDom).trans_lt (by rw [Real.volume_Ioo];exact ENNReal.ofReal_lt_top)
    have hzero : volume J=0:=by
      have hr : volume.real J=0:=le_antisymm (not_lt.mp hpos) measureReal_nonneg
      have he:=ofReal_measureReal (μ:=volume) (s:=J) hfinite
      rw [hr,ENNReal.ofReal_zero] at he
      exact he.symm
    rw [setIntegral_measure_zero _ hzero]
    positivity

end QuantitativePaper
