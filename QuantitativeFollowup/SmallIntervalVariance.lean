module
public import QuantitativeFollowup.SmallIntervalShell
public import QuantitativeFollowup.SmallIntervalDyadicPowers
public import QuantitativeFollowup.SmallIntervalPartition
public import QuantitativePaper.ScoreQuantileVarianceDecomposition

@[expose] public section

/-! Actual localized self-overlap variance summed on its genuine finite
dyadic quantile partition. The final model will discharge localization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def smallIntervalVarianceConstant (K : ℝ) : ℝ :=
  smallIntervalShellConstant K*smallIntervalDyadicConstant

theorem smallIntervalVarianceConstant_pos (K : ℝ) (hK : 0  ≤  K) :
    0<smallIntervalVarianceConstant K := by
  unfold smallIntervalVarianceConstant smallIntervalShellConstant
  exact mul_pos (by positivity) smallIntervalDyadicConstant_pos

theorem smallInterval_localized_self_variance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s  ≤  vectorMeasureFunctional n ν β t s)
    (K omega : ℝ) (hK : 0  ≤  K) (homega : 0  ≤  omega)
    (hQ : ∀v∈Ioo (0:ℝ) (1-s),(parisiFreeQuantile μ s v:ℝ)  ≤  K*(s+v+omega)) :
    let M:=(n:ℝ)*((1-t)*β^2)
    (∫v in Ioo (0:ℝ) (1-s),variance (vectorSelfOverlap (n:=n) μ β t ht.le
      (parisiFreeQuantile μ s v)) (vectorMeasureSpinPathLaw μ β t s ht.le))   ≤  
      smallIntervalVarianceConstant K*((1+logPlus M)/(M*s)+
        M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*omega^(2/3:ℝ))) := by
  dsimp only
  let M:=(n:ℝ)*((1-t)*β^2)
  let L:=1+logPlus M
  let W:=omega^(2/3:ℝ)
  let C:=smallIntervalShellConstant K
  let G:=1/(1-(2:ℝ)^(-(1/3:ℝ)))
  let ψ:=fun v=>variance (vectorSelfOverlap (n:=n) μ β t ht.le
    (parisiFreeQuantile μ s v)) (vectorMeasureSpinPathLaw μ β t s ht.le)
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hL : 0  ≤  L:=by dsimp only [L];linarith [logPlus_nonneg M]
  have hC : 0  ≤  C:=by dsimp only [C,smallIntervalShellConstant];positivity
  have hW : 0  ≤  W:=by dsimp only [W];positivity
  have hG : 0<G:=one_div_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))
  obtain ⟨N,hN,hNext⟩:=exists_nat_pow_near (one_le_one_div hs.1 hs.2.le) (by norm_num : (1:ℝ)<2)
  have hNU : (2:ℝ)^N*s  ≤  1:=(le_div_iff₀ hs.1).mp hN
  have hNX : 1<(2:ℝ)^(N+1)*s:=(div_lt_iff₀ hs.1).mp hNext
  letI : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) (1-s))):=isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo];exact ENNReal.ofReal_ne_top)
  have hψi : IntegrableOn ψ (Ioo (0:ℝ) (1-s)):=
    integrableOn_variance_vectorSelfOverlap hn μ β t s ht.le _ s
  rw [smallInterval_integral_dyadic_partition ψ s hs.1 hψi N hNX]
  have hbound (j:ℕ) (hj:j∈Finset.range (N+1)) :
      (∫v in dyadicQuantileShell s s j,ψ v)   ≤  
        C*(L/(M*((2:ℝ)^j*s))+M^(-(2/3:ℝ))*
          (((2:ℝ)^j*s)^(1/3:ℝ)+((2:ℝ)^j*s)^(-(1/3:ℝ))*W)) := by
    have hU : 0<(2:ℝ)^j*s:=by positivity [hs.1]
    have hU1 : (2:ℝ)^j*s  ≤  1:=
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)  ≤  2)
        (by simpa using Finset.mem_range.mp hj)) hs.1.le).trans hNU
    have hlog : logPlus (M*((2:ℝ)^j*s)^2)  ≤  logPlus M :=
      logPlus_le_of_nonneg_le (by positivity)
        (mul_le_of_le_one_right hM.le (by nlinarith [hU.le,hU1]))
    have hb:=smallInterval_self_overlap_shell hn μ s β t hβ ht hs hμ hmin K omega hK homega hQ j
    dsimp only at hb
    apply hb.trans
    change C*((1+logPlus (M*((2:ℝ)^j*s)^2))/(M*((2:ℝ)^j*s))+_)  ≤  _
    exact mul_le_mul_of_nonneg_left (add_le_add
      (div_le_div_of_nonneg_right (show 1+logPlus (M*((2:ℝ)^j*s)^2) ≤ L from by dsimp only [L];linarith) (mul_nonneg hM.le hU.le)) le_rfl) hC
  apply (Finset.sum_le_sum hbound).trans
  have heq : (∑j∈Finset.range (N+1),C*(L/(M*((2:ℝ)^j*s))+M^(-(2/3:ℝ))*
      (((2:ℝ)^j*s)^(1/3:ℝ)+((2:ℝ)^j*s)^(-(1/3:ℝ))*W))) =
      C*((L/M)*(∑j∈Finset.range (N+1),1/((2:ℝ)^j*s))+
        M^(-(2/3:ℝ))*((∑j∈Finset.range (N+1),((2:ℝ)^j*s)^(1/3:ℝ))+
          (∑j∈Finset.range (N+1),((2:ℝ)^j*s)^(-(1/3:ℝ)))*W)) := by
    rw [←Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    congr 1
    · calc
        _=∑j∈Finset.range (N+1),(L/M)*(1/((2:ℝ)^j*s)):=by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _=_:=by rw [Finset.mul_sum]
    · rw [Finset.sum_add_distrib,←Finset.sum_mul]
  rw [heq]
  have hInv:=smallIntervalDyadic_inverse_sum s hs.1 N
  have hPos:=smallIntervalDyadic_positive_third_sum s hs.1 N hNU
  have hNeg:=smallIntervalDyadic_negative_third_sum s hs.1 N
  have hP1 : (L/M)*(∑j∈Finset.range (N+1),1/((2:ℝ)^j*s))  ≤  2*(L/(M*s)) := by
    convert mul_le_mul_of_nonneg_left hInv (div_nonneg hL hM.le) using 1 <;> field_simp <;> ring
  have hP2 : M^(-(2/3:ℝ))*((∑j∈Finset.range (N+1),((2:ℝ)^j*s)^(1/3:ℝ))+
        (∑j∈Finset.range (N+1),((2:ℝ)^j*s)^(-(1/3:ℝ)))*W)   ≤  
      G*(M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*W)) := by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hPos
      (mul_le_mul_of_nonneg_right hNeg hW)) (Real.rpow_nonneg hM.le (-(2/3:ℝ)))
    convert hh using 1 <;> dsimp only [G] <;> ring
  have hX : 0  ≤  L/(M*s):=div_nonneg hL (mul_nonneg hM.le hs.1.le)
  have hY : 0  ≤  M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*W):=
    mul_nonneg (Real.rpow_nonneg hM.le _) (add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hs.1.le _) hW))
  change C*(_+_)  ≤  smallIntervalVarianceConstant K*(L/(M*s)+M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*W))
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hP1 hP2) hC
  apply hh.trans
  dsimp only [smallIntervalVarianceConstant,smallIntervalDyadicConstant]
  change C*(2*(L/(M*s))+G*(M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*W)))  ≤  
    C*(2+G)*(L/(M*s)+M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*W))
  have hdiff:=mul_nonneg hC (add_nonneg (mul_nonneg hG.le hX)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hY))
  nlinarith only [hdiff]

end QuantitativeFollowup
