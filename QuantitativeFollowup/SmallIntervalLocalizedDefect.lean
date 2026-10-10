module
public import QuantitativeFollowup.SmallIntervalVariance
public import QuantitativeFollowup.SmallIntervalDecomposition
public import QuantitativePaper.FreeTraceCutoff

@[expose] public section

/-! The exact thermal/mean-covariance/self-overlap decomposition gives the
localized actual defect, before the true trial budget is substituted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000
variable {n : ℕ}

def smallIntervalClockConstant (K : ℝ) : ℝ := 913+smallIntervalVarianceConstant K

theorem smallIntervalClockConstant_pos (K : ℝ) (hK : 0 ≤ K) :
    0<smallIntervalClockConstant K := by
  unfold smallIntervalClockConstant
  linarith [smallIntervalVarianceConstant_pos K hK]

theorem smallInterval_localized_defect (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (K omega : ℝ) (hK : 0 ≤ K) (homega : 0 ≤ omega)
    (hQ : ∀v∈Ioo (0:ℝ) (1-s),(parisiFreeQuantile μ s v:ℝ) ≤ K*(s+v+omega)) :
    let M:=(n:ℝ)*((1-t)*β^2)
    vectorInterpolationDefect (n:=n) μ s β t ht.le  ≤ 
      smallIntervalClockConstant K*((1+logPlus M)^2/(M*s)+
        M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*omega^(2/3:ℝ))) := by
  dsimp only
  let M:=(n:ℝ)*((1-t)*β^2)
  let L:=1+logPlus M
  let X:=L^2/(M*s)
  let R:=M^(-(2/3:ℝ))*(1+s^(-(1/3:ℝ))*omega^(2/3:ℝ))
  let C:=smallIntervalVarianceConstant K
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hL : 1 ≤ L:=by dsimp only [L];linarith [logPlus_nonneg M]
  have hR : 0 ≤ R:=by dsimp only [R];positivity [homega,hs.1]
  have hC : 0 ≤ C:=(smallIntervalVarianceConstant_pos K hK).le
  have hA:=vector_free_trace_floor_bound hn μ s β t hβ ht hs hμ hmin
  change vectorInterpolationTraceError (n:=n) μ s β t ht.le ≤ 1/(M*s) at hA
  have hA' : vectorInterpolationTraceError (n:=n) μ s β t ht.le ≤ X :=
    hA.trans (div_le_div_of_nonneg_right (by nlinarith : (1:ℝ) ≤ L^2) (mul_nonneg hM.le hs.1.le))
  have hJ:=vector_mean_direction_covariance_integral_bound hn μ s β t hβ ht hs hμ hmin
  have hJ' : vectorMeanDirectionCovarianceIntegral (n:=n) μ s β t s ht.le ≤ 456*X := by
    convert hJ using 1
    dsimp only [X,L,M]
    ring
  have hV:=smallInterval_localized_self_variance hn μ s β t hβ ht hs hμ hmin K omega hK homega hQ
  dsimp only at hV
  have hV' : vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le ≤ C*(X+R) := by
    apply hV.trans
    change C*(L/(M*s)+R) ≤ C*(X+R)
    apply mul_le_mul_of_nonneg_left _ hC
    have hh:=div_le_div_of_nonneg_right (by nlinarith : L ≤ L^2) (mul_nonneg hM.le hs.1.le)
    change L/(M*s)+R ≤ L^2/(M*s)+R
    linarith only [hh]
  rw [smallInterval_defect_decomposition hn μ s β t hβ ht hs hμ hmin]
  change _ ≤ smallIntervalClockConstant K*(X+R)
  calc
    _ ≤ X+2*(456*X)+C*(X+R):=
      add_le_add (add_le_add hA' (mul_le_mul_of_nonneg_left hJ' (by norm_num : (0:ℝ) ≤ 2))) hV'
    _ ≤ _:=by dsimp only [smallIntervalClockConstant,C];nlinarith only [hR]

end QuantitativeFollowup
