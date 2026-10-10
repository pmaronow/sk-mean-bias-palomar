module
public import QuantitativePaper.P2CutoffBalance
public import QuantitativePaper.P2PowerBalance

@[expose] public section

/-! The sharper p2 quantile estimate for every actual minimizing profile.
The input trial data are local properties of an actual admissible measure;
its variational midpoint gain and regularization are proved internally. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000

def p2QuantileConstant (T k Cs : ℝ) : ℝ :=
  max (16/k) (max ((2/p2MidpointConstant k Cs)^(2/11 : ℝ))
    (4*(2/p2MidpointConstant k Cs)^(2/5 : ℝ)))/T

theorem p2QuantileConstant_pos (T k Cs : ℝ) (hT : 0 < T) (hk : 0 < k) :
    0 < p2QuantileConstant T k Cs :=
  div_pos (lt_of_lt_of_le (div_pos (by norm_num) hk) (le_max_left _ _)) hT

theorem p2_quantile_bound_of_trial_data (T k Cs : ℝ)
    (hT : T ∈ Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hCs : 0 ≤ Cs)
    (n : ℕ) (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β lam r η u x : ℝ) (hβ : 1 ≤ β) (hlam : lam ∈ Icc (0 : ℝ) β)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hη : 0 ≤ η) (hu : u ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor (lam/β)) (hν : ν ∈ scalarFloor (lam/β))
    (hmin : ∀ρ ∈ scalarFloor (lam/β), responseEnergyFunctional n μ β (1-r) lam ≤
      responseEnergyFunctional n ρ β (1-r) lam)
    (hbudget : responseEnergyFunctional n ν β (1-r) lam-responseEnergyFunctional n μ β (1-r) lam ≤ η)
    (hsmall : β*parisiCDF μ x < 2*u)
    (htrial : ∀y ∈ Icc (0 : ℝ) T, k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0 : ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0 : ℝ) T)) :
    x ≤ p2QuantileConstant T k Cs*(r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := by
  let q := min x T
  let c := p2MidpointConstant k Cs
  let B := max ((2/c)^(2/11 : ℝ)) (4*(2/c)^(2/5 : ℝ))
  let K := max (16/k) B
  let rate := r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ)
  have hc : 0 < c := by
    dsimp [c,p2MidpointConstant]
    exact div_pos (mul_pos (pow_pos (responseCurvatureConstant_pos 2) 4) (sq_pos_of_pos hk)) (by positivity)
  have hr0 : 0 < r := hr.1
  have hu0 : 0 < u := hu.1
  have hrate : u ≤ rate := by
    have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr.1 hr.2 (by norm_num : (-3/5 : ℝ) ≤ 0)
    have hm := mul_le_mul_of_nonneg_right hh hu.1.le
    have hn : 0 ≤ r^(-7/11 : ℝ)*η^(2/11 : ℝ) := by positivity
    dsimp only [rate]
    linarith
  have hK : 0 < K := lt_of_lt_of_le (div_pos (by norm_num) hk) (le_max_left _ _)
  have hqnonneg : 0 ≤ q := le_min hx.1 hT.1.le
  have hxq : x ≤ q/T := by
    apply (le_div_iff₀ hT.1).mpr
    apply le_min
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left (show T ≤ 1 by linarith [hT.2]) hx.1
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hx.2 hT.1.le
  have hqRate : q ≤ K*rate := by
    by_cases hsmallq : q ≤ 16*u/k
    · calc
        q ≤ (16/k)*u := by convert hsmallq using 1 <;> ring
        _ ≤ K*u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le
        _ ≤ K*rate := mul_le_mul_of_nonneg_left hrate hK.le
    · have hqpos : 0 < q := lt_trans (div_pos (mul_pos (by norm_num) hu.1) hk) (lt_of_not_ge hsmallq)
      have hq : q ∈ Ioc (0 : ℝ) (1/4) := ⟨hqpos,(min_le_right x T).trans hT.2⟩
      have hlarge : 16*u < k*q := by
        have hh := (div_lt_iff₀ hk).mp (lt_of_not_ge hsmallq)
        simpa only [mul_comm] using hh
      obtain ⟨hm0,hm,hh⟩ := p2_large_cutoff_balance n hn μ ν β lam r q x u η k Cs T
        hβ hlam hr hq hx (min_le_left x T) (min_le_right x T) hu hk hCs hμ hν hmin hbudget
        hsmall hlarge htrial hdensity
      have hbalance := p2_midpoint_balance_rate c r q
        (β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q)) u η hc hr.1 hqpos hm0 hu hm hη hh
      calc
        q ≤ B*rate := hbalance
        _ ≤ K*rate := mul_le_mul_of_nonneg_right (le_max_right _ _) (hu.1.le.trans hrate)
  calc
    x ≤ q/T := hxq
    _ ≤ (K*rate)/T := div_le_div_of_nonneg_right hqRate hT.1.le
    _ = p2QuantileConstant T k Cs*rate := by
      dsimp only [p2QuantileConstant,K,B,c]
      ring

end QuantitativePaper
