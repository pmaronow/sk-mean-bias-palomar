module
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Actual Chernoff optimization for a negative quadratic CGF and a positive
quadratic-plus-sixth CGF. The probability and unbounded range are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω]
set_option maxHeartbeats 1800000

theorem lower_tail_of_negative_cgf_quadratic (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (K : ℝ) (hK : 0<K)
    (hExp : ∀s : ℝ,s<0 → Integrable (fun w=>Real.exp (s*Z w)) P)
    (hBound : ∀s : ℝ,s<0 → cgf Z P s≤K*s^2) (u : ℝ) (hu : 0≤u) :
    P.real {w | Z w≤-u}≤Real.exp (-u^2/(4*K)) := by
  by_cases hu0 : u=0
  · subst u
    simpa using (measureReal_le_one (μ:=P) (s:={w | Z w≤-(0:ℝ)}))
  have hup : 0<u:=lt_of_le_of_ne hu (Ne.symm hu0)
  let s:=-u/(2*K)
  have hs : s<0:=div_neg_of_neg_of_pos (neg_neg_of_pos hup) (by positivity)
  have ht:=measure_le_le_exp_cgf (X:=Z) (μ:=P) (-u) hs.le (hExp s hs)
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  have he : -s*(-u)+K*s^2=-u^2/(4*K):=by
    dsimp only [s]
    field_simp
    <;> ring
  have hb:=hBound s hs
  linarith

theorem upper_tail_of_cgf_quadratic_sixth (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (K Q N : ℝ) (hK : 0<K) (hQ : 0<Q) (hN : 0<N)
    (hExp : ∀s : ℝ,0<s → Integrable (fun w=>Real.exp (s*Z w)) P)
    (hBound : ∀s : ℝ,0<s → cgf Z P s≤K*(Q*s^2+N*s^6))
    (u : ℝ) (hu : 0≤u) :
    P.real {w | u≤Z w}≤Real.exp (-min (1/(8*K)) (1/(2*(4*K)^(1/5:ℝ)))*
      min (u^2/Q) (u^(6/5:ℝ)/N^(1/5:ℝ))) := by
  by_cases hu0 : u=0
  · subst u
    simpa using (measureReal_le_one (μ:=P) (s:={w | (0:ℝ)≤Z w}))
  have hup : 0<u:=lt_of_le_of_ne hu (Ne.symm hu0)
  let x:=u/(4*K*Q)
  let y:=(u/(4*K*N))^(1/5:ℝ)
  let s:=min x y
  have hx : 0<x:=div_pos hup (by positivity)
  have hy : 0<y:=Real.rpow_pos_of_pos (by positivity) _
  have hs : 0<s:=lt_min hx hy
  have hsx : s*(4*K*Q)≤u:=(le_div_iff₀ (by positivity : 0<4*K*Q)).mp (min_le_left x y)
  have hsy : s^5≤u/(4*K*N):=by
    have hh:=pow_le_pow_left₀ hs.le (min_le_right x y) 5
    have he : y^5=u/(4*K*N):=by
      dsimp only [y]
      rw [←Real.rpow_mul_natCast (by positivity : 0≤u/(4*K*N))]
      norm_num
    rwa [he] at hh
  have hsy' : s^5*(4*K*N)≤u:=(le_div_iff₀ (by positivity : 0<4*K*N)).mp hsy
  have hQbound : K*Q*s^2≤s*u/4:=by
    have hh:=mul_le_mul_of_nonneg_left hsx hs.le
    nlinarith only [hh]
  have hNbound : K*N*s^6≤s*u/4:=by
    have hh:=mul_le_mul_of_nonneg_left hsy' hs.le
    nlinarith only [hh]
  have ht:=measure_ge_le_exp_cgf (X:=Z) (μ:=P) u hs.le (hExp s hs)
  have hb:=hBound s hs
  have hFirst : P.real {w | u≤Z w}≤Real.exp (-s*u/2):=
    ht.trans (Real.exp_le_exp.mpr (by nlinarith only [hb,hQbound,hNbound]))
  let c:=min (1/(8*K)) (1/(2*(4*K)^(1/5:ℝ)))
  have hc : 0<c:=lt_min (by positivity) (by positivity)
  have hY : y*u/2=(1/(2*(4*K)^(1/5:ℝ)))*(u^(6/5:ℝ)/N^(1/5:ℝ)):=by
    dsimp only [y]
    rw [Real.div_rpow hu (by positivity),Real.mul_rpow (by positivity) hN.le,
      show u^(6/5:ℝ)=u*u^(1/5:ℝ) by
        rw [show (6/5:ℝ)=1+1/5 by norm_num,Real.rpow_add hup,Real.rpow_one]]
    ring
  have hX : x*u/2=(1/(8*K))*(u^2/Q):=by dsimp only [x];ring
  have hMin : s*u/2=min ((1/(8*K))*(u^2/Q))
      ((1/(2*(4*K)^(1/5:ℝ)))*(u^(6/5:ℝ)/N^(1/5:ℝ))):=by
    dsimp only [s]
    rw [div_eq_mul_inv,min_mul_of_nonneg x y hu,
      min_mul_of_nonneg (x*u) (y*u) (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹)]
    simpa only [←div_eq_mul_inv,hX,hY]
  have hcm : c*min (u^2/Q) (u^(6/5:ℝ)/N^(1/5:ℝ))≤s*u/2:=by
    rw [hMin]
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le).trans
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le).trans
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  exact hFirst.trans (Real.exp_le_exp.mpr (by dsimp only [c] at hcm;linarith))

end FourPapersCommon
