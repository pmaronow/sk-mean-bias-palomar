module
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

/-! Exact integration of bounded reciprocal and power tails. The values at
zero have no effect on these genuine Lebesgue integrals. -/
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem integrableOn_truncated_reciprocal (h b u : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => min h (b/t)) (Ioo 0 u) := by
  refine Integrable.of_bound
    ((measurable_const.min (measurable_const.div measurable_id)).aestronglyMeasurable) h ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (le_min hh (div_nonneg hb ht.1.le))]
  exact min_le_left _ _

theorem integral_truncated_reciprocal (h b : ℝ) (hh : 0<h) (hb : 0≤b) :
    (∫ t : ℝ in Ioo 0 1, min h (b/t)) =
      if h≤b then h else b*(1+Real.log (h/b)) := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  by_cases hbig : h≤b
  · rw [ite_eq_left hbig]
    calc
      (∫ t : ℝ in 0..1,min h (b/t)) = ∫ _t : ℝ in 0..1,h := by
        apply integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        apply min_eq_left
        apply (le_div_iff₀ ht.1).mpr
        exact (mul_le_mul_of_nonneg_left ht.2.le hh.le).trans (by simpa using hbig)
      _ = h := by simp
  · rw [ite_eq_right hbig]
    by_cases hb0 : b=0
    · simp [hb0, min_eq_right hh.le]
    have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
    let a : ℝ := b/h
    have ha : 0<a := div_pos hbpos hh
    have ha1 : a<1 := (div_lt_one hh).mpr (lt_of_not_ge hbig)
    have hba : h*a=b := by dsimp [a]; field_simp
    have hi0 : IntervalIntegrable (fun t : ℝ=>min h (b/t)) volume 0 a :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
        (integrableOn_truncated_reciprocal h b a hh.le hb)
    have hi1 : IntervalIntegrable (fun t : ℝ=>min h (b/t)) volume a 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le ha1.le).mpr
        ((integrableOn_truncated_reciprocal h b 1 hh.le hb).mono_set
          (fun t ht=>⟨ha.trans ht.1,ht.2⟩))
    rw [← integral_add_adjacent_intervals hi0 hi1]
    have he0 : (∫ t : ℝ in 0..a,min h (b/t))=a*h := by
      calc
        _ = ∫ _t : ℝ in 0..a,h := by
          apply integral_congr_Ioo_of_le ha.le
          intro t ht
          apply min_eq_left
          apply (le_div_iff₀ ht.1).mpr
          exact (mul_le_mul_of_nonneg_left ht.2.le hh.le).trans_eq hba
        _ = a*h := by simp
    have he1 : (∫ t : ℝ in a..1,min h (b/t))=b*Real.log (1/a) := by
      calc
        _ = ∫ t : ℝ in a..1,b*(1/t) := by
          apply integral_congr_Ioo_of_le ha1.le
          intro t ht
          change min h (b/t)=b*(1/t)
          rw [min_eq_right ((div_le_iff₀ (ha.trans ht.1)).mpr
            (hba.symm.trans_le (mul_le_mul_of_nonneg_left ht.1.le hh.le)))]
          ring
        _ = b*Real.log (1/a) := by
          rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha zero_lt_one]
    rw [he0,he1]
    have hab : 1/a=h/b := by dsimp [a]; field_simp
    rw [hab]
    nlinarith


theorem integrableOn_truncated_three_halves_local (h b u : ℝ)
    (hh : 0≤h) (hb : 0≤b) :
    IntegrableOn (fun t : ℝ=>min h (b*t^(-(3/2:ℝ)))) (Ioo 0 u) := by
  refine Integrable.of_bound
    ((measurable_const.min (measurable_const.mul (measurable_id.pow_const _))).aestronglyMeasurable) h ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (le_min hh (mul_nonneg hb (Real.rpow_nonneg ht.1.le _)))]
  exact min_le_left _ _

theorem truncated_three_halves_threshold (h b a : ℝ) (hh : 0<h) (hb : 0≤b)
    (ha : 0<a) (hthreshold : b*a^(-(3/2:ℝ))=h) :
    IntegrableOn (fun t : ℝ=>min h (b*t^(-(3/2:ℝ)))) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0,min h (b*t^(-(3/2:ℝ))))=3*h*a := by
  let f : ℝ→ℝ := fun t=>min h (b*t^(-(3/2:ℝ)))
  have he0 : EqOn f (fun _=>h) (Ioo 0 a) := by
    intro t ht
    apply min_eq_left
    rw [←hthreshold]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht.1 ht.2.le (by norm_num)) hb
  have het : EqOn f (fun t=>b*t^(-(3/2:ℝ))) (Ioi a) := by
    intro t ht
    apply min_eq_right
    rw [←hthreshold]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha ht.le (by norm_num)) hb
  have hi0 : IntervalIntegrable f volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      (integrableOn_truncated_three_halves_local h b a hh.le hb)
  have hiPower : IntegrableOn (fun t : ℝ=>b*t^(-(3/2:ℝ))) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) ha).const_mul b
  have hit : IntegrableOn f (Ioi a) :=
    hiPower.congr_fun (fun t ht=>(het ht).symm) measurableSet_Ioi
  have hi : IntegrableOn f (Ioi 0) := by
    rw [←Ioc_union_Ioi_eq_Ioi ha.le]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp hi0).union hit
  refine ⟨hi,?_⟩
  have heI0 : (∫ t : ℝ in 0..a,f t)=a*h := by
    rw [integral_congr_Ioo_of_le ha.le he0]
    simp
  have heIt : (∫ t : ℝ in Ioi a,f t)=2*b*a^(-(1/2:ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi het,MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) ha]
    norm_num
    ring
  have hepow : a^(-(1/2:ℝ))=a*a^(-(3/2:ℝ)) := by
    calc
      a^(-(1/2:ℝ))=a^((1:ℝ)+(-(3/2:ℝ))) := by norm_num
      _ = a^(1:ℝ)*a^(-(3/2:ℝ)) := Real.rpow_add ha _ _
      _ = _ := by rw [Real.rpow_one]
  have heI := integral_interval_add_Ioi hi hit
  rw [heI0,heIt,hepow] at heI
  have hbha : b*(a*a^(-(3/2:ℝ)))=a*h := by
    rw [←hthreshold]
    ring
  nlinarith [hthreshold,hbha]

theorem integral_truncated_three_halves (h b : ℝ) (hh : 0<h) (hb : 0≤b) :
    IntegrableOn (fun t : ℝ=>min h (b*t^(-(3/2:ℝ)))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0,min h (b*t^(-(3/2:ℝ))))=
      3*b^(2/3:ℝ)*h^(1/3:ℝ) := by
  by_cases hb0 : b=0
  · simp [hb0,min_eq_right hh.le]
  have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
  let a : ℝ := (b/h)^(2/3:ℝ)
  have ha : 0<a := Real.rpow_pos_of_pos (div_pos hbpos hh) _
  have hea : a^(3/2:ℝ)=b/h := by
    dsimp [a]
    rw [←Real.rpow_mul (div_nonneg hb hh.le)]
    norm_num
  have hthreshold : b*a^(-(3/2:ℝ))=h := by
    rw [Real.rpow_neg ha.le,hea]
    field_simp
  obtain ⟨hi,he⟩ := truncated_three_halves_threshold h b a hh hb ha hthreshold
  refine ⟨hi,he.trans ?_⟩
  have heha : h*a=b^(2/3:ℝ)*h^(1/3:ℝ) := by
    dsimp [a]
    rw [Real.div_rpow hb hh.le]
    have hep : h/h^(2/3:ℝ)=h^(1/3:ℝ) := by
      calc
        h/h^(2/3:ℝ)=h^(1:ℝ)/h^(2/3:ℝ) := by rw [Real.rpow_one]
        _ = h^((1:ℝ)-(2/3:ℝ)) := (Real.rpow_sub hh _ _).symm
        _ = _ := by norm_num
    calc
      h*(b^(2/3:ℝ)/h^(2/3:ℝ))=b^(2/3:ℝ)*(h/h^(2/3:ℝ)) := by ring
      _ = _ := by rw [hep]
  nlinarith [heha]


theorem integral_truncated_reciprocal_le_height (h b : ℝ) (hh : 0<h) (hb : 0≤b) :
    (∫ t : ℝ in Ioo 0 1,min h (b/t))≤h := by
  rw [integral_truncated_reciprocal h b hh hb]
  split_ifs with hbig
  · exact le_rfl
  · by_cases hb0 : b=0
    · simp [hb0,hh.le]
    have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hh hbpos)
    have hm := mul_le_mul_of_nonneg_left (show 1+Real.log (h/b)≤h/b by linarith) hb
    have he : b*(h/b)=h := by field_simp
    exact hm.trans_eq he

theorem truncated_reciprocal_256_bound (h ε : ℝ) (hh : 0<h) (hε : 0<ε) :
    (∫ t : ℝ in Ioo 0 1,min h ((256*ε)/t))≤
      256*min h (ε*(1+max (Real.log (h/ε)) 0)) := by
  have hheight := integral_truncated_reciprocal_le_height h (256*ε) hh (by positivity)
  have hlarge : (∫ t : ℝ in Ioo 0 1,min h ((256*ε)/t))≤256*h := by
    exact hheight.trans (by nlinarith)
  have hlog : (∫ t : ℝ in Ioo 0 1,min h ((256*ε)/t))≤
      256*(ε*(1+max (Real.log (h/ε)) 0)) := by
    rw [integral_truncated_reciprocal h (256*ε) hh (by positivity)]
    split_ifs with hbig
    · have hm := le_max_right (Real.log (h/ε)) 0
      nlinarith
    · have hd : h/(256*ε)≤h/ε :=
        div_le_div_of_nonneg_left hh.le hε (by nlinarith)
      have hl := (Real.log_le_log (by positivity : 0<h/(256*ε)) hd).trans
        (le_max_left (Real.log (h/ε)) 0)
      have hm := mul_le_mul_of_nonneg_left (show 1+Real.log (h/(256*ε))≤
        1+max (Real.log (h/ε)) 0 by linarith) (show 0≤256*ε by positivity)
      nlinarith
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤256)]
  exact le_min hlarge hlog

theorem truncated_three_halves_512_bound (h ε ell : ℝ)
    (hh : 0<h) (hε : 0<ε) (hell : 0≤ell) :
    (∫ t : ℝ in Ioi 0,min h ((1024*ε*ell)*t^(-(3/2:ℝ))))≤
      512*(ε*ell)^(2/3:ℝ)*h^(1/3:ℝ) := by
  rw [(integral_truncated_three_halves h (1024*ε*ell) hh (by positivity)).2]
  have hk : (1024:ℝ)^(2/3:ℝ)≤144 := by
    calc
      (1024:ℝ)^(2/3:ℝ)≤((12:ℝ)^3)^(2/3:ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 144 := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤12)]
        norm_num
  have he : (1024*ε*ell)^(2/3:ℝ)=
      (1024:ℝ)^(2/3:ℝ)*(ε*ell)^(2/3:ℝ) := by
    rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ)≤1024) (mul_nonneg hε.le hell)]
  rw [he]
  calc
    3*((1024:ℝ)^(2/3:ℝ)*(ε*ell)^(2/3:ℝ))*h^(1/3:ℝ)≤
        3*(144*(ε*ell)^(2/3:ℝ))*h^(1/3:ℝ) := by gcongr
    _ ≤ 512*(ε*ell)^(2/3:ℝ)*h^(1/3:ℝ) := by
      nlinarith [mul_nonneg (Real.rpow_nonneg (mul_nonneg hε.le hell) (2/3:ℝ))
        (Real.rpow_nonneg hh.le (1/3:ℝ))]

end FourPapersCommon
