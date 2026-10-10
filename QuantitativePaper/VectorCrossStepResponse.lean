module
public import QuantitativePaper.VectorSecondResponse
public import QuantitativePaper.VectorGaussianExpectation

@[expose] public section

/-! Mixed differentiation of an actual normalized Gaussian response. The
potential direction and the observed spin direction may differ. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000

def vectorStepCrossResponse {n : ℕ} (c m : ℝ) (f v w h : Field n → ℝ) (x : Field n) : ℝ :=
  vectorStepResponse c m f h x+m * (vectorStepResponse c m f (fun z=>v z * w z) x-
    vectorStepResponse c m f v x * vectorStepResponse c m f w x)

theorem abs_vectorStepCrossResponse_le {n : ℕ} (f v w h : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (R S T : ℝ≥0)
    (hv : ∀z,|v z| ≤ R) (hw : ∀z,|w z| ≤ S) (hh : ∀z,|h z| ≤ T)
    (c m : ℝ) (x : Field n) :
    |vectorStepCrossResponse c m f v w h x| ≤ (T:ℝ)+2 * |m|  * R * S := by
  have hvw : ∀z,|v z * w z| ≤ (R:ℝ) * S:=fun z=>by
    rw [abs_mul]
    exact mul_le_mul (hv z) (hw z) (abs_nonneg _) R.coe_nonneg
  have hb:=abs_vectorStepResponse_le f h K hf c m T hh x
  have hc:=abs_vectorStepResponse_le f (fun z=>v z * w z) K hf c m ((R:ℝ) * S) hvw x
  have hd:=abs_vectorStepResponse_le f v K hf c m R hv x
  have he:=abs_vectorStepResponse_le f w K hf c m S hw x
  have hmul : |vectorStepResponse c m f v x * vectorStepResponse c m f w x| ≤ (R:ℝ) * S:=by
    rw [abs_mul]
    exact mul_le_mul hd he (abs_nonneg _) R.coe_nonneg
  unfold vectorStepCrossResponse
  calc
    _ ≤ |vectorStepResponse c m f h x|+|m|  * |vectorStepResponse c m f (fun z=>v z * w z) x-
      vectorStepResponse c m f v x * vectorStepResponse c m f w x|:=by
        rw [←abs_mul]
        exact abs_add_le _ _
    _ ≤ (T:ℝ)+|m|  * (|vectorStepResponse c m f (fun z=>v z * w z) x|+
      |vectorStepResponse c m f v x * vectorStepResponse c m f w x|):=
      add_le_add hb (mul_le_mul_of_nonneg_left
        (by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (vectorStepResponse c m f (fun z=>v z * w z) x) 0 (vectorStepResponse c m f v x * vectorStepResponse c m f w x))) (abs_nonneg m))
    _ ≤ (T:ℝ)+|m| *((R:ℝ)*S+(R:ℝ)*S):=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (add_le_add hc hmul) (abs_nonneg m))
    _ = _ := by ring

theorem hasDerivAt_vectorStepResponse_cross {n : ℕ} (f v w h : ℝ → Field n → ℝ)
    (K R S T : ℝ≥0) (hf : ∀y,LipschitzWith K (f y))
    (hv : ∀y,Measurable (v y)) (hw : ∀y,Measurable (w y)) (hh : ∀y,Measurable (h y))
    (hbv : ∀y z,|v y z| ≤ R) (hbw : ∀y z,|w y z| ≤ S) (hbh : ∀y z,|h y z| ≤ T)
    (hdf : ∀y z,HasDerivAt (fun r=>f r z) (v y z) y)
    (hdw : ∀y z,HasDerivAt (fun r=>w r z) (h y z) y)
    (c m : ℝ) (x : Field n) (y₀ : ℝ) :
    HasDerivAt (fun y=>vectorStepResponse c m (f y) (w y) x)
      (vectorStepCrossResponse c m (f y₀) (v y₀) (w y₀) (h y₀) x) y₀ := by
  have hs : Continuous (fieldShift c x):=by unfold fieldShift;fun_prop
  have hparam (z:Field n) : LipschitzWith R (fun y=>f y z):=by
    apply lipschitzWith_of_nnnorm_deriv_le (fun y=>(hdf y z).differentiableAt)
    intro y
    rw [(hdf y z).deriv,←NNReal.coe_le_coe]
    simpa only [coe_nnnorm,Real.norm_eq_abs] using hbv y z
  have hvw (y:ℝ) (z:Field n) : |v y z * w y z| ≤ (R:ℝ) * S:=by
    rw [abs_mul]
    exact mul_le_mul (hbv y z) (hbw y z) (abs_nonneg _) R.coe_nonneg
  have hder (y:ℝ) (z:Field n) : HasDerivAt
      (fun r=>Real.exp (m * f r (fieldShift c x z)) * w r (fieldShift c x z))
      (Real.exp (m * f y (fieldShift c x z)) * (m * v y (fieldShift c x z) * w y (fieldShift c x z)+
        h y (fieldShift c x z))) y:=by
    convert (((hdf y _).const_mul m).exp).mul (hdw y _) using 1
    ring
  have hbound : ∀z:Field n,∀y∈Metric.ball y₀ 1,
      ‖Real.exp (m * f y (fieldShift c x z)) * (m * v y (fieldShift c x z) * w y (fieldShift c x z)+
        h y (fieldShift c x z))‖ ≤ 
      ((|m|  * (R:ℝ) * S+T) * Real.exp (|m|  * R)) * Real.exp (m * f y₀ (fieldShift c x z)):=by
    intro z y hy
    have hdist : dist y y₀ < 1:=hy
    have hdif:=(hparam (fieldShift c x z)).dist_le_mul y y₀
    rw [Real.dist_eq] at hdif
    have hmf : m * f y (fieldShift c x z) ≤ m * f y₀ (fieldShift c x z)+|m|  * R:=by
      have hp:=mul_le_mul_of_nonneg_left
        (hdif.trans (mul_le_mul_of_nonneg_left hdist.le R.coe_nonneg)) (abs_nonneg m)
      have hmul:=le_abs_self (m * (f y (fieldShift c x z)-f y₀ (fieldShift c x z)))
      rw [abs_mul] at hmul
      linarith
    have hi : |m * v y (fieldShift c x z) * w y (fieldShift c x z)+h y (fieldShift c x z)| ≤ 
        |m|  * (R:ℝ) * S+T:=by
      calc
        _ ≤ |m * v y (fieldShift c x z) * w y (fieldShift c x z)|+|h y (fieldShift c x z)|:=abs_add_le _ _
        _=|m|  * |v y (fieldShift c x z) * w y (fieldShift c x z)|+|h y (fieldShift c x z)|:=by
          rw [mul_assoc,abs_mul]
        _ ≤ _:=by nlinarith [mul_le_mul_of_nonneg_left (hvw y (fieldShift c x z)) (abs_nonneg m),hbh y (fieldShift c x z)]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (m * f y (fieldShift c x z)) * (|m|  * (R:ℝ) * S+T):=
        mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
      _ ≤ Real.exp (m * f y₀ (fieldShift c x z)+|m|  * R) * (|m|  * (R:ℝ) * S+T):=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmf) (by positivity)
      _=_:=by rw [Real.exp_add];ring
  have hI:=(hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun y z=>Real.exp (m * f y (fieldShift c x z)) * w y (fieldShift c x z))
    (F':=fun y z=>Real.exp (m * f y (fieldShift c x z)) * (m * v y (fieldShift c x z) * w y (fieldShift c x z)+h y (fieldShift c x z)))
    (bound:=fun z=>((|m|  * (R:ℝ) * S+T) * Real.exp (|m|  * R)) * Real.exp (m * f y₀ (fieldShift c x z)))
    (s:=Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ (by norm_num))
    (Eventually.of_forall fun y=>((Real.continuous_exp.comp
      (continuous_const.mul ((hf y).continuous.comp hs))).measurable.mul
      ((hw y).comp hs.measurable)).aestronglyMeasurable)
    (integrable_exp_vectorStep_mul (f y₀) (w y₀) K (hf y₀) (hw y₀) S (hbw y₀) c m x)
    ((Real.continuous_exp.comp (continuous_const.mul ((hf y₀).continuous.comp hs))).measurable.mul
      (((measurable_const.mul ((hv y₀).comp hs.measurable)).mul ((hw y₀).comp hs.measurable)).add
        ((hh y₀).comp hs.measurable))).aestronglyMeasurable
    (Eventually.of_forall hbound)
    ((integrable_exp_vectorStep (f y₀) K (hf y₀) c m x).const_mul _)
    (Eventually.of_forall fun z y _=>hder y z)).2
  have hG:=hasDerivAt_vectorColeHopfStep_response f v K R hf hv hbv hdf c m x y₀
  have hZ : HasDerivAt (fun y=>vectorStepPartition c m (f y) x)
      (vectorStepPartition c m (f y₀) x * (m * vectorStepResponse c m (f y₀) (v y₀) x)) y₀:=by
    simpa only [←vectorStepPartition_eq_exp _ K (hf _) c m x] using (hG.const_mul m).exp
  have hih:=integrable_exp_vectorStep_mul (f y₀) (h y₀) K (hf y₀) (hh y₀) T (hbh y₀) c m x
  have hivw:=integrable_exp_vectorStep_mul (f y₀) (fun z=>v y₀ z * w y₀ z) K (hf y₀)
    ((hv y₀).mul (hw y₀)) ((R:ℝ) * S) (hvw y₀) c m x
  have hsplit : (∫z,Real.exp (m * f y₀ (fieldShift c x z)) * (m * v y₀ (fieldShift c x z) * w y₀ (fieldShift c x z)+h y₀ (fieldShift c x z)) ∂fieldGaussian n)=
      m * (∫z,Real.exp (m * f y₀ (fieldShift c x z)) * (v y₀ (fieldShift c x z) * w y₀ (fieldShift c x z)) ∂fieldGaussian n)+
      (∫z,Real.exp (m * f y₀ (fieldShift c x z)) * h y₀ (fieldShift c x z) ∂fieldGaussian n):=by
    have he : (fun z=>Real.exp (m * f y₀ (fieldShift c x z)) * (m * v y₀ (fieldShift c x z) * w y₀ (fieldShift c x z)+h y₀ (fieldShift c x z)))=
      (fun z=>m * (Real.exp (m * f y₀ (fieldShift c x z)) * (v y₀ (fieldShift c x z) * w y₀ (fieldShift c x z))))+
      (fun z=>Real.exp (m * f y₀ (fieldShift c x z)) * h y₀ (fieldShift c x z)):=by funext z;dsimp;ring
    rw [he]
    change (∫z,m * (Real.exp (m * f y₀ (fieldShift c x z)) * (v y₀ (fieldShift c x z) * w y₀ (fieldShift c x z)))+
      Real.exp (m * f y₀ (fieldShift c x z)) * h y₀ (fieldShift c x z) ∂fieldGaussian n)=_
    rw [integral_add (hivw.const_mul m) hih,integral_const_mul]
  have hquot:=hI.div hZ (vectorStepPartition_pos (f y₀) K (hf y₀) c m x).ne'
  have hval : ((∫z,Real.exp (m * f y₀ (fieldShift c x z)) * (m * v y₀ (fieldShift c x z) * w y₀ (fieldShift c x z)+h y₀ (fieldShift c x z)) ∂fieldGaussian n) * 
      vectorStepPartition c m (f y₀) x-
      (∫z,Real.exp (m * f y₀ (fieldShift c x z)) * w y₀ (fieldShift c x z) ∂fieldGaussian n) * 
        (vectorStepPartition c m (f y₀) x * (m * vectorStepResponse c m (f y₀) (v y₀) x)))/
      vectorStepPartition c m (f y₀) x^2=vectorStepCrossResponse c m (f y₀) (v y₀) (w y₀) (h y₀) x:=by
    rw [hsplit]
    unfold vectorStepCrossResponse
    rw [vectorStepResponse_eq_quotient c m (f y₀) (h y₀) x,
      vectorStepResponse_eq_quotient c m (f y₀) (fun z=>v y₀ z * w y₀ z) x,
      vectorStepResponse_eq_quotient c m (f y₀) (v y₀) x,
      vectorStepResponse_eq_quotient c m (f y₀) (w y₀) x]
    field_simp
    ring
  rw [hval] at hquot
  convert hquot using 1
  funext y
  exact vectorStepResponse_eq_quotient c m (f y) (w y) x

end QuantitativePaper
