module
public import FourPapersCommon.MixtureCoordinate

@[expose] public section

/-! Nonnegative covariance increments after removing one coefficient, and
the literal positive-coordinate decomposition of every variance increment.
The remaining covariance may vanish, including for a pure p-spin mixture. -/
noncomputable section
open Set
namespace FourPapersCommon
namespace AdmissibleEvenMixture
set_option maxHeartbeats 500000

def coordinateBaseIncrement (ξ : AdmissibleEvenMixture) (p : ℕ) (a b : ℝ) : ℝ :=
  ξ.first b-ξ.first a-(p : ℝ)*ξ.coefficient p*(b^(p-1)-a^(p-1))

theorem coordinateBaseIncrement_nonneg (ξ : AdmissibleEvenMixture) (p : ℕ)
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) 1) (hb : b∈Icc (0 : ℝ) 1) (hab : a≤b) :
    0≤ξ.coordinateBaseIncrement p a b := by
  let f:=fun n : ℕ=>(n : ℝ)*ξ.coefficient n*(b^(n-1)-a^(n-1))
  have hsa:=ξ.summable_first (abs_le.mpr ⟨by linarith [ha.1],ha.2⟩)
  have hsb:=ξ.summable_first (abs_le.mpr ⟨by linarith [hb.1],hb.2⟩)
  have hs : Summable f := by simpa only [f,mul_sub] using hsb.sub hsa
  have hnn (n : ℕ) : 0≤f n := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (ξ.nonneg _)) (sub_nonneg.mpr (pow_le_pow_left₀ ha.1 hab _))
  have hle:=hs.le_tsum p (fun n _=>hnn n)
  have he : (∑'n,f n)=ξ.first b-ξ.first a := by
    simpa only [f,mul_sub,first] using hsb.tsum_sub hsa
  rw [he] at hle
  exact sub_nonneg.mpr hle

theorem amplitudeCoordinate_increment (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) {a b : ℝ}
    (ha : a∈Icc (0 : ℝ) 1) (hb : b∈Icc (0 : ℝ) 1) :
    (ξ.amplitudeCoordinate p hp c).first b-(ξ.amplitudeCoordinate p hp c).first a =
      ξ.coordinateBaseIncrement p a b+(c : ℝ)^2*(p : ℝ)*(b^(p-1)-a^(p-1)) := by
  rw [ξ.amplitudeCoordinate_first p hp c (abs_le.mpr ⟨by linarith [hb.1],hb.2⟩),
    ξ.amplitudeCoordinate_first p hp c (abs_le.mpr ⟨by linarith [ha.1],ha.2⟩)]
  unfold coordinateBaseIncrement
  ring

theorem amplitudeCoordinate_increment_scaled (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ) (hc : (c : ℝ)^2=t*M^2)
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) 1) (hb : b∈Icc (0 : ℝ) 1) :
    (ξ.amplitudeCoordinate p hp c).first b-(ξ.amplitudeCoordinate p hp c).first a =
      ξ.coordinateBaseIncrement p a b+t*(M^2*(p : ℝ)*(b^(p-1)-a^(p-1))) := by
  rw [ξ.amplitudeCoordinate_increment p hp c ha hb,hc]
  ring

end AdmissibleEvenMixture
end FourPapersCommon
