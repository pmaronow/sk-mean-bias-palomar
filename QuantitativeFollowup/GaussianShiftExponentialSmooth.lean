module
public import QuantitativeFollowup.GaussianShiftDirectionalLipschitz
public import QuantitativePaper.OpenGaussianRelativeBounds
public import QuantitativePaper.SmoothOpenGaussianAverage
public import QuantitativePaper.VectorColeHopfOrderAllMass
public import FourPapersCommon.ExponentialSmoothAlgebra

@[expose] public section

/-! Genuine Gaussian Cole--Hopf smoothing on an unbounded field domain,
with deterministic parameters confined to an invariant open set. Actual
Gaussian integrals preserve all exponential spatial/parameter jet bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem gaussianShiftColeHopf_value_barrier (f : E→ℝ) (U : Set E)
    (A : Field n→L[ℝ]E) (hA : ∀x∈U,∀z,x+A z∈U)
    (H : ℝ≥0) (hLip : ∀x∈U,∀z,|f (x+A z)-f x|≤H*‖z‖) (mass : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀x∈U,|gaussianShiftColeHopf A mass f x|≤|f x|+C := by
  obtain ⟨C,hC,hb⟩:=vectorColeHopfStep_norm_barrier (n:=n) H 1 |mass|
  refine ⟨C,hC,?_⟩
  intro x hx
  rw [gaussianShiftColeHopf_eq_unitVectorStep]
  have hh:=hb mass ⟨neg_abs_le mass,le_abs_self mass⟩
    (fun z=>f (x+A z)) (lipschitzWith_gaussian_noise_slice f U A hA H hLip x hx)
  simpa only [map_zero,add_zero] using hh

theorem gaussianShiftColeHopf_smooth_exp_positive_jets_on_open (N : ℕ)
    (f : E→ℝ) (U : Set E) (hU : IsOpen U) (hf : ExponentialSmoothOn f U)
    (A : Field n→L[ℝ]E) (hA : ∀x∈U,∀z,x+A z∈U)
    (B L : ℝ) (hL : 0≤L) (hvalue : ∀x∈U,|f x|≤B+L*‖x‖)
    (H : ℝ≥0) (hLip : ∀x∈U,∀z,|f (x+A z)-f x|≤H*‖z‖) (mass : ℝ) :
    ContDiffOn ℝ N (gaussianShiftColeHopf A mass f) U ∧
      ∃C D : ℝ,1≤C ∧ 0≤D ∧ ∀j,1≤j→j≤N→∀x∈U,
        ‖iteratedFDeriv ℝ j (gaussianShiftColeHopf A mass f) x‖≤(C*Real.exp (D*‖x‖))^j := by
  by_cases hm : mass=0
  · obtain ⟨K,D,hK,hD,hj⟩:=hf.common_bound N
    have hfN : ContDiffOn ℝ N f U := fun x hx=>(hf.smooth x hx).of_le (by simp) |>.contDiffWithinAt
    have hp (j : ℕ) (hjN : j≤N) (x : E) (hx : x∈U) :
        ‖iteratedFDeriv ℝ j f x‖≤(K*Real.exp (D*‖x‖))^(j+1) := by
      have hbase : 1≤K*Real.exp (D*‖x‖) :=
        one_le_mul_of_one_le_of_one_le hK (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg _)))
      exact (hj j hjN x hx).trans (le_self_pow₀ hbase (by omega))
    obtain ⟨hs,C,hC,hjets⟩:=gaussianShiftAverage_smooth_exp_jets_on_open N f U hU hfN A hA K D hK hD hp
    have he : gaussianShiftColeHopf A mass f = gaussianShiftAverage A f :=
      funext fun x => by simp [gaussianShiftColeHopf, hm]
    rw [he]
    exact ⟨hs, C, 2*D, hC, by positivity, hjets⟩
  · let g:=fun x:E=>mass*f x
    have hg : ExponentialSmoothOn g U := by
      simpa only [Function.comp_def,ContinuousLinearMap.lsmul_apply,smul_eq_mul] using
        hf.compCLM (ContinuousLinearMap.lsmul ℝ ℝ mass)
    obtain ⟨K,D,hK,hD,hj⟩:=hg.common_bound N
    have hgN : ContDiffOn ℝ N g U := fun x hx=>(hg.smooth x hx).of_le (by simp) |>.contDiffWithinAt
    have hp (j : ℕ) (hj0 : 1≤j) (hjN : j≤N) (x : E) (hx : x∈U) :
        ‖iteratedFDeriv ℝ j g x‖≤(K*Real.exp (D*‖x‖))^j := by
      have hbase : 1≤K*Real.exp (D*‖x‖) :=
        one_le_mul_of_one_le_of_one_le hK (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg _)))
      exact (hj j hjN x hx).trans (le_self_pow₀ hbase (by omega))
    have hv (x : E) (hx : x∈U) : g x≤|mass| *B+(|mass| *L)*‖x‖ := by
      have hh:=mul_le_mul_of_nonneg_left (hvalue x hx) (abs_nonneg mass)
      have hn:=le_abs_self (mass*f x)
      rw [abs_mul] at hn
      dsimp only [g]
      nlinarith only [hh,hn]
    have hl (x : E) (hx : x∈U) (z : Field n) : |g (x+A z)-g x|≤(|mass| *(H:ℝ))*‖z‖ := by
      dsimp only [g]
      rw [←mul_sub,abs_mul]
      exact (mul_le_mul_of_nonneg_left (hLip x hx z) (abs_nonneg mass)).trans_eq (by ring)
    obtain ⟨hs,C,hC,hjets⟩:=log_gaussianShiftPartition_smooth_exp_jets N g U hU hgN A hA
      (|mass| *B) (|mass| *L) K D (|mass| *(H:ℝ))
      (mul_nonneg (abs_nonneg _) hL) (zero_le_one.trans hK) hD hv hp hl
    have he : gaussianShiftColeHopf A mass f=(fun x=>mass⁻¹*Real.log (gaussianShiftPartition A 1 g x)) := by
      funext x
      simp only [gaussianShiftColeHopf,ite_eq_right hm,gaussianShiftPartition,g,one_mul,div_eq_mul_inv,mul_comm]
    rw [he]
    refine ⟨contDiffOn_const.mul hs,max 1 |mass⁻¹| *C,D,
      one_le_mul_of_one_le_of_one_le (le_max_left _ _) hC,hD,?_⟩
    intro j hj0 hjN x hx
    have hhs:=(hs x hx).contDiffAt (hU.mem_nhds hx)
    have hhsj := hhs.of_le (show (j : ℕ∞ω) ≤ N by exact_mod_cast hjN)
    have heq : iteratedFDeriv ℝ j (fun x => mass⁻¹ * Real.log (gaussianShiftPartition A 1 g x)) x =
        mass⁻¹ • iteratedFDeriv ℝ j (fun x => Real.log (gaussianShiftPartition A 1 g x)) x := by
      simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := mass⁻¹) hhsj
    rw [heq]
    simp only [norm_smul,Real.norm_eq_abs]
    have hvbase : 1≤C*Real.exp (D*‖x‖) :=
      one_le_mul_of_one_le_of_one_le hC (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg _)))
    have hmabs : |mass⁻¹|≤(max 1 |mass⁻¹|)^j :=
      (le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))
    have hh:=mul_le_mul hmabs (hjets j hj0 hjN x hx) (norm_nonneg _)
      (pow_nonneg (le_trans (by norm_num) (le_max_left _ _)) _)
    convert hh using 1
    rw [←mul_pow]
    ring


theorem exponentialSmoothOn_gaussianShiftColeHopf
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ExponentialSmoothOn f U)
    (A : Field n →L[ℝ] E) (hA : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L : ℝ) (hL : 0 ≤ L) (hvalue : ∀ x ∈ U, |f x| ≤ B+L*‖x‖)
    (H : ℝ≥0) (hLip : ∀ x ∈ U, ∀ z, |f (x+A z)-f x| ≤ H*‖z‖) (mass : ℝ) :
    ExponentialSmoothOn (gaussianShiftColeHopf A mass f) U := by
  have hs := fun N => gaussianShiftColeHopf_smooth_exp_positive_jets_on_open
    N f U hU hf A hA B L hL hvalue H hLip mass
  refine ⟨fun x hx => ?_, fun r => ?_⟩
  · apply contDiffAt_infty.mpr
    intro N
    exact ((hs N).1 x hx).contDiffAt (hU.mem_nhds hx)
  · cases r with
    | zero =>
      obtain ⟨C, hC, hb⟩ := gaussianShiftColeHopf_value_barrier f U A hA H hLip mass
      refine ⟨max 0 (B+C)+L, 1, by positivity, by norm_num, ?_⟩
      intro x hx
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hlin : |gaussianShiftColeHopf A mass f x| ≤ B+C+L*‖x‖ := by
        linarith [hb x hx, hvalue x hx]
      have hn : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
      have he : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp_iff.mpr (norm_nonneg _)
      have h0 := mul_le_mul_of_nonneg_left he (le_max_left (0:ℝ) (B+C))
      have h1 := mul_le_mul_of_nonneg_left hn hL
      have hb0 := le_max_right (0:ℝ) (B+C)
      simpa only [one_mul] using hlin.trans (by nlinarith only [h0,h1,hb0])
    | succ r =>
      obtain ⟨C,D,hC,hD,hb⟩ := (hs (r+1)).2
      refine ⟨C^(r+1), (r+1:ℕ)*D, by positivity, by positivity, ?_⟩
      intro x hx
      apply (hb (r+1) (by omega) le_rfl x hx).trans_eq
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      congr 1
      ring


theorem contDiffAt_gaussianShiftAverage_of_exponentialSmoothOn
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ExponentialSmoothOn f U)
    (A : Field n →L[ℝ] E) (hA : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (x : E) (hx : x ∈ U) : ContDiffAt ℝ ∞ (gaussianShiftAverage A f) x := by
  apply contDiffAt_infty.mpr
  intro N
  obtain ⟨K,D,hK,hD,hj⟩ := hf.common_bound N
  have hfN : ContDiffOn ℝ N f U := fun y hy =>
    ((hf.smooth y hy).of_le (by simp)).contDiffWithinAt
  have hp (j : ℕ) (hjN : j ≤ N) (y : E) (hy : y ∈ U) :
      ‖iteratedFDeriv ℝ j f y‖ ≤ (K*Real.exp (D*‖y‖))^(j+1) := by
    have hbase : 1 ≤ K*Real.exp (D*‖y‖) := one_le_mul_of_one_le_of_one_le hK
      (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg y)))
    exact (hj j hjN y hy).trans (le_self_pow₀ hbase (by omega))
  have hs := (gaussianShiftAverage_smooth_exp_jets_on_open N f U hU hfN A hA K D hK hD hp).1
  exact (hs x hx).contDiffAt (hU.mem_nhds hx)

end QuantitativeFollowup
