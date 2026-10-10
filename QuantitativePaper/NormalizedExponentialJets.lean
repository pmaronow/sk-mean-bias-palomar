module
public import QuantitativePaper.ExponentialJetBounds

@[expose] public section

/-! Uniform jets of a genuine normalized exponential posterior expectation.
The normalizer equals one at every parameter; locally integrable domination
and differentiation of the expectation are proved rather than assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace Ω]

theorem norm_iteratedFDeriv_exp_smul_const_le (N j : ℕ) (L : E → ℝ)
    (hL : ContDiff ℝ N L) (hj : j ≤ N) (K : ℝ) (hK : 0 ≤ K)
    (hB : ∀i,1 ≤ i → i ≤ N → ∀x,‖iteratedFDeriv ℝ i L x‖ ≤ K^i)
    (v : F) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Real.exp (L y) • v) x‖ ≤
      ‖v‖*((j.factorial : ℝ)*K^j)*Real.exp (L x) := by
  have he : ContDiff ℝ N (fun y => Real.exp (L y)) := hL.exp
  rw [iteratedFDeriv_smul_const_apply (he.of_le (by exact_mod_cast hj)).contDiffAt]
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
  rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_id,one_mul]
  have hh := norm_iteratedFDeriv_exp_mul_le L hL hj 1 K x (fun i hi hij => hB i hi (hij.trans hj) x)
  simp only [one_mul,abs_one,max_self,one_pow,mul_one] at hh
  have hm := mul_le_mul_of_nonneg_left hh (norm_nonneg v)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hm

theorem normalizedExponentialExpectation_jets (N : ℕ) (P : Measure Ω)
    (L : E → Ω → ℝ) (v : Ω → F) (K R : ℝ) (hK : 0 ≤ K)
    (hL : ∀z,ContDiff ℝ N (fun x => L x z))
    (hLip : ∃ M : ℝ≥0,∀z,LipschitzWith M (fun x => L x z))
    (hB : ∀i,1 ≤ i → i ≤ N → ∀x z,‖iteratedFDeriv ℝ i (fun y => L y z) x‖ ≤ K^i)
    (hv : ∀z,‖v z‖ ≤ R)
    (hMeas : ∀i,i ≤ N → ∀x,AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ i (fun y => Real.exp (L y z) • v z) x) P)
    (hi : ∀x,Integrable (fun z => Real.exp (L x z)) P)
    (hNorm : ∀x,(∫z,Real.exp (L x z) ∂P)=1) :
    ContDiff ℝ N (fun x => ∫z,Real.exp (L x z) • v z ∂P) ∧
      ∀j,j ≤ N → ∀x,‖iteratedFDeriv ℝ j (fun y => ∫z,Real.exp (L y z) • v z ∂P) x‖ ≤
        R*(j.factorial : ℝ)*K^j := by
  obtain ⟨M,hM⟩ := hLip
  have hSmooth (z) : ContDiff ℝ N (fun x => Real.exp (L x z) • v z) := (hL z).exp.smul_const _
  have hDom (x : E) : ∃s ∈ 𝓝 x,∃ B : ℕ → Ω → ℝ,
      (∀j,j ≤ N → Integrable (B j) P) ∧
      ∀j,j ≤ N → ∀y ∈ s,∀z,‖iteratedFDeriv ℝ j (fun u => Real.exp (L u z) • v z) y‖ ≤ B j z := by
    let B := fun j z => (R*(j.factorial : ℝ)*K^j*Real.exp M)*Real.exp (L x z)
    refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),B,fun j _ => (hi x).const_mul _,?_⟩
    intro j hj y hy z
    have hb := norm_iteratedFDeriv_exp_smul_const_le N j (fun u => L u z) (hL z) hj K hK
      (fun i hi hij u => hB i hi hij u z) (v z) y
    have he : Real.exp (L y z) ≤ Real.exp M*Real.exp (L x z) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := (hM z).dist_le_mul y x
      rw [Real.dist_eq] at hh
      have hxy : dist y x ≤ 1 := (Metric.mem_ball.mp hy).le
      have hm := mul_le_mul_of_nonneg_left hxy M.coe_nonneg
      have hh' : L y z-L x z ≤ M := (le_abs_self _).trans (hh.trans (by simpa only [mul_one] using hm))
      linarith
    have hp : 0 ≤ (j.factorial : ℝ)*K^j := by positivity
    have hRp := (norm_nonneg (v z)).trans (hv z)
    calc
      _ ≤ R*((j.factorial : ℝ)*K^j)*Real.exp (L y z) := hb.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hv z) hp) (Real.exp_pos _).le)
      _ ≤ R*((j.factorial : ℝ)*K^j)*(Real.exp M*Real.exp (L x z)) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hRp hp)
      _ = _ := by dsimp only [B];ring
  refine ⟨contDiff_integral_of_dominated_derivatives N P _ hSmooth hMeas hDom,?_⟩
  intro j hj x
  rw [iteratedFDeriv_integral_of_dominated_derivatives N P _ hSmooth hMeas hDom j hj x]
  have hh := norm_integral_le_of_norm_le
    (f := fun z => iteratedFDeriv ℝ j (fun y => Real.exp (L y z) • v z) x)
    (g := fun z => (R*(j.factorial : ℝ)*K^j)*Real.exp (L x z)) ((hi x).const_mul _)
    (Eventually.of_forall (fun z => by
      have hp : 0 ≤ (j.factorial : ℝ)*K^j := by positivity
      exact (norm_iteratedFDeriv_exp_smul_const_le N j _ (hL z) hj K hK
        (fun i hi hij y => hB i hi hij y z) (v z) x).trans
        (by
          have hp : 0 ≤ (j.factorial : ℝ)*K^j := by positivity
          have hh := mul_le_mul_of_nonneg_right (hv z) (mul_nonneg hp (Real.exp_pos (L x z)).le)
          simpa only [mul_assoc] using hh)))
  rw [integral_const_mul,hNorm x,mul_one] at hh
  exact hh

end QuantitativePaper
