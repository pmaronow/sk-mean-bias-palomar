module
public import QuantitativeFollowup.ExponentialSmoothComposition

@[expose] public section

/-! Composition with genuine bounded positive jets on an arbitrary normed
range. The unbounded inner function has an actual linear-growth envelope. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2200000
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exponentialSmoothOn_comp_boundedPositiveJets_normed
    (f : F → ℝ) (hf : BoundedPositiveJets f)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hv : ∀ y, |f y| ≤ B+L*‖y‖)
    (g : E → F) (U : Set E) (hg : ExponentialSmoothOn g U)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) (hgv : ∀ x ∈ U, ‖g x‖ ≤ S+T*‖x‖) :
    ExponentialSmoothOn (f ∘ g) U := by
  classical
  refine ⟨fun x hx => hf.1.contDiffAt.comp x (hg.smooth x hx), fun r => ?_⟩
  choose K hK hb using fun i : Fin r => hf.2 (i+1) (by omega)
  let J := B+L*S+L*T+∑ i, K i
  have hsumK := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hK i)
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact add_nonneg (add_nonneg (add_nonneg hB (mul_nonneg hL hS)) (mul_nonneg hL hT)) hsumK
  have houter (x : E) (hx : x ∈ U) (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ J*Real.exp ‖x‖ := by
    cases i with
    | zero =>
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hlin : |f (g x)| ≤ B+L*S+L*T*‖x‖ := by
        have hh := mul_le_mul_of_nonneg_left (hgv x hx) hL
        nlinarith only [hv (g x), hh]
      have hpow : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
      have he : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp_iff.mpr (norm_nonneg x)
      have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hK i)
      have h0 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ B+L*S)
      have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hL hT)
      have h2 := mul_nonneg hsum (Real.exp_pos ‖x‖).le
      dsimp only [J]
      nlinarith only [hlin,h0,h1,h2]
    | succ i =>
      let j : Fin r := ⟨i, by omega⟩
      have hk : K j ≤ J := by
        have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hK i) (Finset.mem_univ j)
        dsimp only [J]
        linarith [mul_nonneg hL hS, mul_nonneg hL hT]
      exact (hb j (g x)).trans (hk.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.one_le_exp_iff.mpr (norm_nonneg x)) hJ))
  obtain ⟨C,D,hC,hD,hgj⟩ := hg.common_bound r
  refine ⟨(r.factorial:ℝ)*J*C^r, 1+(r:ℝ)*D, by positivity, by positivity, ?_⟩
  intro x hx
  have hbase : 1 ≤ C*Real.exp (D*‖x‖) := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg x)))
  apply (DepthPaper.norm_iteratedFDeriv_comp_le_at hf.1.contDiffAt (hg.smooth x hx)
    r (J*Real.exp ‖x‖) (C*Real.exp (D*‖x‖)) (houter x hx)
    (fun i hi hir => (hgj i hir x hx).trans (le_self_pow₀ hbase (by omega)))).trans_eq
  rw [mul_pow, ←Real.exp_nat_mul]
  rw [show (1+(r:ℝ)*D)*‖x‖ = ‖x‖+(r:ℝ)*(D*‖x‖) by ring, Real.exp_add]
  ring

end QuantitativeFollowup
