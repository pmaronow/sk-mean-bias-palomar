module
public import QuantitativePaper.NormalizedExponentialJets

@[expose] public section

/-! Actual differentiation of an exponential expectation whose observable
also depends on the parameter. The envelope is shared by every parameter;
the weighted moments, rather than the reference measure's mass, control
its jets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace Ω]

def exponentialObservableJetCoefficient (j : ℕ) (K : ℝ) : ℝ :=
  (∑i ∈ Finset.range (j+1), (j.choose i : ℝ)*(i.factorial : ℝ))*K^j

theorem exponentialObservableJetCoefficient_nonneg (j : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ exponentialObservableJetCoefficient j K := by
  unfold exponentialObservableJetCoefficient
  positivity

theorem norm_iteratedFDeriv_exp_smul_observable_le (N j : ℕ) (L : E → ℝ)
    (v : E → F) (hL : ContDiff ℝ N L) (hv : ContDiff ℝ N v) (hj : j ≤ N)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hB : ∀i, 1 ≤ i → i ≤ N → ∀x, ‖iteratedFDeriv ℝ i L x‖ ≤ K^i)
    (hV : ∀i, i ≤ N → ∀x, ‖iteratedFDeriv ℝ i v x‖ ≤ A*K^i) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Real.exp (L y) • v y) x‖ ≤
      exponentialObservableJetCoefficient j K*(Real.exp (L x)*A) := by
  apply (norm_iteratedFDeriv_smul_le hL.exp hv x (by exact_mod_cast hj)).trans
  calc
    _ ≤ ∑i ∈ Finset.range (j+1),
        (j.choose i : ℝ)*(i.factorial : ℝ)*K^j*(Real.exp (L x)*A) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := by have hh := Finset.mem_range.mp hi; omega
      have hji : j-i ≤ N := (Nat.sub_le j i).trans hj
      have hE := norm_iteratedFDeriv_exp_mul_le L hL (hij.trans hj) 1 K x
        (fun a ha hai => hB a ha (hai.trans (hij.trans hj)) x)
      simp only [one_mul, abs_one, max_self, one_pow, mul_one] at hE
      have hmul := mul_le_mul hE (hV (j-i) hji x)
        (norm_nonneg _) (by positivity : 0 ≤ (i.factorial : ℝ)*Real.exp (L x)*K^i)
      have hh := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg (j.choose i))
      have hp : K^i*K^(j-i)=K^j := by rw [←pow_add, Nat.add_sub_of_le hij]
      calc
        _ = (j.choose i : ℝ)*(‖iteratedFDeriv ℝ i (fun y => Real.exp (L y)) x‖ *
            ‖iteratedFDeriv ℝ (j-i) v x‖) := by ring
        _ ≤ _ := hh
        _ = (j.choose i : ℝ)*(i.factorial : ℝ)*(K^i*K^(j-i))*(Real.exp (L x)*A) := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      unfold exponentialObservableJetCoefficient
      rw [←Finset.sum_mul, ←Finset.sum_mul]

theorem exponentialParameterizedExpectation_jets (N : ℕ) (P : Measure Ω)
    (L : E → Ω → ℝ) (v : E → Ω → F) (K R : ℝ) (A : Ω → ℝ)
    (hK : 0 ≤ K) (hA : ∀z, 0 ≤ A z)
    (hL : ∀z, ContDiff ℝ N (fun x => L x z))
    (hv : ∀z, ContDiff ℝ N (fun x => v x z))
    (hLip : ∃ M : ℝ≥0, ∀z, LipschitzWith M (fun x => L x z))
    (hB : ∀i, 1 ≤ i → i ≤ N → ∀x z, ‖iteratedFDeriv ℝ i (fun y => L y z) x‖ ≤ K^i)
    (hV : ∀i, i ≤ N → ∀x z, ‖iteratedFDeriv ℝ i (fun y => v y z) x‖ ≤ A z*K^i)
    (hMeas : ∀i, i ≤ N → ∀x, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ i (fun y => Real.exp (L y z) • v y z) x) P)
    (hi : ∀x, Integrable (fun z => Real.exp (L x z)*A z) P)
    (hMoment : ∀x, (∫z, Real.exp (L x z)*A z ∂P) ≤ R) :
    ContDiff ℝ N (fun x => ∫z, Real.exp (L x z) • v x z ∂P) ∧
      ∀j, j ≤ N → ∀x, ‖iteratedFDeriv ℝ j (fun y => ∫z, Real.exp (L y z) • v y z ∂P) x‖ ≤
        exponentialObservableJetCoefficient j K*R := by
  obtain ⟨M,hM⟩ := hLip
  have hSmooth (z) : ContDiff ℝ N (fun x => Real.exp (L x z) • v x z) := (hL z).exp.smul (hv z)
  have hDom (x : E) : ∃s ∈ 𝓝 x, ∃ B : ℕ → Ω → ℝ,
      (∀j, j ≤ N → Integrable (B j) P) ∧
      ∀j, j ≤ N → ∀y ∈ s, ∀z, ‖iteratedFDeriv ℝ j (fun u => Real.exp (L u z) • v u z) y‖ ≤ B j z := by
    let B := fun j z => (exponentialObservableJetCoefficient j K*Real.exp M)*(Real.exp (L x z)*A z)
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), B,
      fun j _ => (hi x).const_mul _, ?_⟩
    intro j hj y hy z
    have hb := norm_iteratedFDeriv_exp_smul_observable_le N j (fun u => L u z) (fun u => v u z)
      (hL z) (hv z) hj K (A z) hK (hA z)
      (fun i hi hij u => hB i hi hij u z) (fun i hij u => hV i hij u z) y
    have he : Real.exp (L y z) ≤ Real.exp M*Real.exp (L x z) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := (hM z).dist_le_mul y x
      rw [Real.dist_eq] at hh
      have hm := mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le M.coe_nonneg
      have hh' : L y z-L x z ≤ M := (le_abs_self _).trans (hh.trans (by simpa only [mul_one] using hm))
      linarith
    exact hb.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (hA z))
      (exponentialObservableJetCoefficient_nonneg j K hK)).trans_eq (by dsimp only [B]; ring))
  refine ⟨contDiff_integral_of_dominated_derivatives N P _ hSmooth hMeas hDom, ?_⟩
  intro j hj x
  rw [iteratedFDeriv_integral_of_dominated_derivatives N P _ hSmooth hMeas hDom j hj x]
  have hh := norm_integral_le_of_norm_le
    (f := fun z => iteratedFDeriv ℝ j (fun y => Real.exp (L y z) • v y z) x)
    (g := fun z => exponentialObservableJetCoefficient j K*(Real.exp (L x z)*A z))
    ((hi x).const_mul _) (.of_forall fun z =>
      norm_iteratedFDeriv_exp_smul_observable_le N j _ _ (hL z) (hv z) hj K (A z) hK (hA z)
        (fun i hi hij y => hB i hi hij y z) (fun i hij y => hV i hij y z) x)
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (hMoment x)
    (exponentialObservableJetCoefficient_nonneg j K hK))

end QuantitativePaper
