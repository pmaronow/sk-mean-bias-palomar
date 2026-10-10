module
public import FourPapersCommon.FiniteStreamingClosedJetLimit

@[expose] public section

/-! Pointwise convergence plus actual uniformly bounded within jets gives
all-order uniform convergence of the true jets on the closed interval. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace FourPapersCommon
open FiniteStreamingPolynomials
set_option maxHeartbeats 1000000

theorem exists_uniform_within_derivative_limit_on_Icc (f D : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hD : ∀ j z, z ∈ Icc (0 : ℝ) 1 → HasDerivWithinAt (f j) (D j z) (Icc 0 1) z)
    (L : ℝ≥0) (hL : ∀ j, LipschitzOnWith L (D j) (Icc 0 1))
    (hu : TendstoUniformlyOn f g atTop (Icc 0 1)) :
    ∃ d : ℝ → ℝ, TendstoUniformlyOn D d atTop (Icc 0 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (d x) (Icc 0 1) x) ∧
      ContinuousOn d (Icc 0 1) := by
  have hc := uniformCauchySeqOn_derivative_on_Icc f D hD L hL hu.uniformCauchySeqOn
  let d := fun x => limUnder atTop (fun j => D j x)
  have ht (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun j => D j x) atTop (𝓝 (d x)) :=
    (hc.cauchySeq hx).tendsto_limUnder
  have hd := hc.tendstoUniformlyOn_of_tendsto ht
  refine ⟨d, hd, fun x hx => ?_, ?_⟩
  · exact hasDerivWithinAt_of_uniform_derivative_limit_on_convex f D g d (Icc 0 1)
      (convex_Icc _ _) hD hd (fun x hx => hu.tendsto_at hx) x hx
  · exact hd.continuousOn (Eventually.of_forall (fun j => (hL j).continuousOn)).frequently

theorem tendstoUniformlyOn_actual_withinJets_on_Icc (F : ℕ → ℕ → ℝ → ℝ)
    (g : ℝ → ℝ)
    (hD : ∀ j r z, z ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (F j r) (F j (r+1) z) (Icc 0 1) z)
    (C : ℕ → ℝ≥0)
    (hB : ∀ j r, 1 ≤ r → ∀ z ∈ Icc (0 : ℝ) 1, ‖F j r z‖ ≤ C r)
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, Tendsto (fun j => F j 0 z) atTop (𝓝 (g z))) :
    (∀ r, TendstoUniformlyOn (fun j => F j r)
      (withinJet g (Icc 0 1) r) atTop (Icc 0 1)) ∧
    (∀ r z, z ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (withinJet g (Icc 0 1) r)
        (withinJet g (Icc 0 1) (r+1) z) (Icc 0 1) z) := by
  have hLip (j r : ℕ) : LipschitzOnWith (C (r+1)) (F j r) (Icc 0 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc _ _) (hD j r)
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hB j (r+1) (by omega) z hz
  have h0 : TendstoUniformlyOn (fun j => F j 0) g atTop (Icc 0 1) :=
    tendstoUniformlyOn_compact_of_pointwise_lipschitzOn _ _ _ _ isCompact_Icc
      (fun j => hLip j 0) hp
  have advance (r : ℕ)
      (hr : TendstoUniformlyOn (fun j => F j r) (withinJet g (Icc 0 1) r)
        atTop (Icc 0 1)) :
      TendstoUniformlyOn (fun j => F j (r+1)) (withinJet g (Icc 0 1) (r+1))
        atTop (Icc 0 1) ∧
      ∀ z ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (withinJet g (Icc 0 1) r)
          (withinJet g (Icc 0 1) (r+1) z) (Icc 0 1) z := by
    obtain ⟨d, hd, hder, hc⟩ := exists_uniform_within_derivative_limit_on_Icc
      (fun j => F j r) (fun j => F j (r+1)) (withinJet g (Icc 0 1) r)
      (fun j => hD j r) (C (r+2)) (fun j => by simpa [Nat.add_assoc] using hLip j (r+1)) hr
    have he (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
        d z = withinJet g (Icc 0 1) (r+1) z :=
      ((hder z hz).derivWithin (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) z hz)).symm
    exact ⟨hd.congr_right he, fun z hz => by rw [← he z hz]; exact hder z hz⟩
  have hall (r : ℕ) : TendstoUniformlyOn (fun j => F j r)
      (withinJet g (Icc 0 1) r) atTop (Icc 0 1) := by
    induction r with
    | zero => exact h0
    | succ r ih => exact (advance r ih).1
  exact ⟨hall, fun r => (advance r (hall r)).2⟩

end FourPapersCommon
