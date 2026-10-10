module
public import QuantitativePaper.VectorTailPosteriorJets
public import QuantitativePaper.VectorClampedScheme

@[expose] public section

/-! Genuine all-order spatial bounds, uniform in profile depth and in every
overlap. The constants are constructed by induction on derivative order using
the actual normalized posterior, with no regularity or moment premise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem exists_uniform_vectorRecursion_jet_bound (n r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ,0 ≤ C ∧ ∀k (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
      j,j ≤ k+2 → ∀x,‖iteratedFDeriv ℝ r (vectorRecursion s β t p j) x‖ ≤ C := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases h1 : r=1
    · subst r
      exact ⟨Real.sqrt (n : ℝ),Real.sqrt_nonneg _,fun k s β t p j _ =>
        norm_vectorRecursion_firstJet_le s β t p j⟩
    · have hr2 : 2 ≤ r := by omega
      choose C hC0 hC using
        (fun i : Fin (r-1) => ih (i+1) (by omega) (by omega))
      let K : ℝ := 1+2*Real.sqrt (n : ℝ)+∑i : Fin (r-1),C i
      have hsum : 0 ≤ ∑i : Fin (r-1),C i := Finset.sum_nonneg fun i _ => hC0 i
      have hK1 : 1 ≤ K := by dsimp only [K];linarith [Real.sqrt_nonneg (n : ℝ)]
      have hK : 0 ≤ K := zero_le_one.trans hK1
      refine ⟨Real.sqrt (n : ℝ)*((r-1).factorial : ℝ)*K^(r-1),by positivity,?_⟩
      intro k s β t p j hj x
      have hB (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r-1) (j : ℕ) (hj : j ≤ k+2)
          (y : Field n) (z : (Fin j → Field n) × Configuration n) :
          ‖iteratedFDeriv ℝ i (fun u => vectorTailPosteriorLogDensity s β t p u j z) y‖ ≤ K^i := by
        let a : Fin (r-1) := ⟨i-1,by omega⟩
        have ha : (a : ℕ)+1=i := by dsimp only [a];omega
        have hUi : ∀j,j ≤ k+2 → ∀y,‖iteratedFDeriv ℝ i (vectorRecursion s β t p j) y‖ ≤ C a := by
          intro j hj y
          have hh := hC a k s β t p j hj y
          rw [ha] at hh
          exact hh
        have hTi (w y : Field n) (σ : Configuration n) :
            ‖iteratedFDeriv ℝ i (fun u => vectorTerminalExponent n β t p (u+w) σ) y‖ ≤
              Real.sqrt (n : ℝ) := by
          by_cases hi1 : i=1
          · rw [hi1]
            exact (norm_vectorTerminalExponent_firstJet β t p w y σ).le
          · rw [vectorTerminalExponent_higherJet_zero β t p w y σ i (by omega),norm_zero]
            positivity
        have hh := norm_vectorTailLogDensity_jet_le s β t p i (Real.sqrt (n : ℝ))
          (C a) (hC0 a) hUi hTi j hj y z
        have hCa : C a ≤ ∑i : Fin (r-1),C i :=
          Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ a)
        have hk : Real.sqrt (n : ℝ)+C a ≤ K := by dsimp only [K];nlinarith [Real.sqrt_nonneg (n : ℝ)]
        exact hh.trans (hk.trans (le_self_pow₀ hK1 (by omega)))
      have hh := norm_vectorRecursion_jet_from_tailScore s β t p (r-1) K hK hB j hj (r-1) le_rfl x
      have he : r-1+1=r := by omega
      rw [he] at hh
      exact hh

def vectorSpatialJetBound (n r : ℕ) : ℝ :=
  if hr : 1 ≤ r then Classical.choose (exists_uniform_vectorRecursion_jet_bound n r hr) else 0

theorem vectorSpatialJetBound_nonneg (n r : ℕ) : 0 ≤ vectorSpatialJetBound n r := by
  unfold vectorSpatialJetBound
  split_ifs with hr
  · exact (Classical.choose_spec (exists_uniform_vectorRecursion_jet_bound n r hr)).1
  · rfl

theorem norm_vectorRecursion_jet_le_uniform {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2) (r : ℕ) (hr : 1 ≤ r) (x : Field n) :
    ‖iteratedFDeriv ℝ r (vectorRecursion s β t p j) x‖ ≤ vectorSpatialJetBound n r := by
  unfold vectorSpatialJetBound
  rw [dif_pos hr]
  exact (Classical.choose_spec (exists_uniform_vectorRecursion_jet_bound n r hr)).2 k s β t p j hj x

theorem norm_vectorTailRecursion_jet_le_uniform {n k : ℕ} (s : RSBScheme k) (β t q : ℝ)
    (hq : q∈Icc 0 1) (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2)
    (r : ℕ) (hr : 1 ≤ r) (x : Field n) :
    ‖iteratedFDeriv ℝ r (vectorTailRecursion s β t q p j) x‖ ≤ vectorSpatialJetBound n r := by
  rw [vectorTailRecursion_eq_clamped s β t q hq p hj]
  exact norm_vectorRecursion_jet_le_uniform _ β t p j (by omega) r hr x

end QuantitativePaper
