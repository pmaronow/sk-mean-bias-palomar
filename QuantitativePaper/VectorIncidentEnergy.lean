module
public import QuantitativePaper.VectorIncidentEnergyCoefficients

@[expose] public section

/-! The sharp coefficient vector is identified with the actual terminal
energy along the conditioned Gaussian prefix, not an auxiliary model. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem sitePrefixGaussianState_disorder {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i))
    (j : Fin (N+1)) :
    (sitePrefixGaussianState s β t i 0 j g).1 =
      ((fun e : Edge n => if he : e.val.1=i ∨ e.val.2=i then
        g ⟨.inl (some e),he⟩ else 0),0) := by
  unfold sitePrefixGaussianState
  rw [vectorPrefixEuclideanHistory_apply,vectorPrefixHistory_disorder]
  apply Prod.ext
  · funext e
    rfl
  · change Real.sqrt (1/2:ℝ) *
      (if ha : siteGaussianPredicate i (.inl none) then g ⟨.inl none,ha⟩ else 0) = 0
    simp [siteGaussianPredicate]

theorem sitePrefixGaussianState_final_field {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    (sitePrefixGaussianState s β t i 0 (Fin.last N) g).2 =
      EuclideanSpace.single i
        (∑ j : Fin N, prefixFieldIncrement s β t j * g ⟨.inr (j,i),rfl⟩) := by
  unfold sitePrefixGaussianState
  rw [vectorPrefixEuclideanHistory_final_field]
  ext l
  change (EuclideanSpace.proj l) (∑ j : Fin N, prefixFieldIncrement s β t j •
    WithLp.toLp 2 (fun l => gaussianCoordinateJoin (siteGaussianPredicate i) (g,0)
      (.inr (j,l)))) = _
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  change (∑ j : Fin N, prefixFieldIncrement s β t j *
    (if ha : l=i then g ⟨.inr (j,l),ha⟩ else 0)) = _
  by_cases hl : l=i
  · subst l
    simp
  · simp [hl,Ne.symm hl,EuclideanSpace.single_apply]

theorem siteTerminalEnergy_eq_inner {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (σ : Configuration n)
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    vectorTerminalExponent n β t
      (sitePrefixGaussianState s β t i 0 (Fin.last N) g).1
      (sitePrefixGaussianState s β t i 0 (Fin.last N) g).2 σ =
    inner ℝ (siteTerminalEnergyCoefficient (N:=N) s β t i σ) g := by
  rw [sitePrefixGaussianState_disorder,sitePrefixGaussianState_final_field]
  unfold vectorTerminalExponent energy Paper.skHamiltonian fieldDot
  simp only [zero_mul,add_zero,PiLp.single_apply,Finset.sum_mul]
  rw [Finset.sum_eq_single i (by intro l _ hli;simp [hli]) (by simp)]
  simp only [ite_true]
  have hir : inner ℝ (siteTerminalEnergyCoefficient (N:=N) s β t i σ) g =
      ∑ a, (siteTerminalEnergyCoefficient (N:=N) s β t i σ) a * g a := by
    simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]
  rw [hir]
  let f : IncidentEdge i ⊕ Fin N → ℝ := fun a => match a with
    | .inl e => (β*Real.sqrt t/Real.sqrt (n:ℝ)*
      Paper.spinSign (σ e.val.val.1)*Paper.spinSign (σ e.val.val.2))*
        g ⟨.inl (some e.val),e.property⟩
    | .inr j => (prefixFieldIncrement s β t j * Paper.spinSign (σ i))*
        g ⟨.inr (j,i),rfl⟩
  have hsum : (∑ a, (siteTerminalEnergyCoefficient (N:=N) s β t i σ) a * g a) =
      ∑ a : IncidentEdge i ⊕ Fin N, f a := by
    rw [←(siteGaussianIndexEquiv (N:=N) i).sum_comp f]
    apply Finset.sum_congr rfl
    intro a hmem
    rcases a with ⟨a,ha⟩
    rcases a with a | j
    · cases a with
      | none => exact False.elim ha
      | some e => rfl
    · have he : j.2=i := ha
      cases j with
      | mk j l =>
        dsimp only [Prod.snd] at he
        subst l
        rfl
  rw [hsum,Fintype.sum_sum_type]
  dsimp only [f]
  simp only [Finset.mul_sum]
  congr 1
  · simp_rw [show ∀e : Edge n,
        β*Real.sqrt t*(1/Real.sqrt (n:ℝ)*
          ((if he : e.val.1=i ∨ e.val.2=i then g ⟨.inl (some e),he⟩ else 0)*
            Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))) =
        if he : e.val.1=i ∨ e.val.2=i then
          (β*Real.sqrt t/Real.sqrt (n:ℝ)*Paper.spinSign (σ e.val.1)*
            Paper.spinSign (σ e.val.2))*g ⟨.inl (some e),he⟩ else 0 from by
      intro e;split_ifs <;> ring]
    let pred : Edge n → Prop := fun e => e.val.1=i ∨ e.val.2=i
    let f0 : Edge n → ℝ := fun e => if he : pred e then
      (β*Real.sqrt t/Real.sqrt (n:ℝ)*Paper.spinSign (σ e.val.1)*
        Paper.spinSign (σ e.val.2))*g ⟨.inl (some e),he⟩ else 0
    have hh := Fintype.sum_subtype_add_sum_subtype pred f0
    have h0 : (∑ e : {e : Edge n // ¬pred e},f0 e.val) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact dif_neg e.property
    rw [h0,add_zero] at hh
    calc
      _ = ∑ e : IncidentEdge i, f0 e.val := hh.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        exact dif_pos e.property
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem siteTerminalEnergy_bound {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : 0 ≤ β) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2) (i : Fin n)
    (σ : Configuration n) (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    |vectorTerminalExponent n β t
      (sitePrefixGaussianState s β t i 0 (Fin.last N) g).1
      (sitePrefixGaussianState s β t i 0 (Fin.last N) g).2 σ| ≤ β*‖g‖ := by
  rw [siteTerminalEnergy_eq_inner,←Real.norm_eq_abs]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_siteTerminalEnergyCoefficient_le s β t hβ ht hN i σ) (norm_nonneg g))

end QuantitativePaper
