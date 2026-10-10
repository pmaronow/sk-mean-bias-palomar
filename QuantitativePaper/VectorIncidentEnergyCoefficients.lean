module
public import QuantitativePaper.VectorPrefixFieldSum
public import QuantitativePaper.VectorTerminalLinear

@[expose] public section

/-! Sharp Euclidean coefficients of the true incident-site terminal energy.
Their squared norm retains both the N-1 triangular disorder coordinates
and the accumulated prefix field variance. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def siteGaussianIndexEquiv {n N : ℕ} (i : Fin n) :
    SiteGaussianIndex (N:=N) i ≃ IncidentEdge i ⊕ Fin N where
  toFun a := by
    rcases a with ⟨a,ha⟩
    rcases a with a | j
    · cases a with
      | none => exact False.elim ha
      | some e => exact .inl ⟨e,ha⟩
    · exact .inr j.1
  invFun a := match a with
    | .inl e => ⟨.inl (some e.val),e.property⟩
    | .inr j => ⟨.inr (j,i),rfl⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    rcases a with a | j
    · cases a with
      | none => exact False.elim ha
      | some e => rfl
    · apply Subtype.ext
      change Sum.inr (j.1,i) = Sum.inr j
      congr 1
      exact Prod.ext rfl ha.symm
  right_inv a := by cases a <;> rfl

def siteTerminalEnergyCoefficient {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (σ : Configuration n) : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i) :=
  WithLp.toLp 2 (fun a => match siteGaussianIndexEquiv i a with
    | .inl e => (β*Real.sqrt t/Real.sqrt (n:ℝ)) *
        Paper.spinSign (σ e.val.val.1)*Paper.spinSign (σ e.val.val.2)
    | .inr j => prefixFieldIncrement s β t j * Paper.spinSign (σ i))

theorem siteTerminalEnergyCoefficient_norm_square {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2) (i : Fin n)
    (σ : Configuration n) :
    ‖siteTerminalEnergyCoefficient (N:=N) s β t i σ‖^2 =
      β^2*t/(n:ℝ)*(n-1:ℕ) + (1-t)*β^2*s.q N := by
  have hn : 0 < n := by have hi := i.isLt; omega
  have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ a : SiteGaussianIndex (N:=N) i, (match siteGaussianIndexEquiv i a with
      | .inl e => β*Real.sqrt t/Real.sqrt (n:ℝ)*
          Paper.spinSign (σ e.val.val.1)*Paper.spinSign (σ e.val.val.2)
      | .inr j => prefixFieldIncrement s β t j * Paper.spinSign (σ i))^2) = _
  let f : IncidentEdge i ⊕ Fin N → ℝ := fun a => match a with
    | .inl e => β*Real.sqrt t/Real.sqrt (n:ℝ)*
        Paper.spinSign (σ e.val.val.1)*Paper.spinSign (σ e.val.val.2)
    | .inr j => prefixFieldIncrement s β t j * Paper.spinSign (σ i)
  change (∑ a, (f (siteGaussianIndexEquiv i a))^2) = _
  rw [(siteGaussianIndexEquiv (N:=N) i).sum_comp (fun a => (f a)^2),
    Fintype.sum_sum_type]
  dsimp only [f]
  simp only [mul_pow,Paper.spinSign_sq,mul_one,div_pow]
  rw [Real.sq_sqrt ht.1, Real.sq_sqrt (by positivity : (0:ℝ)≤n),
    Finset.sum_const, Finset.card_univ,card_incidentEdge,
    prefixFieldIncrement_sum_square s β t ht.2 N hN]
  simp only [nsmul_eq_mul]
  ring

theorem norm_siteTerminalEnergyCoefficient_le {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2)
    (i : Fin n) (σ : Configuration n) :
    ‖siteTerminalEnergyCoefficient (N:=N) s β t i σ‖ ≤ β := by
  have hn : 0 < n := by have hi := i.isLt; omega
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have hm : ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hq := s.q_le_one hN
  have hsq := siteTerminalEnergyCoefficient_norm_square (N:=N) s β t ht hN i σ
  have hfirst : β^2*t/(n:ℝ)*((n-1:ℕ):ℝ) ≤ β^2*t := by
    calc
      _ ≤ β^2*t/(n:ℝ)*(n:ℝ) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by field_simp
  have hsecond : (1-t)*β^2*s.q N ≤ (1-t)*β^2 :=
    mul_le_of_le_one_right (mul_nonneg ht1 (sq_nonneg β)) hq
  nlinarith [norm_nonneg (siteTerminalEnergyCoefficient (N:=N) s β t i σ)]

end QuantitativePaper
