module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

/-! Genuine boundary intervals extracted from one-sided-Lipschitz and
antitone level sets. Neither endpoint nor sign persistence is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem one_sided_negative_boundary_interval (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0 < L) (hA : 0 < A)
    (hslope : ∀ z x : ℝ, 0 ≤ z → z ≤ x → x < q →
      psi x - psi z ≤ L * (x - z))
    (hne : {x : ℝ | x ∈ Ioo (0 : ℝ) q ∧ q - A / (2 * L) ≤ x ∧ psi x < -A}.Nonempty) :
    ∃ a : ℝ, a ∈ Ico (0 : ℝ) q ∧
      {x : ℝ | x ∈ Ioo (0 : ℝ) q ∧ q - A / (2 * L) ≤ x ∧ psi x < -A} ⊆ Icc a q ∧
      volume.real {x : ℝ | x ∈ Ioo (0 : ℝ) q ∧ q - A / (2 * L) ≤ x ∧ psi x < -A} ≤ q - a ∧
      q - a ≤ A / (2 * L) ∧
      ∀ z ∈ Ioo a q, psi z < -A / 2 := by
  let D := {x : ℝ | x ∈ Ioo (0 : ℝ) q ∧ q - A / (2 * L) ≤ x ∧ psi x < -A}
  have hDne : D.Nonempty := hne
  have hb : BddBelow D := ⟨0, fun x hx => hx.1.1.le⟩
  let a := sInf D
  have ha0 : 0 ≤ a := le_csInf hDne (fun x hx => hx.1.1.le)
  have hqa : q - A / (2 * L) ≤ a := le_csInf hDne (fun x hx => hx.2.1)
  have haq : a < q := by
    obtain ⟨x, hx⟩ := hDne
    exact (csInf_le hb hx).trans_lt hx.1.2
  have hsub : D ⊆ Icc a q := fun x hx => ⟨csInf_le hb hx, hx.1.2.le⟩
  have hm : volume.real D ≤ q - a := by
    have hh := measureReal_mono hsub (show volume (Icc a q) ≠ ∞ by simp)
    rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr haq.le)] at hh
    exact hh
  refine ⟨a, ⟨ha0, haq⟩, hsub, hm, by linarith, ?_⟩
  intro z hz
  obtain ⟨x, hx, hxz⟩ := exists_lt_of_csInf_lt hDne hz.1
  have hs := hslope x z hx.1.1.le hxz.le hz.2
  have hdist : z - x < A / (2 * L) := by linarith [hx.2.1, hz.2]
  have hmul := mul_lt_mul_of_pos_left hdist hL
  have hcancel : L * (A / (2 * L)) = A / 2 := by field_simp
  rw [hcancel] at hmul
  linarith [hx.2.2]

theorem antitone_positive_boundary_interval (psi : ℝ → ℝ) (q A : ℝ)
    (hanti : AntitoneOn psi (Icc q 1))
    (hne : {x : ℝ | x ∈ Icc q 1 ∧ A < psi x}.Nonempty) :
    ∃ b : ℝ, b ∈ Icc q 1 ∧
      {x : ℝ | x ∈ Icc q 1 ∧ A < psi x} ⊆ Icc q b ∧
      volume.real {x : ℝ | x ∈ Icc q 1 ∧ A < psi x} = b - q ∧
      ∀ z ∈ Ioo q b, A < psi z := by
  let D := {x : ℝ | x ∈ Icc q 1 ∧ A < psi x}
  have hDne : D.Nonempty := hne
  have hb : BddAbove D := ⟨1, fun x hx => hx.1.2⟩
  let b := sSup D
  have hb1 : b ≤ 1 := csSup_le hDne (fun x hx => hx.1.2)
  have hqb : q ≤ b := by
    obtain ⟨x, hx⟩ := hDne
    exact hx.1.1.trans (le_csSup hb hx)
  have hsub : D ⊆ Icc q b := fun x hx => ⟨hx.1.1, le_csSup hb hx⟩
  have hsign (z : ℝ) (hz : z ∈ Ioo q b) : A < psi z := by
    obtain ⟨x, hx, hzx⟩ := exists_lt_of_lt_csSup hDne hz.2
    exact hx.2.trans_le (hanti ⟨hz.1.le, hz.2.le.trans hb1⟩ hx.1 hzx.le)
  have hin : Ioo q b ⊆ D := fun z hz =>
    ⟨⟨hz.1.le, hz.2.le.trans hb1⟩, hsign z hz⟩
  have he : volume D = volume (Icc q b) := by
    apply le_antisymm (measure_mono hsub)
    rw [Real.volume_Icc, ← Real.volume_Ioo]
    exact measure_mono hin
  have hm : volume.real D = b - q := by
    rw [Measure.real, he, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hqb)]
  exact ⟨b, ⟨hqb, hb1⟩, hsub, hm, hsign⟩

theorem middle_half_closure_inside (a b : ℝ) (hab : a < b) :
    Icc (a + (b - a) / 4) (a + 3 * (b - a) / 4) ⊆ Ioo a b := by
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

end FourPapersCommon
