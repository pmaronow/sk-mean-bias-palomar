module
public import QuantitativePaper.ZeroTemperatureProfileLaw

@[expose] public section

/-! The source's local monotonicity already gives a measurable representative.
No measurability condition is added to its raw admissible class. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ENNReal
namespace QuantitativePaper.ZeroTemperatureProfile

/-- Canonical representative, equal to the supplied source profile on `[0,1)`. -/
def rawExtension (γ : ℝ → ℝ) (q : ℝ) : ℝ :=
  if q ∈ Ico (0 : ℝ) 1 then γ q else 0

@[simp] theorem rawExtension_of_mem (γ : ℝ → ℝ) {q : ℝ} (hq : q ∈ Ico 0 1) :
    rawExtension γ q = γ q := by simp [rawExtension, hq]

theorem measurable_rawExtension (γ : ℝ → ℝ) (hm : MonotoneOn γ (Ico 0 1)) :
    Measurable (rawExtension γ) := by
  have hm' : Monotone (fun q : Ico (0 : ℝ) 1 => γ q) :=
    fun x y hxy => hm x.property y.property hxy
  refine measurable_of_restrict_of_restrict_compl (s := Ico (0 : ℝ) 1) measurableSet_Ico ?_ ?_
  · have he : (Ico (0 : ℝ) 1).domRestrict (rawExtension γ) = fun q : Ico (0 : ℝ) 1 => γ q := by
      funext q
      exact rawExtension_of_mem γ q.property
    rw [he]
    exact hm'.measurable
  · have he : (Ico (0 : ℝ) 1)ᶜ.domRestrict (rawExtension γ) = fun _ => 0 := by
      funext q
      exact ite_eq_right q.property
    rw [he]
    exact measurable_const

/-- Realize exactly the raw admissibility assumptions of the manuscript. -/
def ofRaw {lam : ℝ} (γ : ℝ → ℝ) (hm : MonotoneOn γ (Ico 0 1))
    (hl : ∀ q ∈ Ico 0 1, lam ≤ γ q)
    (hc : ∀ q ∈ Ico 0 1, ContinuousWithinAt γ (Ici q) q)
    (hi : IntervalIntegrable γ volume 0 1) : ZeroTemperatureProfile lam where
  toFun := rawExtension γ
  measurable := measurable_rawExtension γ hm
  monotoneOn := by
    intro x hx y hy hxy
    simpa only [rawExtension_of_mem γ hx, rawExtension_of_mem γ hy] using hm hx hy hxy
  lower := by
    intro q hq
    simpa only [rawExtension_of_mem γ hq] using hl q hq
  rightContinuous := by
    intro q hq
    refine (hc q hq).congr_of_eventuallyEq_of_mem ?_ (by simp)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hq.2), self_mem_nhdsWithin] with x hx hxq
    exact rawExtension_of_mem γ ⟨hq.1.trans hxq, hx⟩
  intervalIntegrable := hi.congr_uIoo (by
    intro q hq
    rw [uIoo_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hq
    exact (rawExtension_of_mem γ ⟨hq.1.le, hq.2⟩).symm)

theorem ofRaw_eqOn {lam : ℝ} (γ : ℝ → ℝ) (hm : MonotoneOn γ (Ico 0 1))
    (hl : ∀ q ∈ Ico 0 1, lam ≤ γ q)
    (hc : ∀ q ∈ Ico 0 1, ContinuousWithinAt γ (Ici q) q)
    (hi : IntervalIntegrable γ volume 0 1) :
    EqOn (ofRaw γ hm hl hc hi) γ (Ico 0 1) := by
  intro q hq
  exact rawExtension_of_mem γ hq

theorem ofRaw_ae_eq {lam : ℝ} (γ : ℝ → ℝ) (hm : MonotoneOn γ (Ico 0 1))
    (hl : ∀ q ∈ Ico 0 1, lam ≤ γ q)
    (hc : ∀ q ∈ Ico 0 1, ContinuousWithinAt γ (Ici q) q)
    (hi : IntervalIntegrable γ volume 0 1) :
    (ofRaw γ hm hl hc hi : ℝ → ℝ) =ᵐ[volume.restrict (Ioc 0 1)] γ := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  exact ofRaw_eqOn γ hm hl hc hi ⟨hq.1.le, hq.2⟩

end QuantitativePaper.ZeroTemperatureProfile
