module
public import HexagonPaper.VariableScalarClockDriver

@[expose] public section

/-! The current paper permits coefficients positive almost everywhere.
The existing genuine Itô/path-likelihood construction uses an everywhere
positive representative.  The bridges below preserve the coefficient,
every prefix clock, every coefficient-weighted drift integral, and the
square-root noise integrand almost everywhere. -/
noncomputable section
open Set MeasureTheory
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 600000

def currentScalarPositiveRepresentative (c : ℝ → ℝ) (q : ℝ) : ℝ :=
  if 0 < c q then c q else 1

theorem currentScalarPositiveRepresentative_measurable (c : ℝ → ℝ)
    (hc : Measurable c) : Measurable (currentScalarPositiveRepresentative c) := by
  exact hc.ite (measurableSet_lt measurable_const hc) measurable_const

theorem currentScalarPositiveRepresentative_positive (c : ℝ → ℝ) (q : ℝ) :
    0 < currentScalarPositiveRepresentative c q := by
  unfold currentScalarPositiveRepresentative
  split_ifs with h
  · exact h
  · norm_num

theorem currentScalarPositiveRepresentative_bounded (c : ℝ → ℝ) (M : ℝ)
    (hM : ∀ q ∈ Icc (0 : ℝ) 1, ‖c q‖ ≤ M) :
    ∀ q ∈ Icc (0 : ℝ) 1, ‖currentScalarPositiveRepresentative c q‖ ≤ max M 1 := by
  intro q hq
  unfold currentScalarPositiveRepresentative
  split_ifs
  · exact (hM q hq).trans (le_max_left _ _)
  · simpa only [norm_one] using (le_max_right M 1)

theorem currentScalarPositiveRepresentative_ae (c : ℝ → ℝ)
    (hpos : ∀ᵐ q ∂volume.restrict (Icc (0 : ℝ) 1), 0 < c q) :
    currentScalarPositiveRepresentative c =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] c := by
  filter_upwards [hpos] with q hq
  simp only [currentScalarPositiveRepresentative, if_pos hq]

theorem currentScalarPositiveRepresentative_sqrt_ae (c : ℝ → ℝ)
    (hpos : ∀ᵐ q ∂volume.restrict (Icc (0 : ℝ) 1), 0 < c q) :
    (fun q => Real.sqrt (currentScalarPositiveRepresentative c q))
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun q => Real.sqrt (c q)) :=
  (currentScalarPositiveRepresentative_ae c hpos).fun_comp Real.sqrt

theorem currentScalarPositiveRepresentative_prefix_ae (c : ℝ → ℝ)
    (hpos : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) 1), 0 < c r)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    currentScalarPositiveRepresentative c =ᵐ[volume.restrict (uIoc (0 : ℝ) q)] c := by
  apply ae_restrict_of_ae_restrict_of_subset ?_
    (currentScalarPositiveRepresentative_ae c hpos)
  intro r hr
  rw [uIoc_of_le hq.1] at hr
  exact ⟨hr.1.le, hr.2.trans hq.2⟩

theorem currentScalarPositiveRepresentative_primitive_eq (c : ℝ → ℝ)
    (hpos : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) 1), 0 < c r)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    scalarCoefficientPrimitive (currentScalarPositiveRepresentative c) q =
      scalarCoefficientPrimitive c q := by
  exact intervalIntegral.integral_congr_ae_restrict
    (currentScalarPositiveRepresentative_prefix_ae c hpos q hq)

theorem currentScalarPositiveRepresentative_drift_integral_eq (c : ℝ → ℝ)
    (hpos : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) 1), 0 < c r)
    (F : ℝ → ℝ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ r in (0 : ℝ)..q, currentScalarPositiveRepresentative c r * F r) =
      ∫ r in (0 : ℝ)..q, c r * F r := by
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [currentScalarPositiveRepresentative_prefix_ae c hpos q hq] with r hr
  rw [hr]

theorem currentScalarPositiveRepresentative_driver_ready (c : ℝ → ℝ)
    (hc : Measurable c) (M : ℝ)
    (hM : ∀ q ∈ Icc (0 : ℝ) 1, ‖c q‖ ≤ M)
    (hpos : ∀ᵐ q ∂volume.restrict (Icc (0 : ℝ) 1), 0 < c q) :
    Measurable (currentScalarPositiveRepresentative c) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ‖currentScalarPositiveRepresentative c q‖ ≤ max M 1) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, 0 < currentScalarPositiveRepresentative c q) ∧
      currentScalarPositiveRepresentative c =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] c ∧
      (∀ q ∈ Icc (0 : ℝ) 1,
        scalarCoefficientPrimitive (currentScalarPositiveRepresentative c) q =
          scalarCoefficientPrimitive c q) := by
  exact ⟨currentScalarPositiveRepresentative_measurable c hc,
    currentScalarPositiveRepresentative_bounded c M hM,
    fun q _ => currentScalarPositiveRepresentative_positive c q,
    currentScalarPositiveRepresentative_ae c hpos,
    currentScalarPositiveRepresentative_primitive_eq c hpos⟩

end HexagonPaper
