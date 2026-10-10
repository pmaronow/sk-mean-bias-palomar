module
public import QuantitativeFollowup.ScalarGaussianHistoryCurve

@[expose] public section

/-! Genuine local norm bounds for the Gaussian input and its derivative.
Zero-variance increments are identically zero; positive increments have a
nonzero square-root denominator in the actual derivative curve. -/
noncomputable section
open Set Filter
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem continuous_scalarSchemeTransportCoefficient (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) :
    Continuous (fun u=>scalarSchemeTransportCoefficient s β φ u i) := by
  unfold scalarSchemeTransportCoefficient
  fun_prop

theorem continuousAt_scalarSchemeTransportCoefficientDerivative_zero (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (i : ℕ) (hi : i≤k+1) :
    ContinuousAt (fun u=>scalarSchemeTransportCoefficientDerivative s β φ u i) 0 := by
  by_cases he : s.q i=s.q (i+1)
  · simp only [scalarSchemeTransportCoefficientDerivative,ite_eq_left he]
    exact continuousAt_const
  · have hp := scalarSchemeTransport_variance_pos s β hβ φ L hφ h0 h1 0 (by simp) i hi he
    have hc : scalarSchemeTransportCoefficient s β φ 0 i≠0 :=
      (Real.sqrt_pos.mpr hp).ne'
    have hd := (continuousAt_const (y:=β^2*(φ (scalarSchemeTransportNode s (i+1))-
      φ (scalarSchemeTransportNode s i)))).div
      (continuousAt_const.mul (continuous_scalarSchemeTransportCoefficient s β φ i).continuousAt)
      (mul_ne_zero (by norm_num : (2:ℝ)≠0) hc)
    simp only [scalarSchemeTransportCoefficientDerivative,ite_eq_right he]
    convert! hd using 1

theorem continuousAt_scalarTransportGaussianDerivative_zero (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) :
    ContinuousAt (fun u=>scalarCoefficientHistoryLinear
      (scalarSchemeTransportCoefficientDerivative s β φ u) (k+2)) 0 := by
  simp_rw [scalarCoefficientHistoryLinear_eq_masks]
  apply tendsto_finsetSum
  intro i _
  exact (continuousAt_scalarSchemeTransportCoefficientDerivative_zero s β hβ φ L hφ h0 h1 i
    (by omega)).smul continuousAt_const

theorem exists_scalarTransportGaussian_local_bounds (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) :
    ∃K H : ℝ≥0,∀ᶠu in 𝓝 (0:ℝ),
      ‖scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)‖≤K ∧
      ‖scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ u) (k+2)‖≤H := by
  let A := fun u=>scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)
  let B := fun u=>scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ u) (k+2)
  let K : ℝ≥0 := ⟨‖A 0‖+1,by positivity⟩
  let H : ℝ≥0 := ⟨‖B 0‖+1,by positivity⟩
  have hA : ContinuousAt A 0 := (hasDerivAt_scalarTransportGaussianHistory s β hβ φ L hφ h0 h1 0 (by simp)).continuousAt
  have hB : ContinuousAt B 0 := continuousAt_scalarTransportGaussianDerivative_zero s β hβ φ L hφ h0 h1
  refine ⟨K,H,?_⟩
  filter_upwards [hA.norm.eventually_lt_const (by linarith : ‖A 0‖<‖A 0‖+1),
    hB.norm.eventually_lt_const (by linarith : ‖B 0‖<‖B 0‖+1)] with u hu hv
  exact ⟨hu.le,hv.le⟩

end QuantitativeFollowup
