module
public import FRSB.Comparison

@[expose] public section

/-! A local supporting inequality orders the actual second derivatives.
Only ordinary first derivatives on a neighborhood and their derivatives
at the comparison point are required. -/
open Set Filter
open scoped Topology
namespace QuantitativeFollowup

theorem second_derivative_comparison_of_local_order (f g df dg : ℝ→ℝ)
    (δ Af Ag : ℝ) (hδ : 0<δ)
    (hf : ∀u∈Ioo (-δ) δ,HasDerivAt f (df u) u)
    (hg : ∀u∈Ioo (-δ) δ,HasDerivAt g (dg u) u)
    (hdf : HasDerivAt df Af 0) (hdg : HasDerivAt dg Ag 0)
    (hle : ∀u∈Ioo (-δ) δ,g u-g 0≤f u-f 0) : Ag≤Af := by
  have hzero : (0:ℝ)∈Ioo (-δ) δ := by constructor <;> linarith
  have hloc : IsLocalMin (fun u=>f u-g u) 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with u hu
    linarith [hle u hu]
  have he : deriv (fun u=>f u-g u)=ᶠ[𝓝 (0:ℝ)] fun u=>df u-dg u := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with u hu
    exact ((hf u hu).sub (hg u hu)).deriv
  have hsecond : HasDerivAt (deriv (fun u=>f u-g u)) (Af-Ag) 0 :=
    (hdf.sub hdg).congr_of_eventuallyEq he
  have hnn := FRSB.localMin_second_deriv_nonneg hloc
    ((hf 0 hzero).continuousAt.sub (hg 0 hzero).continuousAt)
  rw [hsecond.deriv] at hnn
  linarith

end QuantitativeFollowup
