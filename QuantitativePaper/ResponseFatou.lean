module
public import QuantitativePaper.ResponseCurvatureMidpointBound
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-! Fatou passage for genuine nonnegative curvature densities. The limit
functional is never assigned unproved second derivatives. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem response_fatou_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Fj : ℕ→Ω→ℝ) (Gapj : ℕ→ℝ) (Gap : ℝ)
    (hi : ∀j,Integrable (Fj j) P) (hng : ∀j,0≤ᵐ[P] Fj j)
    (hb : ∀j,(∫x,Fj j x∂P)≤Gapj j) (hGap : Tendsto Gapj atTop (nhds Gap))
    (g : Ω→ℝ) (hg : Integrable g P) (hgn : 0≤ᵐ[P] g)
    (hLower : ∀ᵐx∂P,∃Rj : ℕ→ℝ,∃R : ℝ,g x≤R ∧
      Tendsto Rj atTop (nhds R) ∧ ∀j,Rj j≤Fj j x) :
    (∫x,g x∂P)≤Gap:=by
  have hGp : 0≤Gap:=ge_of_tendsto hGap (.of_forall fun j=>
    (integral_nonneg_of_ae (hng j)).trans (hb j))
  have hl : ∀ᵐx∂P,ENNReal.ofReal (g x)≤
      liminf (fun j=>ENNReal.ofReal (Fj j x)) atTop:=by
    filter_upwards [hLower] with x hx
    obtain ⟨Rj,R,hR,hr,hbR⟩:=hx
    exact (ENNReal.ofReal_le_ofReal hR).trans
      ((ENNReal.tendsto_ofReal hr).liminf_eq.symm.le.trans
        (liminf_le_liminf (.of_forall fun j=>ENNReal.ofReal_le_ofReal (hbR j))))
  have hh : ENNReal.ofReal (∫x,g x∂P)≤ENNReal.ofReal Gap:=by
    rw [ofReal_integral_eq_lintegral_ofReal hg hgn]
    calc
      _≤∫⁻x,liminf (fun j=>ENNReal.ofReal (Fj j x)) atTop∂P:=lintegral_mono_ae hl
      _≤liminf (fun j=>∫⁻x,ENNReal.ofReal (Fj j x)∂P) atTop:=
        lintegral_liminf_le' (fun j=>(hi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _≤liminf (fun j=>ENNReal.ofReal (Gapj j)) atTop:=by
        have hb' : ∀ᶠj in atTop,(∫⁻x,ENNReal.ofReal (Fj j x)∂P)≤ENNReal.ofReal (Gapj j):=
          .of_forall fun j=>by
          rw [←ofReal_integral_eq_lintegral_ofReal (hi j) (hng j)]
          exact ENNReal.ofReal_le_ofReal (hb j)
        exact liminf_le_liminf hb'
      _=ENNReal.ofReal Gap:=(ENNReal.tendsto_ofReal hGap).liminf_eq
  exact (ENNReal.ofReal_le_ofReal_iff hGp).mp hh

end QuantitativePaper
