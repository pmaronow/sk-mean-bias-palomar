module
public import QuantitativePaper.ResponseMidpointWeight

@[expose] public section

/-! Direct midpoint improvement under an actual curvature-density limit.
It makes no differentiability claim about the limiting functional. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1600000

theorem response_midpoint_of_curvature_limit_lower
    (F₂ : ℕ→ℝ→ℝ) (Gapj : ℕ→ℝ) (Gap C a : ℝ)
    (hC : 0≤C) (ha : 0≤a) (ham : a≤1/2)
    (hi : ∀j,IntervalIntegrable (fun θ=>min θ (1-θ)*F₂ j θ) volume 0 1)
    (hng : ∀j,∀θ∈Ioo (0:ℝ) 1,0≤F₂ j θ)
    (hb : ∀j,(∫θ in (0:ℝ)..1,min θ (1-θ)*F₂ j θ)≤Gapj j)
    (hGap : Tendsto Gapj atTop (nhds Gap))
    (hLower : ∀θ∈Ioo a (1-a),∃Rj : ℕ→ℝ,∃R : ℝ,C≤R ∧
      Tendsto Rj atTop (nhds R) ∧ ∀j,Rj j≤F₂ j θ) :
    C*(1/4-a^2)≤Gap:=by
  let P : Measure ℝ:=volume.restrict (Ioc (0:ℝ) 1)
  let G : ℕ→ℝ→ℝ:=fun j θ=>min θ (1-θ)*F₂ j θ
  have hphys : ∀ᵐθ∂P,θ∈Ioo (0:ℝ) 1:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with θ hθ hθ1
    exact ⟨hθ.1,lt_of_le_of_ne hθ.2 hθ1⟩
  have hW (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1):0≤min θ (1-θ):=
    le_min hθ.1.le (by linarith [hθ.2])
  have hh:=response_fatou_integral_bound P G Gapj Gap
    (fun j=>(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp (hi j))
    (fun j=>hphys.mono fun θ hθ=>mul_nonneg (hW θ hθ) (hng j θ hθ))
    (fun j=>by simpa only [P,G,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hb j)
    hGap (responseMidpointLowerDensity a C) (integrable_responseMidpointLowerDensity a C ha)
    (hphys.mono fun θ hθ=>by
      by_cases hm : θ∈Ioo a (1-a)
      · rw [responseMidpointLowerDensity,indicator_of_mem hm]
        exact mul_nonneg (hW θ hθ) hC
      · rw [responseMidpointLowerDensity,indicator_of_notMem hm]
        exact le_rfl) ?_
  · rwa [integral_responseMidpointLowerDensity a C ha ham] at hh
  · filter_upwards [hphys] with θ hθ
    by_cases hm : θ∈Ioo a (1-a)
    · obtain ⟨Rj,R,hR,hr,hbR⟩:=hLower θ hm
      refine ⟨fun j=>min θ (1-θ)*Rj j,min θ (1-θ)*R,?_,tendsto_const_nhds.mul hr,?_⟩
      · rw [responseMidpointLowerDensity,indicator_of_mem hm]
        exact mul_le_mul_of_nonneg_left hR (hW θ hθ)
      · intro j
        exact mul_le_mul_of_nonneg_left (hbR j) (hW θ hθ)
    · refine ⟨fun _=>0,0,?_,tendsto_const_nhds,?_⟩
      · rw [responseMidpointLowerDensity,indicator_of_notMem hm]
      · intro j
        exact mul_nonneg (hW θ hθ) (hng j θ hθ)

end QuantitativePaper
