module
public import QuantitativePaper.ZeroTemperatureProfileLawClosure
public import QuantitativePaper.ZeroTemperatureControlInfimum

@[expose] public section

/-! The scalar zero-temperature limit follows from actual profile measures,
actual terminal comparison, and actual L1 completion of unbounded profiles.
No zero-temperature convergence premise is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

theorem zeroScalarValue_le_scalarEnergyValue (lam : ℝ) (hLam : 0 ≤ lam)
    (β : ℝ) (hβ : 0<β) (hLamBeta : lam≤β) :
    zeroScalarValue lam ≤ scalarEnergyValue β lam := by
  have hs : lam/β≤1:=(div_le_one hβ).mpr hLamBeta
  let μ:=constrainedParisiMinimizer β (lam/β) hs
  have hf : μ∈scalarFloor (lam/β):=constrainedParisiMinimizer_mem β (lam/β) hs
  let γ:=ZeroTemperatureProfile.ofParisiMeasure lam β hβ μ hf
  have hz:=zeroScalarValue_le_profile hLam γ
  have hh:=(zeroTemperatureFunctional_parisi_sandwich β hβ μ).1
  change zeroTemperatureFunctional γ ≤ scalarParisiFunctional β μ/β at hh
  have he : scalarEnergyValue β lam=scalarParisiFunctional β μ/β := by
    rw [scalarEnergyValue,constrainedParisiValue_eq_minimum β (lam/β) hs]
  rw [he]
  exact hz.trans hh

/-- Literal scalar limit at every nonnegative root constraint. -/
theorem scalar_zero_temperature_limit (lam : ℝ) (hLam : 0 ≤ lam) :
    Tendsto (fun β:ℝ=>scalarEnergyValue β lam) atTop (𝓝 (zeroScalarValue lam)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (max 0 lam)] with β hβ
    have hβ0 : 0<β:=(le_max_left _ _).trans_lt hβ
    have hLamBeta : lam≤β:=((le_max_right _ _).trans_lt hβ).le
    exact ha.trans_le (zeroScalarValue_le_scalarEnergyValue lam hLam β hβ0 hLamBeta)
  · intro a ha
    obtain ⟨v,hv,hva⟩:=exists_lt_of_csInf_lt (zeroScalarValueSet_nonempty lam) ha
    obtain ⟨γ,rfl⟩:=hv
    have hmid : zeroTemperatureFunctional γ<
        (zeroTemperatureFunctional γ+a)/2 := by linarith
    have ht:=tendsto_zeroTemperatureFunctional_truncation γ γ.measurable γ.intervalIntegrable
      (γ.ae_nonneg hLam)
    obtain ⟨R,hR,hcost⟩:=((eventually_ge_atTop lam).and (ht.eventually (gt_mem_nhds hmid))).exists
    let η:=γ.truncate hLam R hR
    have heta : (η:ℝ→ℝ)=zeroProfileTruncation γ R := rfl
    have hetaCost : zeroTemperatureFunctional η<a := by
      rw [heta]
      linarith
    have hδ : 0<a-zeroTemperatureFunctional η:=sub_pos.mpr hetaCost
    have hlog : Tendsto (fun β:ℝ=>Real.log 2/β) atTop (𝓝 0):=
      tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [eventually_gt_atTop (max 0 R),hlog.eventually (gt_mem_nhds hδ)] with β hβ hb
    have hβ0 : 0<β:=(le_max_left _ _).trans_lt hβ
    have hRβ : R≤β:=((le_max_right _ _).trans_lt hβ).le
    have hupper : ∀q∈Ico (0:ℝ) 1,η q≤β:=fun q _=>(γ.truncate_upper hLam R hR q).trans hRβ
    have hh:=scalarEnergyValue_le_bounded_zeroProfile η hLam β hβ0 hupper
    exact hh.trans_lt (by linarith)

def groundScalarValue : ℝ :=zeroScalarValue 0

theorem scalar_zero_temperature_limit_at_zero :
    Tendsto (fun β:ℝ=>scalarEnergyValue β 0) atTop (𝓝 groundScalarValue) :=
  scalar_zero_temperature_limit 0 le_rfl

end QuantitativePaper
