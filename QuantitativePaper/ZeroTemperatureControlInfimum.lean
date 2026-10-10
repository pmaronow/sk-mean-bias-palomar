module
public import QuantitativePaper.ZeroTemperatureProfileLaw
public import QuantitativePaper.ZeroTemperatureControlFunctional
public import QuantitativePaper.EnergyMomentIdentity

@[expose] public section

/-! The literal infimum over actual integrable monotone zero-temperature
profiles and the actual scalar comparison for every bounded profile. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

def ZeroTemperatureProfile.constantProfile (lam : ℝ) : ZeroTemperatureProfile lam where
  toFun:=fun _=>lam
  measurable:=measurable_const
  monotoneOn:=fun _ _ _ _ _=>le_rfl
  lower:=fun _ _=>le_rfl
  rightContinuous:=fun _ _=>continuousWithinAt_const
  intervalIntegrable:=intervalIntegrable_const

def zeroScalarValueSet (lam : ℝ) : Set ℝ :=
  {v | ∃γ:ZeroTemperatureProfile lam,v=zeroTemperatureFunctional γ}

def zeroScalarValue (lam : ℝ) : ℝ :=sInf (zeroScalarValueSet lam)

theorem ZeroTemperatureProfile.ae_nonneg {lam : ℝ} (γ : ZeroTemperatureProfile lam)
    (hLam : 0 ≤ lam) : ∀ᵐ q ∂volume,q∈Ioc (0:ℝ) 1→0≤γ q := by
  filter_upwards [volume.ae_ne (1:ℝ)] with q hq hqi
  exact hLam.trans (γ.lower q ⟨hqi.1.le,lt_of_le_of_ne hqi.2 hq⟩)

theorem zeroScalarValueSet_nonempty (lam : ℝ) : (zeroScalarValueSet lam).Nonempty :=
  ⟨_,ZeroTemperatureProfile.constantProfile lam,rfl⟩

theorem zeroScalarValueSet_bddBelow (lam : ℝ) (hLam : 0 ≤ lam) :
    BddBelow (zeroScalarValueSet lam) := by
  refine ⟨0,?_⟩
  rintro v ⟨γ,rfl⟩
  exact zeroTemperatureFunctional_nonneg γ γ.measurable γ.intervalIntegrable (γ.ae_nonneg hLam)

theorem zeroScalarValue_nonneg (lam : ℝ) (hLam : 0 ≤ lam) : 0≤zeroScalarValue lam := by
  apply le_csInf (zeroScalarValueSet_nonempty lam)
  rintro v ⟨γ,rfl⟩
  exact zeroTemperatureFunctional_nonneg γ γ.measurable γ.intervalIntegrable (γ.ae_nonneg hLam)

theorem zeroScalarValue_le_profile {lam : ℝ} (hLam : 0 ≤ lam)
    (γ : ZeroTemperatureProfile lam) : zeroScalarValue lam≤zeroTemperatureFunctional γ :=
  csInf_le (zeroScalarValueSet_bddBelow lam hLam) ⟨γ,rfl⟩

theorem scalarEnergyValue_le_bounded_zeroProfile {lam : ℝ} (γ : ZeroTemperatureProfile lam)
    (hLam : 0 ≤ lam) (β : ℝ) (hβ : 0<β) (hupper : ∀q∈Ico (0:ℝ) 1,γ q≤β) :
    scalarEnergyValue β lam ≤ zeroTemperatureFunctional γ+Real.log 2/β := by
  let μ:=γ.parisiMeasure hLam β hβ hupper
  have hf : μ∈scalarFloor (lam/β):=γ.parisiMeasure_mem_floor hLam β hβ hupper
  have hLamBeta : lam≤β:=(γ.lower 0 (by norm_num)).trans (hupper 0 (by norm_num))
  have hs : lam/β≤1:=(div_le_one hβ).mpr hLamBeta
  have he : EqOn (fun q=>β*parisiCDF μ q) γ (Ioo (0:ℝ) 1) := by
    intro q hq
    change β*parisiCDF (γ.parisiMeasure hLam β hβ hupper) q=γ q
    rw [γ.parisiMeasure_cdf hLam β hβ hupper q ⟨hq.1.le,hq.2⟩,mul_div_cancel₀ _ hβ.ne']
  have hv:=div_le_div_of_nonneg_right (constrainedParisiValue_le β (lam/β) hs μ hf) hβ.le
  have hh:=(zeroTemperatureFunctional_parisi_sandwich β hβ μ).2
  rw [zeroTemperatureFunctional_congr_Ioo _ γ he] at hh
  exact hv.trans hh

end QuantitativePaper
