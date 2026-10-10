module
public import HexagonPaper.VariableScalarClockPrimitiveCalculus
public import HexagonPaper.VariableScalarClockJoint
public import QuantitativeFollowup.ParisiContinuousTime

@[expose] public section

/-! The primitive time change satisfies the actual scalar PDE with the
authored bounded measurable coefficient. Time derivatives hold almost
everywhere; the arbitrary profile's countably many CDF jumps are retained. -/
noncomputable section
open Set Filter MeasureTheory Paper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def scalarCoefficientPotential (c : ℝ→ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q) (μ : ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  Real.log 2+parisiPotential (Real.sqrt (scalarCoefficientPrimitive c 1))
    (scalarClockMeasure (scalarCoefficientClock c hint hpos) μ)
    (scalarCoefficientRealClock c hint hpos p.1,p.2)

def scalarCoefficientSpatialField (c : ℝ→ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q) (μ : ParisiMeasure) (j : ℕ) (p : ℝ×ℝ) : ℝ :=
  parisiSpatialField (Real.sqrt (scalarCoefficientPrimitive c 1))
    (scalarClockMeasure (scalarCoefficientClock c hint hpos) μ) j
    (scalarCoefficientRealClock c hint hpos p.1,p.2)

theorem scalarCoefficientClock_ae_cdf_continuous (c : ℝ→ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q) (μ : ParisiMeasure) :
    ∀ᵐq∂volume,q∈Icc (0:ℝ) 1→
      ContinuousAt (parisiCDF (scalarClockMeasure (scalarCoefficientClock c hint hpos) μ))
        (scalarCoefficientRealClock c hint hpos q) := by
  let τ:=scalarCoefficientClock c hint hpos
  let ν:=scalarClockMeasure τ μ
  let S:Set Paper.Overlap:={q | ¬ContinuousAt (parisiCDF ν) (τ q:ℝ)}
  have hS:S.Countable:=by
    apply (parisiCDF_monotone ν).countable_not_continuousAt.preimage
    exact Subtype.val_injective.comp τ.injective
  have hR:(Subtype.val '' S).Countable:=hS.image Subtype.val
  filter_upwards [hR.ae_notMem volume] with q hq
  intro hqi
  have hn : (⟨q,hqi⟩:Paper.Overlap)∉S:=by
    intro hs
    exact hq ⟨⟨q,hqi⟩,hs,rfl⟩
  have he:scalarCoefficientRealClock c hint hpos q=(τ ⟨q,hqi⟩:ℝ):=by
    unfold scalarCoefficientRealClock
    rw [projIcc_of_mem zero_le_one hqi]
  rw [he]
  exact not_not.mp hn

theorem scalarCoefficientPotential_hasDerivAt_spatial (c : ℝ→ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q) (μ : ParisiMeasure) (q x : ℝ) :
    HasDerivAt (fun y=>scalarCoefficientPotential c hint hpos μ (q,y))
      (scalarCoefficientSpatialField c hint hpos μ 1 (q,x)) x := by
  have ht:(scalarCoefficientRealClock c hint hpos q)∈Icc (0:ℝ) 1:=
    (scalarCoefficientClock c hint hpos (projIcc 0 1 zero_le_one q)).property
  simpa only [scalarCoefficientPotential,scalarCoefficientSpatialField,
    parisiSpatialField_one,zero_add] using
    (hasDerivAt_parisiPotential_spatial_all
      (Real.sqrt (scalarCoefficientPrimitive c 1))
      (scalarClockMeasure (scalarCoefficientClock c hint hpos) μ)
      (scalarCoefficientRealClock c hint hpos q) x ht).const_add (Real.log 2)

theorem scalarCoefficientPotential_ae_PDE (c : ℝ→ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀q∈Ioo (0:ℝ) 1,0<c q) (μ : ParisiMeasure) :
    ∀ᵐq∂volume,q∈Ioo (0:ℝ) 1→∀x : ℝ,
      HasDerivAt (fun r=>scalarCoefficientPotential c hint hpos μ (r,x))
        (-(c q/2)*(scalarCoefficientSpatialField c hint hpos μ 2 (q,x)+
          parisiCDF μ q*(scalarCoefficientSpatialField c hint hpos μ 1 (q,x))^2)) q := by
  let τ:=scalarCoefficientClock c hint hpos
  let ν:=scalarClockMeasure τ μ
  let β:=Real.sqrt (scalarCoefficientPrimitive c 1)
  have hβ:β≠0:=(scalarCoefficientClock_temperature c hint hpos).1.ne'
  have hβsq:β^2=scalarCoefficientPrimitive c 1:=
    (scalarCoefficientClock_temperature c hint hpos).2
  have hC:scalarCoefficientPrimitive c 1≠0:=(scalarCoefficient_total_pos c hint hpos).ne'
  filter_upwards [scalarCoefficientClock_ae_hasDerivAt c hint hpos,
    scalarCoefficientClock_ae_cdf_continuous c hint hpos μ] with q hd hc
  intro hqi x
  let z:Paper.Overlap:=⟨q,hqi.1.le,hqi.2.le⟩
  have he:scalarCoefficientRealClock c hint hpos q=(τ z:ℝ):=by
    unfold scalarCoefficientRealClock
    rw [projIcc_of_mem zero_le_one z.property]
  have hτ0:(0:ℝ)<(τ z:ℝ):=by
    have hz:τ (0:Paper.Overlap)=0:=τ.map_bot
    have hh:τ (0:Paper.Overlap)<τ z:=τ.strictMono hqi.1
    change (0:Paper.Overlap)<τ z
    exact hz ▸ hh
  have hτ1:(τ z:ℝ)<1:=by
    have hz:τ (1:Paper.Overlap)=1:=τ.map_top
    have hh:τ z<τ (1:Paper.Overlap):=τ.strictMono hqi.2
    change τ z<(1:Paper.Overlap)
    exact hz ▸ hh
  have hdu:=hasDerivAt_parisiSpatialField_time_of_cdf β hβ ν 0
    (scalarCoefficientRealClock c hint hpos q) x (by rw [he]; exact ⟨hτ0,hτ1⟩)
    (hc z.property)
  have hcomp:=(hdu.comp q (hd hqi)).const_add (Real.log 2)
  have hCDF:parisiCDF ν (scalarCoefficientRealClock c hint hpos q)=parisiCDF μ q:=by
    rw [he]
    exact scalarClockMeasure_cdf τ μ z
  have hright : parisiTimeField β ν 0 (scalarCoefficientRealClock c hint hpos q,x)*
      (c q/scalarCoefficientPrimitive c 1)=
        -(c q/2)*(scalarCoefficientSpatialField c hint hpos μ 2 (q,x)+
          parisiCDF μ q*(scalarCoefficientSpatialField c hint hpos μ 1 (q,x))^2) := by
    dsimp only [scalarCoefficientSpatialField]
    rw [parisiTimeField,parisiSquareSpatialField_zero,parisiSpatialField_one,hCDF,hβsq]
    field_simp
    ring
  rw [hright] at hcomp
  exact hcomp

end HexagonPaper
