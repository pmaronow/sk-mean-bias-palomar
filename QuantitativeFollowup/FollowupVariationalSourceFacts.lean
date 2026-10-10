module
public import QuantitativeFollowup.FollowupConcentratingSourceClosure
public import QuantitativeFollowup.FreeMeasureContact
public import QuantitativePaper.ResponseTraceSharp
public import QuantitativePaper.ResponseCurvatureLower

@[expose] public section

/-! Literal variational/free-measure and beta-only curvature clauses of
follow-up Proposition5.1. Arbitrary-profile second response is separate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper QuantitativePaper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000
variable {n : ℕ}

/-- Every prescribed finite free measure of mass1-s gives an actual floor
probability profile, including any free atom at zero. -/
def profileOfFreeMeasure (s : ℝ) (η : Measure Paper.Overlap)
    (hs : s∈Icc (0:ℝ) 1) (hη : η univ=ENNReal.ofReal (1-s)) : Paper.ParisiMeasure :=
  ⟨ENNReal.ofReal s • Measure.dirac zeroOverlap+η,by
    constructor
    rw [Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul,mul_one,hη,←ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)]
    simp⟩

@[simp] theorem profileOfFreeMeasure_coe (s : ℝ) (η : Measure Paper.Overlap)
    (hs : s∈Icc (0:ℝ) 1) (hη : η univ=ENNReal.ofReal (1-s)) :
    (profileOfFreeMeasure s η hs hη : Measure Paper.Overlap)=ENNReal.ofReal s • Measure.dirac zeroOverlap+η := rfl

theorem profileOfFreeMeasure_mem_floor (s : ℝ) (η : Measure Paper.Overlap)
    (hs : s∈Icc (0:ℝ) 1) (hη : η univ=ENNReal.ofReal (1-s)) :
    profileOfFreeMeasure s η hs hη∈scalarFloor s := by
  rw [mem_scalarFloor_iff]
  unfold zeroMass
  haveI : IsFiniteMeasure η:=⟨by rw [hη];exact ENNReal.ofReal_lt_top⟩
  rw [profileOfFreeMeasure_coe,Measure.add_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton _),smul_eq_mul,mul_one,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top η _),ENNReal.toReal_ofReal hs.1]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

theorem profileOfFreeMeasure_free (s : ℝ) (η : Measure Paper.Overlap)
    (hs : s∈Icc (0:ℝ) 1) (hη : η univ=ENNReal.ofReal (1-s)) :
    parisiFreeMeasure (profileOfFreeMeasure s η hs hη) s=η := by
  have hr:=root_add_parisiFreeMeasure (profileOfFreeMeasure s η hs hη) s hs
    (profileOfFreeMeasure_mem_floor s η hs hη)
  rw [profileOfFreeMeasure_coe] at hr
  haveI : IsFiniteMeasure (ENNReal.ofReal s • Measure.dirac (zeroOverlap:Paper.Overlap)):=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  exact (Measure.add_right_inj _ _ _).mp hr

/-- No free-measure representation premise: any positive energy free measure
of the prescribed mass is realized by an actual admissible probability. -/
theorem localization_profile_of_energy_free (β lam : ℝ) (hβ : 0<β)
    (hlam : lam∈Icc (0:ℝ) β) (η : Measure Paper.Overlap)
    (hη : η univ=ENNReal.ofReal (β-lam)) :
    ∃ν : Paper.ParisiMeasure,ν∈scalarFloor (lam/β) ∧
      ENNReal.ofReal β • parisiFreeMeasure ν (lam/β)=η := by
  have hs : lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  have hm : (ENNReal.ofReal (1/β) • η) univ=ENNReal.ofReal (1-lam/β) := by
    rw [Measure.smul_apply,smul_eq_mul,hη,←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  let ν:=profileOfFreeMeasure (lam/β) (ENNReal.ofReal (1/β) • η) hs hm
  refine ⟨ν,profileOfFreeMeasure_mem_floor _ _ hs hm,?_⟩
  rw [show parisiFreeMeasure ν (lam/β)=ENNReal.ofReal (1/β) • η from
    profileOfFreeMeasure_free _ _ hs hm,smul_smul,←ENNReal.ofReal_mul hβ.le]
  simp [hβ.ne']

/-- Actual energy first variation with the complete prescribed free measure.
The fixed root contribution is proved to cancel. -/
theorem localization_firstvariation_source (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho : ℝ) (hβ : 0<β) (hlam : lam∈Icc (0:ℝ) β) (hrho : 0<rho)
    (hμ : μ∈scalarFloor (lam/β)) (hν : ν∈scalarFloor (lam/β)) :
    HasDerivWithinAt (fun θ=>followupEnergyFunctional n β lam rho (parisiMix μ ν θ))
      (rho/2*((∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β (1-rho) (lam/β) (by linarith) q
        ∂(ENNReal.ofReal β • parisiFreeMeasure ν (lam/β)))-
        (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β (1-rho) (lam/β) (by linarith) q
          ∂(ENNReal.ofReal β • parisiFreeMeasure μ (lam/β))))) (Ici (0:ℝ)) 0 := by
  have ht : 1-rho<1:=by linarith
  have hs : lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  have hG : Continuous (fun q : Paper.Overlap=>vectorOverlapDeficit (n:=n) μ β (1-rho) (lam/β) ht.le q):=
    (continuous_vectorOverlapDeficit μ β (1-rho) (lam/β) ht.le).comp continuous_subtype_val
  have hd:=(hasDerivWithinAt_vectorMeasureFunctional_mix_deficit hn μ ν β (1-rho) (lam/β) hβ.ne' ht).div_const β
  rw [integral_root_add_free μ (lam/β) hs hμ _ hG,
    integral_root_add_free ν (lam/β) hs hν _ hG] at hd
  have hs0 : Icc (0:ℝ) 1=ᶠ[𝓝 (0:ℝ)] Ici 0 := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0:ℝ)<1)] with x hx
    have hxu : x<1:=hx
    apply propext
    simp only [mem_Icc,mem_Ici,and_iff_left hxu.le]
  convert hd.congr_set hs0 using 1
  · rfl
  · rw [integral_smul_measure,integral_smul_measure,ENNReal.toReal_ofReal hβ.le]
    simp only [smul_eq_mul]
    field_simp
    ring

theorem localization_convexity_source (μ ν : Paper.ParisiMeasure)
    (β lam rho : ℝ) (hβ : 0<β) (hlam : 0≤lam) (hrho : 0≤rho) :
    ConvexOn ℝ (Icc (0:ℝ) 1)
      (fun θ=>followupEnergyFunctional n β lam rho (parisiMix μ ν θ)) := by
  have hc:=convexOn_vectorMeasureFunctional_mix n μ ν β (1-rho)
    (by linarith) (lam/β) (div_nonneg hlam hβ.le)
  have hd:=ConvexOn.smul (c:=1/β) (by positivity) hc
  simpa only [followupEnergyFunctional,smul_eq_mul,div_eq_mul_inv,one_mul,mul_one,mul_comm] using hd

/-- The deficit is C1, has the actual derivative x-S and zero derivative at
zero, and its derivative minus x is nonincreasing on the physical band. -/
theorem localization_deficit_source (μ : Paper.ParisiMeasure) (β t outer : ℝ)
    (hβ : β≠0) (ht : t<1) :
    ContDiff ℝ 1 (vectorOverlapDeficit (n:=n) μ β t outer ht.le) ∧
    (∀x : ℝ,HasDerivAt (vectorOverlapDeficit (n:=n) μ β t outer ht.le)
      (x-vectorMeanOverlapReal (n:=n) μ β t outer ht.le x) x) ∧
    deriv (vectorOverlapDeficit (n:=n) μ β t outer ht.le) 0=0 ∧
    AntitoneOn (fun x : ℝ=>deriv (vectorOverlapDeficit (n:=n) μ β t outer ht.le) x-x) (Icc (0:ℝ) 1) := by
  dsimp only [vectorOverlapDeficit]
  have hc:=continuous_vectorMeanOverlapReal (n:=n) μ β t outer ht.le
  have hd (x : ℝ):=hasDerivAt_transportDeficit _ hc x
  refine ⟨contDiff_transportDeficit_one _ hc,hd,?_,?_⟩
  · rw [(hd 0).deriv]
    rw [vectorMeanOverlapReal,projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc 0 1 from ⟨le_rfl,zero_le_one⟩)]
    change 0-vectorMeanOverlap (n:=n) μ β t outer ht.le (0:Paper.Overlap)=0
    rw [vectorMeanOverlap_zero,sub_self]
  · intro x hx y hy hxy
    change deriv (transportDeficit (vectorMeanOverlapReal (n:=n) μ β t outer ht.le)) y-y ≤
      deriv (transportDeficit (vectorMeanOverlapReal (n:=n) μ β t outer ht.le)) x-x
    rw [(hd x).deriv,(hd y).deriv]
    have hs:=vectorMeanOverlapReal_monotoneOn (n:=n) μ β t outer hβ ht hx hy hxy
    linarith

/-- Literal beta-only curvature constant for every actual admissible profile. -/
theorem localization_curvature_source (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β rho lam : ℝ) (hβ : 1<β) (hrho : rho∈Ioc (0:ℝ) 1) (hlam : lam∈Icc (0:ℝ) β)
    (hμ : μ∈scalarFloor (lam/β)) (q : Paper.Overlap) :
    0<responseCurvatureConstant β ∧
    (responseCurvatureConstant β)^2≤responseAveragedCurvature (n:=n) μ β (1-rho) lam (by linarith [hrho.1]) q := by
  have hb : 0<β:=zero_lt_one.trans hβ
  have ht : 1-rho∈Ico (0:ℝ) 1:=⟨by linarith [hrho.2],by linarith [hrho.1]⟩
  have hf : lam≤β*parisiCDF μ 0:=by
    have hh:=scalarFloor_cdf_lower hμ (show (0:ℝ)≤0 from le_rfl)
    exact (le_of_eq (by field_simp : lam=β*(lam/β))).trans (mul_le_mul_of_nonneg_left hh hb.le)
  exact ⟨responseCurvatureConstant_pos β,responseAveragedCurvature_lower hn μ β (1-rho) lam β hβ.le ht hlam.1 hf q
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (parisiCDF_le_one μ q) hb.le)⟩

end QuantitativeFollowup
