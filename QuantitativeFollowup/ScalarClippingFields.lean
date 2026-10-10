module
public import QuantitativeFollowup.ParisiContinuousTime
public import FRSB.UniformSpatialRegularity

@[expose] public section

/-! Actual continuous representatives of the minimizing and clipped time
equations near the origin. Spatial fields remain the genuine PDE jets. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 500000

def scalarSupportCDF (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) (hq : 0≤q) (t : ℝ) : ℝ :=
  momentQuotient β μ (projIcc 0 q hq t)

theorem continuous_scalarSupportCDF (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) q) :
    Continuous (scalarSupportCDF β μ q hq.1.le) := by
  apply (moments_contDiffOn_on_support_interval β hβ μ hmin q hq.1 hq.2.le hsupp).2.continuousOn.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc)
  intro t
  exact (projIcc 0 q hq.1.le t).property

theorem scalarSupportCDF_eq_cdf (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) q) (t : ℝ) (ht : t∈Ico (0:ℝ) q) :
    scalarSupportCDF β μ q hq.1.le t=parisiCDF μ t := by
  unfold scalarSupportCDF
  rw [projIcc_of_mem _ ⟨ht.1,ht.2.le⟩]
  exact (parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq.1 hq.2.le hsupp t ht).symm

def continuousProfileTimeField (β : ℝ) (ν : Paper.ParisiMeasure)
    (g : ℝ→ℝ) (j : ℕ) (p : ℝ×ℝ) : ℝ :=
  -(β^2/2)*(parisiSpatialField β ν (j+2) p+g p.1*parisiSquareSpatialField β ν j p)

theorem continuous_continuousProfileTimeField (β : ℝ) (ν : Paper.ParisiMeasure)
    (g : ℝ→ℝ) (hg : Continuous g) (j : ℕ) :
    Continuous (continuousProfileTimeField β ν g j) := by
  unfold continuousProfileTimeField
  exact continuous_const.mul ((continuous_parisiSpatialField β ν (j+2)).add
    ((hg.comp continuous_fst).mul (continuous_parisiSquareSpatialField β ν j)))

theorem hasDerivAt_spatialField_continuous_profile (β : ℝ) (hβ : β≠0)
    (ν : Paper.ParisiMeasure) (g : ℝ→ℝ) (hg : Continuous g)
    (a b : ℝ) (ha : 0≤a) (hb : b≤1)
    (he : EqOn (parisiCDF ν) g (Ioo a b)) (j : ℕ)
    (t x : ℝ) (ht : t∈Ioo a b) :
    HasDerivAt (fun s=>parisiSpatialField β ν j (s,x))
      (continuousProfileTimeField β ν g j (t,x)) t := by
  have hevent : parisiCDF ν=ᶠ[𝓝 t] g :=
    he.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
  have hc : ContinuousAt (parisiCDF ν) t := hg.continuousAt.congr_of_eventuallyEq hevent
  have hd:=hasDerivAt_parisiSpatialField_time_of_cdf β hβ ν j t x
    ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩ hc
  simpa only [parisiTimeField,continuousProfileTimeField,he ht] using hd

theorem scalar_minimizer_profile_time (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) q) (j : ℕ)
    (t x : ℝ) (ht : t∈Ioo (0:ℝ) q) :
    HasDerivAt (fun s=>parisiSpatialField β μ j (s,x))
      (continuousProfileTimeField β μ (scalarSupportCDF β μ q hq.1.le) j (t,x)) t := by
  apply hasDerivAt_spatialField_continuous_profile β hβ μ _
    (continuous_scalarSupportCDF β hβ μ hmin q hq hsupp) 0 q le_rfl hq.2.le _ j t x ht
  intro r hr
  exact (scalarSupportCDF_eq_cdf β hβ μ hmin q hq hsupp r ⟨hr.1.le,hr.2⟩).symm

theorem scalar_clipped_profile_time (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (j : ℕ) (t x : ℝ) (ht : t∈Ioo (0:ℝ) q) :
    HasDerivAt (fun r=>parisiSpatialField β (scalarClippedTrialMeasure s hs μ) j (r,x))
      (continuousProfileTimeField β (scalarClippedTrialMeasure s hs μ)
        (fun r=>max s (scalarSupportCDF β μ q hq.1.le r)) j (t,x)) t := by
  apply hasDerivAt_spatialField_continuous_profile β hβ _ _
    (continuous_const.max (continuous_scalarSupportCDF β hβ μ hmin q hq hsupp))
    0 q le_rfl hq.2.le _ j t x ht
  intro r hr
  change parisiCDF _ r=max s (scalarSupportCDF β μ q hq.1.le r)
  rw [scalarClippedTrialMeasure_cdf s hs μ r ⟨hr.1.le,hr.2.le.trans hq.2.le⟩,
    scalarSupportCDF_eq_cdf β hβ μ hmin q hq hsupp r ⟨hr.1.le,hr.2⟩]

theorem parisiSquareSpatialField_one_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (t x : ℝ) : parisiSquareSpatialField β μ 1 (t,x)=
      2*parisiGradient β μ (t,x)*parisiHessian β μ (t,x) := by
  have hd:=(hasDerivAt_parisiGradient_spatial_all β μ t x).pow 2
  have he:=(hasDerivAt_parisiSquareSpatialField β μ 0 t x).deriv
  rw [parisiSquareSpatialField_zero] at he
  have hdd:=hd.deriv
  change deriv (fun y=>parisiGradient β μ (t,y)^2) x=_ at hdd
  change deriv (fun y=>parisiGradient β μ (t,y)^2) x=_ at he
  rw [hdd] at he
  simpa only [Nat.cast_ofNat,pow_one,Nat.reduceSub,Nat.zero_add] using he.symm

end QuantitativeFollowup
