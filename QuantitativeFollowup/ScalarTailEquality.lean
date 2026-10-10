module
public import QuantitativeFollowup.ScalarTrialMeasure
public import Paper.ParisiHJBValueFunction
public import Paper.ParisiTimeRegularity

@[expose] public section

/-! Equality of actual scalar PDE solutions when their profiles agree from
the current time onwards. The genuine attained HJB representation proves
the equality; differentiating the equal spatial sections gives every jet. -/
noncomputable section
open Set MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 400000

theorem parisiTimeControlObjective_eq_of_cdf_tail (β x : ℝ)
    (μ ν : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hc : EqOn (parisiCDF μ) (parisiCDF ν) (Icc a 1))
    (A : ℝ→Paper.BrownianSample→ℝ) :
    parisiTimeControlObjective β x μ a A=parisiTimeControlObjective β x ν a A := by
  have hr (r : ℝ) (hr : r∈uIcc (0:ℝ) (1-a)) : parisiCDF μ (a+r)=parisiCDF ν (a+r) := by
    rw [uIcc_of_le (sub_nonneg.mpr ha.2)] at hr
    exact hc ⟨by linarith [hr.1],by linarith [hr.2]⟩
  unfold parisiTimeControlObjective parisiTimeControlEndpoint parisiTimeControlCost
  congr 1
  funext ω
  congr 1
  · congr 1
    congr 1
    congr 1
    congr 1
    apply intervalIntegral.integral_congr
    intro r hrr
    dsimp only
    rw [hr r hrr]
  · apply intervalIntegral.integral_congr
    intro r hrr
    dsimp only
    rw [hr r hrr]

theorem parisiPotential_eq_of_cdf_tail (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hc : EqOn (parisiCDF μ) (parisiCDF ν) (Icc a 1)) (x : ℝ) :
    parisiPotential β μ (a,x)=parisiPotential β ν (a,x) := by
  obtain ⟨A,hA,hv,_⟩:=parisiPotential_all_time_control_representation β hβ μ a ha x
  obtain ⟨B,hB,hw,_⟩:=parisiPotential_all_time_control_representation β hβ ν a ha x
  apply le_antisymm
  · rw [←hv,parisiTimeControlObjective_eq_of_cdf_tail β x μ ν a ha hc A]
    exact parisiTimeControlObjective_le_potential β x hβ ν a ha A hA
  · rw [←hw,←parisiTimeControlObjective_eq_of_cdf_tail β x μ ν a ha hc B]
    exact parisiTimeControlObjective_le_potential β x hβ μ a ha B hB

theorem parisiSpatialField_eq_of_cdf_tail (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hc : EqOn (parisiCDF μ) (parisiCDF ν) (Icc a 1)) (j : ℕ) (x : ℝ) :
    parisiSpatialField β μ j (a,x)=parisiSpatialField β ν j (a,x) := by
  rw [parisiSpatialField_eq_iteratedDeriv β μ j a x ha,
    parisiSpatialField_eq_iteratedDeriv β ν j a x ha]
  congr 2
  funext y
  exact parisiPotential_eq_of_cdf_tail β hβ μ ν a ha hc y

theorem scalarClippedTrialMeasure_cdf_tail (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : s≤parisiCDF μ a) :
    EqOn (parisiCDF (scalarClippedTrialMeasure s hs μ)) (parisiCDF μ) (Icc a 1) := by
  intro r hr
  rw [scalarClippedTrialMeasure_cdf s hs μ r ⟨ha.1.trans hr.1,hr.2⟩,
    max_eq_right (hfloor.trans (parisiCDF_monotone μ hr.1))]

theorem scalarClippedTrialMeasure_spatialField_terminal (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : s≤parisiCDF μ a) (j : ℕ) (x : ℝ) :
    parisiSpatialField β (scalarClippedTrialMeasure s hs μ) j (a,x)=
      parisiSpatialField β μ j (a,x) :=
  parisiSpatialField_eq_of_cdf_tail β hβ _ _ a ha
    (scalarClippedTrialMeasure_cdf_tail s hs μ a ha hfloor) j x

end QuantitativeFollowup
