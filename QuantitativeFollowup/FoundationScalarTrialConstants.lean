module
public import QuantitativePaper.UniformScalarRootTrialLemma
public import QuantitativePaper.AbsoluteComparisonTrialBudget

@[expose] public section

/-! The fixed-temperature scalar trial constants in follow-up Section 2
are supplied by the genuine uniform root/trial theorem. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

def FoundationScalarTrialTarget (β : ℝ) : Prop :=
  ∃ L lambda0 : ℝ,1≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧ lambda0≤β/4 ∧
    ∀μ,IsParisiMinimizer β 0 μ→∀lam∈Icc (0:ℝ) (2*lambda0),
      ∃hs : lam/β∈Icc (0:ℝ) 1,
        let ν:=scalarClippedTrialMeasure (lam/β) hs μ
        ν∈scalarFloor (lam/β) ∧
        0≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
        scalarEnergyValue β lam-scalarEnergyValue β 0≤
          parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ∧
        parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0≤ L*lam^5

theorem foundation_scalar_trial_constants (β : ℝ) (hβ : 1<β) :
    FoundationScalarTrialTarget β := by
  obtain ⟨T,k,Cs,C1,L,hT,hk,hCs,hC1,hL,hL1,hLβ,hLT,hdata⟩:=uniform_scalar_root_trial β hβ
  let lambda0:=min (L/2) (min 1 (β/4))
  have hβp : 0<β:=zero_lt_one.trans hβ
  have h0 : 0< lambda0:=lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have h01 : lambda0≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have h0β : lambda0≤β/4:=(min_le_right _ _).trans (min_le_right _ _)
  have h0L : 2*lambda0≤ L:=by
    have hh : lambda0≤ L/2:=min_le_left _ _
    linarith
  refine ⟨C1,lambda0,hC1,⟨h0,h01⟩,h0β,?_⟩
  intro μ hmin lam hlam
  obtain ⟨hs,hν,hCDF,hEarly,hDen,hzero,hmid,hbound⟩:=
    (hdata β le_rfl μ hmin).2.2.2.2 lam ⟨hlam.1,hlam.2.trans h0L⟩
  exact ⟨hs,hν,hzero,hmid,hbound⟩

theorem foundation_trial_budget (n : ℕ) (hn : 0< n) (β lam t C1 : ℝ)
    (hβ : 0<β) (hs : lam/β∈Ioo (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (μ ν : Paper.ParisiMeasure) (hμ : μ∈scalarFloor (lam/β)) (hν : ν∈scalarFloor (lam/β))
    (hmin : ∀ρ∈scalarFloor (lam/β),vectorMeasureFunctional n μ β t (lam/β)≤
      vectorMeasureFunctional n ρ β t (lam/β))
    (hzero : 0≤ scalarEnergyValue β lam-scalarEnergyValue β 0)
    (hcost : parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0≤ C1*lam^5) :
    0≤ responseEnergyFunctional n ν β t lam-responseEnergyFunctional n μ β t lam ∧
    responseEnergyFunctional n ν β t lam-responseEnergyFunctional n μ β t lam≤
      energyComparisonError n β lam+C1*lam^5 := by
  refine ⟨?_,absolute_trial_budget hn μ ν β lam t C1 hβ hs ht hμ hν hmin hzero hcost⟩
  unfold responseEnergyFunctional
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right (hmin ν hν) hβ.le)

end QuantitativeFollowup
