module
public import QuantitativePaper.UniformScalarSmoothing
public import QuantitativePaper.ScalarEnergyCrudeUpper

@[expose] public section

/-! The universal scalar energy jet estimate in physical Hessian notation. -/
noncomputable section
open Set Paper FRSB
namespace QuantitativePaper
set_option maxHeartbeats 900000

theorem scalarEnergySpatialJet_hessian (β : ℝ) (μ : Paper.ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySpatialJet β μ 1 (q,x)=β*parisiHessian β μ (q,β*x) := by
  unfold scalarEnergySpatialJet
  norm_num only [Nat.reduceAdd,pow_one]
  change β*backwardC β μ (q,β*x)=_
  rw [backwardC_eq_hessian β μ q (β*x) hq]

theorem scalarEnergy_hessian_uniform_early :
    ∃C≥1,∀(β:ℝ),0<β→∀(μ:Paper.ParisiMeasure),scalarParisiFunctional β μ/β≤2→
      ∀q∈Icc (0:ℝ) (1/4),∀x,β*parisiHessian β μ (q,x)≤C := by
  obtain ⟨C,hC,hbound⟩:=scalarEnergySpatialJet_uniform_early
  refine ⟨C,hC,?_⟩
  intro β hβ μ hcost q hq x
  have hh:=hbound β hβ μ hcost 1 (by norm_num) q hq (x/β)
  rw [scalarEnergySpatialJet_hessian β μ q (x/β) ⟨hq.1,hq.2.trans (by norm_num)⟩,
    mul_div_cancel₀ _ hβ.ne'] at hh
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)

theorem scalarEnergy_minimizer_hessian_uniform_early :
    ∃C≥1,∀(β:ℝ),1≤β→∀(μ:Paper.ParisiMeasure),IsParisiMinimizer β 0 μ→
      ∀q∈Icc (0:ℝ) (1/4),∀x,β*parisiHessian β μ (q,x)≤C := by
  obtain ⟨C,hC,hbound⟩:=scalarEnergy_hessian_uniform_early
  refine ⟨C,hC,?_⟩
  intro β hβ μ hmin
  apply hbound β (lt_of_lt_of_le zero_lt_one hβ) μ
  exact (scalarEnergy_minimizer_cost_lt_three_halves β hβ μ hmin).le.trans (by norm_num)

end QuantitativePaper
