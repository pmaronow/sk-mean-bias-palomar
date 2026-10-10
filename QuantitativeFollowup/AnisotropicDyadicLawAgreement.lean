module
public import QuantitativeFollowup.AnisotropicDyadicTail
public import QuantitativeFollowup.AnisotropicFiniteDensity
public import QuantitativeFollowup.AnisotropicMeasureOuterLaw
public import QuantitativePaper.VectorDyadicGridAgreement

@[expose] public section

/-! Exact agreement of the actual anisotropic arbitrary-profile potential
and outer law with their genuine finite dyadic models. Nested grids stabilize
by the proved Gaussian semigroup, rather than by a model-equality premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem anisotropicDyadicTailPotential_grid_succ (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a j : ℕ) (haj : a≤j)
    (q : Paper.Overlap) (P : AnisotropicParameter n) :
    anisotropicDyadicTailPotential D (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) q (j+1) P=
      anisotropicDyadicTailPotential D (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) q j P := by
  let ν:=Paper.parisiGridMeasure μ (vectorDyadicIndex a)
  have he:=anisotropicTailRecursion_grid_refine_coarse D ν (vectorDyadicIndex j) q
  rw [show Paper.parisiGridMeasure ν (vectorDyadicIndex j)=ν from
    parisiGridMeasure_dyadic_refines μ a j haj] at he
  unfold anisotropicDyadicTailPotential
  rw [vectorDyadicIndex_succ]
  simpa only [show 2*vectorDyadicIndex j+1+3=2*vectorDyadicIndex j+4 by omega,ν] using congrFun he P

theorem anisotropicDyadicTailPotential_grid_stable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a j : ℕ) (haj : a+1≤j)
    (q : Paper.Overlap) (P : AnisotropicParameter n) :
    anisotropicDyadicTailPotential D (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) q j P=
      anisotropicDyadicTailPotential D μ q a P := by
  induction j,haj using Nat.le_induction with
  | base =>
    have he:=anisotropicTailRecursion_grid_refine_coarse D μ (vectorDyadicIndex a) q
    unfold anisotropicDyadicTailPotential
    rw [vectorDyadicIndex_succ]
    simpa only [show 2*vectorDyadicIndex a+1+3=2*vectorDyadicIndex a+4 by omega] using congrFun he P
  | succ j hj ih =>
    rw [anisotropicDyadicTailPotential_grid_succ D μ a j (by omega) q P,ih]

theorem anisotropicMeasureTailPotential_grid_eq_finite (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℕ) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    anisotropicMeasureTailPotential D (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) q P=
      anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) q
        (vectorDyadicIndex a+3) P := by
  apply tendsto_nhds_unique
    (tendsto_anisotropicDyadicTailPotential D (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) q P)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (a+1)] with j hj
  exact (anisotropicDyadicTailPotential_grid_stable D μ a j hj q P).symm

theorem anisotropicMeasurePotential_grid_eq_finite (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℕ) (P : AnisotropicParameter n) :
    anisotropicMeasurePotential D (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) P=
      anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a))
        (vectorDyadicIndex a+3) P := by
  rw [←anisotropicMeasureTailPotential_zero,
    anisotropicMeasureTailPotential_grid_eq_finite,anisotropicTailRecursion_zero D _ le_rfl]

theorem anisotropicMeasureOuterPartition_grid_eq_finite (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (j : ℕ) (a : ℝ) :
    anisotropicMeasureOuterPartition D (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) a=
      anisotropicFiniteOuterPartition D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a := by
  unfold anisotropicMeasureOuterPartition anisotropicFiniteOuterPartition
  simp_rw [anisotropicMeasurePotential_grid_eq_finite]
  rfl

theorem anisotropicMeasureOuterLaw_grid_eq_finite (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (j : ℕ) (a : ℝ) :
    anisotropicMeasureOuterLaw D (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) a=
      anisotropicFiniteOuterLaw D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a := by
  unfold anisotropicMeasureOuterLaw anisotropicFiniteOuterLaw
  simp_rw [anisotropicMeasurePotential_grid_eq_finite]
  rfl

end QuantitativeFollowup
