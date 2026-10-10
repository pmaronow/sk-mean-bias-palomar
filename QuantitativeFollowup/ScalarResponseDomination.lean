module
public import QuantitativeFollowup.ScalarResponseFiniteDomination
public import QuantitativeFollowup.ParisiFreeGrid
public import FRSB.ParisiGridTopology
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! The actual scalar multiplier quadratic inequality for arbitrary
overlap profiles. Upward finite approximation preserves the root atom;
joint continuity of the genuine state moments passes the finite bound
to the weak limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_scalarGammaPrime_parameter (β : ℝ) (hβ : β≠0) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap=>GammaPrime β z.1 z.2) := by
  have harg : Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap=>
      (z.1,(z.2,((0:Paper.Overlap),(0:Paper.Overlap))))) := by fun_prop
  have hh := (continuous_scalarResponseKernel0 β hβ).comp harg
  convert! continuous_const.mul hh using 1

theorem continuous_scalar_response_quadratic_integral (β : ℝ) (hβ : β≠0)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun μ : ScalarFloorMeasure a=>∫q : Paper.Overlap,
      φ q*scalarResponseOperator β hβ μ.val a φ q ∂(μ.val:Measure Paper.Overlap)) := by
  exact continuous_integral_probability_family _
    ((φ.continuous.comp continuous_snd).mul
      (continuous_scalarResponseOperator_floor β hβ a ha φ)) _ continuous_subtype_val

theorem continuous_scalar_multiplier_quadratic_integral (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun μ : Paper.ParisiMeasure=>∫q : Paper.Overlap,
      GammaPrime β μ q*φ q^2 ∂(μ:Measure Paper.Overlap)) := by
  exact continuous_integral_probability_family _
    ((continuous_scalarGammaPrime_parameter β hβ).mul
      ((φ.continuous.comp continuous_snd).pow 2)) _ continuous_id

theorem scalar_response_multiplier_domination_full (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (h0 : φ 0=0) (h1 : φ 1=0) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' μ a φ q ∂(μ:Measure Paper.Overlap))≤
      ∫q : Paper.Overlap,GammaPrime β μ q*φ q^2 ∂(μ:Measure Paper.Overlap) := by
  let δ := (1:ℝ)/(2*((L:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have hsmall : δ*(L:ℝ)<1 := by
    dsimp [δ]
    apply (div_mul_eq_mul_div _ _ _).trans_lt ?_
    apply (div_lt_one (by positivity)).mpr
    linarith [L.coe_nonneg]
  let μn : ℕ→ScalarFloorMeasure a := fun n=>
    ⟨parisiGridMeasure μ n,parisiGridMeasure_mem_scalarFloor μ a hμ n⟩
  have hweak : Tendsto μn atTop (𝓝 (⟨μ,hμ⟩:ScalarFloorMeasure a)) :=
    tendsto_subtype_rng.mpr (tendsto_parisiGridMeasure μ)
  have hleft := (continuous_scalar_response_quadratic_integral β hβ.ne' a ha φ).tendsto
    (⟨μ,hμ⟩:ScalarFloorMeasure a) |>.comp hweak
  have hright := (continuous_scalar_multiplier_quadratic_integral β hβ.ne' φ).tendsto μ
    |>.comp (tendsto_parisiGridMeasure μ)
  apply le_of_tendsto_of_tendsto hleft hright
  exact .of_forall fun n=>by
    have hn := scalar_response_multiplier_domination_finite_full (parisiGridRSBScheme μ n)
      β hβ φ L hφ h0 h1 δ hδ hsmall a ha
      (by rw [parisiSchemeMeasure_grid_eq];exact parisiGridMeasure_mem_scalarFloor μ a hμ n)
    rw [parisiSchemeMeasure_grid_eq] at hn
    exact hn

theorem scalar_response_multiplier_domination (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (h0 : φ 0=0) (h1 : φ 1=0) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' μ a φ q ∂parisiFreeMeasure μ a)≤
      ∫q : Paper.Overlap,GammaPrime β μ q*φ q^2 ∂parisiFreeMeasure μ a := by
  have hc : Continuous (fun q : Paper.Overlap=>φ q*scalarResponseOperator β hβ.ne' μ a φ q) :=
    φ.continuous.mul (continuous_scalarResponseOperator β hβ.ne' μ a ha hμ φ)
  have hk : Continuous (fun q : Paper.Overlap=>GammaPrime β μ q*φ q^2) :=
    ((continuousOn_GammaPrime β hβ.ne' μ).comp_continuous continuous_subtype_val
      (fun q=>q.property)).mul (φ.continuous.pow 2)
  rw [integral_parisiFreeMeasure_continuous μ a ha hμ _ hc,
    integral_parisiFreeMeasure_continuous μ a ha hμ _ hk]
  simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,h0,zero_mul,
    zero_pow (by decide : 2≠0),mul_zero,sub_zero]
  exact scalar_response_multiplier_domination_full β hβ μ a ha hμ φ L hφ h0 h1

end QuantitativeFollowup
