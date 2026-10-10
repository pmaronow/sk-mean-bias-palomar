module
public import QuantitativeFollowup.ScalarTwoTransportSmooth
public import QuantitativeFollowup.ScalarMixedDerivativeSymmetry
public import QuantitativeFollowup.ScalarResponseDomination

@[expose] public section

/-! Genuine symmetry of the literal scalar response pairing. At finite
profiles it follows from the actual two-parameter transport Hessian;
upward-grid weak convergence then passes it to arbitrary profiles. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem scalarTwoTransportFunctional_swap (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (u v : ℝ) :
    scalarTwoTransportFunctional β μ φ ψ (u,v)=
      scalarTwoTransportFunctional β μ ψ φ (v,u) := by
  have he : scalarTwoDirection φ ψ (u,v)=scalarTwoDirection ψ φ (v,u) := by
    ext q
    simp only [scalarTwoDirection_apply]
    ring
  unfold scalarTwoTransportFunctional scalarTwoTransportMeasure
  rw [he]

theorem scalar_response_pairing_symmetric_finite_full (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ ψ : C(Paper.Overlap,ℝ)) (Lφ Lψ : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a ψ q
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))=
    ∫q : Paper.Overlap,ψ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap) := by
  let δ : ℝ := 1/(2*((Lφ:ℝ)+Lψ+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hsmallφ : δ*Lφ<1 := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_lt_one (by positivity)).mpr
    linarith [Lφ.coe_nonneg,Lψ.coe_nonneg]
  have hsmallψ : δ*Lψ<1 := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_lt_one (by positivity)).mpr
    linarith [Lφ.coe_nonneg,Lψ.coe_nonneg]
  have hD := hasDerivAt_scalarTwoTransportAxisDerivative_zero s β hβ φ ψ Lψ hψ hψ0 hψ1
    δ hδ hsmallψ a ha hμ
  have hE := hasDerivAt_scalarTwoTransportAxisDerivative_zero s β hβ ψ φ Lφ hφ hφ0 hφ1
    δ hδ hsmallφ a ha hμ
  have hF := (contDiffAt_scalarTwoTransportFunctional_zero s β hβ.ne' φ ψ Lφ Lψ
    hφ hψ hφ0 hφ1 hψ0 hψ1).of_le (by norm_num : (2:ℕ∞ω)≤∞)
  have haxisD : ∀ᶠ u in 𝓝 (0:ℝ),
      HasDerivAt (fun v=>scalarTwoTransportFunctional β (parisiSchemeMeasure s) φ ψ (v,u))
        (scalarTwoTransportAxisDerivative β (parisiSchemeMeasure s) φ ψ u) 0 := by
    have hn : {u : ℝ | |u| *Lψ<1}∈𝓝 (0:ℝ) :=
      (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds (by simp)
    filter_upwards [hn] with u hu
    exact hasDerivAt_scalarTwoTransportFunctional_first_axis s β hβ φ ψ Lφ Lψ hφ hψ
      hφ0 hφ1 hψ0 hψ1 u hu
  have haxisE : ∀ᶠ u in 𝓝 (0:ℝ),
      HasDerivAt (fun v=>scalarTwoTransportFunctional β (parisiSchemeMeasure s) φ ψ (u,v))
        (scalarTwoTransportAxisDerivative β (parisiSchemeMeasure s) ψ φ u) 0 := by
    have hn : {u : ℝ | |u| *Lφ<1}∈𝓝 (0:ℝ) :=
      (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds (by simp)
    filter_upwards [hn] with u hu
    apply (hasDerivAt_scalarTwoTransportFunctional_first_axis s β hβ ψ φ Lψ Lφ hψ hφ
      hψ0 hψ1 hφ0 hφ1 u hu).congr_of_eventuallyEq
    exact .of_forall fun v=>scalarTwoTransportFunctional_swap β _ φ ψ u v
  have he := scalar_mixed_axis_derivative_symmetric _ _ _ _ _ hF hD hE haxisD haxisE
  have hcoef : β^2/2≠0 := by positivity
  have he' := mul_left_cancel₀ hcoef he
  have hi (f g : C(Paper.Overlap,ℝ)) : Integrable (fun q : Paper.Overlap=>
      f q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a g q)
      (parisiSchemeMeasure s:Measure Paper.Overlap) :=
    integrable_overlap_continuous (f.continuous.mul
      (continuous_scalarResponseOperator β hβ.ne' _ a ha hμ g)) _
  have hip : Integrable (fun q : Paper.Overlap=>φ q*ψ q) (parisiSchemeMeasure s:Measure Paper.Overlap) :=
    integrable_overlap_continuous (φ.continuous.mul ψ.continuous) _
  have hipswap : Integrable (fun q : Paper.Overlap=>ψ q*φ q) (parisiSchemeMeasure s:Measure Paper.Overlap) :=
    integrable_overlap_continuous (ψ.continuous.mul φ.continuous) _
  have hleft : (∫q : Paper.Overlap,φ q*(ψ q-scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a ψ q)
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))=
      (∫q : Paper.Overlap,φ q*ψ q ∂(parisiSchemeMeasure s:Measure Paper.Overlap))-
        ∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a ψ q
          ∂(parisiSchemeMeasure s:Measure Paper.Overlap) := by
    simp_rw [mul_sub]
    exact integral_sub hip (hi φ ψ)
  have hright : (∫q : Paper.Overlap,ψ q*(φ q-scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))=
      (∫q : Paper.Overlap,φ q*ψ q ∂(parisiSchemeMeasure s:Measure Paper.Overlap))-
        ∫q : Paper.Overlap,ψ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q
          ∂(parisiSchemeMeasure s:Measure Paper.Overlap) := by
    simp_rw [mul_sub]
    rw [integral_sub hipswap (hi ψ φ)]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun q=>mul_comm _ _
  rw [hleft,hright] at he'
  linarith

theorem continuous_scalar_response_bilinear_integral (β : ℝ) (hβ : β≠0)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (φ ψ : C(Paper.Overlap,ℝ)) :
    Continuous (fun μ : ScalarFloorMeasure a=>∫q : Paper.Overlap,
      φ q*scalarResponseOperator β hβ μ.val a ψ q ∂(μ.val:Measure Paper.Overlap)) := by
  exact continuous_integral_probability_family _
    ((φ.continuous.comp continuous_snd).mul
      (continuous_scalarResponseOperator_floor β hβ a ha ψ)) _ continuous_subtype_val

theorem scalar_response_pairing_symmetric_full (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ ψ : C(Paper.Overlap,ℝ)) (Lφ Lψ : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' μ a ψ q ∂(μ:Measure Paper.Overlap))=
      ∫q : Paper.Overlap,ψ q*scalarResponseOperator β hβ.ne' μ a φ q ∂(μ:Measure Paper.Overlap) := by
  let μn : ℕ→ScalarFloorMeasure a := fun n=>
    ⟨parisiGridMeasure μ n,parisiGridMeasure_mem_scalarFloor μ a hμ n⟩
  have hweak : Tendsto μn atTop (𝓝 (⟨μ,hμ⟩:ScalarFloorMeasure a)) :=
    tendsto_subtype_rng.mpr (tendsto_parisiGridMeasure μ)
  have hleft := (continuous_scalar_response_bilinear_integral β hβ.ne' a ha φ ψ).tendsto
    (⟨μ,hμ⟩:ScalarFloorMeasure a) |>.comp hweak
  have hright := (continuous_scalar_response_bilinear_integral β hβ.ne' a ha ψ φ).tendsto
    (⟨μ,hμ⟩:ScalarFloorMeasure a) |>.comp hweak
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact .of_forall fun n=>by
    have hn := scalar_response_pairing_symmetric_finite_full (parisiGridRSBScheme μ n)
      β hβ φ ψ Lφ Lψ hφ hψ hφ0 hφ1 hψ0 hψ1 a ha
      (by rw [parisiSchemeMeasure_grid_eq];exact parisiGridMeasure_mem_scalarFloor μ a hμ n)
    rw [parisiSchemeMeasure_grid_eq] at hn
    exact hn.symm

theorem scalar_response_pairing_symmetric (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ ψ : C(Paper.Overlap,ℝ)) (Lφ Lψ : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' μ a ψ q ∂parisiFreeMeasure μ a)=
      ∫q : Paper.Overlap,ψ q*scalarResponseOperator β hβ.ne' μ a φ q ∂parisiFreeMeasure μ a := by
  have hleft : Continuous (fun q : Paper.Overlap=>φ q*scalarResponseOperator β hβ.ne' μ a ψ q) :=
    φ.continuous.mul (continuous_scalarResponseOperator β hβ.ne' μ a ha hμ ψ)
  have hright : Continuous (fun q : Paper.Overlap=>ψ q*scalarResponseOperator β hβ.ne' μ a φ q) :=
    ψ.continuous.mul (continuous_scalarResponseOperator β hβ.ne' μ a ha hμ φ)
  rw [integral_parisiFreeMeasure_continuous μ a ha hμ _ hleft,
    integral_parisiFreeMeasure_continuous μ a ha hμ _ hright]
  simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,hφ0,hψ0,zero_mul,mul_zero,sub_zero]
  exact scalar_response_pairing_symmetric_full β hβ μ a ha hμ φ ψ Lφ Lψ hφ hψ hφ0 hφ1 hψ0 hψ1

end QuantitativeFollowup
