module
public import QuantitativeFollowup.ScalarProcessContinuity
public import QuantitativeFollowup.ScalarFutureContinuity

@[expose] public section

/-! Joint weak-profile and level continuity of the eight actual expectation
coefficients in the regrouped scalar response. No response identity is assumed. -/
noncomputable section
open Set MeasureTheory Paper FourPapersCommon FRSB
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [TopologicalSpace A]

theorem continuous_scalarM_comp (β : ℝ) (hβ : β ≠ 0) (ω : Paper.BrownianSample)
    (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ) (p : A → Paper.Overlap) (hp : Continuous p) :
    Continuous (fun a => M β (μ a) (p a) ω) := by
  convert! (continuous_scalarM_parameter β hβ ω).comp (hμ.prodMk hp) using 1

theorem continuous_scalarC_comp (β : ℝ) (hβ : β ≠ 0) (ω : Paper.BrownianSample)
    (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ) (p : A → Paper.Overlap) (hp : Continuous p) :
    Continuous (fun a => C β (μ a) (p a) ω) := by
  convert! (continuous_scalarC_parameter β hβ ω).comp (hμ.prodMk hp) using 1

theorem continuous_scalarCentered_comp (β : ℝ) (hβ : β ≠ 0) (ω : Paper.BrownianSample)
    (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ) (p : A → Paper.Overlap) (hp : Continuous p) :
    Continuous (fun a => scalarCenteredSquare β (μ a) (p a) ω) := by
  convert! (continuous_scalarCenteredSquare_parameter β hβ ω).comp (hμ.prodMk hp) using 1

theorem continuous_scalarFutureSquare_comp (β : ℝ) (ω : Paper.BrownianSample)
    (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ) (r q : A → Paper.Overlap)
    (hr : Continuous r) (hq : Continuous q) :
    Continuous (fun a => scalarFutureSquareExtended β (μ a) (r a) (q a)
      (parisiPhysicalSplitState β 0 (μ a) (r a) ω)) := by
  have hx : Continuous (fun a => parisiPhysicalSplitState β 0 (μ a) (r a) ω) := by
    convert! (continuous_scalarPhysicalSplitState_parameter β 0 ω).comp (hμ.prodMk hr) using 1
  have harg := hμ.prodMk (hr.prodMk (hq.prodMk hx))
  convert! (continuous_scalarFutureSquareExtended β).comp harg using 1

theorem continuous_scalarFutureSquareDerivative_comp (β : ℝ) (hβ : β ≠ 0) (ω : Paper.BrownianSample)
    (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ) (r q : A → Paper.Overlap)
    (hr : Continuous r) (hq : Continuous q) :
    Continuous (fun a => scalarFutureSquareDerivativeExtended β (μ a) (r a) (q a)
      (parisiPhysicalSplitState β 0 (μ a) (r a) ω)) := by
  have hx : Continuous (fun a => parisiPhysicalSplitState β 0 (μ a) (r a) ω) := by
    convert! (continuous_scalarPhysicalSplitState_parameter β 0 ω).comp (hμ.prodMk hr) using 1
  have harg := hμ.prodMk (hr.prodMk (hq.prodMk hx))
  convert! (continuous_scalarFutureSquareDerivativeExtended β hβ).comp harg using 1

theorem scalarFutureSquareExtended_norm_le_one (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (x : ℝ) : ‖scalarFutureSquareExtended β μ r q x‖ ≤ 1 := by
  simpa only [scalarFutureSquareExtended,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := canonicalWienerMeasure)
      (.of_forall fun W => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ _))

theorem scalarFutureSquareDerivativeExtended_norm_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (x : ℝ) : ‖scalarFutureSquareDerivativeExtended β μ r q x‖ ≤ 2*Real.exp (β^2) := by
  simpa only [scalarFutureSquareDerivativeExtended,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := canonicalWienerMeasure)
      (.of_forall fun W => scalarFutureSquareDerivativeExtended_integrand_bound β μ r q x W)

abbrev ScalarResponseKernelParameters := Paper.ParisiMeasure×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))

def scalarResponseKernel0 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,C β μ p ω^2 ∂canonicalBrownianMeasure

theorem scalarResponseKernel0_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖C β μ p ω^2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_C_le_one β μ p ω)

theorem continuous_scalarResponseKernel0 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel0 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      C β z.1 z.2.1 ω^2) := by
    intro ω
    exact (continuous_scalarC_comp β hβ ω _ continuous_fst _ (by fun_prop)).pow 2
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact ((measurable_C β hβ z.1 z.2.1.property).pow_const 2).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel0_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel1 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,M β μ p ω^2*C β μ p ω ∂canonicalBrownianMeasure

theorem scalarResponseKernel1_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖M β μ p ω^2*C β μ p ω‖ ≤ 1 := by rw [norm_mul,norm_pow]; exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β μ p ω)) (norm_C_le_one β μ p ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem continuous_scalarResponseKernel1 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel1 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      M β z.1 z.2.1 ω^2*C β z.1 z.2.1 ω) := by
    intro ω
    exact ((continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop)).pow 2).mul (continuous_scalarC_comp β hβ ω _ continuous_fst _ (by fun_prop))
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact (((measurable_M β z.1 z.2.1 z.2.1.property).pow_const 2).mul (measurable_C β hβ z.1 z.2.1.property)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel1_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel2 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,M β μ p ω*scalarFutureSquareDerivativeExtended β μ p r (parisiPhysicalSplitState β 0 μ p ω) ∂canonicalBrownianMeasure

theorem scalarResponseKernel2_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖M β μ p ω*scalarFutureSquareDerivativeExtended β μ p r (parisiPhysicalSplitState β 0 μ p ω)‖ ≤ 2*Real.exp (β^2) := by rw [norm_mul]; exact (mul_le_mul (scalar_M_norm_le_one β μ p ω) (scalarFutureSquareDerivativeExtended_norm_le β μ p r _) (norm_nonneg _) (by norm_num)).trans_eq (by ring)


theorem measurable_scalarResponseKernel2_integrand (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : Measurable (fun ω : Paper.BrownianSample => M β μ p ω*scalarFutureSquareDerivativeExtended β μ p r (parisiPhysicalSplitState β 0 μ p ω)) := by
  have hx : Continuous (fun x : ℝ => scalarFutureSquareDerivativeExtended β μ p r x) := by
    have harg : Continuous (fun x : ℝ => (μ,(p,(r,x))) : ℝ → ScalarFutureParameters) := by fun_prop
    convert! (continuous_scalarFutureSquareDerivativeExtended β hβ ).comp harg using 1
  have hg := hx.measurable.comp ((measurable_parisiPhysicalSplitState_past β 0 hβ μ p).mono (canonicalBrownianFiltration.le _) le_rfl)
  exact (measurable_M β μ p p.property).mul hg

theorem continuous_scalarResponseKernel2 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel2 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      M β z.1 z.2.1 ω*scalarFutureSquareDerivativeExtended β z.1 z.2.1 z.2.2.1 (parisiPhysicalSplitState β 0 z.1 z.2.1 ω)) := by
    intro ω
    exact (continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop)).mul (continuous_scalarFutureSquareDerivative_comp β hβ ω _ continuous_fst _ _ (by fun_prop) (by fun_prop))
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (2*Real.exp (β^2) : ℝ))
  · intro z
    exact (measurable_scalarResponseKernel2_integrand β hβ z.1 z.2.1 z.2.2.1 z.2.2.2).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel2_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel3 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,M β μ p ω*C β μ p ω*M β μ r ω ∂canonicalBrownianMeasure

theorem scalarResponseKernel3_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖M β μ p ω*C β μ p ω*M β μ r ω‖ ≤ 1 := by
  rw [norm_mul,norm_mul]
  exact (mul_le_mul (mul_le_mul (scalar_M_norm_le_one β μ p ω) (norm_C_le_one β μ p ω) (norm_nonneg _) (by norm_num)) (scalar_M_norm_le_one β μ r ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem continuous_scalarResponseKernel3 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel3 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      M β z.1 z.2.1 ω*C β z.1 z.2.1 ω*M β z.1 z.2.2.1 ω) := by
    intro ω
    exact ((continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop)).mul (continuous_scalarC_comp β hβ ω _ continuous_fst _ (by fun_prop))).mul (continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop))
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact (((measurable_M β z.1 z.2.1 z.2.1.property).mul (measurable_C β hβ z.1 z.2.1.property)).mul (measurable_M β z.1 z.2.2.1 z.2.2.1.property)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel3_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel4 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,scalarCenteredSquare β μ p ω*M β μ (⟨1,by norm_num⟩ : Paper.Overlap) ω*M β μ r ω ∂canonicalBrownianMeasure

theorem scalarResponseKernel4_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖scalarCenteredSquare β μ p ω*M β μ (⟨1,by norm_num⟩ : Paper.Overlap) ω*M β μ r ω‖ ≤ 1 := by
  rw [norm_mul,norm_mul]
  exact (mul_le_mul (mul_le_mul (scalarCenteredSquare_norm_le_one β μ p ω) (scalar_M_norm_le_one β μ (⟨1,by norm_num⟩ : Paper.Overlap) ω) (norm_nonneg _) (by norm_num)) (scalar_M_norm_le_one β μ r ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)


theorem measurable_scalarResponseKernel4_integrand (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : Measurable (fun ω : Paper.BrownianSample => scalarCenteredSquare β μ p ω*M β μ (⟨1,by norm_num⟩ : Paper.Overlap) ω*M β μ r ω) := by
  exact (((measurable_M β μ p p.property).pow_const 2).sub measurable_const).mul (measurable_M β μ (⟨1,by norm_num⟩ : Paper.Overlap) (by norm_num)) |>.mul (measurable_M β μ r r.property)

theorem continuous_scalarResponseKernel4 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel4 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      scalarCenteredSquare β z.1 z.2.1 ω*M β z.1 (⟨1,by norm_num⟩ : Paper.Overlap) ω*M β z.1 z.2.2.1 ω) := by
    intro ω
    exact ((continuous_scalarCentered_comp β hβ ω _ continuous_fst _ (by fun_prop)).mul (continuous_scalarM_comp β hβ ω _ continuous_fst _ continuous_const)).mul (continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop))
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact (measurable_scalarResponseKernel4_integrand β hβ z.1 z.2.1 z.2.2.1 z.2.2.2).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel4_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel5 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,scalarCenteredSquare β μ p ω*M β μ r ω^2 ∂canonicalBrownianMeasure

theorem scalarResponseKernel5_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖scalarCenteredSquare β μ p ω*M β μ r ω^2‖ ≤ 1 := by rw [norm_mul,norm_pow]; exact (mul_le_mul (scalarCenteredSquare_norm_le_one β μ p ω) (pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β μ r ω)) (by positivity) (by norm_num)).trans_eq (by norm_num)


theorem measurable_scalarResponseKernel5_integrand (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : Measurable (fun ω : Paper.BrownianSample => scalarCenteredSquare β μ p ω*M β μ r ω^2) := by
  exact (((measurable_M β μ p p.property).pow_const 2).sub measurable_const).mul ((measurable_M β μ r r.property).pow_const 2)

theorem continuous_scalarResponseKernel5 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel5 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      scalarCenteredSquare β z.1 z.2.1 ω*M β z.1 z.2.2.1 ω^2) := by
    intro ω
    exact (continuous_scalarCentered_comp β hβ ω _ continuous_fst _ (by fun_prop)).mul ((continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop)).pow 2)
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact (measurable_scalarResponseKernel5_integrand β hβ z.1 z.2.1 z.2.2.1 z.2.2.2).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel5_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel6 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,scalarCenteredSquare β μ p ω*M β μ r ω*M β μ ell ω ∂canonicalBrownianMeasure

theorem scalarResponseKernel6_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖scalarCenteredSquare β μ p ω*M β μ r ω*M β μ ell ω‖ ≤ 1 := by
  rw [norm_mul,norm_mul]
  exact (mul_le_mul (mul_le_mul (scalarCenteredSquare_norm_le_one β μ p ω) (scalar_M_norm_le_one β μ r ω) (norm_nonneg _) (by norm_num)) (scalar_M_norm_le_one β μ ell ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)


theorem measurable_scalarResponseKernel6_integrand (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : Measurable (fun ω : Paper.BrownianSample => scalarCenteredSquare β μ p ω*M β μ r ω*M β μ ell ω) := by
  exact (((measurable_M β μ p p.property).pow_const 2).sub measurable_const).mul (measurable_M β μ r r.property) |>.mul (measurable_M β μ ell ell.property)

theorem continuous_scalarResponseKernel6 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel6 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      scalarCenteredSquare β z.1 z.2.1 ω*M β z.1 z.2.2.1 ω*M β z.1 z.2.2.2 ω) := by
    intro ω
    exact ((continuous_scalarCentered_comp β hβ ω _ continuous_fst _ (by fun_prop)).mul (continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop))).mul (continuous_scalarM_comp β hβ ω _ continuous_fst _ (by fun_prop))
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact (measurable_scalarResponseKernel6_integrand β hβ z.1 z.2.1 z.2.2.1 z.2.2.2).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel6_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

def scalarResponseKernel7 (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : ℝ :=
  ∫ ω,scalarCenteredSquare β μ p ω*scalarFutureSquareExtended β μ r ell (parisiPhysicalSplitState β 0 μ r ω) ∂canonicalBrownianMeasure

theorem scalarResponseKernel7_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (ω : Paper.BrownianSample) : ‖scalarCenteredSquare β μ p ω*scalarFutureSquareExtended β μ r ell (parisiPhysicalSplitState β 0 μ r ω)‖ ≤ 1 := by rw [norm_mul]; exact (mul_le_mul (scalarCenteredSquare_norm_le_one β μ p ω) (scalarFutureSquareExtended_norm_le_one β μ r ell _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)


theorem measurable_scalarResponseKernel7_integrand (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) : Measurable (fun ω : Paper.BrownianSample => scalarCenteredSquare β μ p ω*scalarFutureSquareExtended β μ r ell (parisiPhysicalSplitState β 0 μ r ω)) := by
  have hx : Continuous (fun x : ℝ => scalarFutureSquareExtended β μ r ell x) := by
    have harg : Continuous (fun x : ℝ => (μ,(r,(ell,x))) : ℝ → ScalarFutureParameters) := by fun_prop
    convert! (continuous_scalarFutureSquareExtended β ).comp harg using 1
  have hg := hx.measurable.comp ((measurable_parisiPhysicalSplitState_past β 0 hβ μ r).mono (canonicalBrownianFiltration.le _) le_rfl)
  exact (((measurable_M β μ p p.property).pow_const 2).sub measurable_const).mul hg

theorem continuous_scalarResponseKernel7 (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponseKernel7 β z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hc : ∀ ω : Paper.BrownianSample, Continuous (fun z : ScalarResponseKernelParameters =>
      scalarCenteredSquare β z.1 z.2.1 ω*scalarFutureSquareExtended β z.1 z.2.2.1 z.2.2.2 (parisiPhysicalSplitState β 0 z.1 z.2.2.1 ω)) := by
    intro ω
    exact (continuous_scalarCentered_comp β hβ ω _ continuous_fst _ (by fun_prop)).mul (continuous_scalarFutureSquare_comp β ω _ continuous_fst _ _ (by fun_prop) (by fun_prop))
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro z
    exact (measurable_scalarResponseKernel7_integrand β hβ z.1 z.2.1 z.2.2.1 z.2.2.2).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω => scalarResponseKernel7_integrand_bound β z.1 z.2.1 z.2.2.1 z.2.2.2 ω
  · exact integrable_const _
  · exact .of_forall hc

end QuantitativeFollowup
