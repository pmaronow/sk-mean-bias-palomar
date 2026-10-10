module
public import QuantitativeFollowup.ScalarResponseKernelContinuity
public import QuantitativeFollowup.ParisiFreeIntegralContinuity

@[expose] public section

/-! Continuous regrouped scalar response kernels. The discontinuous strict-future
indicator multiplies a coefficient that vanishes exactly on its diagonal.
The representation theorem relating these kernels to the seven-term J is separate. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon FRSB QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem scalarResponseKernel2_diagonal (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p ell : Paper.Overlap) :
    scalarResponseKernel2 β μ p p ell=2*scalarResponseKernel1 β μ p p ell := by
  unfold scalarResponseKernel2 scalarResponseKernel1
  simp_rw [scalarFutureSquareDerivativeExtended_eq β μ p p le_rfl,
    scalarFutureSquareDerivative_self β hβ μ p,scalarGradient_physicalSplitState β hβ,
    scalarHessian_physicalSplitState β hβ]
  rw [←integral_const_mul]
  congr 1
  funext ω
  ring

theorem scalarResponseKernel7_diagonal (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r : Paper.Overlap) :
    scalarResponseKernel7 β μ p r r=scalarResponseKernel5 β μ p r r := by
  unfold scalarResponseKernel7 scalarResponseKernel5
  simp_rw [scalarFutureSquareExtended_eq β μ r r le_rfl,scalarFutureSquare_self β hβ μ r,
    scalarGradient_physicalSplitState β hβ]

def scalarResponsePsi1 (β : ℝ) (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (p r : Paper.Overlap) : ℝ :=
  (if p<r then 2*scalarResponseKernel1 β μ p r 0*φ p-scalarResponseKernel2 β μ p r 0*φ r else 0)
    -2*scalarResponseKernel3 β μ p r 0*φ (min p r)
    -scalarResponseKernel4 β μ p r 0*φ r+(1/2:ℝ)*scalarResponseKernel5 β μ p r 0*φ r

def scalarResponsePsi2 (β : ℝ) (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (p r ell : Paper.Overlap) : ℝ :=
  (1/2:ℝ)*scalarResponseKernel6 β μ p r ell*φ (min r ell)
    +(1/2:ℝ)*(if r<ell then scalarResponseKernel7 β μ p r ell*φ ell-
      scalarResponseKernel5 β μ p r ell*φ r else 0)

theorem continuous_scalarResponseKernel0_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel0 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel0 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel1_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel1 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel1 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel2_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel2 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel2 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel3_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel3 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel3 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel4_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel4 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel4 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel5_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel5 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel5 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel6_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel6 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel6 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponseKernel7_comp {A : Type*} [TopologicalSpace A]
    (β : ℝ) (hβ : β ≠ 0) (μ : A → Paper.ParisiMeasure) (hμ : Continuous μ)
    (p r ell : A → Paper.Overlap) (hp : Continuous p) (hr : Continuous r) (hl : Continuous ell) :
    Continuous (fun z => scalarResponseKernel7 β (μ z) (p z) (r z) (ell z)) := by
  convert! (continuous_scalarResponseKernel7 β hβ).comp (hμ.prodMk (hp.prodMk (hr.prodMk hl))) using 1

theorem continuous_scalarResponsePsi1 (β : ℝ) (hβ : β ≠ 0) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap) => scalarResponsePsi1 β z.1 φ z.2.1 z.2.2) := by
  let A := Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)
  have hk1 := continuous_scalarResponseKernel1_comp (A := A) β hβ Prod.fst continuous_fst
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hk2 := continuous_scalarResponseKernel2_comp (A := A) β hβ Prod.fst continuous_fst
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hb : Continuous (fun z : A =>
      2*scalarResponseKernel1 β z.1 z.2.1 z.2.2 0*φ z.2.1-
        scalarResponseKernel2 β z.1 z.2.1 z.2.2 0*φ z.2.2) :=
    ((continuous_const.mul hk1).mul (φ.continuous.comp (by fun_prop))).sub
      (hk2.mul (φ.continuous.comp (by fun_prop)))
  have hi : Continuous (fun z : A => if z.2.1<z.2.2 then
      2*scalarResponseKernel1 β z.1 z.2.1 z.2.2 0*φ z.2.1-
        scalarResponseKernel2 β z.1 z.2.1 z.2.2 0*φ z.2.2 else 0) := by
    apply Continuous.if _ hb continuous_const
    intro z hz
    have he : z.2.1=z.2.2 := frontier_lt_subset_eq (f := fun z : A => z.2.1) (g := fun z : A => z.2.2) (by fun_prop) (by fun_prop) hz
    rw [←he,scalarResponseKernel2_diagonal β hβ]
    ring
  have hk3 := continuous_scalarResponseKernel3_comp (A := A) β hβ Prod.fst continuous_fst
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hk4 := continuous_scalarResponseKernel4_comp (A := A) β hβ Prod.fst continuous_fst
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hk5 := continuous_scalarResponseKernel5_comp (A := A) β hβ Prod.fst continuous_fst
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  change Continuous (fun z : A => _)
  exact ((hi.sub ((continuous_const.mul hk3).mul (φ.continuous.comp (by fun_prop)))).sub
    (hk4.mul (φ.continuous.comp (by fun_prop)))).add
      ((continuous_const.mul hk5).mul (φ.continuous.comp (by fun_prop)))

theorem continuous_scalarResponsePsi2 (β : ℝ) (hβ : β ≠ 0) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : ScalarResponseKernelParameters => scalarResponsePsi2 β z.1 φ z.2.1 z.2.2.1 z.2.2.2) := by
  have hb : Continuous (fun z : ScalarResponseKernelParameters =>
      scalarResponseKernel7 β z.1 z.2.1 z.2.2.1 z.2.2.2*φ z.2.2.2-
        scalarResponseKernel5 β z.1 z.2.1 z.2.2.1 z.2.2.2*φ z.2.2.1) :=
    ((continuous_scalarResponseKernel7 β hβ).mul (φ.continuous.comp (by fun_prop))).sub
      ((continuous_scalarResponseKernel5 β hβ).mul (φ.continuous.comp (by fun_prop)))
  have hi : Continuous (fun z : ScalarResponseKernelParameters => if z.2.2.1<z.2.2.2 then
      scalarResponseKernel7 β z.1 z.2.1 z.2.2.1 z.2.2.2*φ z.2.2.2-
        scalarResponseKernel5 β z.1 z.2.1 z.2.2.1 z.2.2.2*φ z.2.2.1 else 0) := by
    apply Continuous.if _ hb continuous_const
    intro z hz
    have he : z.2.2.1=z.2.2.2 := frontier_lt_subset_eq (f := fun z : ScalarResponseKernelParameters => z.2.2.1) (g := fun z : ScalarResponseKernelParameters => z.2.2.2) (by fun_prop) (by fun_prop) hz
    rw [←he,scalarResponseKernel7_diagonal β hβ]
    ring
  change Continuous (fun z : ScalarResponseKernelParameters => _)
  exact ((continuous_const.mul (continuous_scalarResponseKernel6 β hβ)).mul
    (φ.continuous.comp (by fun_prop))).add (continuous_const.mul hi)

def scalarRegroupedResponse (β : ℝ) (μ : Paper.ParisiMeasure) (s : ℝ) (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) : ℝ :=
  β^2*(scalarResponseKernel0 β μ p 0 0*φ p
    +(∫ r,scalarResponsePsi1 β μ φ p r ∂parisiFreeMeasure μ s)
    +(∫ r,∫ ell,scalarResponsePsi2 β μ φ p r ell ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s))

abbrev ScalarFloorMeasure (s : ℝ) := {μ : Paper.ParisiMeasure // μ∈scalarFloor s}

theorem continuous_scalarRegroupedResponse (β : ℝ) (hβ : β ≠ 0)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : ScalarFloorMeasure s×Paper.Overlap => scalarRegroupedResponse β z.1.val s φ z.2) := by
  let A := ScalarFloorMeasure s×Paper.Overlap
  have hμ : Continuous (fun z : A => z.1.val) := continuous_subtype_val.comp continuous_fst
  have hp : Continuous (fun z : A => z.2) := continuous_snd
  have h0 := (continuous_scalarResponseKernel0_comp β hβ _ hμ (fun z => z.2) (fun _ => 0) (fun _ => 0) hp continuous_const continuous_const).mul
    (φ.continuous.comp hp)
  have h1f : Continuous (fun z : A×Paper.Overlap => scalarResponsePsi1 β z.1.1.val φ z.1.2 z.2) := by
    have ha : Continuous (fun z : A×Paper.Overlap => (z.1.1.val,(z.1.2,z.2))) :=
      (hμ.comp continuous_fst).prodMk ((hp.comp continuous_fst).prodMk continuous_snd)
    convert! (continuous_scalarResponsePsi1 β hβ φ).comp ha using 1
  have h1 : Continuous (fun z : A => ∫ r,scalarResponsePsi1 β z.1.val φ z.2 r ∂parisiFreeMeasure z.1.val s) :=
    continuous_integral_parisiFreeMeasure_family s hs _ hμ (fun z => z.1.property) _ h1f
  have h2f : Continuous (fun z : (A×Paper.Overlap)×Paper.Overlap =>
      scalarResponsePsi2 β z.1.1.1.val φ z.1.1.2 z.1.2 z.2) := by
    have ha : Continuous (fun z : (A×Paper.Overlap)×Paper.Overlap => (z.1.1.1.val,(z.1.1.2,(z.1.2,z.2)))) :=
      (hμ.comp (continuous_fst.comp continuous_fst)).prodMk
        ((hp.comp (continuous_fst.comp continuous_fst)).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    convert! (continuous_scalarResponsePsi2 β hβ φ).comp ha using 1
  have h2inner : Continuous (fun z : A×Paper.Overlap =>
      ∫ ell,scalarResponsePsi2 β z.1.1.val φ z.1.2 z.2 ell ∂parisiFreeMeasure z.1.1.val s) :=
    continuous_integral_parisiFreeMeasure_family s hs _ (hμ.comp continuous_fst) (fun z => z.1.1.property) _ h2f
  have h2 : Continuous (fun z : A =>
      ∫ r,∫ ell,scalarResponsePsi2 β z.1.val φ z.2 r ell ∂parisiFreeMeasure z.1.val s ∂parisiFreeMeasure z.1.val s) :=
    continuous_integral_parisiFreeMeasure_family s hs _ hμ (fun z => z.1.property) _ h2inner
  change Continuous (fun z : A => _)
  exact continuous_const.mul ((h0.add h1).add h2)

end QuantitativeFollowup
