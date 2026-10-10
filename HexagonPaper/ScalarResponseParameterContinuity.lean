module
public import QuantitativeFollowup.ScalarResponseContinuity

@[expose] public section

/-! Joint continuity of the exact scalar response in its profile and its
continuous transport direction. Strict future intervals retain their atoms;
the original regrouping makes their coefficients vanish on the diagonal. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon FRSB QuantitativePaper
open scoped Topology
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
theorem continuous_scalarResponsePsi1_joint_test (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : (Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×Paper.Overlap) => scalarResponsePsi1 β z.1.1 z.1.2 z.2.1 z.2.2) := by
  let A := (Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×Paper.Overlap)
  have hk1 := continuous_scalarResponseKernel1_comp (A := A) β hβ (fun z => z.1.1) (by fun_prop)
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hk2 := continuous_scalarResponseKernel2_comp (A := A) β hβ (fun z => z.1.1) (by fun_prop)
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hb : Continuous (fun z : A =>
      2*scalarResponseKernel1 β z.1.1 z.2.1 z.2.2 0*z.1.2 z.2.1-
        scalarResponseKernel2 β z.1.1 z.2.1 z.2.2 0*z.1.2 z.2.2) :=
    ((continuous_const.mul hk1).mul (by fun_prop)).sub
      (hk2.mul (by fun_prop))
  have hi : Continuous (fun z : A => if z.2.1<z.2.2 then
      2*scalarResponseKernel1 β z.1.1 z.2.1 z.2.2 0*z.1.2 z.2.1-
        scalarResponseKernel2 β z.1.1 z.2.1 z.2.2 0*z.1.2 z.2.2 else 0) := by
    apply Continuous.if _ hb continuous_const
    intro z hz
    have he : z.2.1=z.2.2 := frontier_lt_subset_eq (f := fun z : A => z.2.1) (g := fun z : A => z.2.2) (by fun_prop) (by fun_prop) hz
    rw [←he,scalarResponseKernel2_diagonal β hβ]
    ring
  have hk3 := continuous_scalarResponseKernel3_comp (A := A) β hβ (fun z => z.1.1) (by fun_prop)
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hk4 := continuous_scalarResponseKernel4_comp (A := A) β hβ (fun z => z.1.1) (by fun_prop)
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  have hk5 := continuous_scalarResponseKernel5_comp (A := A) β hβ (fun z => z.1.1) (by fun_prop)
    (fun z => z.2.1) (fun z => z.2.2) (fun _ => 0) (by fun_prop) (by fun_prop) continuous_const
  change Continuous (fun z : A => _)
  exact ((hi.sub ((continuous_const.mul hk3).mul (by fun_prop))).sub
    (hk4.mul (by fun_prop))).add
      ((continuous_const.mul hk5).mul (by fun_prop))

theorem continuous_scalarResponsePsi2_joint_test (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => scalarResponsePsi2 β z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2) := by
  have hb : Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) =>
      scalarResponseKernel7 β z.1.1 z.2.1 z.2.2.1 z.2.2.2*z.1.2 z.2.2.2-
        scalarResponseKernel5 β z.1.1 z.2.1 z.2.2.1 z.2.2.2*z.1.2 z.2.2.1) :=
    (((continuous_scalarResponseKernel7 β hβ).comp (by fun_prop : Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => (z.1.1,z.2)))).mul (by fun_prop)).sub
      (((continuous_scalarResponseKernel5 β hβ).comp (by fun_prop : Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => (z.1.1,z.2)))).mul (by fun_prop))
  have hi : Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => if z.2.2.1<z.2.2.2 then
      scalarResponseKernel7 β z.1.1 z.2.1 z.2.2.1 z.2.2.2*z.1.2 z.2.2.2-
        scalarResponseKernel5 β z.1.1 z.2.1 z.2.2.1 z.2.2.2*z.1.2 z.2.2.1 else 0) := by
    apply Continuous.if _ hb continuous_const
    intro z hz
    have he : z.2.2.1=z.2.2.2 := frontier_lt_subset_eq (f := fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => z.2.2.1) (g := fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => z.2.2.2) (by fun_prop) (by fun_prop) hz
    rw [←he,scalarResponseKernel7_diagonal β hβ]
    ring
  change Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => _)
  exact ((continuous_const.mul ((continuous_scalarResponseKernel6 β hβ).comp (by fun_prop : Continuous (fun z : ((Paper.ParisiMeasure×C(Paper.Overlap,ℝ))×(Paper.Overlap×(Paper.Overlap×Paper.Overlap))) => (z.1.1,z.2))))).mul
    (by fun_prop)).add (continuous_const.mul hi)


theorem continuous_scalarRegroupedResponse_joint_test (β : ℝ) (hβ : β ≠ 0)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
    Continuous (fun z : (ScalarFloorMeasure s×C(Paper.Overlap,ℝ))×Paper.Overlap =>
      scalarRegroupedResponse β z.1.1.val s z.1.2 z.2) := by
  let A := (ScalarFloorMeasure s×C(Paper.Overlap,ℝ))×Paper.Overlap
  have hμ : Continuous (fun z : A => z.1.1.val) := by fun_prop
  have hp : Continuous (fun z : A => z.2) := continuous_snd
  have hφ : Continuous (fun z : A => z.1.2 z.2) :=
    continuous_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have h0 := (continuous_scalarResponseKernel0_comp β hβ _ hμ (fun z => z.2)
    (fun _ => 0) (fun _ => 0) hp continuous_const continuous_const).mul hφ
  have h1f : Continuous (fun z : A×Paper.Overlap =>
      scalarResponsePsi1 β z.1.1.1.val z.1.1.2 z.1.2 z.2) := by
    have ha : Continuous (fun z : A×Paper.Overlap =>
        ((z.1.1.1.val,z.1.1.2),(z.1.2,z.2))) := by
      dsimp only [A]
      fun_prop
    convert! (continuous_scalarResponsePsi1_joint_test β hβ).comp ha using 1
  have h1 : Continuous (fun z : A => ∫r,
      scalarResponsePsi1 β z.1.1.val z.1.2 z.2 r ∂parisiFreeMeasure z.1.1.val s) :=
    continuous_integral_parisiFreeMeasure_family s hs _ hμ (fun z => z.1.1.property) _ h1f
  have h2f : Continuous (fun z : (A×Paper.Overlap)×Paper.Overlap =>
      scalarResponsePsi2 β z.1.1.1.1.val z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by
    have ha : Continuous (fun z : (A×Paper.Overlap)×Paper.Overlap =>
        ((z.1.1.1.1.val,z.1.1.1.2),(z.1.1.2,(z.1.2,z.2)))) := by
      dsimp only [A]
      fun_prop
    convert! (continuous_scalarResponsePsi2_joint_test β hβ).comp ha using 1
  have h2inner : Continuous (fun z : A×Paper.Overlap => ∫ell,
      scalarResponsePsi2 β z.1.1.1.val z.1.1.2 z.1.2 z.2 ell
        ∂parisiFreeMeasure z.1.1.1.val s) :=
    continuous_integral_parisiFreeMeasure_family s hs _ (hμ.comp continuous_fst)
      (fun z => z.1.1.1.property) _ h2f
  have h2 : Continuous (fun z : A => ∫r,∫ell,
      scalarResponsePsi2 β z.1.1.val z.1.2 z.2 r ell
        ∂parisiFreeMeasure z.1.1.val s ∂parisiFreeMeasure z.1.1.val s) :=
    continuous_integral_parisiFreeMeasure_family s hs _ hμ (fun z => z.1.1.property) _ h2inner
  exact continuous_const.mul ((h0.add h1).add h2)

theorem continuous_scalarResponseOperator_joint_test (β : ℝ) (hβ : β ≠ 0)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
    Continuous (fun z : (ScalarFloorMeasure s×C(Paper.Overlap,ℝ))×Paper.Overlap =>
      scalarResponseOperator β hβ z.1.1.val s z.1.2 z.2) := by
  convert! continuous_scalarRegroupedResponse_joint_test β hβ s hs using 1
  funext z
  exact scalarResponseOperator_eq_regrouped β hβ z.1.1.val s hs z.1.1.property z.1.2 z.2

end HexagonPaper
