module
public import QuantitativePaper.ScalarCylinderJets
public import QuantitativePaper.SmoothOpenGaussianAverage
public import DepthPaper.PointwiseDerivativeBounds
public import FourPapersCommon.PartialIteratedFDerivSmooth

@[expose] public section

/-! Actual derivative bounds for a Gaussian evaluation with a smooth
variable scalar shift. The shift derivatives grow only linearly in the
Gaussian coordinate, uniformly on compact time intervals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

def variableGaussianEvaluation (B : (ℝ×E)→L[ℝ]G) (A : Field n→L[ℝ]G)
    (l : ℝ→ℝ) (z : Field n) (x : ℝ×E) : G:=B x+l x.1 • A z

theorem norm_iteratedFDeriv_clm_le_positive (B : E→L[ℝ]G) (j : ℕ) (hj : 1≤j)
    (x : E) : ‖iteratedFDeriv ℝ j B x‖≤‖B‖ := by
  have he : fderiv ℝ (B : E→G)=fun _=>B:=funext fun x=>B.hasFDerivAt.fderiv
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 1 (B : E→G) x‖≤‖B‖
      simpa only [norm_iteratedFDeriv_one,he] using le_refl ‖B‖
    | succ j =>
      rw [←norm_iteratedFDeriv_fderiv,he,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]
      exact norm_nonneg _

theorem variableGaussianEvaluation_smooth (B : (ℝ×E)→L[ℝ]G) (A : Field n→L[ℝ]G)
    (l : ℝ→ℝ) (x : ℝ×E) (hl : ContDiffAt ℝ ∞ l x.1) (z : Field n) :
    ContDiffAt ℝ ∞ (variableGaussianEvaluation B A l z) x :=
  B.contDiff.contDiffAt.add ((hl.comp x contDiff_fst.contDiffAt).smul_const (A z))

theorem variableGaussianEvaluation_jet_bound (N : ℕ) (B : (ℝ×E)→L[ℝ]G)
    (A : Field n→L[ℝ]G) (l : ℝ→ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hl : ContDiffOn ℝ N l U) (a b : ℝ) (hsub : Icc a b⊆U) :
    ∃ M : ℝ, 1≤M ∧ ∀ j,1≤j→j≤N→∀ x : ℝ×E,x.1∈Icc a b→∀ z,
      ‖iteratedFDeriv ℝ j (variableGaussianEvaluation B A l z) x‖≤
        M*(1+‖z‖) := by
  obtain ⟨C,hC,hj⟩:=exists_scalar_cylinder_jet_bound (E:=E) N l U hU hl a b hsub
  let M:=max 1 (‖B‖+C*‖A‖)
  refine ⟨M,le_max_left _ _,?_⟩
  intro j hj0 hjN x hx z
  have hL : ContDiffAt ℝ j (fun y : ℝ×E=>l y.1) x:=
    ((hl.of_le (by exact_mod_cast hjN)).contDiffAt (hU.mem_nhds (hsub hx))).comp x
      contDiff_fst.contDiffAt
  have hB : ContDiffAt ℝ j (fun y : ℝ×E=>B y) x:=B.contDiff.contDiffAt
  change ‖iteratedFDeriv ℝ j (fun y=>B y+l y.1 • A z) x‖≤_
  have headd : iteratedFDeriv ℝ j (fun y : ℝ×E=>B y+l y.1 • A z) x=
      iteratedFDeriv ℝ j (fun y=>B y) x+
        iteratedFDeriv ℝ j (fun y : ℝ×E=>l y.1 • A z) x:=by
    convert iteratedFDeriv_add_apply hB (hL.smul_const (A z)) using 1 <;> rfl
  rw [headd,iteratedFDeriv_smul_const_apply hL]
  have hs:=((ContinuousLinearMap.id ℝ ℝ).smulRight (A z)).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ j (fun y : ℝ×E=>l y.1) x)
  have hnorm : ‖(ContinuousLinearMap.id ℝ ℝ).smulRight (A z)‖≤‖A z‖:=by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    simp
  have hz:=A.le_opNorm z
  have hb:=norm_iteratedFDeriv_clm_le_positive B j hj0 x
  have hh:=norm_add_le (iteratedFDeriv ℝ j (fun y=>B y) x)
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (A z)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ j (fun y : ℝ×E=>l y.1) x))
  have hs' : ‖((ContinuousLinearMap.id ℝ ℝ).smulRight (A z)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ j (fun y : ℝ×E=>l y.1) x)‖≤C*‖A‖*‖z‖:=by
    apply hs.trans
    calc
      _≤‖A z‖*C:=mul_le_mul hnorm (hj j hjN x hx) (norm_nonneg _) (norm_nonneg _)
      _≤(‖A‖*‖z‖)*C:=mul_le_mul_of_nonneg_right hz (zero_le_one.trans hC)
      _=C*‖A‖*‖z‖:=by ring
  have hMB:‖B‖≤M:=(le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hC) (norm_nonneg _))).trans
    (le_max_right _ _)
  have hMA:C*‖A‖≤M:=(le_add_of_nonneg_left (norm_nonneg B)).trans (le_max_right _ _)
  have hh':=add_le_add hb hs'
  exact (hh.trans hh').trans (by nlinarith [norm_nonneg z])

end QuantitativePaper
