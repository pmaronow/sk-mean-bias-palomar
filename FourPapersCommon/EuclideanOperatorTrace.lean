module
public import FourPapersCommon.EuclideanOperatorMatrix
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Genuine parameter derivatives of the actual Euclidean operator trace. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}
local notation "Vec" => EuclideanSpace ℝ (Fin n)

def euclideanOperatorTrace (L : Vec→L[ℝ]Vec) : ℝ:=Matrix.trace (euclideanOperatorMatrix L)

def euclideanOperatorTraceCLM : (Vec→L[ℝ]Vec)→L[ℝ]ℝ:=
  (Matrix.traceLinearMap (α:=ℝ) (n:=Fin n) (R:=ℝ)).toContinuousLinearMap.comp
    euclideanOperatorMatrixCLM

theorem hasDerivAt_euclideanOperatorTrace {H : ℝ→Vec→L[ℝ]Vec} {L : Vec→L[ℝ]Vec} {a : ℝ}
    (hH : HasDerivAt H L a) :
    HasDerivAt (fun θ=>euclideanOperatorTrace (H θ)) (euclideanOperatorTrace L) a := by
  have hd : HasFDerivAt (euclideanOperatorTraceCLM (n:=n) : (Vec→L[ℝ]Vec)→ℝ)
      euclideanOperatorTraceCLM (H a):=euclideanOperatorTraceCLM.hasFDerivAt
  convert hd.comp_hasDerivAt (E := ℝ) a hH using 1 <;> rfl

theorem deriv_euclideanOperatorTrace (H : ℝ→Vec→L[ℝ]Vec) (a : ℝ)
    (hH : DifferentiableAt ℝ H a) :
    deriv (fun θ=>euclideanOperatorTrace (H θ)) a=euclideanOperatorTrace (deriv H a):=
  (hasDerivAt_euclideanOperatorTrace hH.hasDerivAt).deriv

theorem deriv_deriv_euclideanOperatorTrace (H : ℝ→Vec→L[ℝ]Vec) (a : ℝ)
    (hH : ContDiffAt ℝ ∞ H a) :
    deriv (deriv (fun θ=>euclideanOperatorTrace (H θ))) a=
      euclideanOperatorTrace (deriv (deriv H) a) := by
  have he : deriv (fun θ=>euclideanOperatorTrace (H θ))=ᶠ[𝓝 a]
      (fun θ=>euclideanOperatorTrace (deriv H θ)):=by
    filter_upwards [(hH.of_le (by norm_num : (2 : ℕ∞ω)≤∞)).eventually (by norm_num)] with θ hθ
    exact deriv_euclideanOperatorTrace H θ (hθ.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  exact deriv_euclideanOperatorTrace (deriv H) a
    ((hH.derivWithin (by simp) : ContDiffAt ℝ ∞ (deriv H) a).differentiableAt (by simp))

end FourPapersCommon
