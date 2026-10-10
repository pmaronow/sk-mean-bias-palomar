module
public import FourPapersCommon.PartialFDerivSmooth
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

@[expose] public section

/-! Genuine joint smoothness of all iterated partial spatial derivatives.
The parameter is retained while derivatives are taken in the first variable. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {A E F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_partial_fderiv_first (U : E×A→F) (p : E×A)
    (hU : ContDiffAt ℝ ∞ U p) :
    ContDiffAt ℝ ∞ (fun z : E×A=>fderiv ℝ (fun y=>U (y,z.2)) z.1) p := by
  let V : A×E→F:=fun z=>U (z.2,z.1)
  have hV : ContDiffAt ℝ ∞ V (p.2,p.1):=
    ContDiffAt.comp (f := Prod.swap) (g := U) (p.2,p.1) hU
      (ContinuousLinearEquiv.prodComm ℝ A E).contDiff.contDiffAt
  have hD:=contDiffAt_partial_fderiv V (p.2,p.1) hV
  exact ContDiffAt.comp (f := Prod.swap)
    (g := fun z : A×E=>fderiv ℝ (fun y=>V (z.1,y)) z.2) p hD
      (ContinuousLinearEquiv.prodComm ℝ E A).contDiff.contDiffAt

theorem contDiffAt_partial_iteratedFDeriv (j : ℕ) (U : E×A→F) (p : E×A)
    (hU : ContDiffAt ℝ ∞ U p) :
    ContDiffAt ℝ ∞ (fun z : E×A=>iteratedFDeriv ℝ j (fun y=>U (y,z.2)) z.1) p := by
  induction j generalizing F with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,Function.comp_def,Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.contDiffAt.comp p hU
  | succ j ih =>
    let D : E×A→E→L[ℝ]F:=fun z=>fderiv ℝ (fun y=>U (y,z.2)) z.1
    have hD:ContDiffAt ℝ ∞ D p:=contDiffAt_partial_fderiv_first U p hU
    have hh:=ih D hD
    have hc:ContDiffAt ℝ ∞ (fun z : E×A=>
        (continuousMultilinearCurryRightEquiv' ℝ j E F).symm
          (iteratedFDeriv ℝ j (fun y=>D (y,z.2)) z.1)) p:=
      (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.contDiff.contDiffAt.comp p hh
    simpa only [D,iteratedFDeriv_succ_eq_comp_right,Function.comp_apply] using hc

end FourPapersCommon
