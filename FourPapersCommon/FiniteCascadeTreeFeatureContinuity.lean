module
public import FourPapersCommon.FiniteCascadeTreeFeatureSecondResponse
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Actual continuity of the finite tree's second feature charge. The
potential is the genuine smooth Gaussian cascade, at every recorded vertex. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

private theorem continuous_interiorFieldSum_shift (a : ℕ→ℝ)
    (F : ℕ→FiniteStateField S→ℝ) (hF : ∀j,Continuous (F j))
    (K : FiniteStateField S) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : Records (FiniteStateField S) S T) :
    Continuous (fun θ=>finiteCascadeTreeInteriorFieldSum a F T
      (finiteCascadeShiftRecords K θ T z)) := by
  induction T with
  | leaf => exact continuous_const
  | @advance j T ih =>
      exact (((hF j).comp (continuous_const.add (continuous_id.smul continuous_const))).const_mul _).add (ih z.2)
  | fork T U ihT ihU => exact (ihT z.1).add (ihU z.2)

private theorem continuous_treeFieldSum_shift (a : ℕ→ℝ)
    (F : ℕ→FiniteStateField S→ℝ) (hF : ∀j,Continuous (F j))
    (s : ℝ) (K : FiniteStateField S) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (H : FiniteStateField S) (z : Records (FiniteStateField S) S T) :
    Continuous (fun θ=>finiteCascadeTreeFieldSum a F s T (H+θ • K)
      (finiteCascadeShiftRecords K θ T z)) :=
  (((hF j).comp (continuous_const.add (continuous_id.smul continuous_const))).const_mul _).add
    (continuous_interiorFieldSum_shift a F hF K T z)

theorem continuous_finiteCascadeTreeFeatureSecondCharge (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    Continuous (finiteCascadeTreeFeatureSecondCharge V a L s T H K z) := by
  apply continuous_treeFieldSum_shift
  intro p
  have hc : Continuous (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L p))) :=
    (((contDiff_two_finiteStateGaussianTerminalCascade V a ha L p).fderiv_right
      (m:=1) (by norm_num)).fderiv_right (m:=0) (by norm_num)).continuous
  exact (hc.clm_apply continuous_const).clm_apply continuous_const

theorem continuous_finiteCascadeTreeFeatureSecondNumerator (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    Continuous (fun θ=>Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T H K z θ)*
      ((finiteCascadeTreeFeatureScore V a L s T H K z θ)^2-
        finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ)) := by
  have hn : Continuous (finiteCascadeTreeFeatureLogNumerator V a L s T H K z) :=
    continuous_iff_continuousAt.mpr fun θ=>
      (hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T H K z θ).continuousAt
  have hq : Continuous (finiteCascadeTreeFeatureScore V a L s T H K z) :=
    continuous_iff_continuousAt.mpr fun θ=>
      (hasDerivAt_finiteCascadeTreeFeatureScore V a ha L s T H K z θ).continuousAt
  exact (Real.continuous_exp.comp hn).mul ((hq.pow 2).sub (continuous_finiteCascadeTreeFeatureSecondCharge V a ha L s T H K z))

end FourPapersCommon
