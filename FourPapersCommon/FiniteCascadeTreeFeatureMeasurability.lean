module
public import FourPapersCommon.FiniteCascadeTreeFeatureLaw

@[expose] public section

/-! Actual measurability of the recorded-tree feature scores used in
dominated parameter differentiation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem measurable_finiteCascadeShiftRecords (K : FiniteStateField S) (θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeShiftRecords K θ T) := by
  induction T with
  | leaf => exact measurable_id
  | advance T ih => exact (measurable_fst.add_const _).prodMk (ih.comp measurable_snd)
  | fork T U ihT ihU => exact (ihT.comp measurable_fst).prodMk (ihU.comp measurable_snd)

theorem measurable_finiteCascadeTreeTerminalFeature (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeTreeTerminalFeature K T) := by
  induction T with
  | leaf => exact measurable_of_finite _
  | advance T ih => exact ih.comp measurable_snd
  | fork T U ihT ihU => exact (ihT.comp measurable_fst).add (ihU.comp measurable_snd)

theorem measurable_finiteCascadeTreeInteriorFieldSum (a : ℕ→ℝ)
    (F : ℕ→FiniteStateField S→ℝ) (hF : ∀j,Measurable (F j))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeTreeInteriorFieldSum a F T) := by
  induction T with
  | leaf => exact measurable_const
  | @advance j T ih =>
      exact ((hF j).comp measurable_fst |>.const_mul _).add (ih.comp measurable_snd)
  | fork T U ihT ihU => exact (ihT.comp measurable_fst).add (ihU.comp measurable_snd)

theorem measurable_finiteCascadeTreeFieldSum (a : ℕ→ℝ)
    (F : ℕ→FiniteStateField S→ℝ) (hF : ∀j,Measurable (F j)) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (Function.uncurry (finiteCascadeTreeFieldSum a F s T)) :=
  ((hF j).comp measurable_fst |>.const_mul _).add
    ((measurable_finiteCascadeTreeInteriorFieldSum a F hF T).comp measurable_snd)

theorem measurable_finiteCascadeTreeFeatureScore (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (fun z : FiniteStateField S×Records (FiniteStateField S) S T=>
      finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ) := by
  have hF (j : ℕ) : Measurable (fun Q : FiniteStateField S=>
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K) :=
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).measurable
  exact ((measurable_finiteCascadeTreeTerminalFeature K T).comp measurable_snd).sub
    ((measurable_finiteCascadeTreeFieldSum a _ hF s T).comp
      ((measurable_fst.add_const (θ • K)).prodMk
        ((measurable_finiteCascadeShiftRecords K θ T).comp measurable_snd)))

theorem measurable_finiteCascadeTreeFeatureSecondCharge (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (fun z : FiniteStateField S×Records (FiniteStateField S) S T=>
      finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ) := by
  have hF (j : ℕ) : Measurable (fun Q : FiniteStateField S=>
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) Q K K) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) :=
      (contDiff_two_finiteStateGaussianTerminalCascade V a ha L j).fderiv_right (by norm_num)
    exact ((hd.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
      continuous_const).measurable
  exact (measurable_finiteCascadeTreeFieldSum a _ hF s T).comp
    ((measurable_fst.add_const (θ • K)).prodMk
      ((measurable_finiteCascadeShiftRecords K θ T).comp measurable_snd))

end FourPapersCommon
