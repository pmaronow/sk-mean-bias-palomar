module
public import FourPapersCommon.FiniteCascadeTreeFeatureBounds
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity

@[expose] public section

/-! A terminal feature is an actual perturbation of the finite Gibbs
energy. The resulting full tree probability law has the fixed Gaussian
reference law and the genuine one-leaf Gaussian normalizer. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy OverlapPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteStateGaussianTerminalCascade_terminal_add (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascade (fun σ=>V σ+K σ) a L j H=
      finiteStateGaussianTerminalCascade V a L j (H+K) := by
  induction j generalizing H with
  | zero =>
      simp only [finiteStateGaussianTerminalCascade,finiteStateGaussianCascade,
        gtStateLogPartition,gtStatePartition]
      congr 1
      apply Finset.sum_congr rfl
      intro σ hσ
      congr 1
      simp only [PiLp.add_apply]
      ring
  | succ j ih =>
      change sourceLogAverage _ (a j) (fun z=>
        finiteStateGaussianTerminalCascade (fun σ=>V σ+K σ) a L j (H+L j z))=
        sourceLogAverage _ (a j) (fun z=>finiteStateGaussianTerminalCascade V a L j (H+K+L j z))
      congr 1
      funext z
      rw [ih]
      congr 1
      abel

theorem finiteCascadeTreeTerminalEnergy_terminal_add (V : S→ℝ) (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeTerminalEnergy (fun σ=>V σ+K σ) T H z=
      finiteCascadeTreeTerminalEnergy V T (H+K) (finiteCascadeShiftRecords K 1 T z) := by
  induction T generalizing H with
  | leaf => simp only [finiteCascadeTreeTerminalEnergy,finiteCascadeShiftRecords,id_eq,
      PiLp.add_apply];ring
  | advance T ih =>
      simpa only [finiteCascadeTreeTerminalEnergy,finiteCascadeShiftRecords,one_smul]
        using ih z.1 z.2
  | fork T U ihT ihU => exact congrArg₂ (·+·) (ihT H z.1) (ihU H z.2)

theorem finiteCascadeTreeInteriorFieldSum_terminal_add (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeInteriorFieldSum a (finiteStateGaussianTerminalCascade (fun σ=>V σ+K σ) a L) T z=
      finiteCascadeTreeInteriorFieldSum a (finiteStateGaussianTerminalCascade V a L) T
        (finiteCascadeShiftRecords K 1 T z) := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      simp only [finiteCascadeTreeInteriorFieldSum,finiteCascadeShiftRecords,one_smul,
        finiteStateGaussianTerminalCascade_terminal_add,ih z.2]
  | fork T U ihT ihU => exact congrArg₂ (·+·) (ihT z.1) (ihU z.2)

theorem finiteCascadeShiftRecords_smul (K : FiniteStateField S) (θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    finiteCascadeShiftRecords (θ • K) 1 T z=finiteCascadeShiftRecords K θ T z := by
  induction T with
  | leaf => rfl
  | advance T ih => simp only [finiteCascadeShiftRecords,one_smul,ih z.2]
  | fork T U ihT ihU => exact Prod.ext (ihT z.1) (ihU z.2)

theorem finiteCascadeTreeFeatureLogNumerator_eq_intrinsic (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeFeatureLogNumerator V a L s T H K z θ=
      s*finiteStateGaussianTerminalCascade (fun σ=>V σ+θ*K σ) a L j H+
        finiteCascadeTreeLogDensity (fun σ=>V σ+θ*K σ) a L T H z := by
  rw [finiteCascadeTreeLogDensity_add_root_eq]
  rw [←finiteCascadeTreeFieldSum_eq_charge_sum]
  change finiteCascadeTreeFeatureLogNumerator V a L s T H K z θ=
    finiteCascadeTreeTerminalEnergy (fun σ=>V σ+(θ • K) σ) T H z-
      finiteCascadeTreeFieldSum a (finiteStateGaussianTerminalCascade (fun σ=>V σ+(θ • K) σ) a L) s T H z
  rw [finiteCascadeTreeTerminalEnergy_terminal_add V (θ • K)]
  rw [finiteCascadeTreeFieldSum]
  rw [finiteStateGaussianTerminalCascade_terminal_add V (θ • K),
    finiteCascadeTreeInteriorFieldSum_terminal_add V (θ • K)]
  simp only [finiteCascadeShiftRecords_smul]
  rfl

theorem measurable_finiteCascadeTreeFeatureLogNumerator (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (fun z : FiniteStateField S×Records (FiniteStateField S) S T=>
      finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ) := by
  simp_rw [finiteCascadeTreeFeatureLogNumerator_eq_intrinsic]
  exact (((contDiff_one_finiteStateGaussianTerminalCascade (fun σ=>V σ+θ*K σ) a ha L j).continuous.measurable.comp
    measurable_fst).const_mul s).add
      (measurable_finiteCascadeTreeLogDensity (fun σ=>V σ+θ*K σ) a ha L T)

def finiteCascadeTreeGaussianFeatureLaw (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :=
  finiteCascadeTreeGaussianJointLaw (fun σ=>V σ+θ*K σ) a L s T R H

theorem finiteCascadeTreeGaussianFeatureLaw_probability (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    IsProbabilityMeasure (finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H) :=
  finiteCascadeTreeGaussianJointLaw_probability _ _ ha _ _ _ _ _

theorem finiteCascadeTreeGaussianFeatureLaw_density (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H=
      (finiteCascadeTreeGaussianReferenceLaw L T R H).withDensity (fun z=>ENNReal.ofReal
        (Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)/
          finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+θ*K σ) a L s j R H)) := by
  rw [finiteCascadeTreeGaussianFeatureLaw,finiteCascadeTreeGaussianJointLaw_density _ _ ha]
  congr 1
  funext z
  rw [←finiteCascadeTreeLogDensity_add_root_eq,
    ←finiteCascadeTreeFeatureLogNumerator_eq_intrinsic]

end FourPapersCommon
