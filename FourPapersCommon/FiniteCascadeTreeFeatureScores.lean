module
public import FourPapersCommon.FiniteCascadeBinaryFeature
public import FourPapersCommon.FiniteCascadeTreeCharges

@[expose] public section

/-! Actual first and second terminal-feature derivatives of a finite tree
density. A deterministic terminal feature translates every field on the
tree; all potential derivatives below are genuine cascade derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

@[reducible] def finiteCascadeShiftRecords (K : FiniteStateField S) (θ : ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      Records (FiniteStateField S) S T → Records (FiniteStateField S) S T
  | _, .leaf => id
  | _, .advance T => fun z => (z.1+θ • K,finiteCascadeShiftRecords K θ T z.2)
  | _, .fork T U => Prod.map (finiteCascadeShiftRecords K θ T) (finiteCascadeShiftRecords K θ U)

@[reducible] def finiteCascadeTreeTerminalFeature (K : FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Records (FiniteStateField S) S T → ℝ
  | _, .leaf => fun σ=>K σ
  | _, .advance T => fun z=>finiteCascadeTreeTerminalFeature K T z.2
  | _, .fork T U => fun z=>finiteCascadeTreeTerminalFeature K T z.1+
      finiteCascadeTreeTerminalFeature K U z.2

@[reducible] def finiteCascadeTreeInteriorFieldSum (a : ℕ→ℝ)
    (F : ℕ→FiniteStateField S→ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Records (FiniteStateField S) S T → ℝ
  | _, .leaf => fun _=>0
  | _, @FiniteTerminalGenealogy.advance j T => fun z=>
      (finiteCascadeTreeRootCoefficient a T-a j)*F j z.1+
        finiteCascadeTreeInteriorFieldSum a F T z.2
  | _, .fork T U => fun z=>finiteCascadeTreeInteriorFieldSum a F T z.1+
      finiteCascadeTreeInteriorFieldSum a F U z.2

def finiteCascadeTreeFieldSum (a : ℕ→ℝ) (F : ℕ→FiniteStateField S→ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) : ℝ :=
  (finiteCascadeTreeRootCoefficient a T-s)*F j H+finiteCascadeTreeInteriorFieldSum a F T z

theorem finiteCascadeTreeFieldSum_eq_charge_sum (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeFieldSum a (finiteStateGaussianTerminalCascade V a L) s T H z=
      ((finiteCascadeTreeCharges V a L s T H z).map (fun c=>c.1*c.2)).sum := by
  have hi : finiteCascadeTreeInteriorFieldSum a (finiteStateGaussianTerminalCascade V a L) T z=
      ((finiteCascadeTreeInteriorCharges V a L T z).map (fun c=>c.1*c.2)).sum := by
    induction T with
    | leaf => rfl
    | advance T ih => simpa only [finiteCascadeTreeInteriorFieldSum,finiteCascadeTreeInteriorCharges,
        List.map_cons,List.sum_cons] using congrArg (fun u=>_+u) (ih z.2)
    | fork T U ihT ihU =>
        simpa only [finiteCascadeTreeInteriorFieldSum,finiteCascadeTreeInteriorCharges,
          List.map_append,List.sum_append] using congrArg₂ (·+·) (ihT z.1) (ihU z.2)
  simp only [finiteCascadeTreeFieldSum,finiteCascadeTreeCharges,List.map_cons,List.sum_cons,hi]

private theorem hasDerivAt_interiorFieldSum (a : ℕ→ℝ)
    (F D : ℕ→FiniteStateField S→ℝ) (K : FiniteStateField S)
    (hd : ∀(j : ℕ) (H : FiniteStateField S) (θ : ℝ),
      HasDerivAt (fun u=>F j (H+u • K)) (D j (H+θ • K)) θ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (fun u=>finiteCascadeTreeInteriorFieldSum a F T (finiteCascadeShiftRecords K u T z))
      (finiteCascadeTreeInteriorFieldSum a D T (finiteCascadeShiftRecords K θ T z)) θ := by
  induction T with
  | leaf => exact hasDerivAt_const θ 0
  | @advance j T ih => exact ((hd j z.1 θ).const_mul _).add (ih z.2)
  | fork T U ihT ihU => exact (ihT z.1).add (ihU z.2)

private theorem hasDerivAt_treeFieldSum (a : ℕ→ℝ)
    (F D : ℕ→FiniteStateField S→ℝ) (K : FiniteStateField S)
    (hd : ∀(j : ℕ) (H : FiniteStateField S) (θ : ℝ),
      HasDerivAt (fun u=>F j (H+u • K)) (D j (H+θ • K)) θ)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (fun u=>finiteCascadeTreeFieldSum a F s T (H+u • K) (finiteCascadeShiftRecords K u T z))
      (finiteCascadeTreeFieldSum a D s T (H+θ • K) (finiteCascadeShiftRecords K θ T z)) θ :=
  ((hd j H θ).const_mul _).add (hasDerivAt_interiorFieldSum a F D K hd T z θ)

private theorem hasDerivAt_treeTerminalEnergy (V : S→ℝ) (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (fun u=>finiteCascadeTreeTerminalEnergy V T (H+u • K) (finiteCascadeShiftRecords K u T z))
      (finiteCascadeTreeTerminalFeature K T z) θ := by
  induction T generalizing H with
  | leaf =>
      change HasDerivAt (fun u=>(H+u • K) z+V z) (K z) θ
      simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,id_eq,one_mul] using
        (((hasDerivAt_id θ).mul_const (K z)).const_add (H z)).add_const (V z)
  | advance T ih => exact ih z.1 z.2
  | fork T U ihT ihU => exact (ihT H z.1).add (ihU H z.2)

def finiteCascadeTreeFeatureLogNumerator (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) : ℝ :=
  finiteCascadeTreeTerminalEnergy V T (H+θ • K) (finiteCascadeShiftRecords K θ T z)-
    finiteCascadeTreeFieldSum a (finiteStateGaussianTerminalCascade V a L) s T
      (H+θ • K) (finiteCascadeShiftRecords K θ T z)

def finiteCascadeTreeFeatureScore (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) : ℝ :=
  finiteCascadeTreeTerminalFeature K T z-
    finiteCascadeTreeFieldSum a (fun j Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K)
      s T (H+θ • K) (finiteCascadeShiftRecords K θ T z)

def finiteCascadeTreeFeatureSecondCharge (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) : ℝ :=
  finiteCascadeTreeFieldSum a (fun j Q=>fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) Q K K)
    s T (H+θ • K) (finiteCascadeShiftRecords K θ T z)

theorem hasDerivAt_finiteCascadeTreeFeatureLogNumerator (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (finiteCascadeTreeFeatureLogNumerator V a L s T H K z)
      (finiteCascadeTreeFeatureScore V a L s T H K z θ) θ := by
  apply (hasDerivAt_treeTerminalEnergy V K T H z θ).sub
  apply hasDerivAt_treeFieldSum
  intro p Q u
  have hh := ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).differentiable_one
    (Q+u • K)).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).smul_const K |>.const_add Q)
  simpa only [Function.comp_def,id_eq,one_smul] using hh

theorem hasDerivAt_finiteCascadeTreeFeatureScore (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (finiteCascadeTreeFeatureScore V a L s T H K z)
      (-finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ) θ := by
  have hh : HasDerivAt (fun u=>finiteCascadeTreeFieldSum a
      (fun j Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K)
      s T (H+u • K) (finiteCascadeShiftRecords K u T z))
      (finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ) θ := by
    apply hasDerivAt_treeFieldSum
    intro p Q u
    have hf : ContDiff ℝ 1 (fderiv ℝ (finiteStateGaussianTerminalCascade V a L p)) :=
      (contDiff_two_finiteStateGaussianTerminalCascade V a ha L p).fderiv_right (by norm_num)
    simpa only [Function.comp_def,one_smul,id_eq,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.zero_apply,zero_add,ContinuousLinearMap.flip_apply] using
      ((hf.differentiable_one (Q+u • K)).hasFDerivAt.clm_apply
        (hasFDerivAt_const (K) (Q+u • K))).comp_hasDerivAt u
          ((hasDerivAt_id u).smul_const K |>.const_add Q)
  unfold finiteCascadeTreeFeatureScore
  convert hh.const_sub (finiteCascadeTreeTerminalFeature K T z) using 1

theorem hasDerivAt_finiteCascadeTreeFeatureNumerator (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (fun u=>Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T H K z u))
      (Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T H K z θ)*
        finiteCascadeTreeFeatureScore V a L s T H K z θ) θ := by
  simpa only [mul_comm] using
    (hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T H K z θ).exp

theorem hasDerivAt_finiteCascadeTreeFeatureNumerator_derivative (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    HasDerivAt (fun u=>Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T H K z u)*
      finiteCascadeTreeFeatureScore V a L s T H K z u)
      (Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T H K z θ)*
        ((finiteCascadeTreeFeatureScore V a L s T H K z θ)^2-
          finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ)) θ := by
  convert (hasDerivAt_finiteCascadeTreeFeatureNumerator V a ha L s T H K z θ).mul
    (hasDerivAt_finiteCascadeTreeFeatureScore V a ha L s T H K z θ) using 1 <;> ring

end FourPapersCommon
