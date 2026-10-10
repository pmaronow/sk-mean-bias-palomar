module
public import FourPapersCommon.FiniteCascadeVertexWeights

@[expose] public section

/-! Exact separation of recorded-tree charges into scalar Stieltjes edge
increments and inherited branch levels. This is a combinatorial identity
for the actual vertex charges, including repeated physical levels. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

def finiteCascadeLevelChargeSum (a : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (χ : ℕ → ℝ) : ℝ :=
  ((finiteCascadeVertexCharges a s T).map (fun c => c.1*χ c.2.depth)).sum

@[reducible] def finiteCascadeEdgeLevelSum (a χ : ℕ → ℝ) :
    {j : ℕ} → FiniteTerminalGenealogy j → ℝ
  | _, .leaf => (1-a 0)*χ 0
  | _, @FiniteTerminalGenealogy.advance j T =>
      finiteCascadeEdgeLevelSum a χ T+(a j-a (j+1))*χ (j+1)
  | _, .fork T U => finiteCascadeEdgeLevelSum a χ T+finiteCascadeEdgeLevelSum a χ U

@[reducible] def finiteCascadeBranchLevelSum (a χ : ℕ → ℝ) :
    {j : ℕ} → FiniteTerminalGenealogy j → ℝ
  | _, .leaf => 0
  | _, .advance T => finiteCascadeBranchLevelSum a χ T
  | j, .fork T U =>
      finiteCascadeBranchLevelSum a χ T+finiteCascadeBranchLevelSum a χ U+a j*χ j

theorem finiteCascadeLevelChargeSum_eq_edges_branches (a : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (χ : ℕ → ℝ) :
    finiteCascadeLevelChargeSum a s T χ=
      finiteCascadeEdgeLevelSum a χ T+finiteCascadeBranchLevelSum a χ T+(a j-s)*χ j := by
  induction T generalizing s with
  | leaf => simp [finiteCascadeLevelChargeSum, finiteCascadeVertexCharges,
      finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient]; ring
  | @advance j T ih =>
    have hi:=ih (a j)
    simp only [finiteCascadeLevelChargeSum, finiteCascadeVertexCharges,
      finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
      List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      FiniteCascadeRecordVertex.depth] at hi ⊢
    change _=finiteCascadeEdgeLevelSum a χ T+(a j-a (j+1))*χ (j+1)+
      finiteCascadeBranchLevelSum a χ T+(a (j+1)-s)*χ (j+1)
    linarith only [hi]
  | @fork j T U ihT ihU =>
    have hT:=ihT (a j)
    have hU:=ihU (a j)
    simp only [finiteCascadeLevelChargeSum, finiteCascadeVertexCharges,
      finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
      List.map_cons, List.sum_cons, List.map_append, List.sum_append,
      List.map_map, Function.comp_def, FiniteCascadeRecordVertex.depth] at hT hU ⊢
    change _=finiteCascadeEdgeLevelSum a χ T+finiteCascadeEdgeLevelSum a χ U+
      (finiteCascadeBranchLevelSum a χ T+finiteCascadeBranchLevelSum a χ U+a j*χ j)+
        (a j-s)*χ j
    linarith only [hT,hU]

def finiteCascadeScalarLevelSum (a χ : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1-a 0)*χ 0
  | j+1 => finiteCascadeScalarLevelSum a χ j+(a j-a (j+1))*χ (j+1)

theorem finiteCascadeScalarLevelSum_nonneg (a χ : ℕ → ℝ)
    (ha : Antitone a) (h0 : a 0≤1) (hχ : ∀j, 0≤χ j) (j : ℕ) :
    0≤finiteCascadeScalarLevelSum a χ j := by
  induction j with
  | zero => exact mul_nonneg (sub_nonneg.mpr h0) (hχ 0)
  | succ j ih => exact add_nonneg ih (mul_nonneg
      (sub_nonneg.mpr (ha (Nat.le_succ j))) (hχ (j+1)))

theorem finiteCascadeEdgeLevelSum_le (a χ : ℕ → ℝ)
    (ha : Antitone a) (h0 : a 0≤1) (hχ : ∀j, 0≤χ j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    finiteCascadeEdgeLevelSum a χ T≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*finiteCascadeScalarLevelSum a χ j := by
  induction T with
  | leaf => simp [finiteCascadeEdgeLevelSum, finiteCascadeScalarLevelSum,
      asGenealogy, FiniteCascadeGenealogy.leafCount]
  | @advance j T ih =>
    have hL : 1≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ) := by
      exact_mod_cast FiniteCascadeGenealogy.leafCount_pos (asGenealogy T)
    have hδ : 0≤(a j-a (j+1))*χ (j+1) :=
      mul_nonneg (sub_nonneg.mpr (ha (Nat.le_succ j))) (hχ (j+1))
    change finiteCascadeEdgeLevelSum a χ T+(a j-a (j+1))*χ (j+1)≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        (finiteCascadeScalarLevelSum a χ j+(a j-a (j+1))*χ (j+1))
    nlinarith only [ih, mul_le_mul_of_nonneg_right hL hδ]
  | fork T U ihT ihU =>
    change finiteCascadeEdgeLevelSum a χ T+finiteCascadeEdgeLevelSum a χ U≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T)+
        FiniteCascadeGenealogy.leafCount (asGenealogy U):ℕ):ℝ)*_
    rw [Nat.cast_add, add_mul]
    exact add_le_add ihT ihU

def finiteCascadeStartingMass (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 => a j

/-- The free scalar edge measure starts at the actual right mass at the
root. Its root atom has weight `startingMass-s`, rather than the full mass. -/
def finiteCascadeFreeScalarLevelSum (a χ : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, s => (1-s)*χ 0
  | j+1, s => finiteCascadeScalarLevelSum a χ j+(a j-s)*χ (j+1)

@[reducible] def finiteCascadeUnweightedBranchSum (χ : ℕ → ℝ) :
    {j : ℕ} → FiniteTerminalGenealogy j → ℝ
  | _, .leaf => 0
  | _, .advance T => finiteCascadeUnweightedBranchSum χ T
  | j, .fork T U =>
      finiteCascadeUnweightedBranchSum χ T+finiteCascadeUnweightedBranchSum χ U+χ j

theorem finiteCascadeFreeScalarLevelSum_at_mass (a χ : ℕ → ℝ) (j : ℕ) :
    finiteCascadeFreeScalarLevelSum a χ j (a j)=finiteCascadeScalarLevelSum a χ j := by
  cases j <;> rfl

theorem finiteCascadeUnweightedBranchSum_nonneg (χ : ℕ → ℝ)
    (hχ : ∀j, 0≤χ j) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    0≤finiteCascadeUnweightedBranchSum χ T := by
  induction T with
  | leaf => exact le_rfl
  | advance T ih => exact ih
  | fork T U ihT ihU => exact add_nonneg (add_nonneg ihT ihU) (hχ _)

theorem finiteCascadeLevelChargeSum_advance (a : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (χ : ℕ → ℝ) :
    finiteCascadeLevelChargeSum a s (.advance T) χ=
      finiteCascadeLevelChargeSum a (a j) T χ+(a j-s)*χ (j+1) := by
  simp only [finiteCascadeLevelChargeSum, finiteCascadeVertexCharges,
    finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
    List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    FiniteCascadeRecordVertex.depth]
  ring

theorem finiteCascadeLevelChargeSum_fork (a : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T U : FiniteTerminalGenealogy j) (χ : ℕ → ℝ) :
    finiteCascadeLevelChargeSum a s (.fork T U) χ=
      finiteCascadeLevelChargeSum a s T χ+finiteCascadeLevelChargeSum a s U χ+s*χ j := by
  simp only [finiteCascadeLevelChargeSum, finiteCascadeVertexCharges,
    finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
    List.map_cons, List.sum_cons, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, FiniteCascadeRecordVertex.depth]
  ring

/-- Actual charge domination by the free scalar edge increments and
inherited branch marks. The coefficient is the true number of leaves. -/
theorem finiteCascadeLevelChargeSum_le_free_and_branches (a χ : ℕ → ℝ)
    (ha : Antitone a) (h0 : a 0≤1) (hχ : ∀j, 0≤χ j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (hs : s≤finiteCascadeStartingMass a j) :
    finiteCascadeLevelChargeSum a s T χ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        (finiteCascadeFreeScalarLevelSum a χ j s+finiteCascadeUnweightedBranchSum χ T) := by
  induction T generalizing s with
  | leaf => simp [finiteCascadeLevelChargeSum, finiteCascadeVertexCharges,
      finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
      finiteCascadeFreeScalarLevelSum, asGenealogy, FiniteCascadeGenealogy.leafCount]
  | @advance j T ih =>
    have hbase : a j≤finiteCascadeStartingMass a j := by
      cases j with
      | zero => exact h0
      | succ j => exact ha (Nat.le_succ j)
    have hi:=ih (a j) hbase
    rw [finiteCascadeFreeScalarLevelSum_at_mass] at hi
    have hL : 1≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ) := by
      exact_mod_cast FiniteCascadeGenealogy.leafCount_pos (asGenealogy T)
    have hδ : 0≤(a j-s)*χ (j+1) := mul_nonneg (sub_nonneg.mpr hs) (hχ _)
    rw [finiteCascadeLevelChargeSum_advance]
    change _≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
      (finiteCascadeScalarLevelSum a χ j+(a j-s)*χ (j+1)+finiteCascadeUnweightedBranchSum χ T)
    nlinarith only [hi, mul_le_mul_of_nonneg_right hL hδ]
  | @fork j T U ihT ihU =>
    have hT:=ihT s hs
    have hU:=ihU s hs
    have hs1 : s≤1 := by
      apply hs.trans
      cases j with
      | zero => exact le_rfl
      | succ j => exact (ha (Nat.zero_le j)).trans h0
    have hBT:=finiteCascadeUnweightedBranchSum_nonneg χ hχ T
    have hBU:=finiteCascadeUnweightedBranchSum_nonneg χ hχ U
    have hLT : 0≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ) := by positivity
    have hLU : 0≤(FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ) := by positivity
    have hL : 1≤((FiniteCascadeGenealogy.leafCount (asGenealogy T)+
        FiniteCascadeGenealogy.leafCount (asGenealogy U):ℕ):ℝ) := by
      exact_mod_cast FiniteCascadeGenealogy.leafCount_pos (asGenealogy (.fork T U))
    have hc : s*χ j≤((FiniteCascadeGenealogy.leafCount (asGenealogy T)+
        FiniteCascadeGenealogy.leafCount (asGenealogy U):ℕ):ℝ)*χ j :=
      mul_le_mul_of_nonneg_right (hs1.trans hL) (hχ j)
    rw [finiteCascadeLevelChargeSum_fork]
    change _≤((FiniteCascadeGenealogy.leafCount (asGenealogy T)+
        FiniteCascadeGenealogy.leafCount (asGenealogy U):ℕ):ℝ)*
      (finiteCascadeFreeScalarLevelSum a χ j s+
        (finiteCascadeUnweightedBranchSum χ T+finiteCascadeUnweightedBranchSum χ U+χ j))
    rw [Nat.cast_add] at hc ⊢
    nlinarith only [hT,hU,hc,mul_nonneg hLT hBU,mul_nonneg hLU hBT]

end FourPapersCommon
