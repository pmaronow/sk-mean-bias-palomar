module
public import FourPapersCommon.FiniteCascadeTreeDensity

@[expose] public section

/-! The literal terminal-minus-vertex form of the finite genealogy density.
Its vertex coefficients are nonnegative for a genuine decreasing reverse
mass schedule, and their total is exactly the leaf count minus the root tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

@[reducible] def finiteCascadeTreeRootCoefficient (a : ℕ → ℝ) :
    {j : ℕ} → FiniteTerminalGenealogy j → ℝ
  | _, .leaf => 1
  | _, @FiniteTerminalGenealogy.advance j _ => a j
  | _, .fork T U => finiteCascadeTreeRootCoefficient a T + finiteCascadeTreeRootCoefficient a U

@[reducible] def finiteCascadeTreeTerminalEnergy (V : S → ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → FiniteStateField S →
      Records (FiniteStateField S) S T → ℝ
  | _, .leaf => fun H σ => H σ + V σ
  | _, .advance T => fun _ z => finiteCascadeTreeTerminalEnergy V T z.1 z.2
  | _, .fork T U => fun H z =>
      finiteCascadeTreeTerminalEnergy V T H z.1 + finiteCascadeTreeTerminalEnergy V U H z.2

@[reducible] def finiteCascadeTreeInteriorCharges (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      Records (FiniteStateField S) S T → List (ℝ × ℝ)
  | _, .leaf => fun _ => []
  | _, @FiniteTerminalGenealogy.advance j T => fun z =>
      (finiteCascadeTreeRootCoefficient a T - a j,
        finiteStateGaussianTerminalCascade V a L j z.1) ::
          finiteCascadeTreeInteriorCharges V a L T z.2
  | _, .fork T U => fun z =>
      finiteCascadeTreeInteriorCharges V a L T z.1 ++ finiteCascadeTreeInteriorCharges V a L U z.2

def finiteCascadeTreeCharges (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) : List (ℝ × ℝ) :=
  (finiteCascadeTreeRootCoefficient a T - s,
    finiteStateGaussianTerminalCascade V a L j H) :: finiteCascadeTreeInteriorCharges V a L T z

theorem finiteCascadeTreeRootCoefficient_ge (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hanti : Antitone a) (h0 : a 0 ≤ 1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    a j ≤ finiteCascadeTreeRootCoefficient a T := by
  induction T with
  | leaf => exact h0
  | @advance j T ih => exact hanti (Nat.le_succ j)
  | @fork j T U ihT ihU =>
      change a j ≤ finiteCascadeTreeRootCoefficient a T + finiteCascadeTreeRootCoefficient a U
      linarith [ha j]

theorem finiteCascadeTreeInteriorCharges_nonneg (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    ∀ c ∈ finiteCascadeTreeInteriorCharges V a L T z, 0 ≤ c.1 := by
  induction T with
  | leaf => simp [finiteCascadeTreeInteriorCharges]
  | @advance j T ih =>
      intro c hc
      rcases List.mem_cons.mp hc with h | h
      · subst c
        exact sub_nonneg.mpr (finiteCascadeTreeRootCoefficient_ge a ha hanti h0 T)
      · exact ih z.2 c h
  | fork T U ihT ihU =>
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact ihT z.1 c h
      · exact ihU z.2 c h

theorem finiteCascadeTreeCharges_nonneg (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s ≤ a j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    ∀ c ∈ finiteCascadeTreeCharges V a L s T H z, 0 ≤ c.1 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst c
    exact sub_nonneg.mpr (hs.trans (finiteCascadeTreeRootCoefficient_ge a ha hanti h0 T))
  · exact finiteCascadeTreeInteriorCharges_nonneg V a ha hanti h0 L T z c h

theorem finiteCascadeTreeInteriorCharges_sum (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeRootCoefficient a T +
      ((finiteCascadeTreeInteriorCharges V a L T z).map Prod.fst).sum =
        (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) := by
  induction T with
  | leaf => simp [finiteCascadeTreeRootCoefficient,finiteCascadeTreeInteriorCharges,
      asGenealogy,FiniteCascadeGenealogy.leafCount]
  | @advance j T ih =>
      simp only [finiteCascadeTreeRootCoefficient,finiteCascadeTreeInteriorCharges,List.map_cons,
        List.sum_cons,asGenealogy,FiniteCascadeGenealogy.leafCount]
      linarith [ih z.2]
  | fork T U ihT ihU =>
      simp only [finiteCascadeTreeRootCoefficient,finiteCascadeTreeInteriorCharges,List.map_append,
        List.sum_append,asGenealogy,FiniteCascadeGenealogy.leafCount,Nat.cast_add]
      linarith [ihT z.1,ihU z.2]

theorem finiteCascadeTreeCharges_sum (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    ((finiteCascadeTreeCharges V a L s T H z).map Prod.fst).sum =
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) - s := by
  simp only [finiteCascadeTreeCharges,List.map_cons,List.sum_cons]
  linarith [finiteCascadeTreeInteriorCharges_sum V a L T z]

theorem finiteCascadeTreeLogDensity_eq_terminal_sub_charges (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeLogDensity V a L T H z = finiteCascadeTreeTerminalEnergy V T H z -
      finiteCascadeTreeRootCoefficient a T * finiteStateGaussianTerminalCascade V a L j H -
        ((finiteCascadeTreeInteriorCharges V a L T z).map (fun c => c.1 * c.2)).sum := by
  induction T generalizing H with
  | leaf => simp [finiteCascadeTreeLogDensity,finiteCascadeTreeTerminalEnergy,
      finiteCascadeTreeRootCoefficient,finiteCascadeTreeInteriorCharges,
      finiteStateGaussianTerminalCascade,finiteStateGaussianCascade]
  | @advance j T ih =>
      simp only [finiteCascadeTreeLogDensity,finiteCascadeTreeTerminalEnergy,
        finiteCascadeTreeRootCoefficient,finiteCascadeTreeInteriorCharges,List.map_cons,List.sum_cons]
      rw [ih z.1 z.2]
      ring
  | fork T U ihT ihU =>
      simp only [finiteCascadeTreeLogDensity,finiteCascadeTreeTerminalEnergy,
        finiteCascadeTreeRootCoefficient,finiteCascadeTreeInteriorCharges,List.map_append,List.sum_append]
      rw [ihT H z.1, ihU H z.2]
      ring

theorem finiteCascadeTreeLogDensity_add_root_eq (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    s * finiteStateGaussianTerminalCascade V a L j H + finiteCascadeTreeLogDensity V a L T H z =
      finiteCascadeTreeTerminalEnergy V T H z -
        ((finiteCascadeTreeCharges V a L s T H z).map (fun c => c.1 * c.2)).sum := by
  rw [finiteCascadeTreeLogDensity_eq_terminal_sub_charges]
  simp only [finiteCascadeTreeCharges,List.map_cons,List.sum_cons]
  ring

end FourPapersCommon
