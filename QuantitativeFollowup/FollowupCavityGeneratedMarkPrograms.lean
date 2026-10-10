module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkAttachments
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! Explicit normalized mark histories. These constructors are the
measure operations in an absolute streaming term: a fresh restricted
mark, a singleton atom, an inherited mark, attenuation, and finite
addition. Their numerical budgets depend only on structural counts. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
set_option maxHeartbeats 900000

abbrev CavityGeneratedHistory (Q : Type*) (m : ℕ) := Fin m → Q

def cavityGeneratedHistoryMarks {m : ℕ} :
    Fin m → CavityGeneratedHistory Q m → Q := fun i h => h i

theorem cavityGeneratedHistoryMarks_measurable {m : ℕ} (i : Fin m) :
    Measurable (cavityGeneratedHistoryMarks (Q := Q) i) := measurable_pi_apply i

def cavityGeneratedHistoryAppend {m : ℕ} (z : CavityGeneratedHistory Q m × Q) :
    CavityGeneratedHistory Q (m + 1) := Fin.snoc z.1 z.2

theorem cavityGeneratedHistoryAppend_measurable {m : ℕ} :
    Measurable (cavityGeneratedHistoryAppend (Q := Q) (m := m)) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [cavityGeneratedHistoryAppend, Fin.snoc_last] using measurable_snd
  | cast i => simpa only [cavityGeneratedHistoryAppend, Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

inductive CavityGeneratedMarkProgram (Q : Type*) [MeasurableSpace Q] : ℕ → Type _
  | initial : CavityGeneratedMarkProgram Q 1
  | fresh {m : ℕ} (previous : CavityGeneratedMarkProgram Q m)
      (orderSet : Set (CavityGeneratedHistory Q m × Q)) : CavityGeneratedMarkProgram Q (m + 1)
  | atom {m : ℕ} (previous : CavityGeneratedMarkProgram Q m)
      (q : CavityGeneratedHistory Q m → Q) (hq : Measurable q) :
      CavityGeneratedMarkProgram Q (m + 1)
  | inherited {m : ℕ} (previous : CavityGeneratedMarkProgram Q m) (i : Fin m)
      (multiplicity : ℕ) (weight : CavityGeneratedHistory Q m → ℝ≥0∞)
      (hweight : ∀h, weight h ≤ multiplicity) : CavityGeneratedMarkProgram Q (m + 1)
  | attenuate {m : ℕ} (previous : CavityGeneratedMarkProgram Q m)
      (weight : CavityGeneratedHistory Q m → ℝ≥0∞) (hweight : ∀h, weight h ≤ 1) :
      CavityGeneratedMarkProgram Q m
  | restrict {m : ℕ} (previous : CavityGeneratedMarkProgram Q m)
      (orderSet : Set (CavityGeneratedHistory Q m)) : CavityGeneratedMarkProgram Q m
  | add {m : ℕ} (left right : CavityGeneratedMarkProgram Q m) : CavityGeneratedMarkProgram Q m

namespace CavityGeneratedMarkProgram

def budget : {m : ℕ} → CavityGeneratedMarkProgram Q m → ℕ
  | _, .initial => 1
  | _, .fresh P _ => P.budget
  | _, .atom P _ _ => P.budget
  | _, .inherited P _ k _ _ => k * P.budget
  | _, .attenuate P _ _ => P.budget
  | _, .restrict P _ => P.budget
  | _, .add P R => P.budget + R.budget

def measure (ν : Measure Q) : {m : ℕ} →
    CavityGeneratedMarkProgram Q m → Measure (CavityGeneratedHistory Q m)
  | _, .initial => ν.map (fun q => fun _ : Fin 1 => q)
  | _, .fresh P E => (((P.measure ν).prod ν).restrict E).map cavityGeneratedHistoryAppend
  | _, .atom P q _ =>
      ((P.measure ν).withDensity (fun h => ν {q h})).map (fun h => Fin.snoc h (q h))
  | _, .inherited P i _ w _ =>
      ((P.measure ν).withDensity w).map (fun h => Fin.snoc h (h i))
  | _, .attenuate P w _ => (P.measure ν).withDensity w
  | _, .restrict P E => (P.measure ν).restrict E
  | _, .add P R => P.measure ν + R.measure ν

end CavityGeneratedMarkProgram

end QuantitativeFollowup
