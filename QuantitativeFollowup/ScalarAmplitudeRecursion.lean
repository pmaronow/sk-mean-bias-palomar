module
public import QuantitativeFollowup.ScalarAmplitudeTerminal
public import Paper.ParisiSchemeMeasure

@[expose] public section

/-! Actual finite Gaussian Cole--Hopf recursion at fixed masses and variable
amplitudes. All noise coordinates are fixed standard Gaussian coordinates;
zero amplitudes therefore cause no singular parameter derivative. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarAmplitudeCell (k j : ℕ) : Fin (k+2) := ⟨k+1-j, by omega⟩

def scalarAmplitudeRecursion (s : RSBScheme k) : ℕ → ScalarAmplitudeState (k+2) → ℝ
  | 0 => scalarAmplitudeTerminal
  | j+1 => gaussianShiftColeHopf (scalarAmplitudeCellShift (scalarAmplitudeCell k j))
      (s.m (k+1-j)) (scalarAmplitudeRecursion s j)

theorem scalarAmplitudeRecursion_regular (s : RSBScheme k) (R : ℝ≥0) (j : ℕ) :
    ExponentialSmoothOn (scalarAmplitudeRecursion s j) (scalarAmplitudeDomain (k+2) R) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ scalarAmplitudeDomain (k+2) R,
      |scalarAmplitudeRecursion s j w| ≤ B+(1+(R:ℝ))*‖w‖) ∧
    (∀ w ∈ scalarAmplitudeDomain (k+2) R, ∀ z,
      |scalarAmplitudeRecursion s j (w+scalarAmplitudeNoiseShift (k+2) z)-
        scalarAmplitudeRecursion s j w| ≤ R*‖z‖) := by
  induction j with
  | zero =>
    simp only [scalarAmplitudeRecursion]
    exact ⟨exponentialSmoothOn_scalarAmplitudeTerminal R R.coe_nonneg,
      ⟨0, le_rfl, fun w hw => by simpa only [zero_add] using scalarAmplitudeTerminal_bound R R.coe_nonneg w hw⟩,
      scalarAmplitudeTerminal_noise_lipschitz R⟩
  | succ j ih =>
    obtain ⟨hs, ⟨B,hB,hv⟩, hnoise⟩ := ih
    let i := scalarAmplitudeCell k j
    have hcell (w : ScalarAmplitudeState (k+2)) (hw : w ∈ scalarAmplitudeDomain (k+2) R)
        (z : QuantitativePaper.Field (k+2)) :
        |scalarAmplitudeRecursion s j (w+scalarAmplitudeCellShift i z)-scalarAmplitudeRecursion s j w| ≤ R*‖z‖ :=
      (hnoise w hw (scalarAmplitudeCoordinateProjection i z)).trans
        (mul_le_mul_of_nonneg_left (norm_scalarAmplitudeCoordinateProjection_le i z) R.coe_nonneg)
    have hshift := fun w hw z => scalarAmplitudeDomain_cell_invariant (R:ℝ) w hw i z
    have hsm := exponentialSmoothOn_gaussianShiftColeHopf (scalarAmplitudeRecursion s j)
      (scalarAmplitudeDomain (k+2) R) (scalarAmplitudeDomain_open R) hs
      (scalarAmplitudeCellShift i) hshift B (1+(R:ℝ)) (by positivity) hv R hcell (s.m (k+1-j))
    obtain ⟨C,hC,hbound⟩ := gaussianShiftColeHopf_value_barrier (scalarAmplitudeRecursion s j)
      (scalarAmplitudeDomain (k+2) R) (scalarAmplitudeCellShift i) hshift R hcell (s.m (k+1-j))
    refine ⟨hsm, ⟨B+C, add_nonneg hB hC, ?_⟩, ?_⟩
    · intro w hw
      change |gaussianShiftColeHopf _ _ _ w| ≤ _
      linarith [hbound w hw, hv w hw]
    · intro w hw z
      exact gaussianShiftColeHopf_directional_lipschitz (scalarAmplitudeRecursion s j)
        (scalarAmplitudeDomain (k+2) R) (scalarAmplitudeCellShift i) (scalarAmplitudeNoiseShift (k+2))
        hshift (scalarAmplitudeDomain_noise_invariant R) R R hcell hnoise (s.m (k+1-j))
        (s.m_nonneg (Nat.sub_le _ _)) w hw z

theorem exponentialSmoothOn_scalarAmplitudeRecursion (s : RSBScheme k) (R : ℝ≥0) (j : ℕ) :
    ExponentialSmoothOn (scalarAmplitudeRecursion s j) (scalarAmplitudeDomain (k+2) R) :=
  (scalarAmplitudeRecursion_regular s R j).1

theorem scalarAmplitudeRecursion_value_bound (s : RSBScheme k) (R : ℝ≥0) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ scalarAmplitudeDomain (k+2) R,
      |scalarAmplitudeRecursion s j w| ≤ B+(1+(R:ℝ))*‖w‖ :=
  (scalarAmplitudeRecursion_regular s R j).2.1

end QuantitativeFollowup
