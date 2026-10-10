module
public import QuantitativeFollowup.ExponentialSmoothComposition
public import FourPapersCommon.ExponentialBoundedLinear

@[expose] public section

/-! A literal scalar log-cosh terminal potential on deterministic Gaussian
amplitudes and fixed independent noise coordinates. Only amplitudes are
restricted; field and noise coordinates remain unbounded. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon
set_option maxHeartbeats 2000000
variable {n : ℕ}

abbrev ScalarAmplitudeState (n : ℕ) := QuantitativePaper.Field n × (QuantitativePaper.Field n × ℝ)

def scalarAmplitudeDomain (n : ℕ) (R : ℝ) : Set (ScalarAmplitudeState n) :=
  {w | ‖w.1‖ < R}

def scalarAmplitudeNoiseShift (n : ℕ) : QuantitativePaper.Field n →L[ℝ] ScalarAmplitudeState n :=
  (0 : QuantitativePaper.Field n →L[ℝ] QuantitativePaper.Field n).prod
    ((ContinuousLinearMap.id ℝ (QuantitativePaper.Field n)).prod 0)

def scalarAmplitudeCoordinateProjection (i : Fin n) : QuantitativePaper.Field n →L[ℝ] QuantitativePaper.Field n :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n => ℝ) i).smulRight (EuclideanSpace.single i 1)

def scalarAmplitudeCellShift (i : Fin n) : QuantitativePaper.Field n →L[ℝ] ScalarAmplitudeState n :=
  (scalarAmplitudeNoiseShift n).comp (scalarAmplitudeCoordinateProjection i)

def scalarAmplitudeField (w : ScalarAmplitudeState n) : ℝ := w.2.2+⟪w.1,w.2.1⟫_ℝ

def scalarAmplitudeTerminal (w : ScalarAmplitudeState n) : ℝ :=
  Real.log (Real.cosh (scalarAmplitudeField w))

@[simp] theorem scalarAmplitudeNoiseShift_apply (z : QuantitativePaper.Field n) :
    scalarAmplitudeNoiseShift n z=(0,z,0) := rfl

@[simp] theorem scalarAmplitudeCoordinateProjection_apply (i : Fin n) (z : QuantitativePaper.Field n) :
    scalarAmplitudeCoordinateProjection i z=EuclideanSpace.single i (z i) := by
  ext j
  simp [scalarAmplitudeCoordinateProjection, PiLp.proj_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.single_apply]

theorem norm_scalarAmplitudeCoordinateProjection_le (i : Fin n) (z : QuantitativePaper.Field n) :
    ‖scalarAmplitudeCoordinateProjection i z‖ ≤ ‖z‖ := by
  rw [scalarAmplitudeCoordinateProjection_apply, PiLp.norm_single]
  exact PiLp.norm_apply_le z i

theorem scalarAmplitudeDomain_open (R : ℝ) : IsOpen (scalarAmplitudeDomain n R) :=
  isOpen_lt (continuous_norm.comp continuous_fst) continuous_const

theorem scalarAmplitudeDomain_noise_invariant (R : ℝ) (w : ScalarAmplitudeState n)
    (hw : w ∈ scalarAmplitudeDomain n R) (z : QuantitativePaper.Field n) :
    w+scalarAmplitudeNoiseShift n z ∈ scalarAmplitudeDomain n R := by
  simpa only [scalarAmplitudeDomain, Set.mem_ofPred_eq, scalarAmplitudeNoiseShift_apply,
    Prod.fst_add, add_zero] using hw

theorem scalarAmplitudeDomain_cell_invariant (R : ℝ) (w : ScalarAmplitudeState n)
    (hw : w ∈ scalarAmplitudeDomain n R) (i : Fin n) (z : QuantitativePaper.Field n) :
    w+scalarAmplitudeCellShift i z ∈ scalarAmplitudeDomain n R :=
  scalarAmplitudeDomain_noise_invariant R w hw (scalarAmplitudeCoordinateProjection i z)

theorem scalarAmplitudeField_noise_shift (w : ScalarAmplitudeState n) (z : QuantitativePaper.Field n) :
    scalarAmplitudeField (w+scalarAmplitudeNoiseShift n z)=scalarAmplitudeField w+⟪w.1,z⟫_ℝ := by
  simp [scalarAmplitudeField, scalarAmplitudeNoiseShift_apply, inner_add_right, add_assoc]

theorem scalarAmplitudeField_bound (R : ℝ) (hR : 0 ≤ R) (w : ScalarAmplitudeState n)
    (hw : w ∈ scalarAmplitudeDomain n R) : |scalarAmplitudeField w| ≤ (1+R)*‖w‖ := by
  have ha : ‖w.1‖ ≤ R := hw.le
  have hz : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have hx : |w.2.2| ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using ((norm_snd_le w.2).trans (norm_snd_le w))
  dsimp only [scalarAmplitudeField]
  apply (abs_add_le _ _).trans
  have hi := (abs_real_inner_le_norm w.1 w.2.1).trans
    (mul_le_mul ha hz (norm_nonneg _) hR)
  nlinarith only [hx,hi]

theorem exponentialSmoothOn_scalarAmplitudeField (R : ℝ) :
    ExponentialSmoothOn (scalarAmplitudeField (n:=n)) (scalarAmplitudeDomain n R) := by
  have ha := exponentialSmoothOn_linear
    (ContinuousLinearMap.fst ℝ (QuantitativePaper.Field n) (QuantitativePaper.Field n × ℝ)) (scalarAmplitudeDomain n R)
  have hz := exponentialSmoothOn_linear
    ((ContinuousLinearMap.fst ℝ (QuantitativePaper.Field n) ℝ).comp
      (ContinuousLinearMap.snd ℝ (QuantitativePaper.Field n) (QuantitativePaper.Field n × ℝ))) (scalarAmplitudeDomain n R)
  have hx := exponentialSmoothOn_linear
    ((ContinuousLinearMap.snd ℝ (QuantitativePaper.Field n) ℝ).comp
      (ContinuousLinearMap.snd ℝ (QuantitativePaper.Field n) (QuantitativePaper.Field n × ℝ))) (scalarAmplitudeDomain n R)
  exact hx.add (ha.bilinear hz (innerSL ℝ))

theorem boundedPositiveJets_scalarLogCosh :
    BoundedPositiveJets (fun x : ℝ => Real.log (Real.cosh x)) := by
  simpa only [Paper.parisiPotential_terminal] using boundedPositiveJets_scalarPotential
    1 (Paper.diracOverlap 0 ⟨le_rfl,zero_le_one⟩) 1 ⟨zero_le_one,le_rfl⟩

theorem exponentialSmoothOn_scalarAmplitudeTerminal (R : ℝ) (hR : 0 ≤ R) :
    ExponentialSmoothOn (scalarAmplitudeTerminal (n:=n)) (scalarAmplitudeDomain n R) := by
  apply exponentialSmoothOn_comp_boundedPositiveJets
    (fun x : ℝ => Real.log (Real.cosh x)) boundedPositiveJets_scalarLogCosh
    0 1 le_rfl zero_le_one
    (fun x => by simpa only [Real.norm_eq_abs,zero_add,one_mul] using Paper.norm_logcosh_le_abs x)
    (scalarAmplitudeField (n:=n)) (scalarAmplitudeDomain n R)
    (exponentialSmoothOn_scalarAmplitudeField R) 0 (1+R) le_rfl (by positivity)
    (fun w hw => by simpa only [zero_add] using scalarAmplitudeField_bound R hR w hw)

theorem scalarAmplitudeTerminal_bound (R : ℝ) (hR : 0 ≤ R) (w : ScalarAmplitudeState n)
    (hw : w ∈ scalarAmplitudeDomain n R) : |scalarAmplitudeTerminal w| ≤ (1+R)*‖w‖ := by
  have hh : |scalarAmplitudeTerminal w| ≤ |scalarAmplitudeField w| := by
    simpa only [scalarAmplitudeTerminal, Real.norm_eq_abs] using Paper.norm_logcosh_le_abs (scalarAmplitudeField w)
  exact hh.trans (scalarAmplitudeField_bound R hR w hw)

theorem scalarAmplitudeTerminal_noise_lipschitz (R : ℝ≥0) (w : ScalarAmplitudeState n)
    (hw : w ∈ scalarAmplitudeDomain n R) (z : QuantitativePaper.Field n) :
    |scalarAmplitudeTerminal (w+scalarAmplitudeNoiseShift n z)-scalarAmplitudeTerminal w| ≤ R*‖z‖ := by
  have hh := Paper.lipschitzWith_logcosh.dist_le_mul
    (scalarAmplitudeField (w+scalarAmplitudeNoiseShift n z)) (scalarAmplitudeField w)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, scalarAmplitudeField_noise_shift,
    add_sub_cancel_left] at hh
  unfold scalarAmplitudeTerminal
  rw [scalarAmplitudeField_noise_shift]
  apply hh.trans
  apply (abs_real_inner_le_norm w.1 z).trans
  exact mul_le_mul_of_nonneg_right hw.le (norm_nonneg z)

end QuantitativeFollowup
