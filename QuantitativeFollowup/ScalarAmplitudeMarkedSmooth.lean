module
public import QuantitativeFollowup.ScalarAmplitudeNodes
public import FourPapersCommon.ExponentialPolynomial

@[expose] public section

/-! Genuine C∞ regularity of the marked finite diffusion moment in Gaussian
amplitudes. Gaussian differentiation is justified by actual all-order
exponential envelopes on an unbounded noise domain. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal BigOperators
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem exponentialSmoothOn_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} (S : Finset I) (f : I → E → ℝ) (U : Set E)
    (hf : ∀ i ∈ S, ExponentialSmoothOn (f i) U) :
    ExponentialSmoothOn (fun x => ∑ i ∈ S, f i x) U := by
  classical
  induction S using Finset.induction with
  | empty => simpa using ExponentialSmoothOn.const (0:ℝ) U
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i S)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def scalarAmplitudeMarkedExponent (s : RSBScheme k) (e : Bool) (w : ScalarAmplitudeState (k+2)) : ℝ :=
  spinSign e*scalarAmplitudeField w-
    ∑ i : Fin (k+1), (s.m (i+1)-s.m i)*scalarAmplitudeNodePotential s (i+1) w

def scalarAmplitudeMarkedIntegrand (s : RSBScheme k) (p : ℕ) (e : Bool)
    (w : ScalarAmplitudeState (k+2)) : ℝ :=
  Real.exp (scalarAmplitudeMarkedExponent s e w)*(scalarAmplitudeNodeGradient s p w)^2

def scalarAmplitudeGamma (s : RSBScheme k) (p : ℕ) (w : ScalarAmplitudeState (k+2)) : ℝ :=
  (1/2:ℝ)*∑ e : Bool, gaussianShiftAverage (scalarAmplitudeNoiseShift (k+2))
    (scalarAmplitudeMarkedIntegrand s p e) w

theorem exponentialSmoothOn_scalarAmplitudeMarkedExponent (s : RSBScheme k) (R : ℝ≥0) (e : Bool) :
    ExponentialSmoothOn (scalarAmplitudeMarkedExponent s e) (scalarAmplitudeDomain (k+2) R) := by
  have hleft := (exponentialSmoothOn_scalarAmplitudeField (n:=k+2) R).compCLM
    ((spinSign e) • ContinuousLinearMap.id ℝ ℝ)
  have hright := exponentialSmoothOn_sum (Finset.univ : Finset (Fin (k+1)))
    (fun i w => (s.m (i+1)-s.m i)*scalarAmplitudeNodePotential s (i+1) w)
    (scalarAmplitudeDomain (k+2) R) (fun i _ => by
      simpa only [Function.comp_def,smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul] using
        (exponentialSmoothOn_scalarAmplitudeNodePotential s R (i+1)).compCLM
          ((s.m (i+1)-s.m i) • ContinuousLinearMap.id ℝ ℝ))
  change ExponentialSmoothOn (fun w => spinSign e*scalarAmplitudeField w-
    ∑ i : Fin (k+1), (s.m (i+1)-s.m i)*scalarAmplitudeNodePotential s (i+1) w) _
  simpa only [Function.comp_def,smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul] using hleft.sub hright

theorem scalarAmplitudeMarkedExponent_value_bound (s : RSBScheme k) (R : ℝ≥0) (e : Bool) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ w ∈ scalarAmplitudeDomain (k+2) R,
      |scalarAmplitudeMarkedExponent s e w| ≤ B+L*‖w‖ := by
  classical
  choose B L hB hL hb using fun i : Fin (k+1) => scalarAmplitudeNodePotential_value_bound s R (i+1)
  let c := fun i : Fin (k+1) => |s.m (i+1)-s.m i|
  refine ⟨∑ i,c i*B i,1+(R:ℝ)+∑ i,c i*L i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hB i)),by
      have hh : 0 ≤ ∑ i : Fin (k+1), c i*L i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg (s.m (i+1)-s.m i)) (hL i))
      linarith [R.coe_nonneg], ?_⟩
  intro w hw
  have hsum : |∑ i : Fin (k+1), (s.m (i+1)-s.m i)*scalarAmplitudeNodePotential s (i+1) w| ≤
      ∑ i, c i*(B i+L i*‖w‖) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb i w hw) (abs_nonneg _)
  have hterm : |spinSign e*scalarAmplitudeField w| ≤ (1+(R:ℝ))*‖w‖ := by
    simpa only [abs_mul,abs_spinSign,one_mul] using scalarAmplitudeField_bound R R.coe_nonneg w hw
  change |spinSign e*scalarAmplitudeField w-∑ i : Fin (k+1), (s.m (i+1)-s.m i)*scalarAmplitudeNodePotential s (i+1) w| ≤ _
  have hsub := norm_sub_le (spinSign e*scalarAmplitudeField w)
    (∑ i : Fin (k+1), (s.m (i+1)-s.m i)*scalarAmplitudeNodePotential s (i+1) w)
  simp only [Real.norm_eq_abs] at hsub
  apply (hsub.trans (add_le_add hterm hsum)).trans_eq
  dsimp only [c]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  simp only [←mul_assoc,←Finset.sum_mul]
  ring

theorem exponentialSmoothOn_scalarAmplitudeMarkedIntegrand (s : RSBScheme k) (R : ℝ≥0)
    (p : ℕ) (e : Bool) :
    ExponentialSmoothOn (scalarAmplitudeMarkedIntegrand s p e) (scalarAmplitudeDomain (k+2) R) := by
  obtain ⟨B,L,hB,hL,hv⟩ := scalarAmplitudeMarkedExponent_value_bound s R e
  have hexp := exponentialSmoothOn_exp_of_linear_bound (scalarAmplitudeMarkedExponent s e)
    (scalarAmplitudeDomain (k+2) R) (exponentialSmoothOn_scalarAmplitudeMarkedExponent s R e)
    B L hL (fun w hw => (le_abs_self _).trans (hv w hw))
  have hsquare := (exponentialSmoothOn_scalarAmplitudeNodeGradient s R p).pow 2
  exact hexp.bilinear hsquare (ContinuousLinearMap.mul ℝ ℝ)

theorem contDiffAt_scalarAmplitudeGamma (s : RSBScheme k) (p : ℕ)
    (w : ScalarAmplitudeState (k+2)) : ContDiffAt ℝ ∞ (scalarAmplitudeGamma s p) w := by
  let R : ℝ≥0 := ⟨‖w.1‖+1,by positivity⟩
  have hw : w ∈ scalarAmplitudeDomain (k+2) R := by change ‖w.1‖<‖w.1‖+1;linarith
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro e _
  exact contDiffAt_gaussianShiftAverage_of_exponentialSmoothOn
    (scalarAmplitudeMarkedIntegrand s p e) (scalarAmplitudeDomain (k+2) R)
    (scalarAmplitudeDomain_open R) (exponentialSmoothOn_scalarAmplitudeMarkedIntegrand s R p e)
    (scalarAmplitudeNoiseShift (k+2)) (scalarAmplitudeDomain_noise_invariant R) w hw

end QuantitativeFollowup
