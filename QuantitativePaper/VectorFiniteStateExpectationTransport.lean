module
public import QuantitativePaper.VectorFiniteMarkedTransport
public import QuantitativePaper.VectorMarkedTiltConvergence

@[expose] public section

/-! Actual node-state expectation transport from the Gaussian posterior to
the constructed finite diffusion and its true fractional disorder tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integral_vectorEuclidean_state_eq_finite (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+2)
    (F : VectorState n→ℝ) (hF : Measurable F) (K : ℝ) (hK : ∀x,‖F x‖≤K) :
    (∫p : VectorGaussianSpace n k×Configuration n,F (vectorEuclideanStateLinear s β t i p.1)
      ∂vectorEuclideanJointLaw s β t a)=
      ∫sample,F (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  let H : FiniteHistory (VectorState n) (k+2)×Configuration n→ℝ:=
    fun p=>F (p.1 (Fin.ofNat (k+3) i))
  have hH : Measurable H:=hF.comp ((measurable_pi_apply _).comp measurable_fst)
  have hE (p : VectorGaussianSpace n k×Configuration n) :
      H (vectorEuclideanJointMap s β t p)=F (vectorEuclideanStateLinear s β t i p.1) := by
    rw [vectorEuclideanStateLinear_apply]
    rfl
  have hP (p : VectorDisorderBrownianSample n×Configuration n) :
      H (vectorFiniteHistory s β t ht.le (k+2) p.1,p.2)=
        F (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p.1) := by
    dsimp [H,vectorFiniteHistory,historySample]
    have he : (Fin.ofNat (k+3) i).val=i := by
      simp only [Fin.ofNat_eq_cast,Fin.val_natCast]
      exact Nat.mod_eq_of_lt (by omega)
    simpa only [Nat.mod_eq_of_lt (show i<k+2+1 by omega)]
  have hm : Measurable (fun p : VectorDisorderBrownianSample n×Configuration n=>
      F (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p.1)) :=
    (hF.comp (measurable_vectorFiniteJointState s β t ht.le _)).comp measurable_fst
  calc
    _=∫p,H (vectorEuclideanJointMap s β t p) ∂vectorEuclideanJointLaw s β t a :=
      integral_congr_ae (.of_forall fun p=>(hE p).symm)
    _=∫p,H p ∂vectorJointLaw s β t a:=integral_vectorEuclideanJointLaw_history s β t a H hH
    _=∫p,H (vectorFiniteHistory s β t ht.le (k+2) p.1,p.2)
        ∂vectorFiniteSpinPathLaw s β t a ht.le :=
      (integral_vectorFiniteSpinPathLaw_history s β t a hβ ht H hH).symm
    _=∫p,F (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p.1)
        ∂vectorFiniteSpinPathLaw s β t a ht.le :=
      integral_congr_ae (.of_forall hP)
    _=_ := by
      rw [integral_vectorFiniteSpinPathLaw_bounded s β t a ht.le _ hm K
        (fun p=>hK _)]
      simp only [terminalMean_const]

end QuantitativePaper
