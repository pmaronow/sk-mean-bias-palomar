module
public import FourPapersCommon.ScalarFiniteStateCascade
public import FourPapersCommon.MixedCoordinateScheduleScheme
public import FourPapersCommon.FiniteStateSameMassResponses

@[expose] public section

/-! Actual realization of a changing interaction coefficient by a finite
one-spin Gaussian covariance schedule. The schedule's value is exactly the
selected mixed potential for the original physical overlap measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000

def scalarSpinDirection (v : ℝ) :
    FiniteStateGaussianInput (Fin 1)→L[ℝ]FiniteStateField (Configuration 1) :=
  (replicaSingleSiteSpinCLM (d:=1)).comp (replicaSiteCopyGaussianCLM v (id : Fin 1→Fin 1))

theorem scalarSpinDirection_mul (u v : ℝ) (hu : 0≤u) :
    scalarSpinDirection (u*v)=Real.sqrt u • scalarSpinDirection v := by
  apply ContinuousLinearMap.ext
  intro z
  dsimp only [scalarSpinDirection,ContinuousLinearMap.comp_apply]
  change replicaSingleSiteSpinCLM (replicaSiteCopyGaussianCLM (u*v) (id : Fin 1→Fin 1) z)=
    Real.sqrt u • replicaSingleSiteSpinCLM (replicaSiteCopyGaussianCLM v (id : Fin 1→Fin 1) z)
  rw [←map_smul]
  congr 1
  ext l
  simp only [replicaSiteCopyGaussianCLM_apply,
    WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,Real.sqrt_mul hu]
  ring

def coefficientScheduleMass {k : ℕ} (s : RSBScheme k) (j : ℕ) : ℝ :=
  s.m (k+1-j/3)

def coefficientScheduleUp (j : ℕ) : Bool := decide (j%3≠0)

def coefficientScheduleDirection {k : ℕ} (ξ : AdmissibleEvenMixture) (p : ℕ)
    (M : ℝ) (s : RSBScheme k) (j : ℕ) :
    FiniteStateGaussianInput (Fin 1)→L[ℝ]FiniteStateField (Configuration 1) :=
  scalarSpinDirection (if j%3=2 then coordinateScheduleActive p M s (k+1-j/3)
    else coordinateScheduleBase ξ p s (k+1-j/3))

theorem coefficientScheduleMass_nonneg {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    0 ≤ coefficientScheduleMass s j := s.m_nonneg (by omega)

private theorem terminalCascade_congr_prefix {S I : Type*} [Fintype S] [Fintype I]
    (V : S→ℝ) (a b : ℕ→ℝ)
    (L M : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (J : ℕ)
    (hm : ∀j<J,a j=b j) (hL : ∀j<J,L j=M j) :
    finiteStateGaussianTerminalCascade V a L J=finiteStateGaussianTerminalCascade V b M J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [finiteStateGaussianTerminalCascade,finiteStateGaussianCascade]
    rw [hm J (by omega),hL J (by omega)]
    rw [show finiteStateGaussianCascade a L (gtStateLogPartition V) J=
      finiteStateGaussianCascade b M (gtStateLogPartition V) J from
      ih (fun j hj=>hm j (by omega)) (fun j hj=>hL j (by omega))]
    all_goals rfl

theorem scalarSchemeMass_coefficientSchedule {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) (j : ℕ) :
    scalarSchemeMass (coefficientScheduleClockScheme ξ p hp c M t ht hc s) j=
      coefficientScheduleMass s j := by
  simp only [scalarSchemeMass,coefficientScheduleClockScheme,threefoldScheme_m,mixedClockScheme_m,
    coefficientScheduleMass]
  congr 1
  omega

/-- The actual current Gaussian increment at every scheduled level is the
literal covariance increment of the refined clocked scheme. -/
theorem scalarSchemeSpinInput_coefficientSchedule {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) (j : ℕ)
    (hj : j<3*(k+2)) :
    scalarSchemeSpinInput (coefficientScheduleClockScheme ξ p hp c M t ht hc s)
      (mixedBeta (ξ.amplitudeCoordinate p hp c)) j=
      finiteStateScheduleScale (coefficientScheduleUp j) t • coefficientScheduleDirection ξ p M s j := by
  let i:=k+1-j/3
  have hi : i≤k+1 := by dsimp [i]; omega
  have hv:=coefficientSchedule_three_variances ξ p hp c M t ht hc s i hi
  dsimp only at hv
  let r:=coefficientScheduleClockScheme ξ p hp c M t ht hc s
  have hr : j%3<3 := Nat.mod_lt _ (by norm_num)
  change scalarSpinDirection ((mixedBeta (ξ.amplitudeCoordinate p hp c))^2*
    (r.q (3*k+4+2-j)-r.q (3*k+4+1-j)))=_
  rw [mixedBeta_sq]
  rcases (show j%3=0 ∨ j%3=1 ∨ j%3=2 by omega) with h0|h1|h2
  · have he1 : 3*k+4+2-j=3*(i+1) := by dsimp [i]; omega
    have he2 : 3*k+4+1-j=3*i+2 := by dsimp [i]; omega
    rw [he1,he2,hv.2.2,scalarSpinDirection_mul (1-t) _ (by linarith [ht.2])]
    simp only [coefficientScheduleUp,ne_eq,not_true_eq_false,decide_false,
      finiteStateScheduleScale,Bool.false_eq_true,ite_false,coefficientScheduleDirection,h0,
      show ¬(0 : ℕ)=2 by decide,i]
  · have he1 : 3*k+4+2-j=3*i+2 := by dsimp [i]; omega
    have he2 : 3*k+4+1-j=3*i+1 := by dsimp [i]; omega
    rw [he1,he2,hv.2.1,scalarSpinDirection_mul t _ ht.1]
    simp only [coefficientScheduleUp,ne_eq,show ¬(1 : ℕ)=0 by decide,not_false_eq_true,
      decide_true,finiteStateScheduleScale,ite_true,coefficientScheduleDirection,h1,
      show ¬(1 : ℕ)=2 by decide,i]
    all_goals rfl
  · have he1 : 3*k+4+2-j=3*i+1 := by dsimp [i]; omega
    have he2 : 3*k+4+1-j=3*i := by dsimp [i]; omega
    rw [he1,he2,hv.1,scalarSpinDirection_mul t _ ht.1]
    simp only [coefficientScheduleUp,ne_eq,show ¬(2 : ℕ)=0 by decide,not_false_eq_true,
      decide_true,finiteStateScheduleScale,ite_true,coefficientScheduleDirection,h2,i]

/-- Literal value identification, with the original physical scheme measure,
not an independently supplied Gaussian or PDE representation. -/
theorem coefficientScheduleTerminal_eq_mixedPotential {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) (h : ℝ) :
    finiteStateGaussianScheduledTerminalCascade (scalarSpinPotential h) (coefficientScheduleMass s)
      (coefficientScheduleDirection ξ p M s) coefficientScheduleUp (3*(k+2)) t 0=
      Real.log 2+mixedPotential (ξ.amplitudeCoordinate p hp c) (Paper.parisiSchemeMeasure s) (0,h) := by
  let r:=coefficientScheduleClockScheme ξ p hp c M t ht hc s
  let σ:=ξ.amplitudeCoordinate p hp c
  rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
  have hm (j : ℕ) (_ : j<3*(k+2)) : coefficientScheduleMass s j=scalarSchemeMass r j :=
    (scalarSchemeMass_coefficientSchedule ξ p hp c M t ht hc s j).symm
  have hL (j : ℕ) (hj : j<3*(k+2)) :
      finiteStateScheduleScale (coefficientScheduleUp j) t • coefficientScheduleDirection ξ p M s j=
        scalarSchemeSpinInput r (mixedBeta σ) j :=
    (scalarSchemeSpinInput_coefficientSchedule ξ p hp c M t ht hc s j hj).symm
  rw [terminalCascade_congr_prefix (scalarSpinPotential h) _ _ _ _ (3*(k+2)) hm hL]
  have he:=scalarGaussianTerminalCascade_scheme r (mixedBeta σ) (mixedBeta_pos σ) h
    (3*(k+2)) (by omega) 0
  have hidx : 3*k+4+2-3*(k+2)=0 := by omega
  simp only [map_zero,WithLp.ofLp_zero,Pi.zero_apply,add_zero,hidx,r.q_zero] at he
  rw [he]
  rw [parisiSchemeMeasure_coefficientSchedule]
  simp only [mixedPotential,σ,AdmissibleEvenMixture.clock_zero]

end FourPapersCommon
