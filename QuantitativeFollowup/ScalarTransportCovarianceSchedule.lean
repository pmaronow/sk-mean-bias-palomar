module
public import QuantitativeFollowup.ScalarTransportCellGeometry
public import FourPapersCommon.FiniteStateSignedThreefoldResponse
public import FourPapersCommon.FiniteStateCascadePrefix
public import FourPapersCommon.ScalarFiniteStateCovarianceSchedule
public import FourPapersCommon.ScalarFiniteStateCascadeLaw

@[expose] public section

/-! Actual scalar level transports are realized by genuine signed Gaussian
covariance schedules at every partial recursion depth and starting field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

def scalarTransportScheduleUp (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (j : ℕ) : Bool :=
  if j%3=0 then false else if j%3=1 then true else
    decide (0 ≤ scalarTransportCellSlope s φ (k+1-j/3))

def scalarTransportScheduleDirection (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (j : ℕ) :
    FiniteStateGaussianInput (Fin 1)→L[ℝ]FiniteStateField (Configuration 1) :=
  scalarSpinDirection (β^2*(if j%3=2 then scalarTransportCellActive s φ δ (k+1-j/3)
    else scalarTransportCellBase s φ δ (k+1-j/3)))

theorem scalarTransportRefinedScheme_mass (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ) (j : ℕ) :
    scalarSchemeMass (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu) j=
      coefficientScheduleMass s j := by
  simp only [scalarSchemeMass,scalarTransportRefinedScheme,threefoldScheme_m,scalarTransportScheme_mass,
    coefficientScheduleMass]
  congr 1
  omega

theorem scalarTransportScheduleUp_base (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (i : ℕ) :
    scalarTransportScheduleUp s φ (3*i)=false ∧ scalarTransportScheduleUp s φ (3*i+1)=true := by
  simp [scalarTransportScheduleUp,Nat.mul_comm,Nat.add_mod]

theorem scalarTransportScheduleDirection_base (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (i : ℕ) :
    scalarTransportScheduleDirection s β φ δ (3*i+1)=scalarTransportScheduleDirection s β φ δ (3*i) := by
  simp [scalarTransportScheduleDirection,Nat.mul_comm,Nat.add_mod,Nat.add_div]

theorem scalarTransportScheduleMass_base (s : RSBScheme k) (i : ℕ) :
    coefficientScheduleMass s (3*i+1)=coefficientScheduleMass s (3*i) := by
  simp [coefficientScheduleMass,Nat.mul_comm,Nat.add_div]

theorem scalarTransportRefinedScheme_input (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ) (j : ℕ)
    (hj : j < 3*(k+2)) :
    scalarSchemeSpinInput (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu) β j=
      finiteStateScheduleScale (scalarTransportScheduleUp s φ j) (signedAffineCellTime δ u) •
        scalarTransportScheduleDirection s β φ δ j := by
  let i:=k+1-j/3
  have hi : i ≤ k+1 := by dsimp [i]; omega
  have hv := scalarTransportRefinedScheme_three_cells s φ L hφ h0 h1 δ u hδ hsmall hu i hi
  dsimp only at hv
  let r:=scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu
  let t:=signedAffineCellTime δ u
  have ht := signedAffineCellTime_mem_unit hδ hu
  have hr : j%3 < 3 := Nat.mod_lt _ (by norm_num)
  change scalarSpinDirection (β^2*(r.q (3*k+4+2-j)-r.q (3*k+4+1-j)))=_
  rcases (show j%3=0 ∨ j%3=1 ∨ j%3=2 by omega) with h0j|h1j|h2j
  · have he1 : 3*k+4+2-j=3*(i+1) := by dsimp [i]; omega
    have he2 : 3*k+4+1-j=3*i+2 := by dsimp [i]; omega
    rw [he1,he2,hv.2.2]
    rw [show β^2*((1-signedAffineCellTime δ u)*scalarTransportCellBase s φ δ i)=
      (1-signedAffineCellTime δ u)*(β^2*scalarTransportCellBase s φ δ i) by ring,
      scalarSpinDirection_mul _ _ (by linarith [ht.2])]
    simp only [scalarTransportScheduleUp,h0j,ite_true,finiteStateScheduleScale,
      Bool.false_eq_true,ite_false,scalarTransportScheduleDirection,show ¬(0:ℕ)=2 by decide,i]
  · have he1 : 3*k+4+2-j=3*i+2 := by dsimp [i]; omega
    have he2 : 3*k+4+1-j=3*i+1 := by dsimp [i]; omega
    rw [he1,he2,hv.2.1]
    rw [show β^2*(signedAffineCellTime δ u*scalarTransportCellBase s φ δ i)=
      signedAffineCellTime δ u*(β^2*scalarTransportCellBase s φ δ i) by ring,
      scalarSpinDirection_mul _ _ ht.1]
    simp only [scalarTransportScheduleUp,h1j,show ¬(1:ℕ)=0 by decide,ite_false,ite_true,
      finiteStateScheduleScale,scalarTransportScheduleDirection,show ¬(1:ℕ)=2 by decide,i]
  · have he1 : 3*k+4+2-j=3*i+1 := by dsimp [i]; omega
    have he2 : 3*k+4+1-j=3*i := by dsimp [i]; omega
    rw [he1,he2,hv.1]
    rw [show β^2*(signedAffineCellScale (scalarTransportCellSlope s φ i)
        (signedAffineCellTime δ u)*scalarTransportCellActive s φ δ i)=
      signedAffineCellScale (scalarTransportCellSlope s φ i) (signedAffineCellTime δ u)*
        (β^2*scalarTransportCellActive s φ δ i) by ring,
      scalarSpinDirection_mul _ _ (signedAffineCellScale_mem_unit _ ht).1]
    by_cases hp : 0 ≤ scalarTransportCellSlope s φ i
    · simp only [scalarTransportScheduleUp,h2j,show ¬(2:ℕ)=0 by decide,show ¬(2:ℕ)=1 by decide,
        ite_false,scalarTransportScheduleDirection,ite_true,show k+1-j/3=i from rfl,
        hp,decide_true,finiteStateScheduleScale,signedAffineCellScale]
    · simp only [scalarTransportScheduleUp,h2j,show ¬(2:ℕ)=0 by decide,show ¬(2:ℕ)=1 by decide,
        ite_false,scalarTransportScheduleDirection,ite_true,show k+1-j/3=i from rfl,
        hp,decide_false,finiteStateScheduleScale,Bool.false_eq_true,signedAffineCellScale,ite_false]

theorem scalarTransportSchedule_partial_potential (s : RSBScheme k) (β : ℝ) (hβ : 0 < β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (J : ℕ) (hJ : J ≤ k+2) (h : ℝ) (H : FiniteStateField (Fin 1)) :
    finiteStateGaussianScheduledTerminalCascade (scalarSpinPotential h) (coefficientScheduleMass s)
      (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ) (3*J)
      (signedAffineCellTime δ u) (replicaSingleSiteSpinCLM H)=
      Real.log 2+Paper.parisiPotential β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
        ((scalarLevelTransport φ u (scalarSchemeTransportNode s (k+2-J)):ℝ),scalarSiteAbsolute h H) := by
  let r:=scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu
  rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
  have hm (j : ℕ) (_ : j < 3*J) : coefficientScheduleMass s j=scalarSchemeMass r j :=
    (scalarTransportRefinedScheme_mass s φ L hφ h0 h1 δ u hδ hsmall hu j).symm
  have hA (j : ℕ) (hj : j < 3*J) :
      finiteStateScheduleScale (scalarTransportScheduleUp s φ j) (signedAffineCellTime δ u) •
        scalarTransportScheduleDirection s β φ δ j=scalarSchemeSpinInput r β j :=
    (scalarTransportRefinedScheme_input s β φ L hφ h0 h1 δ u hδ hsmall hu j (by omega)).symm
  rw [finiteStateGaussianTerminalCascade_congr_prefix (scalarSpinPotential h) _ _ _ _ (3*J) hm hA,
    scalarGaussianTerminalCascade_scheme r β hβ h (3*J) (by omega) H]
  rw [scalarTransportRefinedScheme_measure s φ L hφ h0 h1 δ u hδ hsmall hu]
  have hidx : 3*k+4+2-3*J=3*(k+2-J) := by omega
  rw [hidx]
  have hq : r.q (3*(k+2-J))=
      (scalarLevelTransport φ u (scalarSchemeTransportNode s (k+2-J)):ℝ) :=
    threefoldScheme_q_original _ _ _ _ _
  rw [hq]
  rfl

end QuantitativeFollowup
