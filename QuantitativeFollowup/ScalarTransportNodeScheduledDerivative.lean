module
public import QuantitativeFollowup.ScalarTransportCovarianceSchedule
public import FourPapersCommon.ScalarFiniteStateGamma

@[expose] public section

/-! Actual parameter derivatives of the scalar potential at transported
nodes. Both signs and every partial depth are supplied by the genuine
Gaussian schedule; no node-variation conclusion is an input hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

def scalarTransportNodePotential (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) : ℝ :=
  Paper.parisiPotential β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    ((scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ),x)

def scalarTransportNodeScheduleDerivative (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (J : ℕ) (u x : ℝ) : ℝ :=
  finiteStateGaussianScheduledTerminalTime (scalarSpinPotential 0)
    (coefficientScheduleMass s) (coefficientScheduleMass_nonneg s)
    (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ)
    (3*J) (signedAffineCellTime δ u)
    (replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) x))/(2*δ)

theorem scalarTransportNodePotential_eq_schedule (s : RSBScheme k) (β : ℝ) (hβ : 0 < β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportNodePotential s β φ (k+2-J) u x=
      finiteStateGaussianScheduledTerminalCascade (scalarSpinPotential 0) (coefficientScheduleMass s)
        (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ) (3*J)
        (signedAffineCellTime δ u)
        (replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) x))-Real.log 2 := by
  have he := scalarTransportSchedule_partial_potential s β hβ φ L hφ h0 h1 δ u
    hδ hsmall hu J hJ 0 (EuclideanSpace.single (0:Fin 1) x)
  simp only [scalarSiteAbsolute,EuclideanSpace.single_apply,ite_true,zero_add] at he
  dsimp only [scalarTransportNodePotential]
  linarith [he]

theorem hasDerivAt_scalarTransportNodePotential_schedule (s : RSBScheme k) (β : ℝ) (hβ : 0 < β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    HasDerivAt (fun v=>scalarTransportNodePotential s β φ (k+2-J) v x)
      (scalarTransportNodeScheduleDerivative s β φ δ J u x) u := by
  have ht := signedAffineCellTime_mem_interior hδ hu
  have hd := hasDerivAt_finiteStateGaussianScheduledTerminal_time (scalarSpinPotential 0)
    (coefficientScheduleMass s) (coefficientScheduleMass_nonneg s)
    (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ) (3*J)
    (signedAffineCellTime δ u) ht (replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) x))
  have htime : HasDerivAt (signedAffineCellTime δ) (1/(2*δ)) u := by
    unfold signedAffineCellTime
    convert ((hasDerivAt_id u).add_const δ).div_const (2*δ) using 1
    rfl
  have hc := (hd.comp u htime).sub_const (Real.log 2)
  have he : (fun v=>scalarTransportNodePotential s β φ (k+2-J) v x)=ᶠ[𝓝 u]
      (fun v=>finiteStateGaussianScheduledTerminalCascade (scalarSpinPotential 0) (coefficientScheduleMass s)
        (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ) (3*J)
        (signedAffineCellTime δ v) (replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) x))-Real.log 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hu)] with v hv
    exact scalarTransportNodePotential_eq_schedule s β hβ φ L hφ h0 h1 δ v x hδ hsmall
      (abs_le.mpr ⟨hv.1.le,hv.2.le⟩) J hJ
  simpa only [scalarTransportNodeScheduleDerivative,div_eq_mul_inv,one_mul] using
    hc.congr_of_eventuallyEq he

theorem scalarTransportNodeScheduleDerivative_eq_signed_responses (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (δ u x : ℝ) (hδ : 0 < δ) (hu : |u| < δ) (J : ℕ) :
    scalarTransportNodeScheduleDerivative s β φ δ J u x=
      (1/(4*δ))*∑i∈Finset.range J,
        (if scalarTransportScheduleUp s φ (3*i+2) then (1:ℝ) else -1)*
          finiteStateCascadeCovarianceResponse (scalarSpinPotential 0) (coefficientScheduleMass s)
            (fun j=>finiteStateScheduleScale (scalarTransportScheduleUp s φ j) (signedAffineCellTime δ u) •
              scalarTransportScheduleDirection s β φ δ j)
            (3*i+2) (3*J-(3*i+2))
            (replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) x))
            (scalarTransportScheduleDirection s β φ δ (3*i+2)) := by
  unfold scalarTransportNodeScheduleDerivative
  rw [finiteStateGaussianScheduledTerminal_time_signed_threefold (scalarSpinPotential 0)
    (coefficientScheduleMass s) (coefficientScheduleMass_nonneg s)
    (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ) J
    (fun i _=>scalarTransportScheduleUp_base s φ i)
    (fun i _=>scalarTransportScheduleMass_base s i)
    (fun i _=>scalarTransportScheduleDirection_base s β φ δ i)
    (signedAffineCellTime δ u) (signedAffineCellTime_mem_interior hδ hu)]
  field_simp
  ring

theorem continuousOn_scalarTransportNodeScheduleDerivative (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (hδ : 0 < δ) (J : ℕ) :
    ContinuousOn (fun z : ℝ×ℝ=>scalarTransportNodeScheduleDerivative s β φ δ J z.1 z.2)
      (Ioo (-δ) δ ×ˢ univ) := by
  let F : ℝ×ℝ→ℝ×FiniteStateField (Configuration 1) := fun z=>
    (signedAffineCellTime δ z.1,replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) z.2))
  have hF : Continuous F := by
    have hs : Continuous (fun z : ℝ×ℝ=>z.2 • scalarSpinAxis) := continuous_snd.smul continuous_const
    have he : (fun z : ℝ×ℝ=>replicaSingleSiteSpinCLM (EuclideanSpace.single (0:Fin 1) z.2))=
        (fun z=>z.2 • scalarSpinAxis) := by
      funext z
      simp only [scalarSpinAxis, ← map_smul]
      congr 1
      ext i
      simp [PiLp.single_apply,WithLp.ofLp_smul,Pi.smul_apply]
    exact (by dsimp only [signedAffineCellTime]; fun_prop : Continuous (fun z : ℝ×ℝ=>signedAffineCellTime δ z.1)).prodMk (he ▸ hs)
  have hm : MapsTo F (Ioo (-δ) δ ×ˢ univ) (finiteStateGaussianTimeDomain (Configuration 1)) := by
    intro z hz
    exact ⟨signedAffineCellTime_mem_interior hδ (abs_lt.mpr hz.1),mem_univ _⟩
  exact ((continuousOn_finiteStateGaussianScheduledTerminal_time (scalarSpinPotential 0)
    (coefficientScheduleMass s) (coefficientScheduleMass_nonneg s)
    (scalarTransportScheduleDirection s β φ δ) (scalarTransportScheduleUp s φ) (3*J)).comp
      hF.continuousOn hm).div_const (2*δ)

end QuantitativeFollowup
