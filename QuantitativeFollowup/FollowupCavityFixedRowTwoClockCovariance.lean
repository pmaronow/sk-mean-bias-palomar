module
public import QuantitativeFollowup.FollowupCavityFixedRowTwoClock
public import QuantitativeFollowup.FollowupCavityFixedRowMovingDefinitions

@[expose] public section

/-! Actual recorded covariances for the two physical clocks. All three
moments retain their moving model-dependent finite responses. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowRecordedCovariance (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) : ℝ :=
  let P:=anisotropicFiniteRecordedTreeLaw D s a (observationLinearTree (k+2))
  (∫z,cavityFixedRowLastSquare D s d z*cavityFixedRowRestSquare D s d z∂P)-
    (∫z,cavityFixedRowLastSquare D s d z∂P)*(∫z,cavityFixedRowRestSquare D s d z∂P)

theorem cavityFixedRowRecordedCovariance_eq_zero_offset (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) :
    cavityFixedRowRecordedCovariance D s a d=cavityFixedRowCovariance D s a d 0 := by
  simp only [cavityFixedRowRecordedCovariance,cavityFixedRowCovariance,cavityFixedRowProductMean,
    cavityFixedRowLastMean,cavityFixedRowRestMean,cavityFixedRowLaw,map_zero,
    anisotropicFiniteRecordedTreeLaw]
  rfl

theorem cavityFixedRowTwoClockCovariance_eq_weighted
    (beta rho : ℝ) (hbeta : 0<beta) (hrho : rho∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (b : ℝ) (hb : 0<b) (v : ℝ) (hv : 0≤v) :
    let D:=cavityLastVarianceModel n beta rho hbeta hrho b hb
    cavityFixedRowRecordedCovariance (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v) s a d=
      cavityRowWeightedAverage (cavityFixedRowNormalizer D s a) (cavityFixedRowProductMean D s a d) v-
        cavityRowWeightedAverage (cavityFixedRowNormalizer D s a) (cavityFixedRowLastMean D s a d) v*
        cavityRowWeightedAverage (cavityFixedRowNormalizer D s a) (cavityFixedRowRestMean D s a d) v := by
  dsimp only
  let D:=cavityLastVarianceModel n beta rho hbeta hrho b hb
  let P:=cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v
  have hi : cavityFiniteEnergyInput P s=cavityFiniteEnergyInput D s :=
    funext fun j=>cavityFixedRowTwoClockModel_energyInput beta rho hbeta hrho b hb v s j
  have hF : cavityFixedRowLastSquare P s d=cavityFixedRowLastSquare D s d := by
    funext z
    unfold cavityFixedRowLastSquare
    rw [hi]
  have hG : cavityFixedRowRestSquare P s d=cavityFixedRowRestSquare D s d := by
    funext z
    unfold cavityFixedRowRestSquare
    rw [hi]
  obtain ⟨B,hB,hbound⟩:=exists_cavityFixedRowObservable_bounds D s d
  have hf:=measurable_cavityFixedRowLastSquare_from_factory D s d
  have hg:=measurable_cavityFixedRowRestSquare_from_factory D s d
  have hL:=cavityFixedRowTwoClock_weighted_mixture beta rho hbeta hrho b hb v hv s a
    (cavityFixedRowLastSquare D s d) hf B hB (fun z=>(hbound z).1)
  have hR:=cavityFixedRowTwoClock_weighted_mixture beta rho hbeta hrho b hb v hv s a
    (cavityFixedRowRestSquare D s d) hg B hB (fun z=>(hbound z).2.1)
  have hP:=cavityFixedRowTwoClock_weighted_mixture beta rho hbeta hrho b hb v hv s a
    (fun z=>cavityFixedRowLastSquare D s d z*cavityFixedRowRestSquare D s d z)
    (hf.mul hg) B hB (fun z=>(hbound z).2.2)
  change (∫z,cavityFixedRowLastSquare P s d z*cavityFixedRowRestSquare P s d z
    ∂anisotropicFiniteRecordedTreeLaw P s a (observationLinearTree (k+2)))-
    (∫z,cavityFixedRowLastSquare P s d z∂anisotropicFiniteRecordedTreeLaw P s a (observationLinearTree (k+2)))*
    (∫z,cavityFixedRowRestSquare P s d z∂anisotropicFiniteRecordedTreeLaw P s a (observationLinearTree (k+2)))=_
  rw [hF,hG,hL,hR,hP]
  rfl

def cavityFixedRowPhysicalCurveCovariance (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  if hu:u∈Icc (0:ℝ) 1 then
    cavityFixedRowRecordedCovariance (followupCavitySpinModel n beta rho hbeta hrho u hu) s a d
  else 0

theorem cavityFixedRowPhysicalCurveCovariance_eq (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    cavityFixedRowPhysicalCurveCovariance (n:=n) beta rho hbeta hrho s a d u=
      cavityFixedRowRecordedCovariance (followupCavitySpinModel n beta rho hbeta hrho u hu) s a d := by
  simp only [cavityFixedRowPhysicalCurveCovariance,dif_pos hu]

end QuantitativeFollowup
