module
public import QuantitativeFollowup.FollowupCavityObservationPairGeometry

@[expose] public section

/-! One genuine floor-preserving mesh realizes every fixed test on an
observation schedule, so independent binary tests share the actual profile. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {J : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem exists_finite_floor_observation_geometry
    (μ : Paper.ParisiMeasure) (a : ℝ) (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (N : ℕ):
    ∃(K : ℕ)(s : RSBScheme K)(d : ℕ→ℕ)
      (hdepth : observationRefinementDepth d J=K+2),
      Paper.parisiSchemeMeasure s=Paper.parisiGridMeasure μ N ∧ s.q 1=0 ∧ a ≤ s.m 1 ∧
      ∀j,anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j := by
  let r:=Paper.parisiGridRSBScheme μ N
  have hr:r.q 1=0:=Paper.parisiGridSchemeOverlap_one N
  have hm:Paper.parisiSchemeMeasure r=Paper.parisiGridMeasure μ N:=FRSB.parisiSchemeMeasure_grid_eq μ N
  have hf:a≤Paper.parisiCDF (Paper.parisiSchemeMeasure r) 0:=by
    rw [hm,←zeroMass_eq_parisiCDF_zero,parisiGridMeasure_root_mass,zeroMass_eq_parisiCDF_zero]
    exact hfloor
  obtain ⟨K,s,e,hs,hszero,has,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_floor_observation_scheme_embedding r hr a hf q hq J hJ hzero htop
  let d:=observationEmbeddingGaps e
  have hdepth:observationRefinementDepth d J=K+2:=
    (observationRefinementDepth_embedding e he hezero J).trans hetop
  refine ⟨K,s,d,hdepth,hs.trans hm,hszero,has,?_⟩
  intro j
  rw [observationRefinementDepth_embedding e he hezero]
  exact hlevels j

end QuantitativeFollowup
