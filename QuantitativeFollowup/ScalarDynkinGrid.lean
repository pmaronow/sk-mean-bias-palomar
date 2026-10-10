module
public import QuantitativeFollowup.ScalarDynkinCells
public import QuantitativeFollowup.ScalarDynkinWeak
public import FRSB.GridMeasureIdentification
public import Paper.ParisiGradientMesh

@[expose] public section

/-! Actual polynomial Dynkin identities from a fresh physical time to the
terminal time. Genuine cell identities paste across every retained grid node,
and weak approximation gives arbitrary tested Parisi measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000

theorem scalarDynkin_grid_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (hb : beta≠0) (ν : Paper.ParisiMeasure) (n : ℕ)
    (F : MomentPolynomial) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    scalarDynkinMoment P X beta (parisiGridMeasure ν n) F a (1-a)-
      scalarDynkinMoment P X beta (parisiGridMeasure ν n) F a 0=
      ∫r in (0 : ℝ)..(1-a),∫ω,
        scalarDynkinSource X d beta sigma (parisiGridMeasure ν n) F a r ω ∂P := by
  let T := fun i=>parisiGradientMeshTime n a i-a
  let S := fun r=>∫ω,scalarDynkinSource X d beta sigma (parisiGridMeasure ν n) F a r ω ∂P
  let M := scalarDynkinMoment P X beta (parisiGridMeasure ν n) F a
  let G := fun i=>M (T i)-∫r in (0 : ℝ)..T i,S r
  have hSi : ∀l r,IntervalIntegrable S volume l r :=
    scalarDynkinSource_expected_intervalIntegrable hc beta (parisiGridMeasure ν n) F a
  have hT0 (i : ℕ) : 0≤T i := by
    dsimp only [T,parisiGradientMeshTime]
    exact sub_nonneg.mpr (le_max_left _ _)
  have hTzero : T 0=0 := by simp only [T,parisiGradientMeshTime_zero n ha.1,sub_self]
  have hTterm : T (n+1)=1-a := by
    simp only [T,parisiGradientMeshTime_terminal n ha.2]
  have htel := parisiGradientMesh_norm_telescope G (fun _=>0) T (n+1)
    (fun _ _=>intervalIntegrable_const) (by
      intro i hi
      rcases parisiGradientMeshTime_step_cases n a i with heq | hlt
      · have hTi : T i=T (i+1) := congrArg (fun x=>x-a) heq
        simp only [G,hTi,sub_self,norm_zero,intervalIntegral.integral_zero,le_refl]
      · let s := parisiGridRSBScheme ν n
        obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q ν n i hi
        have hq : s.q (i+1)<s.q (i+1+1) := by
          simpa only [s,hq0,hq1,show i+1+1=i+2 by omega] using hjbGridTime_step_lt n i
        have hcell := parisiGradientMeshTime_cell_subset n a i hlt
        have hLeft : s.q (i+1)≤a+T i := by
          have hh := (hcell ⟨le_rfl,hlt.le⟩).1
          simpa only [s,hq0,T,add_sub_cancel] using hh
        have hRight : a+T (i+1)≤ s.q (i+1+1) := by
          have hh := (hcell ⟨hlt.le,le_rfl⟩).2
          simpa only [s,hq1,T,add_sub_cancel,show i+1+1=i+2 by omega] using hh
        have hStep : T i≤T (i+1) := sub_le_sub_right hlt.le a
        have hh := scalarDynkin_finite_cell_closed hc beta hb s (p:=i+1) (by omega) hq
          F a (T i) (T (i+1)) (hT0 i) hLeft hStep hRight
        rw [parisiSchemeMeasure_grid_eq ν n] at hh
        have he : G (i+1)-G i=M (T (i+1))-M (T i)-∫r in T i..T (i+1),S r := by
          have hii := intervalIntegral.integral_interval_sub_left (hSi 0 (T (i+1))) (hSi 0 (T i))
          dsimp only [G]
          linarith
        rw [he]
        change ‖M (T (i+1))-M (T i)-∫r in T i..T (i+1),S r‖≤_
        change M (T (i+1))-M (T i)=∫r in T i..T (i+1),S r at hh
        rw [hh,sub_self,norm_zero,intervalIntegral.integral_zero])
  rw [hTzero,hTterm,intervalIntegral.integral_zero] at htel
  have hz : G (n+1)-G 0=0 := norm_eq_zero.mp (le_antisymm htel (norm_nonneg _))
  simp only [G,hTzero,hTterm,intervalIntegral.integral_same,sub_zero] at hz
  dsimp only [M,S] at hz
  linarith

theorem scalarDynkin_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0→Ω→ℝ} {sigma : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J sigma)
    (beta : ℝ) (hb : beta≠0) (ν : Paper.ParisiMeasure)
    (F : MomentPolynomial) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    scalarDynkinMoment P X beta ν F a (1-a)-scalarDynkinMoment P X beta ν F a 0=
      ∫r in (0 : ℝ)..(1-a),∫ω,scalarDynkinSource X d beta sigma ν F a r ω ∂P := by
  have hν := tendsto_parisiGridMeasure ν
  have hM0 := tendsto_scalarDynkinMoment_of_weak hc beta ν (parisiGridMeasure ν) hν F a 0
  have hM1 := tendsto_scalarDynkinMoment_of_weak hc beta ν (parisiGridMeasure ν) hν F a (1-a)
  have hS := tendsto_scalarDynkinSource_integral_of_weak hc beta ν (parisiGridMeasure ν) hν
    F a (1-a) ha ⟨sub_nonneg.mpr ha.2,le_rfl⟩
  apply tendsto_nhds_unique (hM1.sub hM0)
  exact hS.congr' (.of_forall fun n=>(scalarDynkin_grid_tail hc beta hb ν n F a ha).symm)

end QuantitativeFollowup
