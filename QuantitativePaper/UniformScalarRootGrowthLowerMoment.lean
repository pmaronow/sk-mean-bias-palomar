module
public import QuantitativePaper.UniformScalarRootGrowthBrownianWindow
public import QuantitativePaper.UniformScalarRootGrowthState
public import FRSB.MomentQuotient
public import FRSB.BackwardsTime

@[expose] public section

/-! The actual third-jet square expectation is bounded below by the genuine
Brownian window probability times the quantitative boundary barrier. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000

theorem scalarEnergyJet_two_at_energy_state (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (q : ℝ) (ω : Paper.BrownianSample) :
    scalarEnergySpatialJet β μ 2 (q,FRSB.optimalStateReal β μ ω q/β)=
      β^2*FRSB.jetProcess β μ 3 q ω := by
  have he : β*(FRSB.optimalStateReal β μ ω q/β)=FRSB.optimalStateReal β μ ω q:=by field_simp
  simp only [scalarEnergySpatialJet,Nat.reduceAdd,he,FRSB.jetProcess,←FRSB.backwardD_eq_spatialJet,
    FRSB.backwardD]

theorem scalarRootMomentA_brownian_lower (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (τ ell K q : ℝ) (hτ : 0<τ) (hK : 0≤K)
    (hq : q∈Ioc (0:ℝ) (1/4096)) (hqτ : q≤τ)
    (hsτ : Real.sqrt q≤τ/16) (hsell : 3*Real.sqrt q≤ell)
    (hg : ∀s∈Icc (0:ℝ) q,β*parisiCDF μ s≤32)
    (hbar : ∀x∈Icc (0:ℝ) ell,K*(x-4*q/τ)≤-scalarEnergySpatialJet β μ 2 (q,x)) :
    (K^2*scalarBrownianWindowProbability/16)*q≤β^4*FRSB.quotientNumerator β μ q := by
  let E : Set Paper.BrownianSample:={ω|canonicalBrownian q.toNNReal ω/Real.sqrt q∈Icc (1:ℝ) 2}
  have hE : MeasurableSet E:=measurableSet_Icc.preimage
    ((measurable_canonicalBrownian q.toNNReal).div_const (Real.sqrt q))
  let V : Paper.BrownianSample→ℝ:=fun ω=>
    scalarEnergySpatialJet β μ 2 (q,FRSB.optimalStateReal β μ ω q/β)^2
  have hphys : q∈Icc (0:ℝ) 1:=⟨hq.1.le,hq.2.trans (by norm_num)⟩
  have hVeq (ω : Paper.BrownianSample) : V ω=β^4*(FRSB.jetProcess β μ 3 q ω)^2:=by
    dsimp only [V]
    rw [scalarEnergyJet_two_at_energy_state β hβ.ne' μ q ω]
    ring
  have hVi : Integrable V canonicalBrownianMeasure:=by
    exact (((FRSB.integrable_jetProcess_pow β hβ.ne' μ 2 2 hphys).const_mul (β^4)).congr
      (.of_forall fun ω=>(hVeq ω).symm))
  have hpoint (ω : Paper.BrownianSample) : E.indicator (fun _=>K^2*q/16) ω≤V ω:=by
    by_cases hω : ω∈E
    · rw [indicator_of_mem hω]
      have hs : 0<Real.sqrt q:=Real.sqrt_pos.2 hq.1
      have hsq : (Real.sqrt q)^2=q:=Real.sq_sqrt hq.1.le
      have hX:=scalarEnergyState_on_brownian_window β hβ μ q hq hg ω hω
      have hXI : FRSB.optimalStateReal β μ ω q/β∈Icc (0:ℝ) ell:=
        ⟨(show 0≤Real.sqrt q/2 by positivity).trans hX.1,hX.2.trans hsell⟩
      have hb:=hbar _ hXI
      have hmul:=mul_le_mul_of_nonneg_right hsτ hs.le
      have hdelta : Real.sqrt q/4≤FRSB.optimalStateReal β μ ω q/β-4*q/τ := by
        have hdiv : 4*q/τ≤Real.sqrt q/4 := by
          apply (div_le_iff₀ hτ).mpr
          nlinarith
        linarith [hX.1]
      have hw : K*(Real.sqrt q/4)≤-scalarEnergySpatialJet β μ 2 (q,FRSB.optimalStateReal β μ ω q/β):=
        (mul_le_mul_of_nonneg_left hdelta hK).trans hb
      dsimp only [V]
      have hnn : 0≤K*(Real.sqrt q/4):=by positivity
      nlinarith
    · rw [indicator_of_notMem hω]
      exact sq_nonneg _
  have hi:=integral_mono ((integrable_const (K^2*q/16)).indicator hE) hVi hpoint
  rw [integral_indicator hE,integral_const] at hi
  have hp : canonicalBrownianMeasure.real E=scalarBrownianWindowProbability:=
    scalarBrownianWindow_probability q hq.1
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hi
  change canonicalBrownianMeasure.real E*(K^2*q/16)≤_ at hi
  rw [hp] at hi
  have he : (∫ω,V ω ∂canonicalBrownianMeasure)=β^4*FRSB.quotientNumerator β μ q:=by
    simp_rw [hVeq]
    rw [integral_const_mul]
    congr 1
    simp only [FRSB.quotientNumerator,FRSB.quotientNumeratorPolynomial,FRSB.moment_X_pow,Nat.reduceAdd]
  rw [he] at hi
  nlinarith

end QuantitativePaper
