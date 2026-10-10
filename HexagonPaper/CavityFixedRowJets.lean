module
public import HexagonPaper.CavityTreeNativeAllJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowJets
public import QuantitativeFollowup.FollowupCavityDecouplingGradient
public import QuantitativeFollowup.AnisotropicNodeTheta

@[expose] public section

/-! Actual arbitrary-profile deterministic incident-row first jets at the
independent endpoint, obtained from exact clamped finite kernels and genuine
uniform native jet limits. No product-response identity is assumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityFixedRow_finite_tail_pair_product (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (P : AnisotropicParameter (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    anisotropicFiniteTailPairResponse D s q P (anisotropicCavityRowIndex n i)=
      anisotropicFiniteTailMagnetization R s q (cavityRestParameterProjection n P) i*
        anisotropicFiniteTailMagnetization D s q P (Fin.last n) := by
  dsimp only
  let sc:=vectorClampedScheme s q q.property
  have hm (D : AnisotropicSpinModel (n+1)) :
      anisotropicFiniteTailMagnetization D s q P (Fin.last n)=
        anisotropicFiniteFeatureMean D sc (k+2) (fun σ=>Paper.spinSign (σ (Fin.last n))) P := by
    rw [anisotropicFiniteTailMagnetization_clamped,anisotropicMagnetization_eq_spin_mean]
    rfl
  have hr : anisotropicFiniteTailMagnetization (followupCavityRestSpinModel n β ρ hβ hρ)
      s q (cavityRestParameterProjection n P) i=
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) sc (k+2)
        (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P) := by
    rw [anisotropicFiniteTailMagnetization_clamped,anisotropicMagnetization_eq_spin_mean]
    rfl
  have hlast:=cavityFiniteIncidentFeature_zero sc n β ρ hβ hρ (k+2) (fun _=>1) P
  simp only [one_mul] at hlast
  have hc : anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ)
      sc (k+2) (fun _=>1) (cavityRestParameterProjection n P)=1 := by
    unfold anisotropicFiniteFeatureMean
    simp
  rw [hc,one_mul] at hlast
  rw [anisotropicFiniteTailPairResponse_eq_spinMoment,hr,hm]
  change anisotropicFiniteFeatureMean _ sc (k+2)
    (anisotropicPairFeature (anisotropicCavityRowIndex n i)) P=_
  rw [anisotropicCavityRowIndex,cavityFiniteRowFeature_zero,hlast]

theorem cavityFixedRow_native_tail_pair_product (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (P : AnisotropicParameter (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    anisotropicTailPairResponse D μ q P (anisotropicCavityRowIndex n i)=
      anisotropicMeasureTailMagnetization R μ q (cavityRestParameterProjection n P) i*
        anisotropicMeasureTailMagnetization D μ q P (Fin.last n) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  have hfull:=tendsto_anisotropicFiniteTailPairResponse_moving D μ (anisotropicCavityRowIndex n i)
    (tendsto_const_nhds (x:=q)) (tendsto_const_nhds (x:=P))
  have hrest := (EuclideanSpace.proj i).continuous.continuousAt.tendsto.comp
    ((tendstoUniformly_anisotropicFiniteDyadicTailMagnetization R μ).tendsto_at
      (q,cavityRestParameterProjection n P))
  have hlast := (EuclideanSpace.proj (Fin.last n)).continuous.continuousAt.tendsto.comp
    ((tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ).tendsto_at (q,P))
  simp only [D] at hfull
  simp_rw [cavityFixedRow_finite_tail_pair_product] at hfull
  exact tendsto_nhds_unique hfull (hrest.mul hlast)

theorem cavityFixedRow_native_Vi (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Pr:=cavityRestParameterProjection n P
    HasDerivAt (anisotropicPairParameterPotential D μ q P (anisotropicCavityRowIndex n i))
      (anisotropicMeasureTailMagnetization R μ q Pr i*
        Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))) 0 := by
  dsimp only
  have hh:=hasDerivAt_anisotropicPairParameterPotential_zero
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q
    (anisotropicParameterPoint g x) (anisotropicCavityRowIndex n i)
  rw [cavityFixedRow_native_tail_pair_product,followupCavityMeasureGradient_last_zero] at hh
  exact hh

end HexagonPaper
