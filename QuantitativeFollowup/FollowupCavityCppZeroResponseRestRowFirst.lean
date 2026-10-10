module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowObservableJets

@[expose] public section

/-! The actual rest-spin row derivative is the scalar mean times the
actual rest susceptibility. The proof differentiates Vi=Mi*m along an old
field and uses symmetry of the genuine smooth potential Hessian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem cavityRestProjection_oldDirection (n : ℕ) (l : Fin n) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) l.castSucc) =
      anisotropicCoordinateDirection n l := by
  ext i
  cases i <;> simp [cavityRestParameterProjection,anisotropicCoordinateDirection,
    anisotropicFieldInjection,EuclideanSpace.single_apply]

private theorem cavityOldDirection_last (n : ℕ) (l : Fin n) :
    anisotropicCoordinateDirection (n+1) l.castSucc (Sum.inr (Fin.last n)) = 0 := by
  have hn : Fin.last n ≠ l.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last,Fin.val_castSucc] at hv
    omega
  simp [anisotropicCoordinateDirection,anisotropicFieldInjection,EuclideanSpace.single_apply,hn]

theorem cavityFiniteRestFeature_row_first (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (i l : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    fderiv ℝ (cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j
      (WithLp.toLp 2 (fun σ : Configuration (n+1)=>Paper.spinSign (σ l.castSucc))))
      (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) =
    parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) *
      fderiv ℝ (anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ)
        s j (fun σ=>Paper.spinSign (σ i))) (cavityRestParameterProjection n P)
        (anisotropicCoordinateDirection n l) := by
  dsimp only
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let U := finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j
  let H := anisotropicEnergyMap D P
  let K := anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
  let b : FiniteStateField (Configuration (n+1)) := WithLp.toLp 2
    (fun σ : Configuration (n+1)=>Paper.spinSign (σ l.castSucc))
  let delta := anisotropicCoordinateDirection (n+1) l.castSucc
  let restD := followupCavityRestSpinModel n β ρ hβ hρ
  let Mi := anisotropicFiniteFeatureMean restD s j (fun σ=>Paper.spinSign (σ i))
  let R := cavityRestParameterProjection n P
  let v := anisotropicCoordinateDirection n l
  let m := parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n)))
  have hb : anisotropicEnergyMap D delta = b := by
    ext σ
    exact anisotropicTerminalLinear_coordinate D σ l.castSucc
  have hrest : cavityRestParameterProjection n delta = v :=
    cavityRestProjection_oldDirection n l
  have hlast : delta (Sum.inr (Fin.last n)) = 0 := cavityOldDirection_last n l
  have he : (fun t : ℝ=>fderiv ℝ U (H+t • b) K) =
      fun t=>Mi (R+t • v)*m := by
    funext t
    have hv := cavityFiniteRowFeature_zero s n β ρ hβ hρ j i (P+t • delta)
    rw [←anisotropicFinitePair_energy_first] at hv
    have heH : anisotropicEnergyMap D (P+t • delta) = H+t • b := by
      rw [map_add,map_smul,hb]
    have hex : (P+t • delta) (Sum.inr (Fin.last n)) = P (Sum.inr (Fin.last n)) := by
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hlast,mul_zero,add_zero]
    change fderiv ℝ U (anisotropicEnergyMap D (P+t • delta)) K = _ at hv
    rw [heH,hex] at hv
    simp only [map_add,map_smul,hrest] at hv
    exact hv
  have hU := contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
  have hDK : ContDiff ℝ ∞ (fun Q=>fderiv ℝ U Q K) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hd := ((hDK.differentiable (by simp) H).hasFDerivAt).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0:ℝ) H).add ((hasDerivAt_id (0:ℝ)).smul_const b)) (by simp)
  have hMi : ContDiff ℝ ∞ Mi := by
    have heM : Mi = fun Q=>anisotropicMagnetization restD s j Q i := by
      funext Q
      exact (anisotropicMagnetization_eq_spin_mean restD s j Q i).symm
    rw [heM]
    exact (boundedJets_anisotropicMagnetization_component restD s j i).1
  have hs := ((hMi.differentiable (by simp) R).hasFDerivAt).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0:ℝ) R).add ((hasDerivAt_id (0:ℝ)).smul_const v)) (by simp)
  have hl : HasDerivAt (fun t : ℝ=>fderiv ℝ U (H+t • b) K)
      (fderiv ℝ (fun Q=>fderiv ℝ U Q K) H b) 0 := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,zero_add,one_smul] using hd
  rw [he] at hl
  have hr : HasDerivAt (fun t : ℝ=>Mi (R+t • v)*m) (fderiv ℝ Mi R v*m) 0 := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,zero_add,one_smul] using hs.mul_const m
  change fderiv ℝ (fun Q=>fderiv ℝ U Q b) H K = m*fderiv ℝ Mi R v
  rw [cavity_directional_second_symmetry U hU H b K]
  exact (hl.unique hr).trans (mul_comm _ _)

end QuantitativeFollowup
