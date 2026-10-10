module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativePairSecondAverage
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeScores

@[expose] public section

/-! Actual finite scalar and rest means at every signed outer charge.
Repeated observations are not collapsed or assigned a different mass. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem nativeChargeMean_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityFiniteResponseCharge_node (s : RSBScheme k)
    (c : Option (Option (Fin (k+1)))) :
    anisotropicSchemeNode s (k+2-(k+2-cavityOuterChargePosition (k+1) c)) (by omega)=
      cavityOuterSchemeChargeNode s c :=by
  rw [cavityOuterSchemeChargeNode_eq_position]
  apply Subtype.ext
  change s.q (k+2-(k+2-cavityOuterChargePosition (k+1) c))=
    s.q (cavityOuterChargePosition (k+1) c)
  congr 1
  have hc:=cavityOuterSchemeChargePosition_le c
  omega

theorem cavityFiniteScalarMean_at_native_scheme_charge
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (c : Option (Option (Fin (k+1))))
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeChargeMean_zero_mem
    let μ:=Paper.parisiSchemeMeasure s
    let r:=cavityOuterSchemeChargeNode s c
    let J:=k+2-cavityOuterChargePosition (k+1) c
    parisiFDeriv s (followupCavityScalarBeta n β ρ) J
      (anisotropicProcessParameter D μ r sample (Sum.inr (Fin.last n)))=
      M (followupCavityScalarBeta n β ρ) μ r (sample.2 (Fin.last n)) :=by
  dsimp only
  have he:=cavityFiniteScalarMean_at_native_scheme_node s n β ρ hβ hρ
    (k+2-cavityOuterChargePosition (k+1) c) (by omega) sample
  dsimp only at he
  rw [cavityFiniteResponseCharge_node] at he
  exact he

theorem cavityFiniteRestMean_at_zero_native_scheme_charge
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (c : Option (Option (Fin (k+1)))) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeChargeMean_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let r:=cavityOuterSchemeChargeNode s c
    let J:=k+2-cavityOuterChargePosition (k+1) c
    anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
      (cavityRestParameterProjection n (anisotropicProcessParameter D μ r sample))=
      anisotropicProcessSpinResponse Rest μ r i (cavityRestSampleProjection n sample) :=by
  dsimp only
  have he:=cavityFiniteRestMean_at_zero_native_scheme_node s n β ρ hβ hρ
    (k+2-cavityOuterChargePosition (k+1) c) (by omega) i sample
  dsimp only at he
  rw [cavityFiniteResponseCharge_node] at he
  exact he

end QuantitativeFollowup
