module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFutureProduct
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeScores
public import QuantitativeFollowup.ScalarFutureContinuity

@[expose] public section

/-! The selected binary-feature strict-future integral is the literal
product of the native rest and scalar restart squares. Its identification
uses every actual finite free-measure charge, including repeated nodes. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem freeFutureProduct_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityFiniteFreeFutureSquare_average_eq_native_product
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (J : ℕ) (hJ : J≤k+2) (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 freeFutureProduct_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q sample
    (∫r,if q<r then
      (∑i : Fin n,cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)
      else 0 ∂parisiFreeMeasure μ a)=
      ∫r,if q<r then cavityRestFutureSquare Rest μ q r (cavityRestSampleProjection n sample)*
        scalarFutureSquareExtended (followupCavityScalarBeta n β ρ) μ q r
          (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
            (sample.2 (Fin.last n))) else 0 ∂parisiFreeMeasure μ a :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 freeFutureProduct_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let P:=anisotropicProcessParameter D μ q sample
  let F:=fun r : Paper.Overlap=>if q<r then
    (∑i : Fin n,cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ) else 0
  let G:=fun r : Paper.Overlap=>if q<r then
    cavityRestFutureSquare Rest μ q r (cavityRestSampleProjection n sample)*
      scalarFutureSquareExtended (followupCavityScalarBeta n β ρ) μ q r
        (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
          (sample.2 (Fin.last n))) else 0
  change (∫r,F r ∂parisiFreeMeasure μ a)=∫r,G r ∂parisiFreeMeasure μ a
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq F,
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq G]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  dsimp only [F,G]
  by_cases hqr:q<cavityOuterSchemeChargeNode s c
  · rw [if_pos hqr,if_pos hqr]
    let p:=k+2-cavityOuterChargePosition (k+1) c
    have hp:p≤J :=by
      by_contra hn
      have hpos:=cavityOuterSchemeChargePosition_le c
      have hidx:cavityOuterChargePosition (k+1) c≤k+2-J:=by dsimp only [p] at hn;omega
      have hmono:=s.q_mono' (k+2-J) (by omega)
        (cavityOuterChargePosition (k+1) c) hidx
      have hreverse:cavityOuterSchemeChargeNode s c≤q :=by
        rw [cavityOuterSchemeChargeNode_eq_position]
        exact hmono
      exact not_lt_of_ge hreverse hqr
    have hr:anisotropicSchemeNode s (k+2-p) (by omega)=cavityOuterSchemeChargeNode s c :=by
      rw [cavityOuterSchemeChargeNode_eq_position]
      apply Subtype.ext
      change s.q (k+2-p)=s.q (cavityOuterChargePosition (k+1) c)
      congr 1
      dsimp only [p]
      have hc:=cavityOuterSchemeChargePosition_le c
      omega
    have he:=cavityFiniteIncidentFutureSquare_average_at_native_scheme_node_eq_rest_future
      s n β ρ hβ hρ J p hJ hp sample
    dsimp only at he
    simp only [scalarFutureSquareProcess,←scalarFutureSquareExtended_eq] at he
    rw [hr] at he
    exact he
  · rw [if_neg hqr,if_neg hqr]

end QuantitativeFollowup
