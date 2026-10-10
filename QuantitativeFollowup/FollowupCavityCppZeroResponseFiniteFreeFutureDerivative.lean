module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFutureNativeDerivative
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeScores
public import QuantitativeFollowup.ScalarFutureContinuity

@[expose] public section

/-! Actual strict-future finite-free differential integrals. Every signed
raw charge is retained, including the negative outer root and repeated
nodes; the real free-measure identity performs their exact merger. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem freeFutureDerivative_strict_charge_node (s : RSBScheme k)
    (J : ℕ) (hJ : J≤k+2) (c : Option (Option (Fin (k+1))))
    (hqr : anisotropicSchemeNode s (k+2-J) (by omega)<cavityOuterSchemeChargeNode s c) :
    ∃(p : ℕ)(hp : p≤J),
      anisotropicSchemeNode s (k+2-p) (by omega)=cavityOuterSchemeChargeNode s c := by
  let p:=k+2-cavityOuterChargePosition (k+1) c
  have hp : p≤J := by
    by_contra hn
    have hpos:=cavityOuterSchemeChargePosition_le c
    have hidx : cavityOuterChargePosition (k+1) c≤k+2-J := by dsimp only [p] at hn; omega
    have hmono:=s.q_mono' (k+2-J) (by omega) (cavityOuterChargePosition (k+1) c) hidx
    have hreverse : cavityOuterSchemeChargeNode s c≤anisotropicSchemeNode s (k+2-J) (by omega) := by
      rw [cavityOuterSchemeChargeNode_eq_position]
      exact hmono
    exact not_lt_of_ge hreverse hqr
  refine ⟨p,hp,?_⟩
  rw [cavityOuterSchemeChargeNode_eq_position]
  apply Subtype.ext
  change s.q (k+2-p)=s.q (cavityOuterChargePosition (k+1) c)
  congr 1
  dsimp only [p]
  have hc:=cavityOuterSchemeChargePosition_le c
  omega

theorem cavityFiniteFreeFutureSquare_average_last_derivative_eq_native_product
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (J : ℕ) (hJ : J≤k+2) (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q sample
    (∫r,if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,
      cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)) P
        (anisotropicCoordinateDirection (n+1) (Fin.last n)) else 0 ∂parisiFreeMeasure μ a)=
      ∫r,if q<r then cavityRestFutureSquare Rest μ q r (cavityRestSampleProjection n sample)*
        scalarFutureSquareDerivativeExtended (followupCavityScalarBeta n β ρ) μ q r
          (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
            (sample.2 (Fin.last n))) else 0 ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let P:=anisotropicProcessParameter D μ q sample
  let F:=fun r : Paper.Overlap=>if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,
    cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n)) else 0
  let G:=fun r : Paper.Overlap=>if q<r then
    cavityRestFutureSquare Rest μ q r (cavityRestSampleProjection n sample)*
      scalarFutureSquareDerivativeExtended (followupCavityScalarBeta n β ρ) μ q r
        (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
          (sample.2 (Fin.last n))) else 0
  change (∫r,F r ∂parisiFreeMeasure μ a)=∫r,G r ∂parisiFreeMeasure μ a
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq F,
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq G]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  dsimp only [F,G]
  by_cases hqr : q<cavityOuterSchemeChargeNode s c
  · rw [if_pos hqr,if_pos hqr]
    obtain ⟨p,hp,hr⟩:=freeFutureDerivative_strict_charge_node s J hJ c hqr
    have he:=cavityFiniteIncidentFutureSquare_average_last_derivative_at_native_scheme_node
      s n β ρ hβ hρ J p hJ hp sample
    dsimp only at he
    simp only [←scalarFutureSquareDerivativeExtended_eq] at he
    rw [hr] at he
    exact he
  · rw [if_neg hqr,if_neg hqr]

theorem cavityFiniteFreeFutureSquare_average_old_derivative_eq_native_product
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (J : ℕ) (hJ : J≤k+2) (sample : AnisotropicDisorderBrownianSample (n+1)) (l : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q sample
    let z:=cavityRestSampleProjection n sample
    (∫r,if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,
      cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)) P
        (anisotropicCoordinateDirection (n+1) l.castSucc) else 0 ∂parisiFreeMeasure μ a)=
      ∫r,if q<r then scalarFutureSquareExtended (followupCavityScalarBeta n β ρ) μ q r
          (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
            (sample.2 (Fin.last n)))*
        fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ z.1 q x r)
          (anisotropicMeasureState Rest μ q z) (EuclideanSpace.single l 1)
        else 0 ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let P:=anisotropicProcessParameter D μ q sample
  let z:=cavityRestSampleProjection n sample
  let F:=fun r : Paper.Overlap=>if q<r then fderiv ℝ (fun Q=>(∑i : Fin n,
    cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)) P
      (anisotropicCoordinateDirection (n+1) l.castSucc) else 0
  let G:=fun r : Paper.Overlap=>if q<r then
    scalarFutureSquareExtended (followupCavityScalarBeta n β ρ) μ q r
      (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q (sample.2 (Fin.last n)))*
    fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ z.1 q x r)
      (anisotropicMeasureState Rest μ q z) (EuclideanSpace.single l 1) else 0
  change (∫r,F r ∂parisiFreeMeasure μ a)=∫r,G r ∂parisiFreeMeasure μ a
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq F,
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq G]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  dsimp only [F,G]
  by_cases hqr : q<cavityOuterSchemeChargeNode s c
  · rw [if_pos hqr,if_pos hqr]
    obtain ⟨p,hp,hr⟩:=freeFutureDerivative_strict_charge_node s J hJ c hqr
    have he:=cavityFiniteIncidentFutureSquare_average_old_derivative_at_native_scheme_node
      s n β ρ hβ hρ J p hJ hp sample l
    dsimp only at he
    simp only [scalarFutureSquareProcess,←scalarFutureSquareExtended_eq] at he
    rw [hr] at he
    exact he
  · rw [if_neg hqr,if_neg hqr]

end QuantitativeFollowup
