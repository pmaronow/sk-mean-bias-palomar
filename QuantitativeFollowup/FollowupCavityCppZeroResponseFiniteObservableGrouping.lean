module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestSquareRowJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseObservableAlgebra

@[expose] public section

/-! The literal isolated-spin and rest observable parts of the finite zero-row
response, evaluated in the actual finite potential. All finite charge
weights remain arbitrary signed numbers until Stieltjes transport. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option autoImplicit false
variable {n k : ℕ} {R : Type*} [Fintype R]
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem cavityGrouping_zero_mem : (0:ℝ)∈Icc 0 1 :=⟨le_rfl,zero_le_one⟩

theorem cavityFiniteLastSquare_row_first (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (i : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityGrouping_zero_mem
    fderiv ℝ (cavityFixedRowLastFieldSquare D s j) (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
      2*parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n)))*
        parisiFSecond s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n)))*
        anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
          (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityGrouping_zero_mem
  let b:FiniteStateField (Configuration (n+1)):=WithLp.toLp 2
    (fun σ : Configuration (n+1)=>Paper.spinSign (σ (Fin.last n)))
  have hm : cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j b (anisotropicEnergyMap D P)=
      parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) :=by
    rw [cavityFiniteEnergyFeatureMean_at_parameter]
    simpa only [one_mul,anisotropicFiniteFeatureMean_one] using
      cavityFiniteIncidentFeature_zero s n β ρ hβ hρ j (fun _=>1) P
  unfold cavityFixedRowLastFieldSquare
  rw [cavityFiniteEnergyFeatureSquare_first _ _
    (anisotropicSchemeMass_nonneg s),cavityFiniteLastFeature_row_first,hm]
  ring

theorem cavityFiniteLastObservable_group (s : RSBScheme k) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ)
    (P : AnisotropicParameter (n+1)) (w : R→ℝ) (jr : R→ℕ)
    (Pr : R→AnisotropicParameter (n+1)) (σ : Configuration (n+1)) (Abar : ℝ) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityGrouping_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let m:=parisiFDeriv s B j (P (Sum.inr (Fin.last n)))
    let h:=parisiFSecond s B j (P (Sum.inr (Fin.last n)))
    let M:=fun i=>anisotropicFiniteFeatureMean Rest s j (fun τ=>Paper.spinSign (τ i))
      (cavityRestParameterProjection n P)
    let Mr:=fun r i=>anisotropicFiniteFeatureMean Rest s (jr r) (fun τ=>Paper.spinSign (τ i))
      (cavityRestParameterProjection n (Pr r))
    let mr:=fun r=>parisiFDeriv s B (jr r) (Pr r (Sum.inr (Fin.last n)))
    let E:=fun i : Fin n=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
      (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n))
    let K:=fun i : Fin n=>anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    let Score:=fun i : Fin n=>Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
      ∑r,w r*anisotropicFiniteFeatureMean D s (jr r)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) (Pr r)
    ((n:ℝ)⁻¹/2)*(∑i : Fin n,(
      fderiv ℝ (fun Q=>fderiv ℝ (cavityFixedRowLastFieldSquare D s j) Q (K i))
        (anisotropicEnergyMap D P) (K i)*Abar+
      2*Score i*fderiv ℝ (cavityFixedRowLastFieldSquare D s j)
        (anisotropicEnergyMap D P) (K i)*Abar))=
      Abar*(h^2*(∑i,(M i)^2)/(n:ℝ)+m*(∑i,E i)/(n:ℝ)+
        2*m*h*Paper.spinSign (σ (Fin.last n))*(∑i,Paper.spinSign (σ i.castSucc)*M i)/(n:ℝ)-
        2*m*h*(∑r,w r*mr r*(∑i,M i*Mr r i))/(n:ℝ)) :=by
  dsimp only
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hc : (n:ℝ)⁻¹/2=1/(2*(n:ℝ)) :=by
    simp [div_eq_mul_inv,mul_inv_rev,mul_comm]
  rw [hc]
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityGrouping_zero_mem
  have hsecond (i : Fin n) :
      fderiv ℝ (fun Q=>fderiv ℝ (cavityFixedRowLastFieldSquare D s j) Q
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))))
        (anisotropicEnergyMap D P)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
      2*(anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (fun τ=>Paper.spinSign (τ i)) (cavityRestParameterProjection n P)*
        parisiFSecond s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))))^2+
      2*parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n)))*
        fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
          (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
            (anisotropicCoordinateDirection (n+1) (Fin.last n)) :=by
    unfold cavityFixedRowLastFieldSquare
    exact cavityFiniteLastSquare_row_second s n β ρ hβ hρ j i P
  dsimp only [D] at hsecond
  simp only [hsecond,cavityFiniteLastSquare_row_first,cavityFiniteRowFeature_zero]
  simpa only [Fintype.card_fin,cavityObservableAlgebraSecond,cavityObservableAlgebraFirst,
    cavityDensityAlgebraScore,mul_assoc] using
    (cavityObservableAlgebra_last_group
      (parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))))
      (parisiFSecond s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))))
      Abar (Paper.spinSign (σ (Fin.last n)))
      (fun i=>anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (fun τ=>Paper.spinSign (τ i)) (cavityRestParameterProjection n P))
      (fun i=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
        (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
        (anisotropicCoordinateDirection (n+1) (Fin.last n)))
      (fun i=>Paper.spinSign (σ i.castSucc)) w
      (fun r=>parisiFDeriv s (followupCavityScalarBeta n β ρ) (jr r) (Pr r (Sum.inr (Fin.last n))))
      (fun r i=>anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s (jr r)
        (fun τ=>Paper.spinSign (τ i)) (cavityRestParameterProjection n (Pr r))))

theorem cavityFiniteRestObservable_group (s : RSBScheme k) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ)
    (P : AnisotropicParameter (n+1)) (w : R→ℝ) (jr : R→ℕ)
    (Pr : R→AnisotropicParameter (n+1)) (σ : Configuration (n+1)) (fbar : ℝ) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityGrouping_zero_mem
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let m:=parisiFDeriv s B j (P (Sum.inr (Fin.last n)))
    let h:=parisiFSecond s B j (P (Sum.inr (Fin.last n)))
    let M:=fun i=>anisotropicFiniteFeatureMean Rest s j (fun τ=>Paper.spinSign (τ i))
      (cavityRestParameterProjection n P)
    let H:=fun l i=>fderiv ℝ (anisotropicFiniteFeatureMean Rest s j
      (fun τ=>Paper.spinSign (τ i))) (cavityRestParameterProjection n P)
        (anisotropicCoordinateDirection n l)
    let E:=fun (i l : Fin n)=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
      (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
        (anisotropicCoordinateDirection (n+1) l.castSucc)
    let Mr:=fun r i=>anisotropicFiniteFeatureMean Rest s (jr r) (fun τ=>Paper.spinSign (τ i))
      (cavityRestParameterProjection n (Pr r))
    let mr:=fun r=>parisiFDeriv s B (jr r) (Pr r (Sum.inr (Fin.last n)))
    let K:=fun i : Fin n=>anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    let Score:=fun i : Fin n=>Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))-
      ∑r,w r*anisotropicFiniteFeatureMean D s (jr r)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) (Pr r)
    ((n:ℝ)⁻¹/2)*(∑i : Fin n,(
      fbar*fderiv ℝ (fun Q=>fderiv ℝ (cavityFixedRowRestFieldSquare D s j) Q (K i))
        (anisotropicEnergyMap D P) (K i)+
      2*fderiv ℝ (cavityFixedRowLastFieldSquare D s j) (anisotropicEnergyMap D P) (K i)*
        fderiv ℝ (cavityFixedRowRestFieldSquare D s j) (anisotropicEnergyMap D P) (K i)+
      2*Score i*fbar*fderiv ℝ (cavityFixedRowRestFieldSquare D s j)
        (anisotropicEnergyMap D P) (K i)))=
      fbar*m^2*(∑i,∑l,H l i^2)/(n:ℝ)^2+
      fbar*(∑l,M l*(∑i,E i l))/(n:ℝ)^2+
      4*m^2*h*(∑i,M i*(∑l,M l*H l i))/(n:ℝ)^2+
      2*fbar*m*Paper.spinSign (σ (Fin.last n))*(∑i,Paper.spinSign (σ i.castSucc)*
        (∑l,M l*H l i))/(n:ℝ)^2-
      2*fbar*m*(∑r,w r*mr r*(∑i,Mr r i*(∑l,M l*H l i)))/(n:ℝ)^2 :=by
  dsimp only
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 cavityGrouping_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let m:=parisiFDeriv s B j (P (Sum.inr (Fin.last n)))
  let h:=parisiFSecond s B j (P (Sum.inr (Fin.last n)))
  let M:=fun i=>anisotropicFiniteFeatureMean Rest s j (fun τ=>Paper.spinSign (τ i))
    (cavityRestParameterProjection n P)
  let H:=fun l i=>fderiv ℝ (anisotropicFiniteFeatureMean Rest s j
    (fun τ=>Paper.spinSign (τ i))) (cavityRestParameterProjection n P)
      (anisotropicCoordinateDirection n l)
  let E:=fun (i l : Fin n)=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
    (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
      (anisotropicCoordinateDirection (n+1) l.castSucc)
  have hfirst (i : Fin n) :
      fderiv ℝ (cavityFixedRowRestFieldSquare D s j) (anisotropicEnergyMap D P)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
        cavityObservableAlgebraRestFirst m M H i :=by
    rw [cavityFiniteRestSquare_row_first]
    simp only [cavityObservableAlgebraRestFirst,Fintype.card_fin,div_eq_mul_inv]
    rfl
  have hsecond (i : Fin n) :
      fderiv ℝ (fun Q=>fderiv ℝ (cavityFixedRowRestFieldSquare D s j) Q
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))))
        (anisotropicEnergyMap D P)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
      cavityObservableAlgebraRestSecond m M H E i :=by
    rw [cavityFiniteRestSquare_row_second]
    unfold cavityObservableAlgebraRestSecond
    simp only [Fintype.card_fin]
    change 2*(n:ℝ)⁻¹*(∑l,((m*H l i)^2+M l*E i l))=
      2/(n:ℝ)*(m^2*(∑l,H l i^2)+∑l,M l*E i l)
    simp_rw [mul_pow]
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [div_eq_mul_inv]
  have hc : (n:ℝ)⁻¹/2=1/(2*(n:ℝ)) :=by
    simp [div_eq_mul_inv,mul_inv_rev,mul_comm]
  rw [hc]
  dsimp only [D] at hfirst hsecond
  simp only [hsecond,hfirst,cavityFiniteLastSquare_row_first,cavityFiniteRowFeature_zero]
  simpa only [Fintype.card_fin,cavityObservableAlgebraFirst,cavityDensityAlgebraScore,
    mul_assoc] using
    (cavityObservableAlgebra_rest_group m h fbar (Paper.spinSign (σ (Fin.last n)))
      M (fun i=>Paper.spinSign (σ i.castSucc)) H E w
      (fun r=>parisiFDeriv s B (jr r) (Pr r (Sum.inr (Fin.last n))))
      (fun r i=>anisotropicFiniteFeatureMean Rest s (jr r) (fun τ=>Paper.spinSign (τ i))
        (cavityRestParameterProjection n (Pr r))))

end QuantitativeFollowup
