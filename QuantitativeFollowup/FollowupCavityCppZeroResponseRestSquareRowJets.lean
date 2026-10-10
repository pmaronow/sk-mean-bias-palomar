module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastSquareRowJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestRowFirst
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFieldFeatures

@[expose] public section

/-! The two actual incident-row derivatives of the retained rest square.
Every susceptibility and Wi derivative is evaluated in the true finite
potential; the rest dimension normalization remains explicit. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem energy_old_coordinate (D : AnisotropicSpinModel (n+1)) (l : Fin n) :
    anisotropicEnergyMap D (anisotropicCoordinateDirection (n+1) l.castSucc)=
      WithLp.toLp 2 (fun σ : QuantitativePaper.Configuration (n+1)=>Paper.spinSign (σ l.castSucc)) :=by
  ext σ
  exact anisotropicTerminalLinear_coordinate D σ l.castSucc

private theorem rest_feature_at_energy (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (l : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j
      (WithLp.toLp 2 (fun σ : QuantitativePaper.Configuration (n+1)=>Paper.spinSign (σ l.castSucc)))
      (anisotropicEnergyMap D P)=
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (fun σ=>Paper.spinSign (σ l)) (cavityRestParameterProjection n P) :=by
  dsimp only
  rw [cavityFiniteEnergyFeatureMean_at_parameter]
  simpa only [cavityRestConfiguration] using
    cavityFiniteRestFeature_zero s n β ρ hβ hρ j (fun σ=>Paper.spinSign (σ l)) P

theorem cavityFiniteRestSquare_row_first (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (i : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    fderiv ℝ (cavityFixedRowRestFieldSquare D s j) (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
      2*(n:ℝ)⁻¹*parisiFDeriv s (followupCavityScalarBeta n β ρ) j
        (P (Sum.inr (Fin.last n)))*
      ∑l : Fin n,anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (fun σ=>Paper.spinSign (σ l)) (cavityRestParameterProjection n P)*
        fderiv ℝ (anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
          (fun σ=>Paper.spinSign (σ i))) (cavityRestParameterProjection n P)
            (anisotropicCoordinateDirection n l) :=by
  dsimp only
  unfold cavityFixedRowRestFieldSquare
  rw [cavityFiniteEnergyRestOverlap_first_row _ _ (anisotropicSchemeMass_nonneg s)]
  simp_rw [rest_feature_at_energy s n β ρ hβ hρ j,
    cavityFiniteRestFeature_row_first s n β ρ hβ hρ j i]
  simp only [Fintype.card_fin]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem cavityFiniteRestSquare_row_second (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (i : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let K:=anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    fderiv ℝ (fun Q=>fderiv ℝ (cavityFixedRowRestFieldSquare D s j) Q K)
      (anisotropicEnergyMap D P) K=
      2*(n:ℝ)⁻¹*∑l : Fin n,
        ((parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) *
          fderiv ℝ (anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
            (fun σ=>Paper.spinSign (σ i))) (cavityRestParameterProjection n P)
              (anisotropicCoordinateDirection n l))^2+
        anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
          (fun σ=>Paper.spinSign (σ l)) (cavityRestParameterProjection n P)*
          fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
            (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
              (anisotropicCoordinateDirection (n+1) l.castSucc)) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let e:=anisotropicOrderedCoupling i.castSucc (Fin.last n)
  unfold cavityFixedRowRestFieldSquare
  rw [cavityFiniteEnergyRestOverlap_second_row _ _ (anisotropicSchemeMass_nonneg s)]
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [rest_feature_at_energy s n β ρ hβ hρ j l P,
    cavityFiniteRestFeature_row_first s n β ρ hβ hρ j i l P]
  have hrow:=fderiv_cavityFiniteEnergyRowSecond_at_parameter D s j e P
    (anisotropicCoordinateDirection (n+1) l.castSucc)
  rw [energy_old_coordinate] at hrow
  rw [hrow]

end QuantitativeFollowup
