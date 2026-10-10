module
public import QuantitativeFollowup.FollowupCavityMixtureOuterJointSpatial
public import QuantitativeFollowup.FollowupCavityMixtureCompactBounds
public import QuantitativeFollowup.FollowupCavityMixtureCompactHeatData
public import QuantitativeFollowup.FollowupCavityMixtureVarianceInput
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportContinuity
public import QuantitativeFollowup.FollowupCavityRootCharges

@[expose] public section

/-! The actual positive-last-variance family supplies moving heat data.
Every parameter is the true variance in the unchanged rest-coupling model. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper SpinGlass.Targets
open scoped Topology ContDiff
namespace QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityPositiveVarianceNormalizer_heatData
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a l r : ℝ)
    (hl : 0<l) (hlr : l≤r) :
    Nonempty (CavityMovingRowHeatData (fun z:ℝ×Field n=>
      cavityFixedRowNormalizer (anisotropicReplaceVariance D (Fin.last n) z.1) s a z.2) l r) :=by
  let L:=fun b:ℝ=>cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) b) s
  let LB:=fun b:Icc l r=>L b
  let R:=anisotropicRootEnergyMap D
  let F:=fun z:ℝ×FiniteStateField (Configuration (n+1))=>
    cavityOuterPosteriorNormalizer (fun _=>0) (anisotropicSchemeMass s) (L z.1) a (k+2) R z.2
  have hc(j):Continuous (fun b:Icc l r=>LB b j):=
    continuous_cavityFiniteEnergyInput_positive_variance_band D (Fin.last n) s l r hl j
  have hF:=cavityOuterPosteriorNormalizer_jointSpatial_input_family (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0)
    (anisotropicSchemeMass_antitone s) LB hc a (k+2) R
  obtain ⟨C,hC,hCb⟩:=cavityOuterPosteriorNormalizer_uniform_relative_jets
    (n:=n+1) (J:=AnisotropicCouplingIndex (n+1)) (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0)
    (anisotropicSchemeMass_antitone s) a (k+2) 2
  obtain ⟨B,hB,hBb⟩:=cavityOuterPosterior_family_common_exponential_bound
    (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    LB hc a (k+2) 2 R (fun b H=>F (b,H)) C hC (fun b i hi H=>hCb (LB b) R i hi H)
  have hh:=exists_cavityMovingHeatData_comp_linear F l r hlr hF (cavityFixedRowOffset n)
    B |a| hB (abs_nonneg a) hBb
  have he:(fun z:ℝ×Field n=>F (z.1,cavityFixedRowOffset n z.2))=
    (fun z=>cavityFixedRowNormalizer (anisotropicReplaceVariance D (Fin.last n) z.1) s a z.2):=by
    funext z
    simp only [F,cavityOuterPosteriorNormalizer,cavityFixedRowNormalizer,
      anisotropicRootEnergyMap_replaceVariance_mixture,L,R]
  rw [he] at hh
  exact hh

theorem cavityPositiveVarianceWeightedObservable_heatData
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a l r : ℝ)
    (hl : 0<l) (hlr : l≤r) (d : ℕ)
    (f : ℝ→FiniteStateField (Configuration (n+1))→ℝ)
    (hf : Continuous (fun z:Icc l r×FiniteStateField (Configuration (n+1))=>f z.1 z.2))
    (hsf : ∀b:Icc l r,BoundedJets (f b))
    (G : ℕ→ℝ) (hG : ∀i,0≤G i)
    (hfb : ∀b:Icc l r,∀i H,‖iteratedFDeriv ℝ i (f b) H‖≤G i) :
    Nonempty (CavityMovingRowHeatData (fun z:ℝ×Field n=>
      cavityOuterPosteriorWeightedMean (fun _ : Configuration (n+1)=>0)
        (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) z.1) s)
        a (k+2) (anisotropicRootEnergyMap D) (f z.1)
        (cavityPosteriorLineFieldLinear
          (cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) z.1) s) (k+2) d)
        (cavityFixedRowOffset n z.2)) l r) :=by
  let L:=fun b:ℝ=>cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) b) s
  let LB:=fun b:Icc l r=>L b
  let R:=anisotropicRootEnergyMap D
  let W:=fun b:ℝ=>cavityPosteriorLineFieldLinear (L b) (k+2) d
  let WB:=fun b:Icc l r=>W b
  let F:=fun z:ℝ×FiniteStateField (Configuration (n+1))=>
    cavityOuterPosteriorWeightedMean (fun _=>0) (anisotropicSchemeMass s) (L z.1) a (k+2) R
      (f z.1) (W z.1) z.2
  have hc(j):Continuous (fun b:Icc l r=>LB b j):=
    continuous_cavityFiniteEnergyInput_positive_variance_band D (Fin.last n) s l r hl j
  have hW:Continuous WB:=continuous_cavityPosteriorLineFieldLinear LB hc (k+2) d
  have hF:=cavityOuterPosteriorWeightedMean_jointSpatial_input_family (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0)
    (anisotropicSchemeMass_antitone s) LB hc a (k+2) R (fun z=>f z.1 z.2) hf hsf WB hW G hG hfb
  obtain ⟨C,hC,hCb⟩:=cavityOuterPosteriorWeightedMean_uniform_relative_jets
    (n:=n+1) (J:=AnisotropicCouplingIndex (n+1)) (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0)
    (anisotropicSchemeMass_antitone s) a (k+2) 2 G hG
  obtain ⟨B,hB,hBb⟩:=cavityOuterPosterior_family_common_exponential_bound
    (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    LB hc a (k+2) 2 R (fun b H=>F (b,H)) C hC
    (fun b i hi H=>hCb (LB b) R (f b) (hsf b) (WB b) (hfb b) i hi H)
  exact exists_cavityMovingHeatData_comp_linear F l r hlr hF (cavityFixedRowOffset n)
    B |a| hB (abs_nonneg a) hBb

end QuantitativeFollowup
