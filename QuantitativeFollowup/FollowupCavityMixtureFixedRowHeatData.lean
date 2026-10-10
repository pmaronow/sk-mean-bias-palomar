module
public import QuantitativeFollowup.FollowupCavityMixturePositiveVarianceFactory
public import QuantitativeFollowup.FollowupCavityMixtureVarianceObservables
public import QuantitativeFollowup.FollowupCavityFixedRowMovingDefinitions

@[expose] public section

/-! Model-only moving heat data for the four exact physical row
numerators. The outer mass is arbitrary real. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper SpinGlass.Targets
open scoped Topology ContDiff
namespace QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityPositiveVarianceLastWeighted_heatData
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a l r : ℝ)
    (hl : 0<l) (hlr : l≤r) (d : ℕ) (hd : d≤k+2) :
    Nonempty (CavityMovingRowHeatData (fun z:ℝ×Field n=>
      cavityFixedRowNormalizer (anisotropicReplaceVariance D (Fin.last n) z.1) s a z.2*
      cavityFixedRowLastMean (anisotropicReplaceVariance D (Fin.last n) z.1) s a d z.2) l r) :=by
  let M:=fun b:ℝ=>anisotropicReplaceVariance D (Fin.last n) b
  let f:=fun b:ℝ=>cavityFixedRowLastFieldSquare (M b) s d
  have hh:=cavityPositiveVarianceWeightedObservable_heatData D s a l r hl hlr d f
    (continuous_cavityFixedRowLastFieldSquare_positive_variance_band D s d l r hl)
    (fun b=>boundedJets_cavityFixedRowLastFieldSquare (M b) s d)
    (cavityFixedRowLastCommonJetBound n) (cavityFixedRowLastCommonJetBound_nonneg n)
    (fun b i H=>norm_cavityFixedRowLastFieldSquare_jet_uniform (M b) s d i H)
  have he: (fun z:ℝ×Field n=>
      cavityOuterPosteriorWeightedMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (M z.1) s) a (k+2) (anisotropicRootEnergyMap D) (f z.1)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput (M z.1) s) (k+2) d)
        (cavityFixedRowOffset n z.2))=
      (fun z=>cavityFixedRowNormalizer (M z.1) s a z.2*cavityFixedRowLastMean (M z.1) s a d z.2):=by
    funext z
    rw [cavityOuterPosteriorWeightedMean_eq_normalizer_mul _ _ (anisotropicSchemeMass_nonneg s)
      _ _ _ _ _ (boundedJets_cavityFixedRowLastFieldSquare (M z.1) s d),
      cavityOuterPosteriorMean_eq_lineField_integral _ _ (anisotropicSchemeMass_nonneg s)
        _ _ _ d hd _ _ (boundedJets_cavityFixedRowLastFieldSquare (M z.1) s d).1.continuous.measurable]
    simp only [cavityOuterPosteriorNormalizer,cavityFixedRowNormalizer,
      cavityFixedRowLastMean,cavityFixedRowLastSquare_eq_field,cavityFixedRowLaw,
      M,f,anisotropicRootEnergyMap_replaceVariance_mixture]
  change Nonempty (CavityMovingRowHeatData _ l r) at hh
  rw [he] at hh
  exact hh

theorem cavityPositiveVarianceRestWeighted_heatData
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a l r : ℝ)
    (hl : 0<l) (hlr : l≤r) (d : ℕ) (hd : d≤k+2) :
    Nonempty (CavityMovingRowHeatData (fun z:ℝ×Field n=>
      cavityFixedRowNormalizer (anisotropicReplaceVariance D (Fin.last n) z.1) s a z.2*
      cavityFixedRowRestMean (anisotropicReplaceVariance D (Fin.last n) z.1) s a d z.2) l r) :=by
  let M:=fun b:ℝ=>anisotropicReplaceVariance D (Fin.last n) b
  let f:=fun b:ℝ=>cavityFixedRowRestFieldSquare (M b) s d
  have hh:=cavityPositiveVarianceWeightedObservable_heatData D s a l r hl hlr d f
    (continuous_cavityFixedRowRestFieldSquare_positive_variance_band D s d l r hl)
    (fun b=>boundedJets_cavityFixedRowRestFieldSquare (M b) s d)
    (cavityFixedRowRestCommonJetBound n) (cavityFixedRowRestCommonJetBound_nonneg n)
    (fun b i H=>norm_cavityFixedRowRestFieldSquare_jet_uniform (M b) s d i H)
  have he: (fun z:ℝ×Field n=>
      cavityOuterPosteriorWeightedMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (M z.1) s) a (k+2) (anisotropicRootEnergyMap D) (f z.1)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput (M z.1) s) (k+2) d)
        (cavityFixedRowOffset n z.2))=
      (fun z=>cavityFixedRowNormalizer (M z.1) s a z.2*cavityFixedRowRestMean (M z.1) s a d z.2):=by
    funext z
    rw [cavityOuterPosteriorWeightedMean_eq_normalizer_mul _ _ (anisotropicSchemeMass_nonneg s)
      _ _ _ _ _ (boundedJets_cavityFixedRowRestFieldSquare (M z.1) s d),
      cavityOuterPosteriorMean_eq_lineField_integral _ _ (anisotropicSchemeMass_nonneg s)
        _ _ _ d hd _ _ (boundedJets_cavityFixedRowRestFieldSquare (M z.1) s d).1.continuous.measurable]
    simp only [cavityOuterPosteriorNormalizer,cavityFixedRowNormalizer,
      cavityFixedRowRestMean,cavityFixedRowRestSquare_eq_field,cavityFixedRowLaw,
      M,f,anisotropicRootEnergyMap_replaceVariance_mixture]
  change Nonempty (CavityMovingRowHeatData _ l r) at hh
  rw [he] at hh
  exact hh

theorem cavityPositiveVarianceProductWeighted_heatData
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a l r : ℝ)
    (hl : 0<l) (hlr : l≤r) (d : ℕ) (hd : d≤k+2) :
    Nonempty (CavityMovingRowHeatData (fun z:ℝ×Field n=>
      cavityFixedRowNormalizer (anisotropicReplaceVariance D (Fin.last n) z.1) s a z.2*
      cavityFixedRowProductMean (anisotropicReplaceVariance D (Fin.last n) z.1) s a d z.2) l r) :=by
  let M:=fun b:ℝ=>anisotropicReplaceVariance D (Fin.last n) b
  let f:=fun b:ℝ=>fun H=>cavityFixedRowLastFieldSquare (M b) s d H*cavityFixedRowRestFieldSquare (M b) s d H
  let G:=cavityProductJetBound (cavityFixedRowLastCommonJetBound n) (cavityFixedRowRestCommonJetBound n)
  have hG(i):0≤G i:=cavityProductJetBound_nonneg _ _
    (cavityFixedRowLastCommonJetBound_nonneg n) (cavityFixedRowRestCommonJetBound_nonneg n) i
  have hh:=cavityPositiveVarianceWeightedObservable_heatData D s a l r hl hlr d f
    ((continuous_cavityFixedRowLastFieldSquare_positive_variance_band D s d l r hl).mul
      (continuous_cavityFixedRowRestFieldSquare_positive_variance_band D s d l r hl))
    (fun b=>boundedJets_cavityFixedRowProductFieldSquare (M b) s d)
    G hG (fun b i H=>norm_cavityFixedRowProductFieldSquare_jet_uniform (M b) s d i H)
  have he: (fun z:ℝ×Field n=>
      cavityOuterPosteriorWeightedMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (M z.1) s) a (k+2) (anisotropicRootEnergyMap D) (f z.1)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput (M z.1) s) (k+2) d)
        (cavityFixedRowOffset n z.2))=
      (fun z=>cavityFixedRowNormalizer (M z.1) s a z.2*cavityFixedRowProductMean (M z.1) s a d z.2):=by
    funext z
    rw [cavityOuterPosteriorWeightedMean_eq_normalizer_mul _ _ (anisotropicSchemeMass_nonneg s)
      _ _ _ _ _ (boundedJets_cavityFixedRowProductFieldSquare (M z.1) s d),
      cavityOuterPosteriorMean_eq_lineField_integral _ _ (anisotropicSchemeMass_nonneg s)
        _ _ _ d hd _ _ (boundedJets_cavityFixedRowProductFieldSquare (M z.1) s d).1.continuous.measurable]
    simp only [cavityOuterPosteriorNormalizer,cavityFixedRowNormalizer,
      cavityFixedRowProductMean,cavityFixedRowLastSquare_eq_field,cavityFixedRowRestSquare_eq_field,
      cavityFixedRowLaw,M,f,anisotropicRootEnergyMap_replaceVariance_mixture]
  change Nonempty (CavityMovingRowHeatData _ l r) at hh
  rw [he] at hh
  exact hh

theorem exists_cavityFixedRowMovingHeatData (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    ∃l r:ℝ,0<l ∧ followupCavityD n beta rho∈Ioo l r ∧
      Nonempty (CavityMovingRowHeatData (cavityFixedRowMovingNormalizer (n:=n) beta rho hbeta hrho s a) l r) ∧
      Nonempty (CavityMovingRowHeatData (fun z=>cavityFixedRowMovingNormalizer (n:=n) beta rho hbeta hrho s a z*
        cavityFixedRowMovingLastMean beta rho hbeta hrho s a d z) l r) ∧
      Nonempty (CavityMovingRowHeatData (fun z=>cavityFixedRowMovingNormalizer (n:=n) beta rho hbeta hrho s a z*
        cavityFixedRowMovingRestMean beta rho hbeta hrho s a d z) l r) ∧
      Nonempty (CavityMovingRowHeatData (fun z=>cavityFixedRowMovingNormalizer (n:=n) beta rho hbeta hrho s a z*
        cavityFixedRowMovingProductMean beta rho hbeta hrho s a d z) l r) :=by
  let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
  let v:=followupCavityD n beta rho
  have hv:0<v:=by
    have hh:=D0.variance_pos (Fin.last n)
    simpa only [D0,followupCavitySpinModel_variance_last,followupCavityB_zero,v] using hh
  let l:=v/2
  let r:=2*v
  have hl:0<l:=by dsimp only [l];linarith
  have hlr:l≤r:=by dsimp only [l,r];linarith
  refine ⟨l,r,hl,⟨by dsimp only [l];linarith,by dsimp only [r];linarith⟩,?_,?_,?_,?_⟩
  · exact cavityPositiveVarianceNormalizer_heatData D0 s a l r hl hlr
  · exact cavityPositiveVarianceLastWeighted_heatData D0 s a l r hl hlr d hd
  · exact cavityPositiveVarianceRestWeighted_heatData D0 s a l r hl hlr d hd
  · exact cavityPositiveVarianceProductWeighted_heatData D0 s a l r hl hlr d hd

end QuantitativeFollowup
