module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFutureSelector
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarNodeJets
public import QuantitativeFollowup.FollowupCavityDecouplingCovariance
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestFutureAlias

@[expose] public section

/-! The selected binary-feature future term is the product of the genuine
rest and scalar restarted expectations. All original nodes, including
repeated levels, are retained before any integration or differentiation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteIncidentFutureSquare_average_eq_native_product
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J p : ℕ) (hJ : J≤k+2) (hp : p≤J)
    (P : AnisotropicParameter (n+1)) (g : AnisotropicDisorder n)
    (x : QuantitativePaper.Field n) (y : ℝ)
    (hrest : cavityRestParameterProjection n P=
      anisotropicDisorderInjection n g+anisotropicFieldInjection n x)
    (hlast : P (Sum.inr (Fin.last n))=y)
    (q r : Paper.Overlap) (hq : (q:ℝ)=s.q (k+2-J))
    (hr : (r:ℝ)=s.q (k+2-p)) (hqr : (q:ℝ)≤r) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    (∑i : Fin n,cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)=
      anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g q x r*
      scalarFutureSquare (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s) q r hqr y :=by
  dsimp only
  have hnode : scalarSchemeTransportNode s (k+2-p)=r :=by
    apply Subtype.ext
    exact (scalarSchemeTransportNode_coe s (k+2-p) (by omega)).trans hr.symm
  have hmeshq : anisotropicFiniteMeshNode s (k+2-J)=q :=by
    apply Subtype.ext
    exact (anisotropicFiniteMeshNode_coe s (k+2-J) (by omega)).trans hq.symm
  have hmeshr : anisotropicFiniteMeshNode s (k+2-p)=r :=by
    apply Subtype.ext
    exact (anisotropicFiniteMeshNode_coe s (k+2-p) (by omega)).trans hr.symm
  have hs (i : Fin n) :
      cavityFiniteFutureSquare (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩)
        s J (anisotropicEnergyMap (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) P)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r=
      cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (J-p) i
        (cavityRestParameterProjection n P)*
      cavityFiniteRowFutureScalarSquare s (followupCavityScalarBeta n β ρ) p (J-p)
        (P (Sum.inr (Fin.last n))) :=by
    rw [←hnode]
    exact cavityFiniteIncidentFutureSquare_node_zero s n β ρ hβ hρ J p hJ hp P i
  simp_rw [hs,hrest,hlast]
  rw [←Finset.sum_mul]
  have he : ((∑i : Fin n,cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (J-p) i
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))*
      cavityFiniteRowFutureScalarSquare s (followupCavityScalarBeta n β ρ) p (J-p) y)/(n:ℝ)=
      ((∑i : Fin n,cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (J-p) i
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))/(n:ℝ))*
      cavityFiniteRowFutureScalarSquare s (followupCavityScalarBeta n β ρ) p (J-p) y :=by ring
  rw [he,cavityFiniteRowFutureRestSquare_average_eq_native s β ρ hβ hρ p J hp hJ g x,
    hmeshq,hmeshr,cavityFiniteRowFutureScalarSquare_eq_native s _
      (followupCavityScalarBeta_pos n β ρ hβ hρ) p J hp hJ q r hq hr hqr y]

theorem cavityFiniteIncidentFutureSquare_average_at_native_scheme_node
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J p : ℕ) (hJ : J≤k+2) (hp : p≤J)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let r:=anisotropicSchemeNode s (k+2-p) (by omega)
    let z:=cavityRestSampleProjection n sample
    let hqr : (q:ℝ)≤r:=s.q_mono' _ (by omega) _ (by omega)
    (∑i : Fin n,cavityFiniteFutureSquare D s J
      (anisotropicEnergyMap D (anisotropicProcessParameter D μ q sample))
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)=
      anisotropicRestartMeanSquare Rest μ z.1 q (anisotropicMeasureState Rest μ q z) r*
        scalarFutureSquareProcess (followupCavityScalarBeta n β ρ) μ q r hqr
          (sample.2 (Fin.last n)) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let r:=anisotropicSchemeNode s (k+2-p) (by omega)
  let z:=cavityRestSampleProjection n sample
  have hrest : cavityRestParameterProjection n (anisotropicProcessParameter D μ q sample)=
      anisotropicDisorderInjection n z.1+
        anisotropicFieldInjection n (anisotropicMeasureState Rest μ q z) :=by
    rw [cavityRestProcessParameter_zero μ n β ρ hβ hρ q sample]
    rfl
  have hlast : anisotropicProcessParameter D μ q sample (Sum.inr (Fin.last n))=
      parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q
        (sample.2 (Fin.last n)) :=
    cavityZeroLastProcessParameter_eq_scalarState μ n β ρ hβ hρ q sample
  exact cavityFiniteIncidentFutureSquare_average_eq_native_product s n β ρ hβ hρ J p hJ hp
    (anisotropicProcessParameter D μ q sample) z.1 (anisotropicMeasureState Rest μ q z)
    (parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ q (sample.2 (Fin.last n)))
    hrest hlast q r rfl rfl (s.q_mono' _ (by omega) _ (by omega))

theorem cavityFiniteIncidentFutureSquare_average_at_native_scheme_node_eq_rest_future
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (J p : ℕ) (hJ : J≤k+2) (hp : p≤J)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let r:=anisotropicSchemeNode s (k+2-p) (by omega)
    let z:=cavityRestSampleProjection n sample
    let hqr : (q:ℝ)≤r:=s.q_mono' _ (by omega) _ (by omega)
    (∑i : Fin n,cavityFiniteFutureSquare D s J
      (anisotropicEnergyMap D (anisotropicProcessParameter D μ q sample))
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n:ℝ)=
      cavityRestFutureSquare Rest μ q r z*
        scalarFutureSquareProcess (followupCavityScalarBeta n β ρ) μ q r hqr
          (sample.2 (Fin.last n)) :=by
  dsimp only
  have hqr : anisotropicSchemeNode s (k+2-J) (by omega) ≤
      anisotropicSchemeNode s (k+2-p) (by omega):=s.q_mono' _ (by omega) _ (by omega)
  rw [cavityRestFutureSquare_eq_restartMeanSquare _ _ _ _ hqr]
  exact cavityFiniteIncidentFutureSquare_average_at_native_scheme_node s n β ρ hβ hρ J p hJ hp sample

end QuantitativeFollowup
