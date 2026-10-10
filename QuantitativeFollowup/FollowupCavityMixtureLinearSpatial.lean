module
public import QuantitativeFollowup.FollowupCavityMixtureJointSpatial
public import QuantitativePaper.GaussianColeHopfCoordinateJets

@[expose] public section

/-! Genuine spatial two-jet data survives the physical fixed incident-row
linear energy map. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
variable {P E G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
set_option maxHeartbeats 1300000

theorem CavityJointSpatialTwoJets.comp_linear {F : P×E→ℝ}
    (hF : CavityJointSpatialTwoJets F) (A : G→L[ℝ]E) :
    CavityJointSpatialTwoJets (fun z:P×G=>F (z.1,A z.2)) :=by
  have he(p)(x):fderiv ℝ (fun y=>F (p,A y)) x=
    (fderiv ℝ (fun y=>F (p,y)) (A x)).comp A :=
    (((hF.smooth p).differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt).fderiv
  have hc:Continuous (fun z:P×G=>(z.1,A z.2)):=
    continuous_fst.prodMk (A.continuous.comp continuous_snd)
  have hf:Continuous (fun z:P×G=>fderiv ℝ (fun y=>F (z.1,A y)) z.2):=by
    simp_rw [he]
    exact (hF.first.comp hc).clm_comp continuous_const
  refine ⟨fun p=>(hF.smooth p).comp A.contDiff,hF.value.comp hc,hf,?_⟩
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_clm_apply.mpr
  intro w
  have hh(p)(x):fderiv ℝ (fderiv ℝ (fun y=>F (p,A y))) x v w=
    fderiv ℝ (fderiv ℝ (fun y=>F (p,y))) (A x) (A v) (A w) :=by
    let M : (E→L[ℝ]ℝ)→L[ℝ](G→L[ℝ]ℝ):=
      (ContinuousLinearMap.compL ℝ G E ℝ).flip A
    have hs:ContDiff ℝ ∞ (fderiv ℝ (fun y=>F (p,y))):=(hF.smooth p).fderiv_right (by simp)
    have hfun:fderiv ℝ (fun y=>F (p,A y))=M ∘ fderiv ℝ (fun y=>F (p,y)) ∘ A:=funext (he p)
    rw [hfun]
    have hd:=M.hasFDerivAt.comp x ((hs.differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt)
    rw [hd.fderiv]
    rfl
  simp_rw [hh]
  exact ((hF.second.comp hc).clm_apply continuous_const).clm_apply continuous_const

theorem norm_cavitySpatialJet_comp_linear {F : E→ℝ} (hF : ContDiff ℝ ∞ F)
    (A : G→L[ℝ]E) (r : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ r (fun y=>F (A y)) x‖≤
      ‖iteratedFDeriv ℝ r F (A x)‖*‖A‖^r :=by
  change ‖iteratedFDeriv ℝ r (F ∘ A) x‖≤_
  rw [iteratedFDeriv_comp_linear_on_open F univ isOpen_univ (hF.of_le (by simp)).contDiffOn le_rfl A x (mem_univ _)]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ r F (A x)) (fun _=>A)

end QuantitativeFollowup
