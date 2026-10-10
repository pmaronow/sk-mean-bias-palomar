module
public import QuantitativeFollowup.FollowupCavityPathRecordedScore
public import QuantitativeFollowup.FollowupCavityPhysicalRowResponse

@[expose] public section

/-! Root disorder directions are shared terminal features at every retained
vertex. Their literal Hessian score is the actual recorded row curvature. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityPathVertexField_root_single (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (e : AnisotropicCouplingIndex n) :
    cavityPathVertexField D s i T v (EuclideanSpace.single (Sum.inl e) 1)=
      D.coupling e • anisotropicCouplingFeature e := by
  classical
  have hleft : finiteGaussianLeft
      (EuclideanSpace.single (Sum.inl e) 1 : CavityPathGaussianSpace T n)=EuclideanSpace.single e 1:=by
    ext l
    simp [finiteGaussianLeft,PiLp.single_apply]
  have hright : finiteGaussianRight
      (EuclideanSpace.single (Sum.inl e) 1 : CavityPathGaussianSpace T n)=0:=by
    ext l
    simp [finiteGaussianRight,PiLp.single_apply]
  change finiteCascadeRecordVertexCLM _ T v (anisotropicRootEnergyMap D (finiteGaussianLeft _),finiteGaussianRight _)=_
  rw [hleft,hright,finiteCascadeRecordVertexCLM_initial]
  ext σ
  simp only [anisotropicRootEnergyMap_single,PiLp.smul_apply,smul_eq_mul]

theorem finiteCascadeTreeTerminalFeature_eq_vertex_marks {S : Type} [Fintype S]
    (K : FiniteStateField S) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (p : Records (FiniteStateField S) S T) :
    finiteCascadeTreeTerminalFeature K T p=
      ((finiteCascadeTerminalVertices T (finiteCascadeRecordTerminalSpins T p)).map
        (fun c=>K c.2)).sum := by
  induction T with
  | leaf => simp only [finiteCascadeTreeTerminalFeature,finiteCascadeRecordTerminalSpins,
      finiteCascadeTerminalVertices,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,id_eq]
  | advance T ih => simpa only [finiteCascadeTreeTerminalFeature,finiteCascadeRecordTerminalSpins,
      finiteCascadeTerminalVertices,Function.comp_def,List.map_map] using ih p.2
  | fork T U ihT ihU =>
    rcases p with ⟨pT,pU⟩
    simpa only [finiteCascadeTreeTerminalFeature,finiteCascadeRecordTerminalSpins,finiteCascadeTerminalVertices,
      List.map_append,List.sum_append,List.map_map,Function.comp_def,Prod.map_apply] using
      congrArg₂ (·+·) (ihT pT) (ihU pU)

def cavityPathRecordFeatureCurvature (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ)
    (e : AnisotropicCouplingIndex n) (p : CavityPathRecordSpace T n) : ℝ :=
  finiteCascadeIntrinsicRowCurvature (fun _ : Configuration n=>0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T p

theorem cavityPathRecordFeatureCurvature_vertex_formula (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ)
    (e : AnisotropicCouplingIndex n) (p : CavityPathRecordSpace T n) :
    cavityPathRecordFeatureCurvature D s a i T b e p=
      (finiteCascadeTreeTerminalFeature (anisotropicCouplingFeature e) T p.2-
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>c.1*
          fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
            (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth)
              (c.2.field p.1 p.2) (anisotropicCouplingFeature e))).sum)^2-
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>c.1*
          fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
            (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth))
              (c.2.field p.1 p.2) (anisotropicCouplingFeature e) (anisotropicCouplingFeature e))).sum := by
  unfold cavityPathRecordFeatureCurvature finiteCascadeIntrinsicRowCurvature finiteCascadeTreeGaussianRowCurvature
  rw [finiteCascadeTreeFeatureScore_eq_vertex_sum,finiteCascadeTreeFeatureSecondCharge_eq_vertex_sum]
  simp only [zero_smul,add_zero,finiteCascadeShiftRecords_zero]

theorem cavityPath_root_hessian_recorded_curvature (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n)
    (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (fderiv ℝ (fun z=>cavityPathNumerator D s a i T σ (b,z))) y
      (EuclideanSpace.single (Sum.inl e) 1) (EuclideanSpace.single (Sum.inl e) 1)=
      cavityPathNumerator D s a i T σ (b,y)*(D.coupling e)^2*
        cavityPathRecordFeatureCurvature D s a i T b e (cavityPathFixedRecord D s i T σ y) := by
  rw [hessian_cavityPathNumerator_spatial,cavityPathRecordFeatureCurvature_vertex_formula]
  have hterm := finiteCascadeTreeTerminalFeature_eq_vertex_marks (anisotropicCouplingFeature e) T
    (cavityPathFixedRecord D s i T σ y).2
  have hsp:=finiteCascadeRecordTerminalSpins_referenceRoot
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T (anisotropicRootEnergyMap D) 0 y σ
  change finiteCascadeRecordTerminalSpins T (cavityPathFixedRecord D s i T σ y).2=σ at hsp
  rw [hsp] at hterm
  simp_rw [cavityPathVertexField_eq_fixed_record]
  unfold cavityPathSpatialScore chargedDirectionalScore cavityPathSpatialSecondCharge chargedDirectionalCurvature
    exponentialDensityHessian
  rw [cavityPathTerminalEnergy_eq_vertex_sum]
  simp_rw [cavityPathVertexField_root_single D s i T _ e]
  simp only [PiLp.smul_apply,smul_eq_mul,map_smul,ContinuousLinearMap.smul_apply]
  rw [hterm]
  have ht := List.sum_map_mul_left (finiteCascadeTerminalVertices T σ)
    (fun c=>anisotropicCouplingFeature e c.2) (D.coupling e)
  have hmean := List.sum_map_mul_left (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun c=>c.1*fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth)
        (cavityPathVertexField D s i T c.2 y) (anisotropicCouplingFeature e)) (D.coupling e)
  have hH := List.sum_map_mul_left (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun c=>c.1*fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth))
        (cavityPathVertexField D s i T c.2 y) (anisotropicCouplingFeature e) (anisotropicCouplingFeature e))
          ((D.coupling e)^2)
  have hmEq : ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
      c.1*(D.coupling e*fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth)
          (cavityPathVertexField D s i T c.2 y) (anisotropicCouplingFeature e)))).sum=
      D.coupling e*((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
        c.1*fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth)
            (cavityPathVertexField D s i T c.2 y) (anisotropicCouplingFeature e))).sum := by
    rw [←hmean]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c _
    ring
  rw [ht,hmEq]
  have hhEq : ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>c.1*
      (D.coupling e*(D.coupling e*fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade
        (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
          (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth))
            (cavityPathVertexField D s i T c.2 y) (anisotropicCouplingFeature e) (anisotropicCouplingFeature e))))).sum=
      (D.coupling e)^2*((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>c.1*
        fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth))
            (cavityPathVertexField D s i T c.2 y) (anisotropicCouplingFeature e) (anisotropicCouplingFeature e))).sum := by
    rw [←hH]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c _
    ring
  rw [hhEq]
  ring

end QuantitativeFollowup
