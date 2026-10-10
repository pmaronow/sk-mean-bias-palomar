module
public import QuantitativeFollowup.FollowupCavityPathScore
public import FourPapersCommon.FiniteCascadeTerminalVertices
public import FourPapersCommon.FiniteWeightedGram

@[expose] public section

/-! Actual selected increment directions at every charged and terminal
vertex. They are the shared-path coefficients of the physical overlap clock. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavitySelectedEdgeMask_projection (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (e : GaussianCoordinateIndex (Fin n) T) :
    finiteCascadeEdgeMultiplier (cavitySelectedPathMask i) T e=
      if cavitySelectedEdgeMask i T e then 1 else 0 := by
  induction T with
  | leaf => exact Empty.elim e
  | advance T ih =>
    cases e with
    | inl l => simp [finiteCascadeEdgeMultiplier,cavitySelectedEdgeMask,cavitySelectedPathMask]
    | inr e => exact ih e
  | fork T U ihT ihU =>
    cases e with
    | inl e => exact ihT e
    | inr e => exact ihU e

theorem finiteCascadePathCoefficient_eq_zero_of_unselected (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (e : GaussianCoordinateIndex (Fin n) T) (he : cavitySelectedEdgeMask i T e=false) :
    finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e=0 := by
  induction v with
  | root T => rfl
  | @child j T v ih =>
    cases e with
    | inl l =>
      have hli : l≠i:=by simpa only [cavitySelectedEdgeMask,Sum.elim_inl,decide_eq_false_iff_not] using he
      simp only [finiteCascadePathCoefficient,Sum.elim_inl,if_neg hli]
    | inr e => exact ih e he
  | left v ih =>
    cases e with
    | inl e => exact ih e he
    | inr e => rfl
  | right v ih =>
    cases e with
    | inl e => rfl
    | inr e => exact ih e he

theorem cavityPathVertexField_selected_single (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (e : GaussianCoordinateIndex (Fin n) T) (he : cavitySelectedEdgeMask i T e=true) :
    cavityPathVertexField D s i T v (EuclideanSpace.single (Sum.inr e) 1)=
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i v e • cavityCoordinateFeature i := by
  classical
  have hleft : finiteGaussianLeft
      (EuclideanSpace.single (Sum.inr e) 1 : CavityPathGaussianSpace T n)=0:=by
    ext l
    simp [finiteGaussianLeft,PiLp.single_apply]
  have hright : finiteGaussianRight
      (EuclideanSpace.single (Sum.inr e) 1 : CavityPathGaussianSpace T n)=EuclideanSpace.single e 1:=by
    ext l
    simp [finiteGaussianRight,PiLp.single_apply]
  have hproj : finiteGaussianDiagonal (finiteCascadeEdgeMultiplier (cavitySelectedPathMask i) T)
      (EuclideanSpace.single e 1)=EuclideanSpace.single e 1:=by
    rw [finiteGaussianDiagonal_single,cavitySelectedEdgeMask_projection,he]
    simp
  change finiteCascadeRecordVertexCLM _ T v
    (anisotropicRootEnergyMap D (finiteGaussianLeft _),finiteGaussianRight _)=_
  rw [hleft,hright,map_zero]
  have hh:=cavitySelectedPathFieldCLM_single D s i T v e
  unfold cavitySelectedPathFieldCLM at hh
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,hproj] at hh
  exact hh

theorem cavityPathTerminalEnergy_eq_vertex_sum (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (y : CavityPathGaussianSpace T n) :
    cavityPathTerminalEnergy D s i T σ y=
      ((finiteCascadeTerminalVertices T σ).map (fun c=>cavityPathVertexField D s i T c.1 y c.2)).sum :=
  finiteCascadeReferenceTerminalEnergy_eq_vertex_sum _ T σ
    (anisotropicRootEnergyMap D (finiteGaussianLeft y)) (finiteGaussianRight y)

def cavityPathSelectedVertexMean (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (y : CavityPathGaussianSpace T n)
    (v : FiniteCascadeRecordVertex T) : ℝ :=
  fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth)
      (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i)

def cavityPathSignedMarks (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (b : ℝ) (y : CavityPathGaussianSpace T n) : List (ℝ×FiniteCascadeRecordVertex T) :=
  (finiteCascadeTerminalVertices T σ).map (fun c=>(Paper.spinSign (c.2 i),c.1)) ++
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
      (fun c=>(-c.1*cavityPathSelectedVertexMean D s i T b y c.2,c.2))

theorem cavityPathSpatialScore_selected_single (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n)
    (e : GaussianCoordinateIndex (Fin n) T) (he : cavitySelectedEdgeMask i T e=true) :
    cavityPathSpatialScore D s a i T σ b y (EuclideanSpace.single (Sum.inr e) 1)=
      ((cavityPathSignedMarks D s a i T σ b y).map (fun c=>
        c.1*finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e)).sum := by
  unfold cavityPathSpatialScore chargedDirectionalScore
  rw [cavityPathTerminalEnergy_eq_vertex_sum]
  simp_rw [cavityPathVertexField_selected_single D s i T _ e he]
  simp only [PiLp.smul_apply,smul_eq_mul,map_smul,cavityCoordinateFeature_apply]
  unfold cavityPathSignedMarks cavityPathSelectedVertexMean
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def]
  have ht : ((finiteCascadeTerminalVertices T σ).map (fun c=>
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.1 e*Paper.spinSign (c.2 i))).sum=
      ((finiteCascadeTerminalVertices T σ).map (fun c=>
        Paper.spinSign (c.2 i)*finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.1 e)).sum:=by
    apply congrArg List.sum
    apply List.map_congr_left
    intro c _
    ring
  rw [ht]
  have hc : ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
      -c.1*fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth)
          (cavityPathVertexField D s i T c.2 y) (cavityCoordinateFeature i)*
            finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e)).sum=
      -((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
        c.1*(finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) i c.2 e*
          fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
            (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) c.2.depth)
              (cavityPathVertexField D s i T c.2 y) (cavityCoordinateFeature i)))).sum:=by
    generalize finiteCascadeVertexCharges (anisotropicSchemeMass s) a T=cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      ring
  rw [hc]
  ring

end QuantitativeFollowup
