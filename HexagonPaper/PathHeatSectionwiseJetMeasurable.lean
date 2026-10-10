module
public import HexagonPaper.PathHeatSignedJetMeasurable
public import HexagonPaper.PathHeatSectionwiseAnalyticSource

@[expose] public section

/-! Actual signed jets of a sectionwise source are weakly Borel measurable
jointly in all variables, although their total-variation continuity is only
assumed with the auxiliary variables fixed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem measurable_pathHeatAuxiliaryReassociationInverse
    {Z A V : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace V] :
    Measurable (fun u : Z×(A×V)=>((u.1,u.2.1),u.2.2)) :=
  (MeasurableEquiv.prodAssoc (α:=Z) (β:=A) (γ:=V)).symm.measurable

section Reassociation
variable {Z E K X : Type*}
  [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace K]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] [SecondCountableTopology X]

theorem continuous_pathHeatSectionwise_reassociated_ell
    (d : PathHeatSectionwiseSignedSource Z E K X) :
    Continuous (fun u : (Z×(E×K))×C(X,ℝ)=>d.ell (u.1.1,(u.1.2,u.2))) :=
  d.continuous_ell.comp (Homeomorph.prodAssoc Z (E×K) C(X,ℝ)).continuous

theorem continuous_pathHeatSectionwise_reassociated_phi
    (d : PathHeatSectionwiseSignedSource Z E K X) :
    Continuous (fun u : (Z×(E×K))×C(X,ℝ)=>d.phi (u.1.1,(u.1.2,u.2))) :=
  d.continuous_phi.comp (Homeomorph.prodAssoc Z (E×K) C(X,ℝ)).continuous

end Reassociation

variable {E K X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {a b : ℝ}
local instance : MeasurableSpace C(X,ℝ) := borel C(X,ℝ)
local instance : BorelSpace C(X,ℝ) := ⟨rfl⟩

theorem measurable_pathHeatSectionwise_score
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C) (h : C(X,ℝ)) :
    Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>pathHeatSignedScore (d.S θ) h) := by
  let fseq : ℕ→Icc a b×((E×K)×C(X,ℝ))→ℝ := fun n θ=>
    (n:ℝ)*(d.ell (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))-d.ell θ)
  apply measurable_of_tendsto_metrizable (f:=fseq)
  · intro n
    have ht : Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>
        (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.add_const _))
    exact measurable_const.mul ((d.continuous_ell.measurable.comp ht).sub d.continuous_ell.measurable)
  · rw [tendsto_pi_nhds]
    intro θ
    exact ((hs.ell_derivative θ.1 θ.2.1 θ.2.2).lim_real h).comp
      tendsto_natCast_atTop_atTop

theorem measurable_pathHeatSectionwise_phi_score
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C) (h : C(X,ℝ)) :
    Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>pathHeatSignedScore (d.P θ) h) := by
  let fseq : ℕ→Icc a b×((E×K)×C(X,ℝ))→ℝ := fun n θ=>
    (n:ℝ)*(d.phi (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))-d.phi θ)
  apply measurable_of_tendsto_metrizable (f:=fseq)
  · intro n
    have ht : Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>
        (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.add_const _))
    exact measurable_const.mul ((d.continuous_phi.measurable.comp ht).sub d.continuous_phi.measurable)
  · rw [tendsto_pi_nhds]
    intro θ
    exact ((hs.phi_derivative θ.1 θ.2.1 θ.2.2).lim_real h).comp
      tendsto_natCast_atTop_atTop

theorem measurable_pathHeatSectionwise_hessian
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C) (h k : C(X,ℝ)) :
    Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>pathHeatSignedHessian (d.M θ) h k) := by
  let fseq : ℕ→Icc a b×((E×K)×C(X,ℝ))→ℝ := fun n θ=>
    (n:ℝ)*(pathHeatSignedScore (d.S (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))) k-
      pathHeatSignedScore (d.S θ) k)
  have hm := measurable_pathHeatSectionwise_score hab d C hs k
  apply measurable_of_tendsto_metrizable (f:=fseq)
  · intro n
    have ht : Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>
        (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.add_const _))
    exact measurable_const.mul ((hm.comp ht).sub hm)
  · rw [tendsto_pi_nhds]
    intro θ
    have hd := ((hs.score_derivative θ.1 θ.2.1 θ.2.2).lim_real h).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop)
    have he := (ContinuousLinearMap.apply ℝ ℝ k).continuous.continuousAt.tendsto.comp hd
    simpa only [Function.comp_def,fseq,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply,smul_eq_mul,ContinuousLinearMap.apply_apply,Prod.mk.eta] using he

theorem measurable_pathHeatSectionwise_phi_hessian
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C) (h k : C(X,ℝ)) :
    Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>pathHeatSignedHessian (d.Q θ) h k) := by
  let fseq : ℕ→Icc a b×((E×K)×C(X,ℝ))→ℝ := fun n θ=>
    (n:ℝ)*(pathHeatSignedScore (d.P (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))) k-
      pathHeatSignedScore (d.P θ) k)
  have hm := measurable_pathHeatSectionwise_phi_score hab d C hs k
  apply measurable_of_tendsto_metrizable (f:=fseq)
  · intro n
    have ht : Measurable (fun θ : Icc a b×((E×K)×C(X,ℝ))=>
        (θ.1,(θ.2.1,θ.2.2+(n:ℝ)⁻¹ • h))) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.add_const _))
    exact measurable_const.mul ((hm.comp ht).sub hm)
  · rw [tendsto_pi_nhds]
    intro θ
    have hd := ((hs.phi_score_derivative θ.1 θ.2.1 θ.2.2).lim_real h).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop)
    have he := (ContinuousLinearMap.apply ℝ ℝ k).continuous.continuousAt.tendsto.comp hd
    simpa only [Function.comp_def,fseq,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply,smul_eq_mul,ContinuousLinearMap.apply_apply,Prod.mk.eta] using he


end HexagonPaper
