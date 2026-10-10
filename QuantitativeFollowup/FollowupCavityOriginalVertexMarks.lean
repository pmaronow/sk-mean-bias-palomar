module
public import FourPapersCommon.FiniteCascadeSingleVertexMarks
public import QuantitativeFollowup.FollowupCavityOriginalPairDefect

@[expose] public section

/-! Original-fresh overlap marks. An original terminal spin stays in the
record, while the extra mark is a genuine normalized continuation from
the retained vertex. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def anisotropicSingleVertexMarkedLaw (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T)) :=
  finiteCascadeSingleVertexMarkedLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) v (anisotropicTrimmedRecordedTreeLaw D s a T)

instance anisotropicSingleVertexMarkedLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) : IsProbabilityMeasure (anisotropicSingleVertexMarkedLaw D s a T v) :=
  finiteCascadeSingleVertexMarkedLaw_probability _ _ (anisotropicSchemeMass_nonneg s) _ _ _

theorem anisotropicSingleVertexMarkedLaw_fst (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) :
    (anisotropicSingleVertexMarkedLaw D s a T v).fst=anisotropicTrimmedRecordedTreeLaw D s a T :=
  finiteCascadeSingleVertexMarkedLaw_fst _ _ (anisotropicSchemeMass_nonneg s) _ _ _

def cavityOriginalVertexOverlapSum (n : ℕ) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (σ : TerminalSpins (Configuration (n+1)) (trimRoot T)) (τ : Configuration (n+1)) : ℝ :=
  ((finiteCascadeTerminalVertices (trimRoot T) σ).map (fun c=>
    cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 v) c.2 τ)).sum

def cavityOriginalVertexConditionalSum (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  ((finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)).map
    (fun c=>(∑l : Fin n,anisotropicCouplingFeature (cavityIncidentEdge l) c.2*
      anisotropicVertexMean D s v (anisotropicCouplingFeature (cavityIncidentEdge l)) r)/(n:ℝ)-
      cavityPhysicalCommonOverlap s (trimRoot T) c.1 v*Paper.spinSign (c.2 (Fin.last n))*
        anisotropicVertexMean D s v (cavityCoordinateFeature (Fin.last n)) r)).sum

private theorem integral_list_map_sum_real {Ω A : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (xs : List A) (f : A→Ω→ℝ) (hf : ∀a,Integrable (f a) P) :
    (∫ω,(xs.map (fun a=>f a ω)).sum∂P)=(xs.map (fun a=>∫ω,f a ω∂P)).sum := by
  have hii (ys : List A) : Integrable (fun ω=>(ys.map (fun a=>f a ω)).sum) P := by
    induction ys with
    | nil => exact integrable_zero _ _ _
    | cons a ys ih =>
      simp only [List.map_cons,List.sum_cons]
      convert! (hf a).add ih using 1
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hf a) (hii xs),ih]

theorem integral_cavityGibbsKernel_original_overlap (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (j : ℕ) (H : FiniteStateField (Configuration (n+1)))
    (q : ℝ) (σ : Configuration (n+1)) :
    (∫τ,cavitySpinOverlapDefect n q σ τ ∂finiteStateCascadeGibbsKernel
      (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j H)=
      (∑l : Fin n,anisotropicCouplingFeature (cavityIncidentEdge l) σ*
        fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j) H
            (anisotropicCouplingFeature (cavityIncidentEdge l)))/(n:ℝ)-
        q*Paper.spinSign (σ (Fin.last n))*
          fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
            (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j) H (cavityCoordinateFeature (Fin.last n)) := by
  have := isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
  unfold cavitySpinOverlapDefect
  rw [integral_sub (Integrable.of_finite.div_const _) ((Integrable.of_finite).const_mul _),
    integral_div,integral_finset_sum _ (fun _ _=>Integrable.of_finite)]
  simp_rw [integral_const_mul,←fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _
    (anisotropicSchemeMass_nonneg s)]
  rfl

theorem integral_anisotropicSingleVertexMarkedLaw_original_overlap
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫z,F z.1*cavityOriginalVertexOverlapSum n s T v
      (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2
      ∂anisotropicSingleVertexMarkedLaw D s a T v)=
      ∫r,F r*cavityOriginalVertexConditionalSum D s T v r
        ∂anisotropicTrimmedRecordedTreeLaw D s a T := by
  classical
  let A:=fun z : TerminalSpins (Configuration (n+1)) (trimRoot T)×Configuration (n+1)=>
    cavityOriginalVertexOverlapSum n s T v z.1 z.2
  let B : ℝ:=∑z : TerminalSpins (Configuration (n+1)) (trimRoot T)×Configuration (n+1),|A z|
  have hb (z) : |A z|≤B:=Finset.single_le_sum (f:=fun z=>|A z|) (fun _ _=>abs_nonneg _) (Finset.mem_univ z)
  have hspin : Measurable (fun z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
      (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2,z.2)) :=
    ((measurable_finiteCascadeRecordTerminalSpins _).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hm : Measurable (fun z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
      F z.1*A (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2,z.2)) :=
    (hF.comp measurable_fst).mul ((measurable_of_finite A).comp hspin)
  have hi : Integrable (fun z=>F z.1*A (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2,z.2))
      (anisotropicSingleVertexMarkedLaw D s a T v) := by
    apply (integrable_const (C*B)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖F z.1*A (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2,z.2)‖≤_
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb z.1) (hb _) (abs_nonneg _) hC
  have := finiteCascadeSingleVertexKernel_markov (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) v
  have := isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) v.depth
  rw [anisotropicSingleVertexMarkedLaw,finiteCascadeSingleVertexMarkedLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only [A]
    rw [finiteCascadeSingleVertexKernel,Kernel.comap_apply,integral_const_mul]
    congr 1
    unfold cavityOriginalVertexOverlapSum cavityOriginalVertexConditionalSum
    rw [integral_list_map_sum_real _ _ _ (fun _=>Integrable.of_finite)]
    simp_rw [integral_cavityGibbsKernel_original_overlap]
    rfl

theorem cavityRecordedOriginalVertexDefect_eq_vertex_sum (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityRecordedOriginalVertexDefect D s a T b r=
      ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
        c.1*cavityOriginalVertexConditionalSum (anisotropicReplaceVariance D (Fin.last n) b) s T c.2 r)).sum := by
  unfold cavityRecordedOriginalVertexDefect
  rw [list_double_sum_comm_real]
  simp only [cavityRecordedMarkPairDefect,cavityRecordedMarkIncidentMean,cavityRecordedMarkEpsilonMean,
    cavityRecordedMarkVertex,Sum.elim_inl,Sum.elim_inr]
  unfold cavityOriginalVertexConditionalSum
  simp_rw [List.sum_map_mul_left]
  rfl

end QuantitativeFollowup
