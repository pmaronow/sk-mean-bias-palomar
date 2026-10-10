module
public import FourPapersCommon.FiniteCascadeFutureMarks
public import QuantitativeFollowup.FollowupCavityOverlapMarks
public import QuantitativeFollowup.FollowupCavityRowStieltjesCurvature

@[expose] public section

/-! Literal future marks for the physical cavity tree. The pair shares the
genuine continuation field until the requested future node, then uses two
independent normalized terminal continuations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def anisotropicFutureVertexMarkedLaw (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) :=
  finiteCascadeFutureMarkedLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) v (cavityFiniteFutureDepth s v.depth q)
      (anisotropicTrimmedRecordedTreeLaw D s a T)

instance anisotropicFutureVertexMarkedLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap) :
    IsProbabilityMeasure (anisotropicFutureVertexMarkedLaw D s a T v q) :=
  finiteCascadeFutureMarkedLaw_probability _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _

theorem anisotropicFutureVertexMarkedLaw_fst (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap) :
    (anisotropicFutureVertexMarkedLaw D s a T v q).fst=anisotropicTrimmedRecordedTreeLaw D s a T :=
  finiteCascadeFutureMarkedLaw_fst _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _

theorem integral_anisotropicFutureVertexMarkedLaw_square (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap)
    (F : CavityPathRecordSpace (trimRoot T) n→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) (K : FiniteStateField (Configuration n)) :
    (∫z,F z.1*K z.2.1*K z.2.2 ∂anisotropicFutureVertexMarkedLaw D s a T v q)=
      ∫r,F r*anisotropicVertexFutureSquare D s v K r q
        ∂anisotropicTrimmedRecordedTreeLaw D s a T :=
  integral_finiteCascadeFutureMarkedLaw_product _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _
    F hF C hC hFb K K

def cavityFutureVertexConditionalDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  (∑l : Fin n,anisotropicVertexFutureSquare D s v (anisotropicCouplingFeature (cavityIncidentEdge l)) r q)/(n:ℝ)-
    (q:ℝ)*anisotropicVertexFutureSquare D s v (cavityCoordinateFeature (Fin.last n)) r q

theorem integral_anisotropicFutureVertexMarkedLaw_overlapDefect
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
      ∂anisotropicFutureVertexMarkedLaw D s a T v q)=
      ∫r,F r*cavityFutureVertexConditionalDefect D s v q r
        ∂anisotropicTrimmedRecordedTreeLaw D s a T := by
  classical
  letI := finiteCascadeFuturePairKernel_markov (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
      v (cavityFiniteFutureDepth s v.depth q)
  let B : ℝ:=∑σ : Configuration (n+1)×Configuration (n+1),|cavitySpinOverlapDefect n q σ.1 σ.2|
  have hb (σ : Configuration (n+1)×Configuration (n+1)) : |cavitySpinOverlapDefect n q σ.1 σ.2|≤B :=
    Finset.single_le_sum (f:=fun τ : Configuration (n+1)×Configuration (n+1)=>
      |cavitySpinOverlapDefect n q τ.1 τ.2|) (fun τ _=>abs_nonneg _) (Finset.mem_univ σ)
  have hm : Measurable (fun z : CavityPathRecordSpace (trimRoot T) (n+1)×
      (Configuration (n+1)×Configuration (n+1))=>F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2) :=
    (hF.comp measurable_fst).mul ((measurable_of_finite
      (fun σ : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q σ.1 σ.2)).comp measurable_snd)
  have hi : Integrable (fun z=>F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2)
      (anisotropicFutureVertexMarkedLaw D s a T v q) := by
    apply (integrable_const (C*B)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2‖≤_
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb z.1) (hb z.2) (abs_nonneg _) hC
  rw [anisotropicFutureVertexMarkedLaw,finiteCascadeFutureMarkedLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only
    rw [finiteCascadeFuturePairKernel_apply]
    letI := isProbabilityMeasure_finiteStateCascadeSplitLaw (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
      (cavityFiniteFutureDepth s v.depth q) (v.depth-cavityFiniteFutureDepth s v.depth q)
        (v.field r.1 r.2)
    rw [integral_const_mul]
    congr 1
    unfold cavitySpinOverlapDefect cavityFutureVertexConditionalDefect
    simp_rw [mul_assoc]
    rw [integral_sub (Integrable.of_finite.div_const _) ((Integrable.of_finite).const_mul (q:ℝ)),
      integral_div,integral_finset_sum _ (fun _ _=>Integrable.of_finite),integral_const_mul]
    simp_rw [←finiteStateCascadePairMoment_eq_splitLaw _ _ (anisotropicSchemeMass_nonneg s)]
    rfl

end QuantitativeFollowup
