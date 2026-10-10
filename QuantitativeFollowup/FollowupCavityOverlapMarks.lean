module
public import QuantitativeFollowup.FollowupCavityVertexMarks
public import QuantitativeFollowup.FollowupCavityIncidentIndexSum
public import QuantitativeFollowup.FollowupCavityNodeBModel
public import QuantitativeFollowup.FollowupCavityPathRecordedScore

@[expose] public section

/-! Literal independent terminal marks turn conditional mean products into
the cavity overlap defect. The marking law is the actual normalized future
cascade at each retained vertex, with its deletion law already proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavitySpinOverlapDefect (n : ℕ) (q : ℝ)
    (σ τ : Configuration (n+1)) : ℝ :=
  (∑l : Fin n,anisotropicCouplingFeature (cavityIncidentEdge l) σ*
    anisotropicCouplingFeature (cavityIncidentEdge l) τ)/(n:ℝ)-
      q*cavityCoordinateFeature (Fin.last n) σ*cavityCoordinateFeature (Fin.last n) τ

theorem cavitySpinOverlapDefect_eq (n : ℕ) (q : ℝ) (σ τ : Configuration (n+1)) :
    cavitySpinOverlapDefect n q σ τ=
      Paper.spinSign (σ (Fin.last n))*Paper.spinSign (τ (Fin.last n))*
        ((∑l : Fin n,Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc))/(n:ℝ)-q) := by
  unfold cavitySpinOverlapDefect
  simp only [anisotropicCouplingFeature,cavityIncidentEdge,cavityCoordinateFeature_apply]
  have h : (∑l : Fin n,Paper.spinSign (σ l.castSucc)*Paper.spinSign (σ (Fin.last n))*
      (Paper.spinSign (τ l.castSucc)*Paper.spinSign (τ (Fin.last n))))=
      Paper.spinSign (σ (Fin.last n))*Paper.spinSign (τ (Fin.last n))*
        (∑l : Fin n,Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h]
  ring

def cavityCrossVertexConditionalDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v w : FiniteCascadeRecordVertex (trimRoot T))
    (q : ℝ) (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  (∑l : Fin n,anisotropicVertexMean D s v (anisotropicCouplingFeature (cavityIncidentEdge l)) r*
    anisotropicVertexMean D s w (anisotropicCouplingFeature (cavityIncidentEdge l)) r)/(n:ℝ)-
      q*anisotropicVertexMean D s v (cavityCoordinateFeature (Fin.last n)) r*
        anisotropicVertexMean D s w (cavityCoordinateFeature (Fin.last n)) r

theorem measurable_anisotropicVertexMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n)) : Measurable (anisotropicVertexMean D s v K) := by
  exact (((contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) v.depth).continuous_fderiv
        (by simp)).clm_apply continuous_const).measurable.comp v.measurable_field

theorem anisotropicVertexMean_abs_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n)) (r : CavityPathRecordSpace (trimRoot T) n) :
    |anisotropicVertexMean D s v K r| ≤ ‖K‖ :=
  finiteStateCascadeFirst_abs_le _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _

theorem integral_anisotropicCrossVertexMarkedLaw_overlapDefect
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T))
    (q : ℝ) (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r| ≤ C) :
    (∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
      ∂anisotropicCrossVertexMarkedLaw D s a T v w)=
      ∫r,F r*cavityCrossVertexConditionalDefect D s v w q r
        ∂anisotropicTrimmedRecordedTreeLaw D s a T := by
  classical
  let P:=anisotropicTrimmedRecordedTreeLaw D s a T
  let Q:=anisotropicCrossVertexMarkedLaw D s a T v w
  have hiQ (K M : FiniteStateField (Configuration (n+1))) :
      Integrable (fun z=>F z.1*(K z.2.1*M z.2.2)) Q := by
    apply (integrable_const (C*‖K‖*‖M‖)).mono'
      ((hF.comp measurable_fst).mul (((measurable_of_finite K).comp
        (measurable_fst.comp measurable_snd)).mul ((measurable_of_finite M).comp
          (measurable_snd.comp measurable_snd)))).aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖F z.1*(K z.2.1*M z.2.2)‖ ≤ _
      rw [Real.norm_eq_abs,abs_mul,abs_mul,←mul_assoc]
      exact mul_le_mul (mul_le_mul (hFb z.1)
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2.1)
          (abs_nonneg _) hC)
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le M z.2.2)
          (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
  have hiP (K M : FiniteStateField (Configuration (n+1))) :
      Integrable (fun r=>F r*(anisotropicVertexMean D s v K r*anisotropicVertexMean D s w M r)) P := by
    apply (integrable_const (C*‖K‖*‖M‖)).mono'
      (hF.mul ((measurable_anisotropicVertexMean D s v K).mul
        (measurable_anisotropicVertexMean D s w M))).aestronglyMeasurable
    exact .of_forall fun r=>by
      change ‖F r*(anisotropicVertexMean D s v K r*anisotropicVertexMean D s w M r)‖ ≤ _
      rw [Real.norm_eq_abs,abs_mul,abs_mul,←mul_assoc]
      exact mul_le_mul (mul_le_mul (hFb r) (anisotropicVertexMean_abs_le D s v K r)
        (abs_nonneg _) hC) (anisotropicVertexMean_abs_le D s w M r)
          (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
  have hdist (x : ℝ) (f : Fin n→ℝ) (y z : ℝ) :
      x*((∑l,f l)/(n:ℝ)-q*y*z)=(∑l,x*f l)/(n:ℝ)-q*(x*(y*z)) := by
    rw [←Finset.mul_sum]
    ring
  simp only [cavitySpinOverlapDefect,cavityCrossVertexConditionalDefect]
  simp_rw [hdist]
  rw [integral_sub ((integrable_finset_sum _ (fun l _=>hiQ _ _)).div_const _)
    ((hiQ _ _).const_mul q),integral_div,integral_finset_sum _ (fun l _=>hiQ _ _),integral_const_mul]
  rw [integral_sub ((integrable_finset_sum _ (fun l _=>hiP _ _)).div_const _)
    ((hiP _ _).const_mul q),integral_div,integral_finset_sum _ (fun l _=>hiP _ _),integral_const_mul]
  have hp (K M : FiniteStateField (Configuration (n+1))) :
      (∫z,F z.1*(K z.2.1*M z.2.2) ∂anisotropicCrossVertexMarkedLaw D s a T v w)=
        ∫r,F r*(anisotropicVertexMean D s v K r*anisotropicVertexMean D s w M r) ∂P := by
    simpa only [mul_assoc] using
      integral_anisotropicCrossVertexMarkedLaw_product D s a T v w F hF C hC hFb K M
  apply congrArg₂ (fun x y : ℝ=>x/(n:ℝ)-q*y)
  · apply Finset.sum_congr rfl
    intro l _
    exact hp _ _
  · exact hp _ _

end QuantitativeFollowup
