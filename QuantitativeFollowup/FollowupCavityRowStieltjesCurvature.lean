module
public import QuantitativeFollowup.FollowupCavityPhysicalRowResponse
public import QuantitativeFollowup.FollowupCavityVertexMarks
public import QuantitativeFollowup.FollowupCavityBinaryNodeStieltjes
public import FourPapersCommon.FiniteCascadeVertexWeights

@[expose] public section

/-! The actual physical incident-row curvature with its current and
strict-future conditional square terms. The starting CDF is the right CDF
and the free measure removes exactly the prescribed root mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def anisotropicVertexOverlap (s : RSBScheme k) {T : FiniteTerminalGenealogy (k+2)}
    (v : FiniteCascadeRecordVertex (trimRoot T)) :=
  scalarSchemeTransportNode s (k+2-v.depth)

def anisotropicVertexHessian (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n))
    (z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :=
  fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) v.depth))
      (v.field z.1 z.2) K K

def anisotropicVertexFutureSquare (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n))
    (z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T))
    (q : Paper.Overlap) := cavityFiniteFutureSquare D s v.depth (v.field z.1 z.2) K q

theorem anisotropicVertexHessian_free_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1 = 0)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1)
    (z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :
    anisotropicVertexHessian D s v K z =
      1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s v)*
        (anisotropicVertexMean D s v K z)^2 -
      ∫q,if anisotropicVertexOverlap s v < q then anisotropicVertexFutureSquare D s v K z q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  have hv : v.depth ≤ k+2 := by have hh := v.depth_le; omega
  exact cavityFiniteBinaryFeature_node_free_stieltjes D s v.depth hv a ha has hq
    (v.field z.1 z.2) K hK

private theorem weighted_three_term_sum {A : Type} (l : List (ℝ×A)) (f g : A → ℝ) :
    (l.map (fun c => c.1*(1-f c.2-g c.2))).sum =
      (l.map Prod.fst).sum - (l.map (fun c => c.1*f c.2)).sum -
        (l.map (fun c => c.1*g c.2)).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring

theorem anisotropicIncidentCurvature_free_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1 = 0)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2))
    (z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :
    anisotropicIncidentCurvature D s a e T z =
      (finiteCascadeTreeTerminalFeature (anisotropicCouplingFeature e) (trimRoot T) z.2 -
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
          (fun c => c.1*anisotropicVertexMean D s c.2 (anisotropicCouplingFeature e) z)).sum)^2 -
      (FiniteCascadeGenealogy.leafCount (asGenealogy (trimRoot T)):ℝ) + a +
      ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c =>
        c.1*(Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
          (anisotropicVertexMean D s c.2 (anisotropicCouplingFeature e) z)^2))).sum +
      ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c =>
        c.1*(∫q,if anisotropicVertexOverlap s c.2 < q then
          anisotropicVertexFutureSquare D s c.2 (anisotropicCouplingFeature e) z q else 0
            ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum := by
  have hb (σ : Configuration n) : anisotropicCouplingFeature e σ*anisotropicCouplingFeature e σ=1 := by
    simp only [anisotropicCouplingFeature_apply]
    calc
      _ = (Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))^2 := by ring
      _ = 1 := by rw [mul_pow,Paper.spinSign_sq,Paper.spinSign_sq,mul_one]
  have hcore : anisotropicIncidentCurvature D s a e T z =
      (finiteCascadeTreeTerminalFeature (anisotropicCouplingFeature e) (trimRoot T) z.2 -
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
          (fun c => c.1*anisotropicVertexMean D s c.2 (anisotropicCouplingFeature e) z)).sum)^2 -
      ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
        (fun c => c.1*anisotropicVertexHessian D s c.2 (anisotropicCouplingFeature e) z)).sum := by
    simp only [anisotropicIncidentCurvature,finiteCascadeIntrinsicRowCurvature,
      finiteCascadeTreeGaussianRowCurvature,finiteCascadeTreeFeatureScore_eq_vertex_sum,
      finiteCascadeTreeFeatureSecondCharge_eq_vertex_sum,zero_smul,add_zero,
      finiteCascadeShiftRecords_zero,anisotropicVertexMean,anisotropicVertexHessian]
  rw [hcore]
  simp_rw [anisotropicVertexHessian_free_stieltjes D s a ha has hq _ _ hb z]
  rw [weighted_three_term_sum (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T))
    (fun v => Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s v)*
      (anisotropicVertexMean D s v (anisotropicCouplingFeature e) z)^2)
    (fun v => ∫q,if anisotropicVertexOverlap s v < q then
      anisotropicVertexFutureSquare D s v (anisotropicCouplingFeature e) z q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a),finiteCascadeVertexCharges_sum]
  ring

end QuantitativeFollowup
