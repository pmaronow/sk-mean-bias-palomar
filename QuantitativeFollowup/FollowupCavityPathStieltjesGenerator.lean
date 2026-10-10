module
public import QuantitativeFollowup.FollowupCavityPathGramClock
public import QuantitativeFollowup.FollowupCavityNodeBStieltjes
public import FourPapersCommon.FiniteCascadeVertexWeights

@[expose] public section

/-! Physical path-variance cancellation with the actual strict-future free
Stieltjes measure. The right CDF at every retained node includes its atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityPathVertexOverlap (s : RSBScheme k) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : Paper.Overlap:=scalarSchemeTransportNode s (k+2-v.depth)

def cavityPathVertexFutureSquare (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (y : CavityPathGaussianSpace T n)
    (v : FiniteCascadeRecordVertex T) (q : Paper.Overlap) : ℝ:=
  cavityFiniteFutureSquare (anisotropicReplaceVariance D i b) s v.depth
    (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i) q

theorem cavityPathVertex_hessian_parameter_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    (b : ℝ) (y : CavityPathGaussianSpace T n) (v : FiniteCascadeRecordVertex T) :
    s.q (k+2-v.depth)*cavityPathVertexBinaryHessian D s i T b y v+
      2*cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth
        (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i)=
      1-s.q (k+2-v.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s v)*
        (cavityPathSelectedVertexMean D s i T b y v)^2-
        ∫r,if cavityPathVertexOverlap s v<r then (r:ℝ)*cavityPathVertexFutureSquare D s i T b y v r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  have hv:=v.depth_le.trans hj
  have hH:=cavityFiniteBinaryFeature_node_free_stieltjes (anisotropicReplaceVariance D i b) s v.depth hv
    a ha has hq (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i)
      (cavityCoordinateFeature_binary i)
  have hB:=cavityFiniteNodeBResponse_free_stieltjes (anisotropicReplaceVariance D i b) s v.depth hv
    a ha has hq (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i)
      (cavityCoordinateFeature_binary i)
  have hi (F : Paper.Overlap→ℝ) : Integrable F (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a):=by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  have he : s.q (k+2-v.depth)*(∫r,if cavityPathVertexOverlap s v<r then
      cavityPathVertexFutureSquare D s i T b y v r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
      (∫r,if cavityPathVertexOverlap s v<r then ((r:ℝ)-s.q (k+2-v.depth))*
        cavityPathVertexFutureSquare D s i T b y v r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∫r,if cavityPathVertexOverlap s v<r then (r:ℝ)*cavityPathVertexFutureSquare D s i T b y v r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a:=by
    rw [←integral_const_mul,←integral_add (hi _) (hi _)]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      by_cases hr:cavityPathVertexOverlap s v<r
      · simp only [if_pos hr];ring
      · simp only [if_neg hr,mul_zero,add_zero]
  change cavityPathVertexBinaryHessian D s i T b y v=
    1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s v)*
      (cavityPathSelectedVertexMean D s i T b y v)^2-
      (∫r,if cavityPathVertexOverlap s v<r then cavityPathVertexFutureSquare D s i T b y v r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) at hH
  change cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth
      (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i)=
    (1/2:ℝ)*(1-s.q (k+2-v.depth)-
      ∫r,if cavityPathVertexOverlap s v<r then ((r:ℝ)-s.q (k+2-v.depth))*
        cavityPathVertexFutureSquare D s i T b y v r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) at hB
  rw [hH,hB]
  linarith only [he]

private theorem weighted_list_three_terms {A : Type} (cs : List (ℝ×A)) (f g : A→ℝ) :
    (cs.map (fun c=>c.1*(1-f c.2-g c.2))).sum=
      (cs.map Prod.fst).sum-(cs.map (fun c=>c.1*f c.2)).sum-(cs.map (fun c=>c.1*g c.2)).sum:=by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons,List.sum_cons];rw [ih];ring

private theorem weighted_list_linear_combination {A : Type} (cs : List (ℝ×A))
    (f g : A→ℝ) :
    2*(cs.map (fun c=>c.1*f c.2)).sum+(cs.map (fun c=>c.1*g c.2)).sum=
      (cs.map (fun c=>c.1*(g c.2+2*f c.2))).sum:=by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons,List.sum_cons];rw [←ih];ring

theorem cavityPathScoreGenerator_free_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : Fin n) (T : FiniteTerminalGenealogy (k+1))
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (y : CavityPathGaussianSpace T n) :
    cavityPathScoreGenerator D s a i T σ b y=(1/2:ℝ)*
      (cavityPathSharedClockGram D s a i T σ b y-
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+a+
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
          c.1*(s.q (k+2-c.2.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s c.2)*
            (cavityPathSelectedVertexMean D s i T b y c.2)^2))).sum+
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
          c.1*(∫r,if cavityPathVertexOverlap s c.2<r then
            (r:ℝ)*cavityPathVertexFutureSquare D s i T b y c.2 r else 0
              ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum) := by
  rw [cavityPathScoreGenerator_eq_shared_clock]
  simp only [show k+2-(k+1)=1 by omega,hq,sub_zero]
  unfold cavityPathParameterCharge
  have hh:=weighted_list_linear_combination (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v=>cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth
      (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i))
    (fun v=>s.q (k+2-v.depth)*cavityPathVertexBinaryHessian D s i T b y v)
  simp_rw [cavityPathVertex_hessian_parameter_stieltjes D s a ha has hq i T (by omega) b y] at hh
  rw [weighted_list_three_terms (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v=>s.q (k+2-v.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s v)*
      (cavityPathSelectedVertexMean D s i T b y v)^2)
    (fun v=>∫r,if cavityPathVertexOverlap s v<r then
      (r:ℝ)*cavityPathVertexFutureSquare D s i T b y v r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a),finiteCascadeVertexCharges_sum] at hh
  simp only [mul_assoc] at hh ⊢
  linarith only [hh]

end QuantitativeFollowup
