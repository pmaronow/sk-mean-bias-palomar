module
public import QuantitativeFollowup.FollowupCavityPathRecordedScore

@[expose] public section

/-! The actual retained-field score has the same strict-future Stieltjes
form at every field record, including records outside the Gaussian support. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityPathRecordFutureSquare (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (v : FiniteCascadeRecordVertex T)
    (p : CavityPathRecordSpace T n) (q : Paper.Overlap) : ℝ:=
  cavityFiniteFutureSquare (anisotropicReplaceVariance D i b) s v.depth (v.field p.1 p.2)
    (cavityCoordinateFeature i) q

theorem cavityPathRecord_hessian_parameter_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    (b : ℝ) (v : FiniteCascadeRecordVertex T) (p : CavityPathRecordSpace T n) :
    s.q (k+2-v.depth)*cavityPathRecordHessian D s i T b v p+
      2*cavityPathRecordParameter D s i T b v p=
      1-s.q (k+2-v.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s v)*
        (cavityPathRecordMean D s i T b v p)^2-
        ∫r,if cavityPathVertexOverlap s v<r then (r:ℝ)*cavityPathRecordFutureSquare D s i T b v p r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  have hv:=v.depth_le.trans hj
  have hH:=cavityFiniteBinaryFeature_node_free_stieltjes (anisotropicReplaceVariance D i b) s v.depth hv
    a ha has hq (v.field p.1 p.2) (cavityCoordinateFeature i) (cavityCoordinateFeature_binary i)
  have hB:=cavityFiniteNodeBResponse_free_stieltjes (anisotropicReplaceVariance D i b) s v.depth hv
    a ha has hq (v.field p.1 p.2) (cavityCoordinateFeature i) (cavityCoordinateFeature_binary i)
  have hi (F : Paper.Overlap→ℝ) : Integrable F (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a):=by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  have he : s.q (k+2-v.depth)*(∫r,if cavityPathVertexOverlap s v<r then
      cavityPathRecordFutureSquare D s i T b v p r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
      (∫r,if cavityPathVertexOverlap s v<r then ((r:ℝ)-s.q (k+2-v.depth))*
        cavityPathRecordFutureSquare D s i T b v p r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∫r,if cavityPathVertexOverlap s v<r then (r:ℝ)*cavityPathRecordFutureSquare D s i T b v p r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a:=by
    rw [←integral_const_mul,←integral_add (hi _) (hi _)]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      by_cases hr:cavityPathVertexOverlap s v<r
      · simp only [if_pos hr];ring
      · simp only [if_neg hr,mul_zero,add_zero]
  change cavityPathRecordHessian D s i T b v p=
    1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s v)*
      (cavityPathRecordMean D s i T b v p)^2-
      (∫r,if cavityPathVertexOverlap s v<r then cavityPathRecordFutureSquare D s i T b v p r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) at hH
  change cavityPathRecordParameter D s i T b v p=
    (1/2:ℝ)*(1-s.q (k+2-v.depth)-
      ∫r,if cavityPathVertexOverlap s v<r then ((r:ℝ)-s.q (k+2-v.depth))*
        cavityPathRecordFutureSquare D s i T b v p r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) at hB
  rw [hH,hB]
  linarith only [he]

private theorem recorded_weighted_list_three_terms {A : Type} (cs : List (ℝ×A)) (f g : A→ℝ) :
    (cs.map (fun c=>c.1*(1-f c.2-g c.2))).sum=
      (cs.map Prod.fst).sum-(cs.map (fun c=>c.1*f c.2)).sum-(cs.map (fun c=>c.1*g c.2)).sum:=by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons,List.sum_cons];rw [ih];ring

private theorem recorded_weighted_list_linear {A : Type} (cs : List (ℝ×A)) (f g : A→ℝ) :
    2*(cs.map (fun c=>c.1*f c.2)).sum+(cs.map (fun c=>c.1*g c.2)).sum=
      (cs.map (fun c=>c.1*(g c.2+2*f c.2))).sum:=by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons,List.sum_cons];rw [←ih];ring

theorem cavityPathRecordScore_free_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : Fin n) (T : FiniteTerminalGenealogy (k+1)) (b : ℝ) (p : CavityPathRecordSpace T n) :
    cavityPathRecordScore D s a i T b p=(1/2:ℝ)*
      (cavityPathRecordClockGram D s a i T b p-
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+a+
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
          c.1*(s.q (k+2-c.2.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s c.2)*
            (cavityPathRecordMean D s i T b c.2 p)^2))).sum+
        ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
          c.1*(∫r,if cavityPathVertexOverlap s c.2<r then
            (r:ℝ)*cavityPathRecordFutureSquare D s i T b c.2 p r else 0
              ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum) := by
  unfold cavityPathRecordScore
  simp only [show k+2-(k+1)=1 by omega,hq,sub_zero]
  have hh:=recorded_weighted_list_linear (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v=>cavityPathRecordParameter D s i T b v p)
    (fun v=>s.q (k+2-v.depth)*cavityPathRecordHessian D s i T b v p)
  simp_rw [cavityPathRecord_hessian_parameter_stieltjes D s a ha has hq i T (by omega) b] at hh
  rw [recorded_weighted_list_three_terms (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v=>s.q (k+2-v.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s v)*
      (cavityPathRecordMean D s i T b v p)^2)
    (fun v=>∫r,if cavityPathVertexOverlap s v<r then
      (r:ℝ)*cavityPathRecordFutureSquare D s i T b v p r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a),finiteCascadeVertexCharges_sum] at hh
  simp only [mul_assoc] at hh ⊢
  linarith only [hh]

end QuantitativeFollowup
