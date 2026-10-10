module
public import QuantitativeFollowup.ScalarFiniteResponseLinear

@[expose] public section

/-! The seven-term pointwise score is exactly the finite linear form of
bounded physical integrands. Strict future indicators are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem scalarTransportCovarianceLevel_eq_min (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (i j : Fin (k+3)) :
    scalarTransportCovarianceLevel s φ i j=
      φ (min (scalarSchemeTransportNode s i) (scalarSchemeTransportNode s j)) := by
  unfold scalarTransportCovarianceLevel
  congr 1
  rcases le_total (i:ℕ) (j:ℕ) with hij|hji
  · have hq : scalarSchemeTransportNode s i≤ scalarSchemeTransportNode s j := by
      change (scalarSchemeTransportNode s i:ℝ)≤ scalarSchemeTransportNode s j
      rw [scalarSchemeTransportNode_coe _ _ (by omega),scalarSchemeTransportNode_coe _ _ (by omega)]
      exact s.q_mono' j (by omega) i hij
    rw [min_eq_left hij,min_eq_left hq]
  · have hq : scalarSchemeTransportNode s j≤ scalarSchemeTransportNode s i := by
      change (scalarSchemeTransportNode s j:ℝ)≤ scalarSchemeTransportNode s i
      rw [scalarSchemeTransportNode_coe _ _ (by omega),scalarSchemeTransportNode_coe _ _ (by omega)]
      exact s.q_mono' i (by omega) j hji
    rw [min_eq_right hji,min_eq_right hq]

theorem scalarFiniteSevenTermResponse_eq_linear (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (z : Paper.BrownianSample×Bool) :
    scalarFiniteSevenTermResponse s β φ p
      (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) (Paper.spinSign z.2)
      (Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p))=
      scalarFiniteResponseLinear s φ (scalarSchemeTransportNode s p)
        (fun j r ell=>scalarResponseSample j β (Paper.parisiSchemeMeasure s)
          (scalarSchemeTransportNode s p) r ell z) := by
  let μ:=Paper.parisiSchemeMeasure s
  let qp:=scalarSchemeTransportNode s p
  let w:=fun i : Fin (k+1)=>s.m (i+1)-s.m i
  let q:=fun i : Fin (k+1)=>scalarSchemeTransportNode s (scalarFiniteAtomIndex i)
  let m:=fun r : Paper.Overlap=>M β μ r z.1
  let h:=C β μ qp z.1
  let c:=m qp^2-Gamma β μ qp
  let dg:=fun r : Paper.Overlap=>scalarFutureSquareDerivativeExtended β μ qp r (parisiPhysicalSplitState β 0 μ qp z.1)
  let g:=fun r ell : Paper.Overlap=>scalarFutureSquareExtended β μ r ell (parisiPhysicalSplitState β 0 μ r z.1)
  have e2 (i : Fin (k+1)) : w i*(if qp<q i then m qp*dg (q i)*φ (q i) else 0)=
      m qp*(w i*(if qp<q i then φ (q i)*dg (q i) else 0)) := by split_ifs <;> ring
  have e3 (i : Fin (k+1)) : w i*(m qp*h*m (q i))*φ (min qp (q i))=
      m qp*h*(w i*m (q i)*φ (min qp (q i))) := by ring
  have e4 (i : Fin (k+1)) : w i*(c*Paper.spinSign z.2*m (q i))*φ (q i)=
      c*Paper.spinSign z.2*(w i*m (q i)*φ (q i)) := by ring
  have e5 (i : Fin (k+1)) : w i*Paper.parisiCDF μ (q i)*(c*m (q i)^2)*φ (q i)=
      c*(w i*Paper.parisiCDF μ (q i)*m (q i)^2*φ (q i)) := by ring
  have e6 (i j : Fin (k+1)) : w i*(w j*(c*m (q i)*m (q j))*φ (min (q i) (q j)))=
      c*(w i*w j*m (q i)*m (q j)*φ (min (q i) (q j))) := by ring
  have e7 (i j : Fin (k+1)) : w i*(w j*(if q i<q j then c*g (q i) (q j)*φ (q j) else 0))=
      c*(w i*(w j*(if q i<q j then φ (q j)*g (q i) (q j) else 0))) := by split_ifs <;> ring
  rw [scalarFiniteResponseLinear_eq_natural]
  unfold scalarFiniteSevenTermResponse scalarFiniteNodeFutureValue scalarFiniteNodeFutureSlope
  simp only [scalarFiniteNodeGradient_physical s β hβ,scalarFiniteNodeHessian_physical s β hβ,
    scalarTransportCovarianceLevel_eq_min,WithLp.ofLp_toLp,scalarSelectedHistory_node s β hβ,
    setIntegral_scalarScheme_nodes,scalarResponseSample,Fin.isValue,Fin.coe_ofNat_eq_mod,Nat.reduceMod,
    scalarCenteredSquare]
  change _ = _
  change φ qp*(h^2+2*(1-Paper.parisiCDF μ qp)*m qp^2*h)
    -m qp*(∑i,w i*(if qp<q i then φ (q i)*dg (q i) else 0))
    -2*m qp*h*(∑i,w i*m (q i)*φ (min (q i) qp))
    -c*Paper.spinSign z.2*(∑i,w i*m (q i)*φ (q i))
    +(1/2:ℝ)*c*(∑i,w i*Paper.parisiCDF μ (q i)*m (q i)^2*φ (q i))
    +(1/2:ℝ)*c*(∑i,∑j,w i*w j*m (q i)*m (q j)*φ (min (q i) (q j)))
    +(1/2:ℝ)*c*(∑i,w i*(∑j,w j*(if q i<q j then φ (q j)*g (q i) (q j) else 0))) =
    (h^2+2*(1-Paper.parisiCDF μ qp)*(m qp^2*h))*φ qp
    -(∑i,w i*(if qp<q i then m qp*dg (q i)*φ (q i) else 0))
    -2*(∑i,w i*(m qp*h*m (q i))*φ (min qp (q i)))
    -(∑i,w i*(c*Paper.spinSign z.2*m (q i))*φ (q i))
    +(1/2:ℝ)*(∑i,w i*Paper.parisiCDF μ (q i)*(c*m (q i)^2)*φ (q i))
    +(1/2:ℝ)*(∑i,w i*(∑j,w j*(c*m (q i)*m (q j))*φ (min (q i) (q j))))
    +(1/2:ℝ)*(∑i,w i*(∑j,w j*(if q i<q j then c*g (q i) (q j)*φ (q j) else 0)))
  simp_rw [e2,e3,e4,e5]
  have hd6 : (∑i,w i*(∑j,w j*(c*m (q i)*m (q j))*φ (min (q i) (q j))))=
      c*(∑i,∑j,w i*w j*m (q i)*m (q j)*φ (min (q i) (q j))) := by
    simp only [Finset.mul_sum]
    simp_rw [e6]
  have hd7 : (∑i,w i*(∑j,w j*(if q i<q j then c*g (q i) (q j)*φ (q j) else 0)))=
      c*(∑i,w i*(∑j,w j*(if q i<q j then φ (q j)*g (q i) (q j) else 0))) := by
    simp only [Finset.mul_sum]
    simp_rw [e7]
  rw [hd6,hd7]
  simp only [←Finset.mul_sum,min_comm]
  ring

end QuantitativeFollowup
