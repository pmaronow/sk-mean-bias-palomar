module
public import QuantitativeFollowup.ScalarGaussianHistoryCurve
public import QuantitativeFollowup.ScalarPartialCovarianceResponse
public import FRSB.FiniteForwardAction

@[expose] public section

/-! Atom-exact finite Stieltjes boundary identities. Repeated finite nodes
are included in the right-continuous CDF; the future integral is strict at
the starting level. No response formula is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2600000
variable {k : ℕ}

private theorem reverse_mass_telescope (a : ℕ→ℝ) (N : ℕ) :
    (∑r∈Finset.range N,(a r-a (r+1)))=a 0-a N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; ring

theorem integral_scalarScheme_reverse (s : RSBScheme k) (f : Paper.Overlap→ℝ) :
    (∫q,f q ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∑r∈Finset.range (k+2),(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
        f (scalarSchemeTransportNode s (k+1-r)) := by
  have he : (∑i : Fin (k+1),(s.m (i+1)-s.m i)*f (Paper.parisiSchemeAtom s i))=
      ∑i : Fin (k+1),(s.m (i+1)-s.m i)*f (scalarSchemeTransportNode s (i+1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn : Paper.parisiSchemeAtom s i=scalarSchemeTransportNode s (i+1) := by
      apply Subtype.ext
      exact (scalarSchemeTransportNode_coe s (i+1) (by have hh:=i.isLt; omega)).symm
    rw [hn]
  rw [FRSB.integral_parisiSchemeMeasure,he,
    Fin.sum_univ_eq_sum_range (fun i=>(s.m (i+1)-s.m i)*f (scalarSchemeTransportNode s (i+1)))]
  conv_rhs => rw [show k+2=(k+1)+1 by omega,Finset.sum_range_succ]
  have hz : (scalarSchemeMass s (k+1)-scalarSchemeMass s (k+1+1))*
      f (scalarSchemeTransportNode s (k+1-(k+1)))=0 := by
    simp [scalarSchemeMass]
  rw [hz,add_zero]
  have hrev:=Finset.sum_range_reflect
    (fun i=>(s.m (i+1)-s.m i)*f (scalarSchemeTransportNode s (i+1))) (k+1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [←hrev]
  apply Finset.sum_congr rfl
  intro r hr
  have hri:=Finset.mem_range.mp hr
  simp only [scalarSchemeMass]
  rw [show k-r+1=k+1-r by omega,show k+1-(r+1)=k-r by omega]


private theorem scheme_node_mono (s : RSBScheme k) (i j : ℕ) (hi : i ≤ k+2)
    (hj : j ≤ k+2) (hij : i ≤ j) : scalarSchemeTransportNode s i ≤ scalarSchemeTransportNode s j := by
  change (scalarSchemeTransportNode s i:ℝ) ≤ (scalarSchemeTransportNode s j:ℝ)
  rw [scalarSchemeTransportNode_coe s i hi,scalarSchemeTransportNode_coe s j hj]
  exact s.q_mono' j hj i hij

private theorem sum_range_small_piece (N J : ℕ) (hJN : J ≤ N) (f : ℕ→ℝ) :
    (∑r∈Finset.range N,if r < J then f r else 0)=∑r∈Finset.range J,f r := by
  have he : (∑r∈Finset.range J,if r < J then f r else 0)=
      ∑r∈Finset.range N,if r < J then f r else 0 := by
    apply Finset.sum_subset (Finset.range_mono hJN)
    intro r hr hnot
    simp only [Finset.mem_range] at hnot
    simp [hnot]
  rw [←he]
  apply Finset.sum_congr rfl
  intro r hr
  simp [Finset.mem_range.mp hr]

theorem scalarScheme_stieltjes_boundary (s : RSBScheme k) (J : ℕ) (hJ : J ≤ k+2)
    (F : Paper.Overlap→ℝ) :
    scalarSchemeMass s J*F (scalarSchemeTransportNode s (k+2-J))+
      (∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
        F (scalarSchemeTransportNode s (k+1-r)))=
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (k+2-J))*
        F (scalarSchemeTransportNode s (k+2-J))+
      ∫q,if scalarSchemeTransportNode s (k+2-J) < q then F q else 0
        ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
  let q:=scalarSchemeTransportNode s (k+2-J)
  let w:=fun r=>scalarSchemeMass s r-scalarSchemeMass s (r+1)
  let G:=fun z:Paper.Overlap=>if z ≤ q then F q else F z
  have hG : (∫z,G z ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*F q+
        ∫z,if q < z then F z else 0 ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
    have he : G=(fun z=>(if z ≤ q then (1:ℝ) else 0)*F q)+
        (fun z=>if q < z then F z else 0) := by
      funext z
      by_cases hz:z ≤ q
      · simp [G,hz,not_lt_of_ge hz]
      · simp [G,hz,lt_of_not_ge hz]
    rw [he]
    simp only [Pi.add_apply]
    rw [integral_add (FRSB.integrable_parisiSchemeMeasure s _) (FRSB.integrable_parisiSchemeMeasure s _),
      integral_mul_const]
    have hCDF : (∫z:Paper.Overlap,if z ≤ q then (1:ℝ) else 0
        ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
        Paper.parisiCDF (Paper.parisiSchemeMeasure s) q := by
      change (∫z:Paper.Overlap,if (z:ℝ) ≤ (q:ℝ) then (1:ℝ) else 0
        ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=_
      exact (Paper.parisiCDF_eq_integral_upperIndicator _ _).symm
    rw [hCDF]
  have hnode (r : ℕ) (hr : r∈Finset.range (k+2)) :
      G (scalarSchemeTransportNode s (k+1-r))=
        if r < J then F (scalarSchemeTransportNode s (k+1-r)) else F q := by
    have hrN:=Finset.mem_range.mp hr
    by_cases hrJ:r < J
    · have horder : q ≤ scalarSchemeTransportNode s (k+1-r) :=
        scheme_node_mono s (k+2-J) (k+1-r) (by omega) (by omega) (by omega)
      by_cases hz:scalarSchemeTransportNode s (k+1-r) ≤ q
      · have heq:=le_antisymm hz horder
        simp [G,hrJ,heq]
      · simp [G,hrJ,hz]
    · have horder : scalarSchemeTransportNode s (k+1-r) ≤ q :=
        scheme_node_mono s (k+1-r) (k+2-J) (by omega) (by omega) (by omega)
      simp [G,hrJ,horder]
  have hsum : (∑r∈Finset.range (k+2),w r*G (scalarSchemeTransportNode s (k+1-r)))=
      (∑r∈Finset.range J,w r*F (scalarSchemeTransportNode s (k+1-r)))+
        scalarSchemeMass s J*F q := by
    have he : (∑r∈Finset.range (k+2),w r*G (scalarSchemeTransportNode s (k+1-r)))=
        (∑r∈Finset.range (k+2),if r < J then w r*F (scalarSchemeTransportNode s (k+1-r)) else 0)+
        ((∑r∈Finset.range (k+2),w r)-(∑r∈Finset.range (k+2),if r < J then w r else 0))*F q := by
      rw [sub_mul,Finset.sum_mul,Finset.sum_mul,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hnode r hr]
      by_cases hrJ:r < J <;> simp [hrJ]
    rw [he,sum_range_small_piece (k+2) J hJ,
      sum_range_small_piece (k+2) J hJ]
    have htot : (∑r∈Finset.range (k+2),w r)=1 := by
      dsimp only [w]
      rw [reverse_mass_telescope]
      simp [scalarSchemeMass,s.m_top,s.m_zero]
    have hpre : (∑r∈Finset.range J,w r)=1-scalarSchemeMass s J := by
      dsimp only [w]
      rw [reverse_mass_telescope]
      simp [scalarSchemeMass,s.m_top]
    rw [htot,hpre]
    ring
  rw [←hG,integral_scalarScheme_reverse]
  change scalarSchemeMass s J*F q+(∑r∈Finset.range J,w r*F (scalarSchemeTransportNode s (k+1-r)))=
    ∑r∈Finset.range (k+2),w r*G (scalarSchemeTransportNode s (k+1-r))
  rw [hsum]
  ring

end QuantitativeFollowup
