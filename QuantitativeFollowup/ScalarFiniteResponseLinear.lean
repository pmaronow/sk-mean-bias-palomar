module
public import QuantitativeFollowup.ScalarResponseSamples

@[expose] public section

/-! A finite linear form of the seven response terms. This representation
allows Bochner expectation to commute with every term after genuine bounded
integrability has been established. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

abbrev ScalarFiniteResponseFeature (k : ℕ) :=
  Unit ⊕ Unit ⊕ Fin (k+1) ⊕ Fin (k+1) ⊕ Fin (k+1) ⊕ Fin (k+1) ⊕
    (Fin (k+1)×Fin (k+1)) ⊕ (Fin (k+1)×Fin (k+1))

def scalarFiniteResponseFeatureData (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (p : Paper.Overlap) (f : ScalarFiniteResponseFeature k) : ℝ×(Fin 8×(Paper.Overlap×Paper.Overlap)) :=
  let w:=fun i : Fin (k+1)=>s.m (i+1)-s.m i
  let q:=fun i : Fin (k+1)=>scalarSchemeTransportNode s (scalarFiniteAtomIndex i)
  match f with
  | Sum.inl _ => (φ p,(0,(p,0)))
  | Sum.inr (Sum.inl _) => (2*(1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) p)*φ p,(1,(p,0)))
  | Sum.inr (Sum.inr (Sum.inl i)) => (-w i*φ (q i)*(if p<q i then 1 else 0),(2,(q i,0)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => (-2*w i*φ (min p (q i)),(3,(q i,0)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => (-w i*φ (q i),(4,(q i,0)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) => ((1/2:ℝ)*w i*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (q i)*φ (q i),(5,(q i,0)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j))))))) => ((1/2:ℝ)*w i*w j*φ (min (q i) (q j)),(6,(q i,q j)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((i,j)))))))) => ((1/2:ℝ)*w i*w j*φ (q j)*(if q i<q j then 1 else 0),(7,(q i,q j)))

def scalarFiniteResponseLinear (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (p : Paper.Overlap) (F : Fin 8→Paper.Overlap→Paper.Overlap→ℝ) : ℝ :=
  ∑i : ScalarFiniteResponseFeature k,
    (scalarFiniteResponseFeatureData s φ p i).1*
      F (scalarFiniteResponseFeatureData s φ p i).2.1
        (scalarFiniteResponseFeatureData s φ p i).2.2.1
        (scalarFiniteResponseFeatureData s φ p i).2.2.2

theorem integral_scalarFiniteResponseLinear (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    (∫z,scalarFiniteResponseLinear s φ p
      (fun j r ell=>scalarResponseSample j β (Paper.parisiSchemeMeasure s) p r ell z)
      ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s))=
      scalarFiniteResponseLinear s φ p
        (fun j r ell=>scalarResponseCoefficient j β (Paper.parisiSchemeMeasure s) p r ell) := by
  unfold scalarFiniteResponseLinear
  rw [integral_finsetSum _ (fun i _=>(integrable_scalarResponseSample _ β hβ _ _ _ _).const_mul _)]
  simp_rw [integral_const_mul,integral_scalarResponseSample]

theorem integrable_scalarFiniteResponseLinear (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    Integrable (fun z=>scalarFiniteResponseLinear s φ p
      (fun j r ell=>scalarResponseSample j β (Paper.parisiSchemeMeasure s) p r ell z))
      (scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s)) := by
  unfold scalarFiniteResponseLinear
  exact integrable_finsetSum _ (fun i _=>(integrable_scalarResponseSample _ β hβ _ _ _ _).const_mul _)

theorem setIntegral_scalarScheme_nodes (s : RSBScheme k) (a : Paper.Overlap)
    (f : Paper.Overlap→ℝ) :
    (∫r in Ioi a,f r ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∑i : Fin (k+1),(s.m (i+1)-s.m i)*
        (if a<scalarSchemeTransportNode s (scalarFiniteAtomIndex i)
          then f (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) else 0) := by
  rw [←integral_indicator measurableSet_Ioi,integral_scalarScheme_nodes]
  apply Finset.sum_congr rfl
  intro i _
  simp only [indicator_apply,mem_Ioi]

theorem scalarFiniteResponseLinear_expansion (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (p : Paper.Overlap) (F : Fin 8→Paper.Overlap→Paper.Overlap→ℝ) :
    scalarFiniteResponseLinear s φ p F=
      φ p*F 0 p 0+2*(1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) p)*φ p*F 1 p 0+
      (∑i : Fin (k+1),-(s.m (i+1)-s.m i)*φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*
        (if p<scalarSchemeTransportNode s (scalarFiniteAtomIndex i) then 1 else 0)*
        F 2 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0)+
      (∑i : Fin (k+1),-2*(s.m (i+1)-s.m i)*φ (min p (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))*
        F 3 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0)+
      (∑i : Fin (k+1),-(s.m (i+1)-s.m i)*φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*
        F 4 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0)+
      (∑i : Fin (k+1),(1/2:ℝ)*(s.m (i+1)-s.m i)*
        Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*
        φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*
        F 5 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0)+
      (∑i : Fin (k+1),∑j : Fin (k+1),(1/2:ℝ)*(s.m (i+1)-s.m i)*(s.m (j+1)-s.m j)*
        φ (min (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))
          (scalarSchemeTransportNode s (scalarFiniteAtomIndex j)))*
        F 6 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))
          (scalarSchemeTransportNode s (scalarFiniteAtomIndex j)))+
      (∑i : Fin (k+1),∑j : Fin (k+1),(1/2:ℝ)*(s.m (i+1)-s.m i)*(s.m (j+1)-s.m j)*
        φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex j))*
        (if scalarSchemeTransportNode s (scalarFiniteAtomIndex i)<
          scalarSchemeTransportNode s (scalarFiniteAtomIndex j) then 1 else 0)*
        F 7 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))
          (scalarSchemeTransportNode s (scalarFiniteAtomIndex j))) := by
  simp only [scalarFiniteResponseLinear,Fintype.sum_sum_type,Fintype.sum_prod_type,
    scalarFiniteResponseFeatureData,Fintype.sum_unique]
  ring


theorem scalarFiniteResponseLinear_eq_natural (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (p : Paper.Overlap) (F : Fin 8→Paper.Overlap→Paper.Overlap→ℝ) :
    scalarFiniteResponseLinear s φ p F=
      (F 0 p 0+2*(1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) p)*F 1 p 0)*φ p
      -(∑i : Fin (k+1),(s.m (i+1)-s.m i)*
        (if p<scalarSchemeTransportNode s (scalarFiniteAtomIndex i)
          then F 2 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0*φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) else 0))
      -2*(∑i : Fin (k+1),(s.m (i+1)-s.m i)*F 3 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0*
        φ (min p (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))))
      -(∑i : Fin (k+1),(s.m (i+1)-s.m i)*F 4 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0*
        φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))
      +(1/2:ℝ)*(∑i : Fin (k+1),(s.m (i+1)-s.m i)*
        Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*
        F 5 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) 0*φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))
      +(1/2:ℝ)*(∑i : Fin (k+1),(s.m (i+1)-s.m i)*(∑j : Fin (k+1),(s.m (j+1)-s.m j)*
        F 6 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) (scalarSchemeTransportNode s (scalarFiniteAtomIndex j))*
        φ (min (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) (scalarSchemeTransportNode s (scalarFiniteAtomIndex j)))))
      +(1/2:ℝ)*(∑i : Fin (k+1),(s.m (i+1)-s.m i)*(∑j : Fin (k+1),(s.m (j+1)-s.m j)*
        (if scalarSchemeTransportNode s (scalarFiniteAtomIndex i)<scalarSchemeTransportNode s (scalarFiniteAtomIndex j)
          then F 7 (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) (scalarSchemeTransportNode s (scalarFiniteAtomIndex j))*
            φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex j)) else 0))) := by
  let w:=fun i : Fin (k+1)=>s.m (i+1)-s.m i
  let q:=fun i : Fin (k+1)=>scalarSchemeTransportNode s (scalarFiniteAtomIndex i)
  have e2 (i : Fin (k+1)) : -w i*φ (q i)*(if p<q i then 1 else 0)*F 2 (q i) 0=
      -(w i*(if p<q i then F 2 (q i) 0*φ (q i) else 0)) := by split_ifs <;> ring
  have e3 (i : Fin (k+1)) : -2*w i*φ (min p (q i))*F 3 (q i) 0=
      -2*(w i*F 3 (q i) 0*φ (min p (q i))) := by ring
  have e4 (i : Fin (k+1)) : -w i*φ (q i)*F 4 (q i) 0=-(w i*F 4 (q i) 0*φ (q i)) := by ring
  have e5 (i : Fin (k+1)) : (1/2:ℝ)*w i*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (q i)*φ (q i)*F 5 (q i) 0=
      (1/2:ℝ)*(w i*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (q i)*F 5 (q i) 0*φ (q i)) := by ring
  have e6 (i j : Fin (k+1)) : (1/2:ℝ)*w i*w j*φ (min (q i) (q j))*F 6 (q i) (q j)=
      (1/2:ℝ)*(w i*(w j*F 6 (q i) (q j)*φ (min (q i) (q j)))) := by ring
  have e7 (i j : Fin (k+1)) : (1/2:ℝ)*w i*w j*φ (q j)*(if q i<q j then 1 else 0)*F 7 (q i) (q j)=
      (1/2:ℝ)*(w i*(w j*(if q i<q j then F 7 (q i) (q j)*φ (q j) else 0))) := by split_ifs <;> ring
  rw [scalarFiniteResponseLinear_expansion]
  change _ = _
  simp only [←show ∀i,w i=s.m (i+1)-s.m i from fun _=>rfl,
    ←show ∀i,q i=scalarSchemeTransportNode s (scalarFiniteAtomIndex i) from fun _=>rfl] at *
  simp_rw [e2,e3,e4,e5,e6,e7]
  simp only [Finset.sum_neg_distrib,←Finset.mul_sum]
  ring

end QuantitativeFollowup
