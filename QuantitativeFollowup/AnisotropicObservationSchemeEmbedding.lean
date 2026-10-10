module
public import QuantitativeFollowup.AnisotropicRecordedProfileFiniteTree
public import OverlapPaper.ScalarFiniteObservationScheme
public import FourPapersCommon.FiniteSchemeRepeatNodes
public import FourPapersCommon.FiniteObservationTreeRefinement

@[expose] public section

/-! Genuine finite schemes containing a complete observation schedule.
Repeated observations receive distinct retained indices, without changing
any atom of the original probability law. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace QuantitativeFollowup
open FourPapersCommon SpinGlass.Targets Paper
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

theorem anisotropicRecordedSchemeSchedule_antitone (s : RSBScheme k) :
    Antitone (anisotropicRecordedSchemeSchedule s) := by
  intro i j hij
  apply Subtype.coe_le_coe.mp
  rw [anisotropicRecordedSchemeSchedule,anisotropicRecordedSchemeSchedule,
    anisotropicFiniteMeshNode_coe s _ (Nat.sub_le _ _),
    anisotropicFiniteMeshNode_coe s _ (Nat.sub_le _ _)]
  exact s.q_mono' _ (Nat.sub_le _ _) _ (Nat.sub_le_sub_left hij _)

theorem scalarObservationRefinement_q_one_zero (s : RSBScheme k) (hs : s.q 1=0)
    (p : Paper.Overlap) : (scalarObservationRefinement s p).q 1=0 := by
  change (threefoldScheme s _ _ _).q (3*0+1)=0
  rw [threefoldScheme_q_first]
  simp only [scalarObservationInsertedLevel,zero_add,s.q_zero,hs]
  rw [min_eq_right p.property.1,max_self]

theorem exists_scalar_same_measure_zero_scheme_observations (s : RSBScheme k)
    (hs : s.q 1=0) (E : Finset Paper.Overlap) :
    ∃(K : ℕ)(r : RSBScheme K),parisiSchemeMeasure r=parisiSchemeMeasure s ∧ r.q 1=0 ∧
      ∀p∈E,∃j : Fin (K+3),scalarSchemeTransportNode r j=p := by
  induction E using Finset.induction_on with
  | empty => exact ⟨k,s,rfl,hs,by simp⟩
  | @insert p E hp ih =>
      obtain ⟨K,r,hr,hzero,hE⟩:=ih
      refine ⟨3*K+4,scalarObservationRefinement r p,
        (scalarObservationRefinement_measure r p).trans hr,
        scalarObservationRefinement_q_one_zero r hzero p,?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with hzp|hzE
      · subst z
        exact exists_scalarObservationRefinement_node r p
      · obtain ⟨j,hj⟩:=hE z hzE
        exact ⟨⟨3*(j:ℕ),by have := j.isLt;omega⟩,
          (OverlapPaper.scalarObservationRefinement_preserves_node r p j).trans hj⟩

private theorem exists_scheme_reverse_node_below_top (s : RSBScheme k) (hs : s.q 1=0)
    (p : Paper.Overlap) (hp : ∃i : Fin (k+3),scalarSchemeTransportNode s i=p) :
    ∃b : ℕ,b≤k+1 ∧ anisotropicRecordedSchemeSchedule s b=p := by
  obtain ⟨i,hi⟩:=hp
  by_cases hiz : (i:ℕ)=0
  · refine ⟨k+1,le_rfl,?_⟩
    apply Subtype.ext
    have he:=congrArg Subtype.val hi
    rw [scalarSchemeTransportNode_coe _ _ (by have := i.isLt;omega),hiz,s.q_zero] at he
    rw [anisotropicRecordedSchemeSchedule,show k+2-(k+1)=1 by omega,
      anisotropicFiniteMeshNode_coe s 1 (by omega),hs]
    exact he
  · refine ⟨k+2-(i:ℕ),by have := i.isLt;omega,?_⟩
    apply Subtype.ext
    have he:=congrArg Subtype.val hi
    rw [scalarSchemeTransportNode_coe _ _ (by have := i.isLt;omega)] at he
    rw [anisotropicRecordedSchemeSchedule,
      show k+2-(k+2-(i:ℕ))=(i:ℕ) by have := i.isLt;omega,
      anisotropicFiniteMeshNode_coe s _ (by have := i.isLt;omega)]
    exact he

/-- A genuine same-measure scheme and strict reverse index embedding of
all requested times, including repeats and both endpoints. -/
theorem exists_same_measure_observation_scheme_embedding (s : RSBScheme k)
    (hs : s.q 1=0) (q : ℕ→Paper.Overlap) (hq : Antitone q) (J : ℕ)
    (hJ : 0<J) (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) :
    ∃(K : ℕ)(r : RSBScheme K)(e : ℕ→ℕ),parisiSchemeMeasure r=parisiSchemeMeasure s ∧
      r.q 1=0 ∧ StrictMono e ∧ e 0=0 ∧ e J=K+2 ∧
      ∀j,anisotropicRecordedSchemeSchedule r (e j)=q j := by
  let E:= (Finset.range (J+1)).image q
  obtain ⟨K,r,hr,hrzero,hE⟩:=exists_scalar_same_measure_zero_scheme_observations s hs E
  have hex (j : Fin (J+1)) : ∃b : ℕ,b≤K+1 ∧ anisotropicRecordedSchemeSchedule r b=q j := by
    apply exists_scheme_reverse_node_below_top r hrzero
    exact hE (q j) (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr j.isLt,rfl⟩)
  let b : Fin (J+1)→ℕ:=fun j=>Nat.find (hex j)
  have hb (j : Fin (J+1)) : b j≤K+1 ∧ anisotropicRecordedSchemeSchedule r (b j)=q j := Nat.find_spec (hex j)
  have hbmono : Monotone b := by
    intro i j hij
    by_contra hn
    have hji : b j<b i:=Nat.lt_of_not_ge hn
    have hv := anisotropicRecordedSchemeSchedule_antitone r hji.le
    rw [(hb i).2,(hb j).2] at hv
    have heq : q i=q j := le_antisymm hv (hq hij)
    have hc : b i≤b j:=Nat.find_min' (hex i) ⟨(hb j).1,(hb j).2.trans heq.symm⟩
    omega
  have hbzero : b ⟨0,by omega⟩=0 := by
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min' (hex ⟨0,by omega⟩)
    refine ⟨by omega,?_⟩
    apply Subtype.ext
    rw [anisotropicRecordedSchemeSchedule,Nat.sub_zero,
      anisotropicFiniteMeshNode_coe r _ le_rfl,r.q_top,hzero]
  let C:=J+2
  have hC : 2≤C:=by dsimp [C];omega
  let R:=repeatNodeScheme r C hC
  let e : ℕ→ℕ:=fun j=>if hj:j<J then C*b ⟨j,by omega⟩+j else C*(K+2)+(j-J)
  have hezero : e 0=0 := by
    have hbz : b 0=0 := hbzero
    simp [e,hJ,hbz]
  have hetop : e J=C*(K+2) := by simp [e]
  have hesucc (j : ℕ) : e j<e (j+1) := by
    by_cases hj : j+1<J
    · have hj' : j<J:=by omega
      simp only [e,dif_pos hj',dif_pos hj]
      have hbm:=hbmono (show (⟨j,by omega⟩:Fin (J+1))≤⟨j+1,by omega⟩ from Nat.le_succ j)
      have hm:=Nat.mul_le_mul_left C hbm
      omega
    · by_cases hj' : j<J
      · have he : j+1=J:=by omega
        rw [he,hetop]
        simp only [e,dif_pos hj']
        have hbi:=(hb ⟨j,by omega⟩).1
        have hm:=Nat.mul_le_mul_left C hbi
        have hc : C*(K+2)=C*(K+1)+C:=by ring
        dsimp [C] at *
        omega
      · simp only [e,dif_neg hj',dif_neg hj]
        omega
  have helevels (j : ℕ) : anisotropicRecordedSchemeSchedule R (e j)=q j := by
    by_cases hj : j<J
    · apply Subtype.ext
      have hbj:=(hb ⟨j,by omega⟩)
      rw [anisotropicRecordedSchemeSchedule,repeatNodeScheme_depth r C hC]
      have heval : e j=C*b ⟨j,by omega⟩+j:=by simp [e,hj]
      rw [heval,anisotropicFiniteMeshNode_coe R (C*(K+2)-(C*b ⟨j,by omega⟩+j))
        (by rw [repeatNodeScheme_depth r C hC];exact Nat.sub_le _ _),
        repeatNodeScheme_q_backward_block r C hC _ j hbj.1 (by dsimp [C];omega)]
      have hz:=congrArg Subtype.val hbj.2
      rw [anisotropicRecordedSchemeSchedule,anisotropicFiniteMeshNode_coe r _ (Nat.sub_le _ _)] at hz
      exact hz
    · apply Subtype.ext
      have heval : C*(K+2)≤e j:=by simp only [e,dif_neg hj];omega
      have ht : (q j:ℝ)=0 := by
        have hv:=hq (show J≤j by omega)
        exact le_antisymm (htop ▸ hv) (q j).property.1
      rw [anisotropicRecordedSchemeSchedule,repeatNodeScheme_depth r C hC,
        Nat.sub_eq_zero_of_le heval,anisotropicFiniteMeshNode_coe R 0 (Nat.zero_le _),R.q_zero,ht]
  refine ⟨C*(K+2)-2,R,e,
    (parisiSchemeMeasure_repeatNodeScheme r C hC).trans hr,?_,
    strictMono_nat_of_lt_succ hesucc,hezero,?_,helevels⟩
  · change r.q (min ((1+C-1)/C) (K+2))=0
    have hc : 1+C-1=C:=by omega
    rw [hc,Nat.div_self (by omega : 0<C),min_eq_left (by omega)]
    exact hrzero
  · simpa only [repeatNodeScheme_depth r C hC] using hetop

end QuantitativeFollowup
