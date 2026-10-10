module
public import FRSB.CDFMeasureExt
public import Paper.ParisiSchemeMeasure

@[expose] public section

/-! Canonical right-CDF masses on unchanged finite nodes. This removes
unused zero masses at repeated nodes without changing the atomic law. -/
noncomputable section
open Set MeasureTheory Filter
namespace FourPapersCommon
open Paper SpinGlass.Targets
set_option maxHeartbeats 600000
variable {k : ℕ}

theorem schemeCDF_penultimate (s : RSBScheme k) :
    parisiCDF (parisiSchemeMeasure s) (s.q (k+1))=1 := by
  by_cases hq : s.q (k+1)<1
  · exact (parisiCDF_scheme_cell s (by omega)
      ⟨le_rfl,by simpa only [s.q_top] using hq⟩).trans s.m_top
  · exact parisiCDF_eq_one_of_one_le _ (le_of_not_gt hq)

def cdfMassScheme (s : RSBScheme k) : RSBScheme k where
  q:=s.q
  q_zero:=s.q_zero
  q_top:=s.q_top
  q_mono:=s.q_mono
  m p:=if p=0 then 0 else parisiCDF (parisiSchemeMeasure s) (s.q (min p (k+1)))
  m_zero:=by simp
  m_top:=by simp only [show k+1≠0 by omega,ite_false,min_self];exact schemeCDF_penultimate s
  m_mono p hp:=by
    by_cases hz : p=0
    · subst p
      simp only [ite_true,show 0+1≠0 by omega,ite_false]
      exact parisiCDF_nonneg _ _
    · simp only [hz,ite_false,show p+1≠0 by omega]
      apply parisiCDF_monotone
      exact s.q_mono' (min (p+1) (k+1)) (by omega) (min p (k+1))
        (min_le_min_right _ (Nat.le_succ p))

@[simp] theorem cdfMassScheme_q (s : RSBScheme k) (p : ℕ) : (cdfMassScheme s).q p=s.q p := rfl

@[simp] theorem cdfMassScheme_m_one (s : RSBScheme k) :
    (cdfMassScheme s).m 1=parisiCDF (parisiSchemeMeasure s) (s.q 1) := by
  simp only [cdfMassScheme,show (1:ℕ)≠0 by omega,ite_false,min_eq_left (by omega : 1≤k+1)]

theorem parisiSchemeMeasure_cdfMassScheme (s : RSBScheme k) :
    parisiSchemeMeasure (cdfMassScheme s)=parisiSchemeMeasure s := by
  apply FRSB.eq_of_parisiCDF_ae_eq
  apply Eventually.of_forall
  intro t
  by_cases ht0 : t<0
  · rw [FRSB.parisiCDF_eq_zero_of_lt_zero _ ht0,FRSB.parisiCDF_eq_zero_of_lt_zero _ ht0]
  by_cases ht1 : 1≤t
  · rw [parisiCDF_eq_one_of_one_le _ ht1,parisiCDF_eq_one_of_one_le _ ht1]
  obtain ⟨p,hp,hcell,_⟩:=exists_parisiFinite_right_cell s ⟨le_of_not_gt ht0,lt_of_not_ge ht1⟩
  rw [parisiCDF_scheme_cell (cdfMassScheme s) hp (by simpa only [cdfMassScheme_q] using hcell),
    parisiCDF_scheme_cell s hp hcell]
  by_cases hp0 : p=0
  · subst p
    simp only [cdfMassScheme,ite_true,s.m_zero]
  · simp only [cdfMassScheme,hp0,ite_false,min_eq_left hp]
    exact parisiCDF_scheme_cell s hp ⟨le_rfl,hcell.1.trans_lt hcell.2⟩

/-- The profile floor is exactly retained, even when observation insertion
introduced arbitrarily many repeated zero levels. -/
theorem cdfMassScheme_preserves_floor (s : RSBScheme k) (hs : s.q 1=0)
    (a : ℝ) (ha : a≤parisiCDF (parisiSchemeMeasure s) 0) : a≤(cdfMassScheme s).m 1 := by
  rw [cdfMassScheme_m_one,hs]
  exact ha

end FourPapersCommon
