module
public import QuantitativePaper.VectorPrefixGaussianLaw
public import QuantitativePaper.VectorSiteSymmetry

@[expose] public section

/-! The literal exponent of the normalized Gaussian prefix density. Both
the initial disorder tilt and every chronological transition are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def vectorPrefixLogWeight {n k:ℕ} (s:RSBScheme k) (β t a:ℝ):
    (N:ℕ)→FiniteHistory (VectorState n) N→ℝ
  | 0 =>fun h=>a*vectorRecursion s β t (h 0).1 (k+2) (h 0).2
  | N+1 =>fun h=>
      vectorPrefixLogWeight s β t a N (historySplit N h).1+
        s.m N*(vectorRecursion s β t (h (Fin.last (N+1))).1 (k+1-N)
          (h (Fin.last (N+1))).2-
          vectorRecursion s β t ((historySplit N h).1 (Fin.last N)).1 (k+2-N)
            ((historySplit N h).1 (Fin.last N)).2)

theorem vectorPrefixHistory_disorder {n k:ℕ} (s:RSBScheme k) (β t:ℝ) (N:ℕ)
    (p:VectorPrefixCoordinates n N) (i:Fin (N+1)):
    (vectorPrefixHistory s β t N p i).1=p.1:=
  independentHistory_preserved _ Prod.fst (vectorCoordinateUpdate_disorder s β t) N _ i

theorem vectorPrefixHistory_initial {n k:ℕ} (s:RSBScheme k) (β t:ℝ) (N:ℕ)
    (p:VectorPrefixCoordinates n N):vectorPrefixHistory s β t N p 0=(p.1,0):=
  independentHistory_initial _ N _

theorem vectorPrefixHistoryDensity_eq_exp {n k:ℕ} (s:RSBScheme k)
    (β t a:ℝ) (N:ℕ) (hN:N≤k+2) (h:FiniteHistory (VectorState n) N)
    (hx:(h 0).2=0) (hp:∀i,(h i).1=(h 0).1):
    vectorPrefixHistoryDensity s β t a N h=
      ENNReal.ofReal (Real.exp (vectorPrefixLogWeight s β t a N h)/
        vectorOuterPartition (n:=n) s β t a):=by
  induction N with
  | zero =>
    simp only [vectorPrefixHistoryDensity,finiteHistoryDensity,mul_one,
      vectorPrefixLogWeight,vectorInitialStateWeight,vectorOuterWeight,hx]
  | succ N ih =>
    let h0:FiniteHistory (VectorState n) N:=(historySplit N h).1
    let y:VectorState n:=(historySplit N h).2
    have he:h=Fin.snoc h0 y:=((historySplit N).symm_apply_apply h).symm
    have hzero:h0 0=h 0:=by rw [he,Fin.snoc_apply_zero]
    have hdis(i:Fin (N+1)):(h0 i).1=(h0 0).1:=by
      have hh:=hp i.castSucc
      rw [he,Fin.snoc_castSucc,Fin.snoc_apply_zero] at hh
      exact hh
    have hy:y.1=(h0 (Fin.last N)).1:=by
      have hl:=hp (Fin.last (N+1))
      rw [he,Fin.snoc_last,Fin.snoc_apply_zero] at hl
      exact hl.trans (hdis _).symm
    have hD:=ih (by omega) h0 (by rw [hzero];exact hx) hdis
    change vectorInitialStateWeight s β t a (h 0)*
      (finiteHistoryDensity (vectorProfileWeight s β t) N h0*
        vectorProfileWeight s β t N (h0 (Fin.last N)) y)=_
    rw [←mul_assoc,←hzero]
    change vectorPrefixHistoryDensity s β t a N h0*
      vectorProfileWeight s β t N (h0 (Fin.last N)) y=_
    rw [hD,vectorProfileWeight_eq_exp s β t N (by omega),
      ←ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t a).le)]
    congr 1
    change Real.exp (vectorPrefixLogWeight s β t a N h0)/vectorOuterPartition s β t a*
      Real.exp (s.m N*(vectorRecursion s β t (h0 (Fin.last N)).1 (k+1-N) y.2-
        vectorRecursion s β t (h0 (Fin.last N)).1 (k+2-N) (h0 (Fin.last N)).2))=
      Real.exp (vectorPrefixLogWeight s β t a N h0+
        s.m N*(vectorRecursion s β t y.1 (k+1-N) y.2-
          vectorRecursion s β t (h0 (Fin.last N)).1 (k+2-N) (h0 (Fin.last N)).2))/
        vectorOuterPartition s β t a
    rw [hy]
    rw [Real.exp_add]
    ring

theorem vectorPrefixGaussianLaw_eq_exp {n k:ℕ} (s:RSBScheme k)
    (β t a:ℝ) (N:ℕ) (hN:N≤k+2):
    vectorPrefixGaussianLaw (n:=n) s β t a N=
      (vectorPrefixCoordinateLaw n N).withDensity
        (fun p=>ENNReal.ofReal (Real.exp (vectorPrefixLogWeight s β t a N
          (vectorPrefixHistory s β t N p))/vectorOuterPartition (n:=n) s β t a)):=by
  unfold vectorPrefixGaussianLaw
  congr 1
  funext p
  apply vectorPrefixHistoryDensity_eq_exp s β t a N hN
  · rw [vectorPrefixHistory_initial]
  · intro i
    rw [vectorPrefixHistory_disorder,vectorPrefixHistory_disorder]

end QuantitativePaper
