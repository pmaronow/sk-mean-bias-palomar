module
public import QuantitativePaper.ResponseTentCellSplit
public import FourPapersCommon.CellDifferenceTelescope

@[expose] public section

/-! Genuine tent-tested FTC from affine closed-subinterval identities.
Every corner is handled by a finite subdivision; no derivative at a
corner or omitted boundary term is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000

theorem responseTent_tested_interval (ell a b : ℝ) (hell : 0<ell) (hab : a≤b)
    (p : ℕ) (R H : ℝ→ℝ)
    (hInt : IntervalIntegrable (fun q=>(p:ℝ)*responseTentSlope ell q*
      (responseTent ell q)^(p-1)*R q+(responseTent ell q)^p*H q) volume a b)
    (hFTC : ∀α δ l u : ℝ,l≤u→a≤l→u≤b→
      (α+δ*u)^p*R u-(α+δ*l)^p*R l=
        ∫q in l..u,(p:ℝ)*δ*(α+δ*q)^(p-1)*R q+(α+δ*q)^p*H q) :
    (responseTent ell b)^p*R b-(responseTent ell a)^p*R a=
      ∫q in a..b,(p:ℝ)*responseTentSlope ell q*(responseTent ell q)^(p-1)*R q+
        (responseTent ell q)^p*H q := by
  let T:=responseTentCellNode ell a b
  let f:=fun q=>(p:ℝ)*responseTentSlope ell q*(responseTent ell q)^(p-1)*R q+
    (responseTent ell q)^p*H q
  have hpart (j : ℕ) (hj : j<4) : IntervalIntegrable f volume (T j) (T (j+1)):=by
    apply hInt.mono_set
    rw [uIcc_of_le (responseTentCellNode_step ell a b hell hab j hj),uIcc_of_le hab]
    exact Icc_subset_Icc (responseTentCellNode_mem ell a b hab j (by omega)).1
      (responseTentCellNode_mem ell a b hab (j+1) (by omega)).2
  have hpiece (j : ℕ) (hj : j<4) :
      (responseTent ell (T (j+1)))^p*R (T (j+1))-(responseTent ell (T j))^p*R (T j)=
        ∫q in T j..T (j+1),f q:=by
    have hle:=responseTentCellNode_step ell a b hell hab j hj
    by_cases heq : T j=T (j+1)
    · rw [heq,sub_self,intervalIntegral.integral_same]
    · have hlt : T j<T (j+1):=lt_of_le_of_ne hle heq
      have haff:=hFTC (responseTentCellAlpha j) (responseTentCellDelta ell j) (T j) (T (j+1)) hle
        (responseTentCellNode_mem ell a b hab j (by omega)).1
        (responseTentCellNode_mem ell a b hab (j+1) (by omega)).2
      rw [←responseTentCell_piece ell a b hell hab j hj hlt (T (j+1)) ⟨hle,le_rfl⟩,
        ←responseTentCell_piece ell a b hell hab j hj hlt (T j) ⟨le_rfl,hle⟩] at haff
      refine haff.trans (intervalIntegral.integral_congr_ae ?_)
      filter_upwards [volume.ae_ne (T (j+1)),ae_deriv_responseTent hell] with q hqne hqd
      intro hq
      rw [uIoc_of_le hle] at hq
      have hqo : q∈Ioo (T j) (T (j+1)):=⟨hq.1,lt_of_le_of_ne hq.2 hqne⟩
      have hd:=(hasDerivAt_responseTentCell_piece ell a b hell hab j hj q hqo).deriv
      rw [hqd] at hd
      have hv:=responseTentCell_piece ell a b hell hab j hj hlt q ⟨hqo.1.le,hqo.2.le⟩
      dsimp only [f]
      rw [hd,hv]
  have hsum:=Finset.sum_congr rfl (fun j hj=>hpiece j (Finset.mem_range.mp hj))
  have htel:=FourPapersCommon.sum_cell_differences_of_match
    (fun (_i : ℕ) q=>(responseTent ell q)^p*R q) T 3 (by intros; rfl)
  have hint:=intervalIntegral.sum_integral_adjacent_intervals (n:=4) hpart
  rw [htel,hint] at hsum
  simpa only [T,Nat.reduceAdd,responseTentCellNode_zero,responseTentCellNode_four,f] using hsum

end QuantitativePaper
