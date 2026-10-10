module
public import FourPapersCommon.DyadicQuantileIntegral

@[expose] public section

/-! The actual entire free-quantile domain is a finite disjoint dyadic
union once the largest level is reached; no atomic exclusion is made. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem smallInterval_dyadic_partition (s : ℝ) (hs : 0<s) (N : ℕ)
    (hNext : 1<(2:ℝ)^(N+1)*s) :
    (⋃j∈Finset.range (N+1),dyadicQuantileShell s s j)=Ioo (0:ℝ) (1-s) := by
  ext v
  constructor
  · rintro ⟨_,⟨j,rfl⟩,hj⟩
    obtain ⟨_,⟨_,rfl⟩,hv⟩:=hj
    exact hv.1
  · intro hv
    have hcover:=dyadicQuantileShells_cover s s hs
    have hvall : v∈⋃j:ℕ,dyadicQuantileShell s s j := by
      rw [hcover]
      exact ⟨hv,by simp only [sub_self,mem_Ici];exact hv.1.le⟩
    obtain ⟨j,hj⟩:=mem_iUnion.mp hvall
    have hjN : j ≤ N := by
      by_contra h
      have hpow : (2:ℝ)^(N+1) ≤ (2:ℝ)^j:=pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul:=mul_le_mul_of_nonneg_right hpow hs.le
      have hvlo:=hj.2.1
      linarith [hv.2]
    exact mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr (by omega),hj⟩

theorem smallInterval_integral_dyadic_partition (ψ : ℝ → ℝ) (s : ℝ) (hs : 0<s)
    (hψ : IntegrableOn ψ (Ioo (0:ℝ) (1-s))) (N : ℕ) (hNext : 1<(2:ℝ)^(N+1)*s) :
    (∫v in Ioo (0:ℝ) (1-s),ψ v)=
      ∑j∈Finset.range (N+1),∫v in dyadicQuantileShell s s j,ψ v := by
  rw [←smallInterval_dyadic_partition s hs N hNext]
  apply integral_biUnion_finset
  · exact fun j _=>(dyadicQuantileShell_ordConnected s s j).measurableSet
  · intro j _ l _ hjl
    exact dyadicQuantileShells_pairwiseDisjoint s s hs hjl
  · exact fun j _=>hψ.mono_set (dyadicQuantileShell_subset s s j)

end QuantitativeFollowup
