module
public import QuantitativePaper.VectorInterpolationRootSchedule
public import QuantitativePaper.VectorProfileMeasure

@[expose] public section

/-! The descending cascade split weights are precisely the actual finite
Stieltjes free measure, including the retained root atom. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
variable {k : ℕ}

def vectorRootInterpolationOverlap (s : RSBScheme k) (p : ℕ) : Paper.Overlap :=
  ⟨s.q (k+2-p),s.q_nonneg (Nat.sub_le _ _),s.q_le_one (Nat.sub_le _ _)⟩

theorem vectorRootInterpolation_free_measure_sum (s : RSBScheme k) (a : ℝ)
    (ha : a ≤ s.m 1) (f : Paper.Overlap→ℝ) :
    (∑p∈Finset.range (k+1),(vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
      f (vectorRootInterpolationOverlap s (p+1)))=
      ∫q,f q∂vectorProfileFreeMeasure s a := by
  classical
  rw [integral_vectorProfileFreeMeasure s a ha,Fintype.sum_option,Finset.sum_range_succ]
  simp only [vectorPosteriorFeatureWeight,vectorRootInterpolationMass,lt_self_iff_false,
    ite_false,show k<k+1 by omega,ite_true,show k+1-k=1 by omega]
  have hroot : vectorRootInterpolationOverlap s (k+1)=vectorProfileAtom s none := by
    apply Subtype.ext
    simp [vectorRootInterpolationOverlap,vectorProfileAtom,vectorPosteriorFeatureTime]
  rw [hroot]
  rw [add_comm]
  congr 1
  let g : ℕ→ℝ:=fun p=>(vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
    f (vectorRootInterpolationOverlap s (p+1))
  change (∑p∈Finset.range k,g p)=∑i:Fin k,(s.m (i+2)-s.m (i+1))*f (vectorProfileAtom s (some i))
  rw [←Fin.sum_univ_eq_sum_range g]
  calc
    (∑p:Fin k,g p)=∑p:Fin k,(s.m ((Fin.rev p:Fin k)+2)-s.m ((Fin.rev p:Fin k)+1))*
        f (vectorProfileAtom s (some (Fin.rev p))) := by
      apply Finset.sum_congr rfl
      intro p _
      have hp:p.val<k:=p.isLt
      dsimp only [g]
      simp only [vectorRootInterpolationMass,show p.val<k+1 by omega,
        show p.val+1<k+1 by omega,ite_true]
      have h₁ : (Fin.rev p:Fin k).val+2=k+1-p.val := by simp only [Fin.rev];omega
      have h₂ : (Fin.rev p:Fin k).val+1=k+1-(p.val+1) := by simp only [Fin.rev];omega
      rw [h₁,h₂]
      congr 1
      apply congrArg f
      apply Subtype.ext
      dsimp only [vectorRootInterpolationOverlap,vectorProfileAtom,vectorPosteriorFeatureTime]
      change s.q (k+2-(p.val+1))=s.q ((Fin.rev p).val+2)
      rw [h₁]
      congr 1
      omega
    _=_:=by
      simpa only [Fin.revPerm_apply] using Equiv.sum_comp (Fin.revPerm (n:=k))
        (fun i:Fin k=>(s.m (i+2)-s.m (i+1))*f (vectorProfileAtom s (some i)))

end QuantitativePaper
