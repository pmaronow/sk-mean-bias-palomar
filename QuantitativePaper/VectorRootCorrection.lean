module
public import QuantitativePaper.VectorRootFreeMeasure
public import FourPapersCommon.FiniteWeightedDifferences

@[expose] public section

/-! Exact CDF correction cancellation against the finite descending
Stieltjes overlap-square moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
variable {k : ℕ}

theorem vectorRootInterpolation_square_correction (s : RSBScheme k) (a : ℝ)
    (hq : s.q 1=0) :
    (∑p∈Finset.range (k+1),(vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
      (vectorRootInterpolationOverlap s (p+1):ℝ)^2)=
      1-2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q := by
  classical
  let mass:=vectorRootInterpolationMass s a
  let f : ℕ→ℝ:=fun p=>(s.q (k+2-p))^2
  have hsum:=finite_weighted_differences mass f (k+1)
  have hsource : (∑p∈Finset.range (k+1),mass p*(f p-f (p+1)))=
      2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q := by
    rw [Paper.parisiScheme_cdf_integral]
    rw [←Finset.sum_range_reflect (fun p=>s.m (p+1)*(s.q (p+2)^2-s.q (p+1)^2)) (k+1)]
    have he : (∑p∈Finset.range (k+1),mass p*(f p-f (p+1)))=
        ∑p∈Finset.range (k+1),s.m (k+1-1-p+1)*
          (s.q (k+1-1-p+2)^2-s.q (k+1-1-p+1)^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp':p<k+1:=Finset.mem_range.mp hp
      dsimp only [mass,f]
      rw [vectorRootInterpolationMass,if_pos hp']
      rw [show k+2-(p+1)=k+1-p by omega,
        show k+1-1-p+2=k+2-p by omega,show k+1-1-p+1=k+1-p by omega]
    rw [he]
    ring
  have hm0 : mass 0=1:=by simp [mass,vectorRootInterpolationMass,s.m_top]
  have hf0 : f 0=1:=by simp [f,s.q_top]
  have hfN : f (k+1)=0:=by simp [f,hq]
  rw [hsource,hm0,hf0,hfN] at hsum
  dsimp only [mass,f] at hsum
  simpa only [vectorRootInterpolationOverlap] using (by linarith :
    (∑p∈Finset.range (k+1),(vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
      (s.q (k+2-(p+1)))^2)=1-2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q)

end QuantitativePaper
