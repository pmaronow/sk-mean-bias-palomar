module
public import QuantitativePaper.VectorPrefixDensityLipschitz

@[expose] public section

/-! Genuine finite-prefix normalization in Euclidean Gaussian coordinates.
No conditional-density or normalizing-integral conclusion is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem vectorPrefixEuclideanLaw_probability {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) (hN : N≤k+2) :
    IsProbabilityMeasure (vectorPrefixEuclideanLaw (n:=n) s β t a N) := by
  rw [←Measure.isProbabilityMeasure_map_iff
    (vectorPrefixEuclideanCoordinates n N).measurable.aemeasurable,vectorPrefixEuclideanLaw_map]
  exact vectorPrefixGaussianLaw_probability s β t a N

theorem vectorPrefixEuclideanLaw_eq_exp {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) (hN : N≤k+2) :
    vectorPrefixEuclideanLaw (n:=n) s β t a N=
      (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)).withDensity
        (fun z=>ENNReal.ofReal (Real.exp (vectorPrefixLogWeight s β t a N
          (vectorPrefixEuclideanHistory s β t N z))/vectorOuterPartition (n:=n) s β t a)) := by
  unfold vectorPrefixEuclideanLaw
  congr 1
  funext z
  apply vectorPrefixHistoryDensity_eq_exp s β t a N hN
  · rw [vectorPrefixEuclideanHistory_apply,vectorPrefixHistory_initial]
  · intro j
    rw [vectorPrefixEuclideanHistory_apply,vectorPrefixHistory_disorder,vectorPrefixHistory_disorder]

private theorem measurable_vectorPrefixLogWeight_history {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) :
    Measurable (vectorPrefixLogWeight (n:=n) s β t a N) := by
  induction N with
  | zero =>
    exact measurable_const.mul ((measurable_vectorRecursion s β t (k+2)).comp
      (measurable_pi_apply (0:Fin 1)))
  | succ N ih =>
    have hp := ih.comp (historySplit N).measurable.fst
    have h1 : Measurable (fun h : FiniteHistory (VectorState n) (N+1)=>
        vectorRecursion s β t (h (Fin.last (N+1))).1 (k+1-N)
          (h (Fin.last (N+1))).2) :=
      (measurable_vectorRecursion (n:=n) s β t (k+1-N)).comp
        (measurable_pi_apply (Fin.last (N+1)))
    have h0 := (measurable_vectorRecursion (n:=n) s β t (k+2-N)).comp
      ((measurable_pi_apply (Fin.last N)).comp (historySplit N).measurable.fst)
    exact hp.add (measurable_const.mul (h1.sub h0))

theorem measurable_vectorPrefixEuclideanLogWeight {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) :
    Measurable (fun z : VectorPrefixGaussianSpace n N=>vectorPrefixLogWeight s β t a N
      (vectorPrefixEuclideanHistory s β t N z)) :=
  (measurable_vectorPrefixLogWeight_history s β t a N).comp
    (vectorPrefixEuclideanHistory s β t N).measurable

theorem integral_vectorPrefixEuclideanLaw {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) (hN : N≤k+2) (F : VectorPrefixGaussianSpace n N→ℝ) :
    (∫z,F z∂vectorPrefixEuclideanLaw s β t a N)=
      (∫z,Real.exp (vectorPrefixLogWeight s β t a N (vectorPrefixEuclideanHistory s β t N z))*F z
        ∂SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N))/
          vectorOuterPartition (n:=n) s β t a := by
  let V := fun z : VectorPrefixGaussianSpace n N=>vectorPrefixLogWeight s β t a N
    (vectorPrefixEuclideanHistory s β t N z)
  have hV := measurable_vectorPrefixEuclideanLogWeight (n:=n) s β t a N
  have hpos := vectorOuterPartition_pos (n:=n) s β t a
  rw [vectorPrefixEuclideanLaw_eq_exp s β t a N hN,
    integral_withDensity_eq_integral_toReal_smul (hV.exp.div_const _ |>.ennreal_ofReal)
      (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hpos.le)]
  change (∫z,(Real.exp (V z)/vectorOuterPartition (n:=n) s β t a)*F z∂_)=_
  have he : (fun z=>(Real.exp (V z)/vectorOuterPartition (n:=n) s β t a)*F z)=
      fun z=>(Real.exp (V z)*F z)/vectorOuterPartition (n:=n) s β t a := by funext z;ring
  rw [he,integral_div]

theorem integrable_exp_vectorPrefixEuclideanLogWeight {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) (hN : N≤k+2) :
    Integrable (fun z : VectorPrefixGaussianSpace n N=>Real.exp (vectorPrefixLogWeight s β t a N
      (vectorPrefixEuclideanHistory s β t N z)))
        (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)) := by
  letI := vectorPrefixEuclideanLaw_probability (n:=n) s β t a N hN
  have hi : Integrable (fun _ : VectorPrefixGaussianSpace n N=>(1:ℝ))
      (vectorPrefixEuclideanLaw s β t a N) := integrable_const _
  have hpos := vectorOuterPartition_pos (n:=n) s β t a
  rw [vectorPrefixEuclideanLaw_eq_exp s β t a N hN,
    integrable_withDensity_iff_integrable_smul'
      ((measurable_vectorPrefixEuclideanLogWeight (n:=n) s β t a N).exp.div_const _ |>.ennreal_ofReal)
      (.of_forall fun _=>ENNReal.ofReal_lt_top)] at hi
  simp only [smul_eq_mul,mul_one] at hi
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hpos.le)] at hi
  have hh := hi.mul_const (vectorOuterPartition (n:=n) s β t a)
  simpa only [div_mul_cancel₀ _ hpos.ne'] using hh

theorem integral_exp_vectorPrefixEuclideanLogWeight {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) (hN : N≤k+2) :
    (∫z : VectorPrefixGaussianSpace n N,Real.exp (vectorPrefixLogWeight s β t a N
      (vectorPrefixEuclideanHistory s β t N z))
        ∂SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N))=
      vectorOuterPartition (n:=n) s β t a := by
  letI := vectorPrefixEuclideanLaw_probability (n:=n) s β t a N hN
  have hh := integral_vectorPrefixEuclideanLaw (n:=n) s β t a N hN (fun _=>1)
  simp only [integral_const,probReal_univ,one_smul,mul_one] at hh
  exact (by simpa using ((eq_div_iff (vectorOuterPartition_pos (n:=n) s β t a).ne').mp hh).symm)

theorem siteGaussianJoin_law {n N : ℕ} (i : Fin n) :
    ((SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)).prod
      (SYK.standardGaussianMeasureOnEuclidean (SiteComplementIndex (N:=N) i))).map
        (gaussianCoordinateJoin (siteGaussianPredicate i))=
      SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N) := by
  rw [←siteGaussianSplit_law i,
    Measure.map_map (gaussianCoordinateJoin (siteGaussianPredicate i)).measurable
      (gaussianCoordinateSplit (siteGaussianPredicate i)).measurable]
  have he : gaussianCoordinateJoin (siteGaussianPredicate (N:=N) i)∘gaussianCoordinateSplit
      (siteGaussianPredicate (N:=N) i)=(id : VectorPrefixGaussianSpace n N→VectorPrefixGaussianSpace n N) :=
    funext (gaussianCoordinateJoin_split _)
  rw [he,Measure.map_id]

end QuantitativePaper
