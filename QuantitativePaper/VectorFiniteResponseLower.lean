module
public import QuantitativePaper.VectorRootCellCurvature
public import QuantitativePaper.VectorPrefixObservableTransport

@[expose] public section

/-! The conditional site estimate yields the physical expected Hessian
trace under the actual finite tilted diffusion, with the true root floor
and the incoming/outgoing mass conditions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def vectorFiniteNodeCurvature {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (N : ℕ) (i : Fin n) (x : VectorState n) : ℝ :=
  β*(vectorFieldHessian s β t x.1 (k+2-N) x.2 (EuclideanSpace.single i 1)) i

theorem continuous_vectorFiniteNodeCurvature {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (N : ℕ) (i : Fin n) :
    Continuous (vectorFiniteNodeCurvature s β t N i) :=
  (continuous_vectorFieldHessian_component s β t (k+2-N) i i).const_mul β

theorem abs_vectorFiniteNodeCurvature_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (N : ℕ) (i : Fin n) (x : VectorState n) :
    |vectorFiniteNodeCurvature s β t N i x| ≤ β := by
  rw [vectorFiniteNodeCurvature,abs_of_nonneg (mul_nonneg hβ
    (vectorFieldHessian_diagonal_nonneg s β t x.1 (k+2-N) x.2 i))]
  exact (vectorPhysicalHessian_diagonal_bounds s β t hβ x.1 (k+2-N) x.2 i).2

theorem vectorFiniteNodeCurvature_expected_lower {n k : ℕ} (s : RSBScheme k)
    (β t a U : ℝ) (hβ : 0 < β) (ht : t ∈ Ico 0 1)
    (ha0 : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0)
    (N : ℕ) (hNpos : 0 < N) (hN : N ≤ k+2) (i : Fin n)
    (hm : 1 ≤ β*observableDepthMass s (k+2-N))
    (hin : β*(if N=1 then a else s.m (N-1)) ≤ max 1 U) :
    responseCurvatureConstant U ≤
      ∫sample,vectorFiniteNodeCurvature s β t N i
        (vectorFiniteJointState s β t ht.2.le (s.q N).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  have hh := integral_vectorPrefixSiteCurvature_root_lower s β t a U hβ
    ⟨ht.1,ht.2.le⟩ ha0 ha hq N hNpos hN i hm hin
  have he := integral_vectorPrefixEuclideanLaw_finiteState s β t a hβ.ne' ht.2 N hN
    (vectorFiniteNodeCurvature s β t N i)
    (continuous_vectorFiniteNodeCurvature s β t N i).measurable β
    (abs_vectorFiniteNodeCurvature_le s β t hβ.le N i)
  change responseCurvatureConstant U ≤
    ∫z,vectorFiniteNodeCurvature s β t N i
      (vectorPrefixEuclideanHistory s β t N z (Fin.last N))
      ∂vectorPrefixEuclideanLaw s β t a N at hh
  rw [he] at hh
  exact hh

theorem vectorFiniteNodeTrace_expected_lower {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β t a U : ℝ) (hβ : 0 < β) (ht : t ∈ Ico 0 1)
    (ha0 : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0)
    (N : ℕ) (hNpos : 0 < N) (hN : N ≤ k+2)
    (hm : 1 ≤ β*observableDepthMass s (k+2-N))
    (hin : β*(if N=1 then a else s.m (N-1)) ≤ max 1 U) :
    responseCurvatureConstant U ≤ (1/(n : ℝ))*
      ∫sample,∑i : Fin n,vectorFiniteNodeCurvature s β t N i
        (vectorFiniteJointState s β t ht.2.le (s.q N).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  letI := vectorFiniteDisorderTilt_probability (n:=n) s β t a
  have hi (i : Fin n) : Integrable (fun sample=>vectorFiniteNodeCurvature s β t N i
      (vectorFiniteJointState s β t ht.2.le (s.q N).toNNReal sample))
      (vectorFiniteDisorderTilt s β t a) :=
    Integrable.of_bound ((continuous_vectorFiniteNodeCurvature s β t N i).measurable.comp
      (measurable_vectorFiniteJointState s β t ht.2.le _)).aestronglyMeasurable β
      (.of_forall fun sample=>by simpa only [Real.norm_eq_abs] using
        abs_vectorFiniteNodeCurvature_le s β t hβ.le N i _)
  rw [integral_finsetSum _ (fun i _=>hi i)]
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin n))) (fun i _=>
    vectorFiniteNodeCurvature_expected_lower s β t a U hβ ht ha0 ha hq N hNpos hN i hm hin)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1/(n : ℝ))
  simpa only [←mul_assoc,one_div_mul_cancel hnR.ne',one_mul] using hh

end QuantitativePaper
