module
public import QuantitativePaper.VectorSiteGaussianCoordinates
public import QuantitativePaper.VectorEnergyRegularity

@[expose] public section

/-! Actual incident-site conditioned prefix observables. The log density is
even and the site magnetization is odd under negation of the independent
incident-site Gaussian block. Smoothness and continuity are inherited from
the constructed finite recursion and linear Gaussian history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem vectorPrefixLogWeight_site_reflection {n k : ℕ} (s : RSBScheme k)
    (i : Fin n) (β t a : ℝ) (N : ℕ) (h : FiniteHistory (VectorState n) N) :
    vectorPrefixLogWeight s β t a N (fun j => siteStateReflection i (h j)) =
      vectorPrefixLogWeight s β t a N h := by
  induction N with
  | zero =>
    change a * vectorRecursion s β t (siteDisorderReflection i (h 0).1) (k+2)
      (siteFieldReflection i (h 0).2) = _
    rw [vectorRecursion_site_reflection]
    rfl
  | succ N ih =>
    have hprefix : (historySplit N (fun j => siteStateReflection i (h j))).1 =
        fun j => siteStateReflection i ((historySplit N h).1 j) := rfl
    simp only [vectorPrefixLogWeight, hprefix]
    rw [ih]
    change _ + s.m N *
      (vectorRecursion s β t (siteDisorderReflection i (h (Fin.last (N+1))).1)
        (k+1-N) (siteFieldReflection i (h (Fin.last (N+1))).2) -
       vectorRecursion s β t
        (siteDisorderReflection i ((historySplit N h).1 (Fin.last N)).1) (k+2-N)
        (siteFieldReflection i ((historySplit N h).1 (Fin.last N)).2)) = _
    rw [vectorRecursion_site_reflection, vectorRecursion_site_reflection]

private theorem contDiff_vectorPrefixLogWeight_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) (N : ℕ)
    (h : E → FiniteHistory (VectorState n) N) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z => vectorPrefixLogWeight s β t a N (h z)) := by
  induction N with
  | zero =>
    exact contDiff_const.mul ((contDiff_vectorRecursion_joint s β t (k+2)).comp
      ((ContinuousLinearMap.proj (0 : Fin 1) :
        FiniteHistory (VectorState n) 0 →L[ℝ] VectorState n).contDiff.comp hh))
  | succ N ih =>
    let h0 : E → FiniteHistory (VectorState n) N := fun z => (historySplit N (h z)).1
    have hh0 : ContDiff ℝ ∞ h0 :=
      (ContinuousLinearMap.pi fun j : Fin (N+1) =>
        (ContinuousLinearMap.proj j.castSucc : FiniteHistory (VectorState n) (N+1) →L[ℝ]
          VectorState n)).contDiff.comp hh
    have hp1 := (contDiff_vectorRecursion_joint s β t (k+1-N)).comp
      ((ContinuousLinearMap.proj (Fin.last (N+1))).contDiff.comp hh)
    have hp0 := (contDiff_vectorRecursion_joint s β t (k+2-N)).comp
      ((ContinuousLinearMap.proj (Fin.last N)).contDiff.comp hh0)
    exact (ih h0 hh0).add (contDiff_const.mul (hp1.sub hp0))

def sitePrefixGaussianState {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (j : Fin (N+1)) (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) : VectorState n :=
  vectorPrefixEuclideanHistory s β t N
    (gaussianCoordinateJoin (siteGaussianPredicate i) (g,b)) j

def sitePrefixGaussianLogWeight {n k N : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) : ℝ :=
  vectorPrefixLogWeight s β t a N (fun j => sitePrefixGaussianState s β t i b j g)

def sitePrefixGaussianMagnetization {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) : ℝ :=
  vectorMagnetization s β t (sitePrefixGaussianState s β t i b (Fin.last N) g).1
    (k+2-N) (sitePrefixGaussianState s β t i b (Fin.last N) g).2 i

def sitePrefixGaussianCurvature {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) : ℝ :=
  β * (vectorFieldHessian s β t (sitePrefixGaussianState s β t i b (Fin.last N) g).1
    (k+2-N) (sitePrefixGaussianState s β t i b (Fin.last N) g).2
    (EuclideanSpace.single i 1)) i

theorem sitePrefixGaussianState_neg {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (j : Fin (N+1)) (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    sitePrefixGaussianState s β t i b j (-g) =
      siteStateReflection i (sitePrefixGaussianState s β t i b j g) := by
  unfold sitePrefixGaussianState
  rw [siteGaussianJoin_neg, vectorPrefixEuclideanHistory_site_reflection]

theorem sitePrefixGaussianLogWeight_even {n k N : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    sitePrefixGaussianLogWeight s β t a i b (-g) = sitePrefixGaussianLogWeight s β t a i b g := by
  unfold sitePrefixGaussianLogWeight
  simp_rw [sitePrefixGaussianState_neg]
  exact vectorPrefixLogWeight_site_reflection s i β t a N _

theorem sitePrefixGaussianMagnetization_odd {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    sitePrefixGaussianMagnetization s β t i b (-g) = -sitePrefixGaussianMagnetization s β t i b g := by
  unfold sitePrefixGaussianMagnetization
  rw [sitePrefixGaussianState_neg]
  simpa only [siteStateReflection, siteSign, ite_true, neg_one_mul] using
    vectorSpinMean_site_reflection s i i β t _ (k+2-N) _

theorem contDiff_sitePrefixGaussianState {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) (j : Fin (N+1)) :
    ContDiff ℝ ∞ (sitePrefixGaussianState s β t i b j) :=
  (ContinuousLinearMap.proj j).contDiff.comp
    ((vectorPrefixEuclideanHistory s β t N).contDiff.comp
      ((gaussianCoordinateJoin (siteGaussianPredicate i)).contDiff.comp
        (contDiff_id.prodMk contDiff_const)))

theorem contDiff_sitePrefixGaussianLogWeight {n k N : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) :
    ContDiff ℝ ∞ (sitePrefixGaussianLogWeight s β t a i b) :=
  contDiff_vectorPrefixLogWeight_comp s β t a N _
    (contDiff_pi.mpr (fun j => contDiff_sitePrefixGaussianState s β t i b j))

theorem contDiff_sitePrefixGaussianMagnetization {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) :
    ContDiff ℝ ∞ (sitePrefixGaussianMagnetization s β t i b) :=
  (boundedJets_vectorMagnetization_component s β t (k+2-N) i).1.comp
    (contDiff_sitePrefixGaussianState s β t i b (Fin.last N))

theorem continuous_sitePrefixGaussianCurvature {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) :
    Continuous (sitePrefixGaussianCurvature s β t i b) :=
  ((continuous_vectorFieldHessian_component s β t (k+2-N) i i).comp
    (contDiff_sitePrefixGaussianState s β t i b (Fin.last N)).continuous).const_mul β

theorem abs_sitePrefixGaussianMagnetization_le_one {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    |sitePrefixGaussianMagnetization s β t i b g| ≤ 1 :=
  vectorMagnetization_component_bound s β t _ (k+2-N) _ i

theorem sitePrefixGaussianCurvature_diagonal_bound {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i))
    (hm : 1 ≤ β * observableDepthMass s (k+2-N)) :
    1 - |sitePrefixGaussianMagnetization s β t i b g| ≤
      sitePrefixGaussianCurvature s β t i b g :=
  vectorPhysicalHessian_one_sub_abs_le s β t hβ _ (k+2-N) _ i hm

theorem abs_sitePrefixGaussianCurvature_le {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : 0 ≤ β) (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    |sitePrefixGaussianCurvature s β t i b g| ≤ β := by
  have h0 := vectorFieldHessian_diagonal_nonneg s β t
    (sitePrefixGaussianState s β t i b (Fin.last N) g).1 (k+2-N)
    (sitePrefixGaussianState s β t i b (Fin.last N) g).2 i
  have h1 := (vectorPhysicalHessian_diagonal_bounds s β t hβ
    (sitePrefixGaussianState s β t i b (Fin.last N) g).1 (k+2-N)
    (sitePrefixGaussianState s β t i b (Fin.last N) g).2 i).2
  unfold sitePrefixGaussianCurvature
  rw [abs_of_nonneg (mul_nonneg hβ h0)]
  exact h1

end QuantitativePaper
