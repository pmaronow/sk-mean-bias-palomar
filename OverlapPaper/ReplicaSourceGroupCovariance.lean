module
public import OverlapPaper.ReplicaSourceFiniteState

@[expose] public section

/-! Actual independent Gaussian site/group fields and their full replica
covariance. One group field is copied to every replica in that group. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace OverlapPaper

variable {n d g : ℕ}

def replicaGroupSpinVector (groupOf : Fin d → Fin g) (l : Fin d)
    (σ : ReplicaConfiguration n d) : EuclideanSpace ℝ (Fin n × Fin g) :=
  WithLp.toLp 2 (fun p => if groupOf l = p.2 then spin (σ l p.1) else 0)

theorem inner_replicaGroupSpinVector (groupOf : Fin d → Fin g)
    (l j : Fin d) (σ τ : ReplicaConfiguration n d) :
    inner ℝ (replicaGroupSpinVector groupOf l σ) (replicaGroupSpinVector groupOf j τ) =
      if groupOf l = groupOf j then ∑ i : Fin n, spin (σ l i) * spin (τ j i) else 0 := by
  classical
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [replicaGroupSpinVector, dotProduct, star_trivial, WithLp.ofLp_toLp,
    Fintype.sum_prod_type]
  have he (i : Fin n) :
      (∑ z : Fin g, (if groupOf l = z then spin (σ l i) else 0) *
        (if groupOf j = z then spin (τ j i) else 0)) =
        if groupOf l = groupOf j then spin (σ l i) * spin (τ j i) else 0 := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : groupOf l = groupOf j
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [he]
  by_cases h : groupOf l = groupOf j <;> simp [h]

theorem covariance_inner_stdGaussian {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] (x y : A) :
    cov[fun z => inner ℝ x z, fun z => inner ℝ y z; stdGaussian A] = inner ℝ x y := by
  have H := covarianceBilin_apply_eq_cov
    (IsGaussian.memLp_id (stdGaussian A) 2 (by simp)) x y
  rw [covarianceBilin_stdGaussian] at H
  exact H.symm

def replicaGroupFieldCoordinate (v : ℝ) (groupOf : Fin d → Fin g)
    (σ : ReplicaConfiguration n d) : EuclideanSpace ℝ (Fin n × Fin g) →L[ℝ] ℝ :=
  ∑ l : Fin d, Real.sqrt v • innerSL ℝ (replicaGroupSpinVector groupOf l σ)

theorem replicaGroupFieldCoordinate_covariance (v : ℝ) (hv : 0 ≤ v)
    (groupOf : Fin d → Fin g) (σ τ : ReplicaConfiguration n d) :
    cov[replicaGroupFieldCoordinate v groupOf σ, replicaGroupFieldCoordinate v groupOf τ;
      stdGaussian (EuclideanSpace ℝ (Fin n × Fin g))] =
        (n : ℝ) * replicaFieldCovariance (fun l j => if groupOf l = groupOf j then v else 0) σ τ := by
  classical
  unfold replicaFieldCovariance
  have he (ρ : ReplicaConfiguration n d) :
      (replicaGroupFieldCoordinate v groupOf ρ : EuclideanSpace ℝ (Fin n × Fin g) → ℝ) =
      fun z => ∑ l : Fin d, Real.sqrt v * inner ℝ (replicaGroupSpinVector groupOf l ρ) z := by
    funext z
    simp [replicaGroupFieldCoordinate]
  rw [he σ, he τ]
  have hi (ρ : ReplicaConfiguration n d) (l : Fin d) :
      MemLp (fun z : EuclideanSpace ℝ (Fin n × Fin g) => Real.sqrt v *
        inner ℝ (replicaGroupSpinVector groupOf l ρ) z) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin g))) := by
    simpa only [coe_innerSL_apply] using
      (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin n × Fin g)))
        (innerSL ℝ (replicaGroupSpinVector groupOf l ρ)) 2 (by simp)).const_mul (Real.sqrt v)
  rw [covariance_fun_sum_fun_sum (hi σ) (hi τ)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_inner_stdGaussian, inner_replicaGroupSpinVector]
  simp only [replicaFieldCovariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : groupOf l = groupOf j
  · simp only [h, if_true, overlap]
    have hn : (n : ℝ) * ((∑ i : Fin n, spin (σ l i) * spin (τ j i)) / n) =
        ∑ i : Fin n, spin (σ l i) * spin (τ j i) := by
      by_cases hn : n = 0
      · simp [hn]
      · field_simp
    rw [show (n : ℝ) * (v * ((∑ i : Fin n, spin (σ l i) * spin (τ j i)) / n)) =
      v * ((n : ℝ) * ((∑ i : Fin n, spin (σ l i) * spin (τ j i)) / n)) by ring, hn]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hv]
  · simp [h]

def replicaGroupFieldCLM (D : Matrix (Fin d) (Fin d) ℝ) (η v : ℝ)
    (groupOf : Fin d → Fin g) :
    EuclideanSpace ℝ (Fin n × Fin g) →L[ℝ] FourPapersCommon.FiniteStateField
      (ReplicaSourceState n d D η) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun σ => replicaGroupFieldCoordinate v groupOf σ.1 z)
      map_add' := by intro x y; ext σ; simp
      map_smul' := by intro c x; ext σ; simp }

theorem replicaGroupFieldCLM_apply (D : Matrix (Fin d) (Fin d) ℝ) (η v : ℝ)
    (groupOf : Fin d → Fin g) (z : EuclideanSpace ℝ (Fin n × Fin g))
    (σ : ReplicaSourceState n d D η) :
    replicaGroupFieldCLM D η v groupOf z σ = replicaGroupFieldCoordinate v groupOf σ.1 z := rfl

end OverlapPaper
