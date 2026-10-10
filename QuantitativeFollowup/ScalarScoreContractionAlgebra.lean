module
public import QuantitativeFollowup.GaussianCovarianceMatrix

@[expose] public section

/-! Finite algebra behind a one-coordinate Gaussian response. These identities
are separate from the actual parameter derivative: they collapse the spatial
score contraction and cancel the third spatial derivative and curvature score. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

/-- A one-coordinate observable, a general first score, and a diagonal second
logarithmic score, all as literal scalar entries. -/
def scalarSparseGaussianScore {ι : Type*} [DecidableEq ι]
    (p : ι) (b diag : ι→ℝ) (Fp Fpp centered : ℝ) (i j : ι) : ℝ :=
  (if i=p ∧ j=p then Fpp else 0)+
    (if j=p then b i*Fp else 0)+(if i=p then b j*Fp else 0)+
      centered*((if i=j then diag i else 0)+b i*b j)

theorem scalar_sparse_score_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι) (K : ι→ι→ℝ) (hK : ∀i j,K i j=K j i)
    (b diag : ι→ℝ) (Fp Fpp centered : ℝ) :
    (1/2:ℝ)*(∑i,∑j,K i j*scalarSparseGaussianScore p b diag Fp Fpp centered i j)=
      (1/2:ℝ)*K p p*Fpp+Fp*(∑i,K i p*b i)+
        (1/2:ℝ)*centered*((∑i,K i i*diag i)+(∑i,∑j,K i j*b i*b j)) := by
  have h1 : (∑i,∑j,K i j*(if i=p ∧ j=p then Fpp else 0))=K p p*Fpp := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro i _ hip
      simp [hip]
    · simp
  have h2 : (∑i,∑j,K i j*(if j=p then b i*Fp else 0))=Fp*(∑i,K i p*b i) := by
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=>by ring
  have h3 : (∑i,∑j,K i j*(if i=p then b j*Fp else 0))=Fp*(∑i,K i p*b i) := by
    rw [Finset.sum_comm]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=>by rw [hK];ring
  have h4 : (∑i,∑j,K i j*(if i=j then diag i else 0))=∑i,K i i*diag i := by
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have he (i j : ι) : K i j*scalarSparseGaussianScore p b diag Fp Fpp centered i j=
      K i j*(if i=p ∧ j=p then Fpp else 0)+K i j*(if j=p then b i*Fp else 0)+
        K i j*(if i=p then b j*Fp else 0)+
        centered*(K i j*(if i=j then diag i else 0)+K i j*b i*b j) := by
    unfold scalarSparseGaussianScore
    ring
  have h5 : (∑i,∑j,centered*(K i j*(if i=j then diag i else 0)+K i j*b i*b j))=
      centered*((∑i,K i i*diag i)+(∑i,∑j,K i j*b i*b j)) := by
    simp_rw [←Finset.mul_sum, Finset.sum_add_distrib]
    rw [h4]
  simp_rw [he,Finset.sum_add_distrib]
  rw [h1,h2,h3,h5]
  ring

theorem scalar_response_third_derivative_cancel (φ m h third a : ℝ) :
    -φ*(m*third+2*a*m^2*h)+φ*(h^2+m*third)+2*φ*m^2*h=
      φ*(h^2+2*(1-a)*m^2*h) := by ring

theorem scalar_response_curvature_score_cancel {ι : Type*} [Fintype ι]
    (w φ h a m : ι→ℝ) (centered : ℝ) :
    (1/2:ℝ)*centered*(∑i,w i*φ i*(h i+a i*m i^2))-
      (1/2:ℝ)*centered*(∑i,w i*φ i*h i)=
        (1/2:ℝ)*centered*(∑i,w i*φ i*a i*m i^2) := by
  have he : (∑i,w i*φ i*(h i+a i*m i^2))=
      (∑i,w i*φ i*h i)+(∑i,w i*φ i*a i*m i^2) := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _=>by ring
  rw [he]
  ring

end QuantitativeFollowup
