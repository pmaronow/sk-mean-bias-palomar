module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralNativeProcesses
public import QuantitativeFollowup.AnisotropicSpinPathCovariance
public import QuantitativeFollowup.AnisotropicProcessCovarianceEnergy

@[expose] public section

/-! The native noise-energy polarization is literally H Lambda H.
Every matrix is constructed from the actual all-profile derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def nativeAnisotropicProcessHessianMatrix (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) (anisotropicProcessParameter D μ q p)
    (anisotropicFieldInjection n (EuclideanSpace.single i 1))
    (anisotropicFieldInjection n (EuclideanSpace.single j 1))

def nativeAnisotropicVarianceMatrix (D : AnisotropicSpinModel n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal D.variance

def nativeAnisotropicProcessHessianNoiseMatrix (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) : Matrix (Fin n) (Fin n) ℝ :=
  nativeAnisotropicProcessHessianMatrix D μ q p*nativeAnisotropicVarianceMatrix D*
    nativeAnisotropicProcessHessianMatrix D μ q p

theorem nativeAnisotropicProcessHessianMatrix_symmetric (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    nativeAnisotropicProcessHessianMatrix D μ q p i j=nativeAnisotropicProcessHessianMatrix D μ q p j i :=
  ((anisotropicMeasureTailPotential_hessian_limit D μ q).2.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

theorem nativeAnisotropicProcessSpinCovariance_symmetric (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    anisotropicProcessSpinCovariance D μ q p i j=anisotropicProcessSpinCovariance D μ q p j i := by
  unfold anisotropicProcessSpinCovariance anisotropicTailSpinCovariance
  simp only [anisotropicOrderedCoupling,min_comm,max_comm,mul_comm]

theorem nativeAnisotropicUnitInput_basis (D : AnisotropicSpinModel n) (l : Fin n) :
    anisotropicUnitInput D (EuclideanSpace.single l 1)=
      Real.sqrt (D.variance l) • anisotropicFieldInjection n (EuclideanSpace.single l 1) := by
  change anisotropicFieldInjection n (anisotropicNoiseMap D (EuclideanSpace.single l 1))=_
  rw [←map_smul]
  congr 1
  ext i
  by_cases hi:i=l <;> simp [anisotropicNoiseMap_apply,EuclideanSpace.single_apply,hi]

theorem nativeAnisotropicProcessHessianMatrix_polarization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    nativeAnisotropicProcessHessianMatrix D μ q p i j=
      (nativeAnisotropicProcessDirectionalHessian D μ (EuclideanSpace.single i 1+EuclideanSpace.single j 1) q p-
        nativeAnisotropicProcessDirectionalHessian D μ (EuclideanSpace.single i 1-EuclideanSpace.single j 1) q p)/4 := by
  unfold nativeAnisotropicProcessDirectionalHessian
  simp only [map_add,map_sub,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply]
  change _=(_+nativeAnisotropicProcessHessianMatrix D μ q p j i+_-
    (_-nativeAnisotropicProcessHessianMatrix D μ q p j i-(_-_)))/4
  rw [nativeAnisotropicProcessHessianMatrix_symmetric D μ q p j i]
  unfold nativeAnisotropicProcessHessianMatrix
  ring

theorem nativeAnisotropicProcessHessianNoiseMatrix_entry (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    nativeAnisotropicProcessHessianNoiseMatrix D μ q p i j=
      ∑l : Fin n,D.variance l*nativeAnisotropicProcessHessianMatrix D μ q p l i*
        nativeAnisotropicProcessHessianMatrix D μ q p l j := by
  unfold nativeAnisotropicProcessHessianNoiseMatrix nativeAnisotropicVarianceMatrix
  rw [Matrix.mul_assoc,Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [nativeAnisotropicProcessHessianMatrix_symmetric D μ q p i l]
  ring

theorem nativeAnisotropicProcessHessianNoiseMatrix_polarization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    nativeAnisotropicProcessHessianNoiseMatrix D μ q p i j=
      (nativeAnisotropicProcessDirectionalNoiseEnergy D μ (EuclideanSpace.single i 1+EuclideanSpace.single j 1) q p-
        nativeAnisotropicProcessDirectionalNoiseEnergy D μ (EuclideanSpace.single i 1-EuclideanSpace.single j 1) q p)/4 := by
  rw [nativeAnisotropicProcessHessianNoiseMatrix_entry]
  unfold nativeAnisotropicProcessDirectionalNoiseEnergy
  simp only [map_add,map_sub,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply]
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  rw [nativeAnisotropicUnitInput_basis]
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change D.variance l * nativeAnisotropicProcessHessianMatrix D μ q p l i *
      nativeAnisotropicProcessHessianMatrix D μ q p l j =
    ((Real.sqrt (D.variance l)*nativeAnisotropicProcessHessianMatrix D μ q p l i+
      Real.sqrt (D.variance l)*nativeAnisotropicProcessHessianMatrix D μ q p l j)^2-
     (Real.sqrt (D.variance l)*nativeAnisotropicProcessHessianMatrix D μ q p l i-
      Real.sqrt (D.variance l)*nativeAnisotropicProcessHessianMatrix D μ q p l j)^2)/4
  calc
    _=(Real.sqrt (D.variance l))^2*nativeAnisotropicProcessHessianMatrix D μ q p l i*
        nativeAnisotropicProcessHessianMatrix D μ q p l j:=by rw [Real.sq_sqrt (D.variance_pos l).le]
    _=_:=by ring

theorem nativeAnisotropicCovarianceMatrix_polarization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    anisotropicProcessSpinCovariance D μ q p i j=
      (anisotropicTailCovarianceQuadratic D μ q (anisotropicProcessParameter D μ q p)
          (EuclideanSpace.single i 1+EuclideanSpace.single j 1)-
        anisotropicTailCovarianceQuadratic D μ q (anisotropicProcessParameter D μ q p)
          (EuclideanSpace.single i 1-EuclideanSpace.single j 1))/4 := by
  let C : Fin n→Fin n→ℝ:=anisotropicProcessSpinCovariance D μ q p
  let u : Field n:=EuclideanSpace.single i 1
  let v : Field n:=EuclideanSpace.single j 1
  change C i j=((∑l : Fin n,∑m : Fin n,C l m * (u+v) l * (u+v) m)-
    (∑l : Fin n,∑m : Fin n,C l m * (u-v) l * (u-v) m))/4
  simp only [PiLp.add_apply,PiLp.sub_apply,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [u,v,EuclideanSpace.single_apply,mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [show C j i=C i j from nativeAnisotropicProcessSpinCovariance_symmetric D μ q p j i]
  ring

end QuantitativeFollowup
