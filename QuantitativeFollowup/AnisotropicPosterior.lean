module
public import QuantitativeFollowup.AnisotropicHistoryLinear
public import QuantitativeFollowup.AnisotropicFiniteConvexity
public import QuantitativePaper.VectorPosteriorCoercivity

@[expose] public section

/-! The literal anisotropic spin-conditioned Gaussian posterior. Its
Lebesgue density and Hessian coercivity follow from the actual normalized
finite model, with the root floor and every mass increment retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def anisotropicEuclideanHistoryPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (z : AnisotropicGaussianSpace n k) : ℝ :=
  anisotropicFinitePotential D s (k+2-i) (anisotropicEuclideanStateLinear D s i z)

def anisotropicEuclideanTerminalLinear (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (σ : Configuration n) : AnisotropicGaussianSpace n k→L[ℝ]ℝ :=
  (anisotropicTerminalLinear D σ).comp (anisotropicEuclideanStateLinear D s (k+2))

def anisotropicPosteriorPotential (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (σ : Configuration n) (z : AnisotropicGaussianSpace n k) : ℝ :=
  standardGaussianPotential z-anisotropicEuclideanTerminalLinear D s σ z+
    (s.m 1-a)*anisotropicEuclideanHistoryPotential D s 1 z+
    (∑i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*anisotropicEuclideanHistoryPotential D s (i+2) z)+
    Real.log (anisotropicFiniteOuterPartition D s a)

theorem contDiff_anisotropicEuclideanHistoryPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : ContDiff ℝ ∞ (anisotropicEuclideanHistoryPotential D s i) :=
  (contDiff_anisotropicFinitePotential D s (k+2-i)).comp (anisotropicEuclideanStateLinear D s i).contDiff

theorem convexOn_anisotropicEuclideanHistoryPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : ConvexOn ℝ univ (anisotropicEuclideanHistoryPotential D s i) :=
  (convexOn_anisotropicFinitePotential D s (k+2-i)).comp_linearMap
    (anisotropicEuclideanStateLinear D s i).toLinearMap

theorem contDiff_anisotropicPosteriorPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (σ : Configuration n) :
    ContDiff ℝ ∞ (anisotropicPosteriorPotential D s a σ) := by
  unfold anisotropicPosteriorPotential
  exact (((contDiff_standardGaussianPotential.sub (anisotropicEuclideanTerminalLinear D s σ).contDiff).add
    (contDiff_const.mul (contDiff_anisotropicEuclideanHistoryPotential D s 1))).add
    (ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_anisotropicEuclideanHistoryPotential D s (i+2))))).add contDiff_const

theorem anisotropicSchemeInput_root_zero (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (hq : s.q 1=0) : anisotropicSchemeInput D s (k+1)=0 := by
  unfold anisotropicSchemeInput
  have h1 : k+2-(k+1)=1 := by omega
  rw [h1,Nat.sub_self,hq,s.q_zero]
  ext z i
  simp only [sub_self,Real.sqrt_zero,ContinuousLinearMap.smul_apply,zero_smul,zero_apply,PiLp.zero_apply]

theorem anisotropicFinitePotential_root_eq (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (hq : s.q 1=0) (P : AnisotropicParameter n) :
    anisotropicFinitePotential D s (k+2) P=anisotropicFinitePotential D s (k+1) P := by
  rw [show k+2=(k+1)+1 by omega,anisotropicFinitePotential_coleHopf,
    anisotropicSchemeInput_root_zero D s hq]
  simp [anisotropicSchemeMass,s.m_zero,OverlapPaper.sourceLogAverage]

theorem anisotropicCoordinateHistory_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (hq : s.q 1=0) (p : AnisotropicGaussianCoordinates n k) :
    anisotropicCoordinateHistory D s p (1 : Fin (k+3))=anisotropicCoordinateHistory D s p 0 := by
  change independentHistory (anisotropicCoordinateUpdate D s) (k+2)
    (anisotropicDisorderInjection n p.1,p.2) (0 : Fin (k+2)).succ = _
  rw [independentHistory_next]
  simp only [Fin.val_zero,Nat.sub_zero,Fin.castSucc_zero,anisotropicCoordinateUpdate,
    anisotropicSchemeInput_root_zero D s hq,ContinuousLinearMap.zero_apply,add_zero]
  rfl

theorem anisotropicEuclideanHistoryPotential_root_eq (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (hq : s.q 1=0) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanHistoryPotential D s 0 z=anisotropicEuclideanHistoryPotential D s 1 z := by
  unfold anisotropicEuclideanHistoryPotential
  rw [anisotropicEuclideanStateLinear_apply,anisotropicEuclideanStateLinear_apply]
  have h1 : historyExtended (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z)) 1 =
      anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z) (1 : Fin (k+3)) := by
    have he : (1 : ℕ)=(1 : Fin (k+3)).val := by simp
    rw [he,historyExtended_fin]
  rw [h1,anisotropicCoordinateHistory_one D s hq]
  simp only [Nat.sub_zero,historyExtended]
  rw [anisotropicFinitePotential_root_eq D s hq]
  congr 1

theorem anisotropicEuclideanDensity_eq_posterior (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (z : AnisotropicGaussianSpace n k)
    (σ : Configuration n) : anisotropicEuclideanDensity D s a (z,σ)=ENNReal.ofReal
      (Real.exp (standardGaussianPotential z-anisotropicPosteriorPotential D s a σ z)) := by
  unfold anisotropicEuclideanDensity anisotropicEuclideanJointMap
  rw [anisotropicFiniteJointDensity_eq_stieltjes,Finset.sum_range_succ',s.m_zero]
  have he (i : ℕ) : anisotropicHistoryPotential D s
      (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z)) i =
      anisotropicEuclideanHistoryPotential D s i z := by
    unfold anisotropicHistoryPotential anisotropicEuclideanHistoryPotential
    rw [anisotropicEuclideanStateLinear_apply]
  simp_rw [he]
  rw [anisotropicEuclideanHistoryPotential_root_eq D s hq]
  unfold anisotropicPosteriorPotential anisotropicEuclideanTerminalLinear
  rw [ContinuousLinearMap.comp_apply,anisotropicEuclideanStateLinear_apply]
  have ht : historyExtended (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z)) (k+2) =
      anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z) (Fin.last (k+2)) := by
    simpa only [Fin.val_last] using historyExtended_fin
      (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z)) (Fin.last (k+2))
  rw [ht]
  congr 2
  simp only [Nat.zero_add,zero_mul,sub_zero]
  ring

def anisotropicPosteriorCorrection (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (σ : Configuration n) (z : AnisotropicGaussianSpace n k) : ℝ :=
  anisotropicPosteriorPotential D s a σ z-standardGaussianPotential z

theorem convexOn_anisotropicPosteriorCorrection (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (σ : Configuration n) :
    ConvexOn ℝ univ (anisotropicPosteriorCorrection D s a σ) := by
  have he : anisotropicPosteriorCorrection D s a σ = fun z =>
      -anisotropicEuclideanTerminalLinear D s σ z+(s.m 1-a)*anisotropicEuclideanHistoryPotential D s 1 z+
      (∑i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*anisotropicEuclideanHistoryPotential D s (i+2) z)+
      Real.log (anisotropicFiniteOuterPartition D s a) := by
    funext z
    unfold anisotropicPosteriorCorrection anisotropicPosteriorPotential
    ring
  rw [he]
  have hL : ConvexOn ℝ univ (fun z => -anisotropicEuclideanTerminalLinear D s σ z) :=
    (-(anisotropicEuclideanTerminalLinear D s σ).toLinearMap).convexOn convex_univ
  have hR := (convexOn_anisotropicEuclideanHistoryPotential D s 1).smul (sub_nonneg.mpr ha)
  have hS := convexOn_finite_sum_univ (Finset.range k)
    (fun i z => (s.m (i+2)-s.m (i+1))*anisotropicEuclideanHistoryPotential D s (i+2) z)
    (fun i hi => by
      simpa only [smul_eq_mul] using (convexOn_anisotropicEuclideanHistoryPotential D s (i+2)).smul
        (vectorStieltjesCoefficient_nonneg s (Finset.mem_range.mp hi)))
  convert! ((hL.add hR).add hS).add_const (Real.log (anisotropicFiniteOuterPartition D s a)) using 1

theorem anisotropicPosteriorPotential_hessian_lower (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (σ : Configuration n)
    (z w : AnisotropicGaussianSpace n k) :
    ‖w‖^2 ≤ directionalHessian (anisotropicPosteriorPotential D s a σ) z w := by
  have hc : ContDiff ℝ 2 (anisotropicPosteriorCorrection D s a σ) :=
    ((contDiff_anisotropicPosteriorPotential D s a σ).sub contDiff_standardGaussianPotential).of_le (by simp)
  have he : anisotropicPosteriorPotential D s a σ =
      fun y => standardGaussianPotential y+anisotropicPosteriorCorrection D s a σ y := by
    funext y
    unfold anisotropicPosteriorCorrection
    ring
  rw [he,directionalHessian_add _ _ (contDiff_standardGaussianPotential.of_le (by simp)) hc,
    directionalHessian_standardGaussianPotential]
  exact le_add_of_nonneg_right (directionalHessian_nonneg_of_convex _ hc
    (convexOn_anisotropicPosteriorCorrection D s a ha σ) z w)

end QuantitativeFollowup
