module
public import QuantitativeFollowup.AnisotropicFieldRightInverse
public import QuantitativeFollowup.AnisotropicMagnetization
public import QuantitativePaper.VectorFieldDerivative

@[expose] public section

/-! Actual field derivatives and zero-overlap response for the
anisotropic Gaussian history, including repeated zero levels. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

theorem anisotropicFieldDirection_sum (w : Field n) :
    anisotropicFieldInjection n w=∑l : Fin n,w l • anisotropicCoordinateDirection n l := by
  ext i
  cases i with
  | inl e => simp [anisotropicFieldInjection,anisotropicCoordinateDirection]
  | inr l => simp [anisotropicFieldInjection,anisotropicCoordinateDirection,Pi.single_apply]

theorem fderiv_anisotropicFinitePotential_field (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    fderiv ℝ (anisotropicFinitePotential D s j) P (anisotropicFieldInjection n w)=
      inner ℝ (anisotropicMagnetization D s j P) w := by
  rw [anisotropicFieldDirection_sum,map_sum]
  simp_rw [map_smul,smul_eq_mul,←anisotropicMagnetization_apply]
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem contDiff_anisotropicEuclideanMagnetization (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : ContDiff ℝ ∞ (anisotropicEuclideanMagnetization D s i) :=
  contDiff_piLp' 2 (fun l => (boundedJets_anisotropicEuclideanMagnetization_component D s i l).1)

theorem anisotropicEuclideanHistoryPotential_rightInverse_deriv (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin (k+3)) (hi : 0 < s.q i)
    (z : AnisotropicGaussianSpace n k) (w : Field n) :
    fderiv ℝ (anisotropicEuclideanHistoryPotential D s i) z
      (anisotropicEuclideanFieldRightInverse D s i w)=
      inner ℝ (anisotropicEuclideanMagnetization D s i z) w := by
  let U := anisotropicFinitePotential D s (k+2-i)
  let L := anisotropicEuclideanStateLinear D s i
  have hu : Differentiable ℝ U := (contDiff_anisotropicFinitePotential D s _).differentiable (by simp)
  change fderiv ℝ (U ∘ L) z (anisotropicEuclideanFieldRightInverse D s i w)=_
  rw [fderiv_comp z (hu (L z)) L.differentiableAt,ContinuousLinearMap.comp_apply,L.fderiv,
    anisotropicEuclideanStateLinear_rightInverse D s i hi]
  exact fderiv_anisotropicFinitePotential_field D s _ (L z) w

theorem anisotropicEuclideanStateLinear_zero_overlap (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin (k+3)) (hi : s.q i=0) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanStateLinear D s i z=
      anisotropicDisorderInjection n (anisotropicEuclideanCoordinates n k z).1 := by
  rw [anisotropicEuclideanStateLinear_apply]
  have he : Fin.ofNat (k+3) i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  change anisotropicCoordinateHistory D s _ (Fin.ofNat (k+3) i.val)=_
  rw [he,anisotropicCoordinateHistory_sum]
  have hz (j : Fin (k+2)) (hj : j.val < i.val) : anisotropicPhysicalFieldIncrement s j=0 := by
    have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (k+2))))
      (f := fun l => if l.val < i.val then (anisotropicPhysicalFieldIncrement s l)^2 else 0)
      (fun l _ => by split_ifs <;> positivity) (Finset.mem_univ j)
    rw [anisotropicPhysicalFieldIncrement_prefix_sq,hi,ite_eq_left hj] at hs
    nlinarith [sq_nonneg (anisotropicPhysicalFieldIncrement s j)]
  have hs : (∑j : Fin (k+2),if j.val < i.val then anisotropicPhysicalFieldIncrement s j •
      anisotropicFieldInjection n (anisotropicNoiseMap D ((anisotropicEuclideanCoordinates n k z).2 j)) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < i.val
    · simp [hj,hz j hj]
    · simp [hj]
  rw [hs,add_zero]

theorem anisotropicMagnetization_zero_field (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (disorder : AnisotropicDisorder n) :
    anisotropicMagnetization D s j (anisotropicDisorderInjection n disorder)=0 := by
  have hg : anisotropicParameterGauge (fun _ : Fin n => false) (anisotropicDisorderInjection n disorder)=
      anisotropicDisorderInjection n disorder := by
    ext i
    cases i <;> simp [anisotropicDisorderInjection,anisotropicParameterGauge_apply,
      anisotropicParameterGaugeSign,Paper.spinSign]
  ext l
  have hh := anisotropicMagnetization_component_gauge D s (fun _ => false) j
    (anisotropicDisorderInjection n disorder) l
  rw [hg] at hh
  simp only [Paper.spinSign,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul] at hh
  change anisotropicMagnetization D s j (anisotropicDisorderInjection n disorder) l=0
  linarith

theorem anisotropicEuclideanMagnetization_zero_overlap (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin (k+3)) (hi : s.q i=0) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanMagnetization D s i z=0 := by
  rw [anisotropicEuclideanMagnetization,anisotropicEuclideanStateLinear_zero_overlap D s i hi,
    anisotropicMagnetization_zero_field]

end QuantitativeFollowup
