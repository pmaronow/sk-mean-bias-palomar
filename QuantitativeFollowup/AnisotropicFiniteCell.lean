module
public import QuantitativeFollowup.AnisotropicFiniteTailResponse

@[expose] public section

/-! Exact identification of the actual restarted anisotropic recursion on
every closed cell with a single Cole--Hopf evolution. Whitening is performed
on the genuine diagonal noise map, retaining the fixed physical disorder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 400000

theorem anisotropicTailRecursion_prefix_of_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : ℝ) {j : ℕ} (hj : j ≤ k+2) (hq : q ≤ s.q (k+2-j)) :
    anisotropicTailRecursion D s q j=anisotropicFinitePotential D s j := by
  induction j with
  | zero => exact (anisotropicFinitePotential_terminal_softmax D s).symm
  | succ j ih =>
    have hl : q ≤ s.q (k+1-j) := by simpa only [show k+2-(j+1)=k+1-j by omega] using hq
    have hh := hl.trans (s.q_mono' (k+2-j) (by omega) (k+1-j) (by omega))
    rw [anisotropicTailRecursion,anisotropicFinitePotential_gaussianShiftColeHopf,
      ih (by omega) hh,max_eq_right hh,max_eq_right hl]
    rfl

theorem anisotropicTailRecursion_constant_suffix (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : ℝ) (J : ℕ) (hJ : J ≤ k+2) (hq : s.q (k+2-J) ≤ q)
    {j : ℕ} (hJj : J ≤ j) (hj : j ≤ k+2) :
    anisotropicTailRecursion D s q j=anisotropicTailRecursion D s q J := by
  induction j with
  | zero =>
    have he : J=0 := by omega
    subst J
    rfl
  | succ j ih =>
    by_cases he : J=j+1
    · rw [he]
    · have hj' : J ≤ j := by omega
      have hh := (s.q_mono' (k+2-J) (by omega) (k+2-j) (by omega)).trans hq
      have hl := (s.q_mono' (k+2-j) (by omega) (k+1-j) (by omega)).trans hh
      funext P
      rw [anisotropicTailRecursion,max_eq_left hh,max_eq_left hl]
      simp only [sub_self,Real.sqrt_zero]
      have hA : (0 : ℝ) • anisotropicUnitInput D=(0 : Field n→L[ℝ]AnisotropicParameter n) := by
        ext w i
        simp
      rw [hA,gaussianShiftColeHopf_zero_input]
      exact congrFun (ih hj' (by omega)) P

theorem anisotropicTailRecursion_eq_cell (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : ℝ) (i : ℕ) (hi : i ≤ k+1) (hq : q∈Icc (s.q i) (s.q (i+1))) :
    anisotropicTailRecursion D s q (k+2)=
      gaussianShiftColeHopf (Real.sqrt (s.q (i+1)-q) • anisotropicUnitInput D)
        (s.m i) (anisotropicFinitePotential D s (k+1-i)) := by
  rw [anisotropicTailRecursion_constant_suffix D s q (k+2-i) (by omega)
    (by simpa only [show k+2-(k+2-i)=i by omega] using hq.1) (by omega) le_rfl]
  rw [show k+2-i=(k+1-i)+1 by omega,anisotropicTailRecursion]
  have hi0 : k+1-(k+1-i)=i := by omega
  have hi1 : k+2-(k+1-i)=i+1 := by omega
  rw [hi0,hi1,max_eq_left hq.1,max_eq_right hq.2,
    anisotropicTailRecursion_prefix_of_le D s q (by omega)
      (by simpa only [hi1] using hq.2)]

def anisotropicWhitenedFinitePotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (g : AnisotropicDisorder n) (y : Field n) : ℝ :=
  anisotropicFinitePotential D s j
    (anisotropicDisorderInjection n g+anisotropicUnitInput D y)

def anisotropicWhitenedFiniteTailPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (g : AnisotropicDisorder n) (y : Field n) : ℝ :=
  anisotropicFiniteTailPotential D s q
    (anisotropicDisorderInjection n g+anisotropicUnitInput D y)

theorem anisotropicWhitenedFiniteTailPotential_eq_cell (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (i : ℕ) (hi : i ≤ k+1)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) (g : AnisotropicDisorder n) :
    anisotropicWhitenedFiniteTailPotential D s q g=
      vectorColeHopfStep (s.q (i+1)-q) (s.m i)
        (anisotropicWhitenedFinitePotential D s (k+1-i) g) := by
  funext y
  unfold anisotropicWhitenedFiniteTailPotential anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_cell D s q i hi hq]
  exact gaussianShiftColeHopf_smul_eq_vectorStep _ _ _ _ _ _

theorem fderiv_anisotropicFiniteTailPotential_field (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) :
    fderiv ℝ (anisotropicFiniteTailPotential D s q) P (anisotropicFieldInjection n w)=
      inner ℝ (anisotropicFiniteTailMagnetization D s q P) w := by
  rw [anisotropicFieldDirection_sum,map_sum]
  simp_rw [map_smul,smul_eq_mul]
  change (∑i : Fin n,w i*anisotropicFiniteTailMagnetization D s q P i)=_
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem gradient_anisotropicWhitenedFiniteTailPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (g : AnisotropicDisorder n) (y : Field n) :
    gradient (anisotropicWhitenedFiniteTailPotential D s q g) y=
      anisotropicNoiseMap D (anisotropicFiniteTailMagnetization D s q
        (anisotropicDisorderInjection n g+anisotropicUnitInput D y)) := by
  let P := anisotropicDisorderInjection n g+anisotropicUnitInput D y
  have hu := (contDiff_anisotropicFiniteTailPotential D s q).differentiable (by simp)
  have hc : HasFDerivAt (fun z : Field n=>anisotropicDisorderInjection n g+anisotropicUnitInput D z)
      (anisotropicUnitInput D) y :=
    (anisotropicUnitInput D).hasFDerivAt.const_add (anisotropicDisorderInjection n g)
  have he := ((hu P).hasFDerivAt.comp y hc).fderiv
  apply (InnerProductSpace.toDual ℝ (Field n)).injective
  ext w
  rw [toDual_gradient]
  change fderiv ℝ (anisotropicFiniteTailPotential D s q ∘
      (fun z : Field n=>anisotropicDisorderInjection n g+anisotropicUnitInput D z)) y w=
    inner ℝ (anisotropicNoiseMap D (anisotropicFiniteTailMagnetization D s q P)) w
  rw [he,ContinuousLinearMap.comp_apply]
  change fderiv ℝ (anisotropicFiniteTailPotential D s q) P
      (anisotropicFieldInjection n (anisotropicNoiseMap D w))=_
  rw [fderiv_anisotropicFiniteTailPotential_field,←anisotropicNoiseMap_selfAdjoint]

end QuantitativeFollowup
