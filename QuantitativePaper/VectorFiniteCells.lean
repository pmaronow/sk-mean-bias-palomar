module
public import QuantitativePaper.VectorHeatCalculus

@[expose] public section

/-! Actual continuous-overlap Cole--Hopf interpolation inside every finite
profile cell. Both endpoint identities and the physical time derivative are
proved from the genuine Gaussian step. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorFiniteCellPotential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (i : ℕ) (q : ℝ) (x : Field n) : ℝ :=
  vectorColeHopfStep ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
    (vectorRecursion s β t p (k+1-i)) x

theorem vectorFiniteCellPotential_right {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (i : ℕ) (x : Field n) :
    vectorFiniteCellPotential s β t p i (s.q (i+1)) x=
      vectorRecursion s β t p (k+1-i) x := by
  simp [vectorFiniteCellPotential]

theorem vectorFiniteCellPotential_left {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (i : ℕ) (hi : i ≤ k+1) (x : Field n) :
    vectorFiniteCellPotential s β t p i (s.q i) x=
      vectorRecursion s β t p (k+2-i) x := by
  have hj : k+2-i=(k+1-i)+1 := by omega
  have h₁ : k+1-(k+1-i)=i := by omega
  have h₂ : k+2-(k+1-i)=i+1 := by omega
  rw [hj,vectorRecursion]
  simp only [h₁,h₂,vectorFiniteCellPotential]
  have hv : (1-t)*β^2*(s.q (i+1)-s.q i)=(1-t)*(β^2*(s.q (i+1)-s.q i)) := by ring
  rw [hv]

theorem vectorFiniteCellPotential_joint_smooth_bounded_jets {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (i : ℕ) (q : ℝ) (N : ℕ) :
    ContDiff ℝ N (fun p : VectorParameter n => vectorFiniteCellPotential s β t p.1 i q p.2) ∧
    ∃ K : ℝ,1 ≤ K ∧ ∀ j,1 ≤ j → j ≤ N → ∀ p : VectorParameter n,
      ‖iteratedFDeriv ℝ j (fun p : VectorParameter n => vectorFiniteCellPotential s β t p.1 i q p.2) p‖≤K^j := by
  obtain ⟨hSmooth,K,hK,hJets⟩ := vectorRecursion_joint_smooth_bounded_jets (n := n) s β t N (k+1-i)
  let v := (1-t)*β^2*(s.q (i+1)-q)
  let m := s.m i
  have hh := gaussianShiftColeHopf_smooth_bounded_jets N
    (fun p : VectorParameter n => vectorRecursion s β t p.1 (k+1-i) p.2) hSmooth
    (vectorJointLipschitzConstant n β t) (vectorRecursion_joint_lipschitz s β t (k+1-i))
    K hK hJets (vectorJointShift n v) m
  have he : gaussianShiftColeHopf (vectorJointShift n v) m
      (fun p : VectorParameter n => vectorRecursion s β t p.1 (k+1-i) p.2)=
      fun p : VectorParameter n => vectorFiniteCellPotential s β t p.1 i q p.2 := by
    funext p
    exact gaussianShiftColeHopf_vectorRecursion s β t v m (k+1-i) p
  rw [he] at hh
  exact hh

theorem contDiff_vectorFiniteCellPotential_joint {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (q : ℝ) :
    ContDiff ℝ ∞ (fun p : VectorParameter n => vectorFiniteCellPotential s β t p.1 i q p.2) :=
  contDiff_infty.mpr fun N => (vectorFiniteCellPotential_joint_smooth_bounded_jets s β t i q N).1

theorem hasDerivAt_vectorFiniteCellPotential_time {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n × ℝ)
    (i : ℕ) (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) :
    HasDerivAt (fun r => vectorFiniteCellPotential s β t p i r x)
      (-((1-t)*β^2)/2*
        ∑l : Fin n,vectorStepResponse ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
          (vectorRecursion s β t p (k+1-i))
          (fun y => (vectorFieldHessian s β t p (k+1-i) y (EuclideanSpace.single l (1 : ℝ))) l+
            s.m i*(vectorMagnetization s β t p (k+1-i) y l)^2) x) q := by
  have hc : 0<(1-t)*β^2 := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hv : 0<(1-t)*β^2*(s.q (i+1)-q) := mul_pos hc (sub_pos.mpr hq)
  have hd := hasDerivAt_vectorColeHopfStep_variance s β t p (k+1-i) (s.m i) x hv
  have ha : HasDerivAt (fun r : ℝ => (1-t)*β^2*(s.q (i+1)-r)) (-((1-t)*β^2)) q := by
    convert ((hasDerivAt_const q (s.q (i+1))).sub (hasDerivAt_id q)).const_mul ((1-t)*β^2) using 1
    · funext r
      simp only [Pi.sub_apply,Function.const_apply,id_eq]
    · ring
  convert hd.comp q ha using 1
  · rfl
  · ring

end QuantitativePaper
