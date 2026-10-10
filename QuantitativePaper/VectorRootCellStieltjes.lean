module
public import QuantitativePaper.VectorPrefixDensityLipschitz

@[expose] public section

/-! The repeated zero node is retained in the scheme. Its identical
potentials combine the initial tilt with the true first outgoing mass,
so positive outer tilts require the actual root floor, not `m 0 = 0`. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def discreteMassIncrement (m : ℕ→ℝ) (a : ℝ) (j : ℕ) : ℝ :=
  if j=0 then m 0-a else m j-m (j-1)

theorem discretePrefixWeight_telescope_generic (m : ℕ→ℝ) (a : ℝ)
    (N : ℕ) (hN : 0 < N) (u : Fin (N+1)→ℝ) :
    discretePrefixWeight m a N u=m (N-1)*u (Fin.last N)-
      ∑j : Fin N,discreteMassIncrement m a j*u j.castSucc := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h0 : N=0
    · subst N
      simp [discretePrefixWeight,discreteMassIncrement]
      ring
    · rw [discretePrefixWeight,ih (by omega),Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,Nat.add_sub_cancel,discreteMassIncrement]
      rw [if_neg h0]
      ring

theorem sum_discreteMassIncrement (m : ℕ→ℝ) (a : ℝ)
    (N : ℕ) (hN : 0 < N) :
    (∑j : Fin N,discreteMassIncrement m a j)=m (N-1)-a := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h0 : N=0
    · subst N
      simp [discreteMassIncrement]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih (by omega)]
      simp only [discreteMassIncrement,if_neg h0,Nat.add_sub_cancel]
      ring

theorem discretePrefixWeight_remove_zero (m : ℕ→ℝ) (a : ℝ) (hm : m 0=0)
    (N : ℕ) (u : Fin (N+2)→ℝ) (hu : u 0=u ⟨1,by omega⟩) :
    discretePrefixWeight m a (N+1) u=
      discretePrefixWeight (fun j=>m (j+1)) a N (fun j=>u j.succ) := by
  induction N with
  | zero => simp [discretePrefixWeight,hm,hu]
  | succ N ih =>
    conv_lhs => rw [discretePrefixWeight]
    conv_rhs => rw [discretePrefixWeight]
    rw [ih (fun j=>u j.castSucc) (by simpa using hu)]
    simp only [Fin.succ_last,Fin.val_last]
    congr 2

theorem sitePrefixGaussianPotential_zero_cell {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (hN : 0 < N) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) :
    sitePrefixGaussianPotential s β t i b 0=
      sitePrefixGaussianPotential s β t i b ⟨1,by omega⟩ := by
  funext g
  let z := gaussianCoordinateJoin (siteGaussianPredicate (N:=N) i) (g,b)
  let p := vectorPrefixEuclideanCoordinates n N z
  have hs : sitePrefixGaussianState s β t i b ⟨1,by omega⟩ g=
      sitePrefixGaussianState s β t i b 0 g := by
    have hh := independentHistory_next (vectorCoordinateUpdate s β t) N ((p.1,0),p.2)
      (⟨0,hN⟩ : Fin N)
    unfold sitePrefixGaussianState
    simp only [vectorPrefixEuclideanHistory_apply]
    change vectorPrefixHistory s β t N p ⟨1,by omega⟩=
      vectorPrefixHistory s β t N p 0
    simpa [vectorPrefixHistory,vectorCoordinateUpdate,vectorStateUpdate,fieldShift,hq,s.q_zero] using hh
  unfold sitePrefixGaussianPotential
  rw [hs]
  change vectorRecursion s β t _ (k+2) _=vectorRecursion s β t _ (k+1) _
  rw [show k+2=(k+1)+1 by omega,vectorRecursion]
  simp [hq,s.q_zero,vectorColeHopfStep_zero_variance]

theorem sitePrefixGaussianLogWeight_shifted {n k M : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=M+1) i)) :
    sitePrefixGaussianLogWeight s β t a i b=
      fun g=>discretePrefixWeight (fun j=>s.m (j+1)) a M
        (fun j=>sitePrefixGaussianPotential s β t i b j.succ g) := by
  funext g
  rw [show sitePrefixGaussianLogWeight s β t a i b g=
    discretePrefixWeight s.m a (M+1)
      (fun j=>sitePrefixGaussianPotential s β t i b j g) from
        vectorPrefixLogWeight_eq_discrete s β t a (M+1) _]
  apply discretePrefixWeight_remove_zero s.m a s.m_zero M
  exact congrFun (sitePrefixGaussianPotential_zero_cell s β t hq (by omega) i b) g

theorem norm_fderiv_sitePrefixGaussianLogWeight_root_cell_le {n k M : ℕ}
    (s : RSBScheme k) (β t a : ℝ) (hβ : 0 ≤ β) (ht : t ∈ Icc 0 1)
    (ha0 : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0)
    (hN : M+1 ≤ k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=M+1) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=M+1) i)) :
    ‖fderiv ℝ (sitePrefixGaussianLogWeight s β t a i b) g‖ ≤
      2*β*(if M=0 then a else s.m M) := by
  rw [sitePrefixGaussianLogWeight_shifted s β t a hq i b]
  by_cases hM : M=0
  · subst M
    simp only [discretePrefixWeight,ite_true]
    change ‖fderiv ℝ (fun x=>a*sitePrefixGaussianPotential s β t i b 1 x) g‖ ≤ 2*β*a
    rw [show (fun x=>a*sitePrefixGaussianPotential s β t i b 1 x)=
      (fun x=>a • sitePrefixGaussianPotential s β t i b 1 x) from rfl,
      fderiv_fun_const_smul ((contDiff_sitePrefixGaussianPotential s β t i b 1).differentiable
        (by simp) g),norm_smul,Real.norm_eq_abs,abs_of_nonneg ha0]
    have hh := norm_fderiv_sitePrefixGaussianPotential_le s β t hβ ht hN i b 1 g
    nlinarith
  · have hMp : 0 < M := by omega
    let m := fun j=>s.m (j+1)
    let F := fun j : Fin (M+1)=>sitePrefixGaussianPotential s β t i b j.succ
    have hf (j : Fin (M+1)) := contDiff_sitePrefixGaussianPotential s β t i b j.succ
    have hd (j : Fin (M+1)) := (hf j).differentiable (by simp) g
    have hc (j : Fin M) : 0 ≤ discreteMassIncrement m a j := by
      unfold discreteMassIncrement
      split_ifs with h0
      · simpa [m,h0] using sub_nonneg.mpr ha
      · apply sub_nonneg.mpr
        exact s.m_mono' (j.val+1) (by omega) (j.val-1+1) (by omega)
    have hsum := norm_fderiv_nonnegative_sum_le
      (fun j : Fin M=>discreteMassIncrement m a j) (fun j : Fin M=>F j.castSucc)
      β hc (fun j=>hf j.castSucc)
      (fun j x=>norm_fderiv_sitePrefixGaussianPotential_le s β t hβ ht hN i b j.castSucc.succ x) g
    rw [sum_discreteMassIncrement m a M hMp] at hsum
    have hm : 0 ≤ m (M-1) := s.m_nonneg (by omega)
    change ‖fderiv ℝ (fun x=>discretePrefixWeight m a M (fun j=>F j x)) g‖ ≤ _
    have heF : (fun x=>discretePrefixWeight m a M (fun j=>F j x))=
      (fun x=>m (M-1)*F (Fin.last M) x-
        ∑j : Fin M,discreteMassIncrement m a j*F j.castSucc x) := by
      funext x
      exact discretePrefixWeight_telescope_generic m a M hMp _
    rw [heF]
    rw [fderiv_fun_sub ((hd (Fin.last M)).const_mul (m (M-1)))
      (DifferentiableAt.fun_sum (fun (j : Fin M) _=>
        (hd j.castSucc).const_mul (discreteMassIncrement m a j)))]
    apply (norm_sub_le _ _).trans
    have hfirst : ‖fderiv ℝ (fun x=>m (M-1)*F (Fin.last M) x) g‖ ≤ m (M-1)*β := by
      rw [show (fun x=>m (M-1)*F (Fin.last M) x)=
        (fun x=>m (M-1) • F (Fin.last M) x) from rfl,
        fderiv_fun_const_smul (hd (Fin.last M)),norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left
        (norm_fderiv_sitePrefixGaussianPotential_le s β t hβ ht hN i b (Fin.last M).succ g) hm
    have he : m (M-1)=s.m M := by dsimp [m];congr 1;omega
    rw [he] at hfirst hsum
    rw [if_neg hM]
    change ‖fderiv ℝ (fun x=>m (M-1)*F (Fin.last M) x) g‖+
      ‖fderiv ℝ (fun x=>∑j : Fin M,discreteMassIncrement m a j*F j.castSucc x) g‖ ≤ _
    rw [he]
    nlinarith

end QuantitativePaper
