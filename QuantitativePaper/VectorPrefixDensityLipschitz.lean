module
public import QuantitativePaper.VectorPrefixPotentialLipschitz
public import QuantitativePaper.VectorPrefixStieltjes

@[expose] public section

/-! The literal sharp prefix-density bound from discrete Stieltjes
telescoping. It depends only on the incoming physical mass. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem norm_fderiv_nonnegative_sum_le {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (c : I→ℝ) (F : I→E→ℝ) (B : ℝ) (hc : ∀i,0≤c i)
    (hF : ∀i,ContDiff ℝ ∞ (F i)) (hB : ∀i x,‖fderiv ℝ (F i) x‖≤B) (x : E) :
    ‖fderiv ℝ (fun y=>∑ i,c i*F i y) x‖≤(∑ i,c i)*B := by
  have hdf i := (hF i).differentiable (by norm_num) x
  rw [fderiv_fun_sum (fun i _=>(hdf i).const_mul (c i))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i,c i*B := Finset.sum_le_sum fun i _=>by
      rw [show (fun y=>c i*F i y)=(fun y=>c i • F i y) from rfl,
        fderiv_fun_const_smul (hdf i),norm_smul,Real.norm_eq_abs,abs_of_nonneg (hc i)]
      exact mul_le_mul_of_nonneg_left (hB i x) (hc i)
    _ = _ := by rw [Finset.sum_mul]

theorem sitePrefixGaussianLogWeight_stieltjes {n k N : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hN : 0<N) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) :
    sitePrefixGaussianLogWeight s β t a i b =
      fun g=>s.m (N-1)*sitePrefixGaussianPotential s β t i b (Fin.last N) g-
        ∑ j : Fin N,prefixMassIncrement s a j*
          sitePrefixGaussianPotential s β t i b j.castSucc g := by
  funext g
  exact vectorPrefixLogWeight_stieltjes s β t a N hN _

theorem norm_fderiv_sitePrefixGaussianLogWeight_le {n k N : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hβ : 0≤β) (ht : t∈Icc 0 1) (ha0 : 0≤a) (ha : a ≤ s.m 0)
    (hN0 : 0<N) (hN : N≤k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    ‖fderiv ℝ (sitePrefixGaussianLogWeight s β t a i b) g‖≤2*β*s.m (N-1) := by
  have hm : 0≤ s.m (N-1) := s.m_nonneg (by omega)
  have hf j := contDiff_sitePrefixGaussianPotential s β t i b j
  have hd j := (hf j).differentiable (by norm_num) g
  have hc (j : Fin N) : 0≤prefixMassIncrement s a j :=
    prefixMassIncrement_nonneg s a ha j (by omega)
  have hsum := norm_fderiv_nonnegative_sum_le
    (fun j : Fin N=>prefixMassIncrement s a j)
    (fun j : Fin N=>sitePrefixGaussianPotential s β t i b j.castSucc) β hc
    (fun j=>hf j.castSucc)
    (fun j x=>norm_fderiv_sitePrefixGaussianPotential_le s β t hβ ht hN i b j.castSucc x) g
  rw [sum_prefixMassIncrement s a N hN0] at hsum
  rw [sitePrefixGaussianLogWeight_stieltjes s β t a hN0 i b,
    fderiv_fun_sub ((hd (Fin.last N)).const_mul (s.m (N-1)))
      (DifferentiableAt.fun_sum (fun (j : Fin N) _=>
        (hd j.castSucc).const_mul (prefixMassIncrement s a j)))]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖fderiv ℝ (fun x=>s.m (N-1)*
      sitePrefixGaussianPotential s β t i b (Fin.last N) x) g‖≤ s.m (N-1)*β := by
    rw [show (fun x=>s.m (N-1)*sitePrefixGaussianPotential s β t i b (Fin.last N) x)=
        (fun x=>s.m (N-1) • sitePrefixGaussianPotential s β t i b (Fin.last N) x) from rfl,
      fderiv_fun_const_smul (hd (Fin.last N)),norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_left
      (norm_fderiv_sitePrefixGaussianPotential_le s β t hβ ht hN i b (Fin.last N) g) hm
  nlinarith [hfirst,hsum]

theorem norm_fderiv_sitePrefixGaussianLogWeight_zero_le {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hβ : 0≤β) (ht : t∈Icc 0 1) (ha0 : 0≤a) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=0) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=0) i)) :
    ‖fderiv ℝ (sitePrefixGaussianLogWeight s β t a i b) g‖≤2*β*a := by
  have he : sitePrefixGaussianLogWeight s β t a i b=
      fun x=>a • sitePrefixGaussianPotential s β t i b 0 x := rfl
  rw [he,fderiv_fun_const_smul ((contDiff_sitePrefixGaussianPotential s β t i b 0).differentiable
      (by norm_num) g),norm_smul,Real.norm_eq_abs,abs_of_nonneg ha0]
  have hh := mul_le_mul_of_nonneg_left
    (norm_fderiv_sitePrefixGaussianPotential_le s β t hβ ht (by omega) i b 0 g) ha0
  nlinarith

end QuantitativePaper
