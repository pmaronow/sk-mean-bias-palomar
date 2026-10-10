module
public import QuantitativeFollowup.ScalarFiniteGaussianExpectation
public import QuantitativeFollowup.ScalarFiniteHeatData

@[expose] public section

/-! Uniform Gaussian first-derivative envelopes for the actual scalar marked
density and squared-gradient observable. The constants are independent of the
finite profile and therefore also apply to genuinely transported profiles. -/
noncomputable section
open Set
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {k : ℕ}

theorem scalarScheme_mass_sum (s : RSBScheme k) :
    (∑i : Fin (k+1),(s.m (i+1)-s.m i))=1 := by
  simpa only [s.m_top,s.m_zero,sub_zero] using
    (Fin.sum_univ_eq_sum_range (fun i : ℕ=>s.m (i+1)-s.m i) (k+1)).trans
      (parisiScheme_mass_telescope s (k+1))

theorem norm_scalarFiniteEuclideanExponent_first_le (s : RSBScheme k)
    (β : ℝ) (e : Bool) (x : QuantitativePaper.Field (k+3)) :
    ‖fderiv ℝ (scalarFiniteEuclideanExponent s β e) x‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [scalarFiniteEuclideanExponent_first]
  have he : ‖Paper.spinSign e‖=1 := by cases e <;> norm_num [Paper.spinSign]
  have hsum : ‖∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiGradient β
      (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩)*v ⟨i+1,by omega⟩‖≤‖v‖ := by
    calc
      _ ≤ ∑i : Fin (k+1),‖(s.m (i+1)-s.m i)*Paper.parisiGradient β
          (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩)*v ⟨i+1,by omega⟩‖ := norm_sum_le _ _
      _ ≤ ∑i : Fin (k+1),(s.m (i+1)-s.m i)*‖v‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,norm_mul,Real.norm_of_nonneg (sub_nonneg.mpr (s.m_mono i (by omega)))]
        have hfirst : (s.m (i+1)-s.m i)*‖Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
            (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩)‖ ≤ (s.m (i+1)-s.m i) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (Paper.norm_parisiGradient_le_one β (Paper.parisiSchemeMeasure s) _)
            (sub_nonneg.mpr (s.m_mono i (by omega)))
        exact mul_le_mul hfirst (PiLp.norm_apply_le v _) (norm_nonneg _)
          (sub_nonneg.mpr (s.m_mono i (by omega)))
      _ = ‖v‖ := by rw [←Finset.sum_mul,scalarScheme_mass_sum,one_mul]
  have hlast : ‖Paper.spinSign e*v (Fin.last (k+2))‖≤‖v‖ := by
    simpa only [norm_mul,he,one_mul] using PiLp.norm_apply_le v (Fin.last (k+2))
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_scalarFiniteGradientSquare_first_le (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    ‖fderiv ℝ (scalarFiniteGradientSquare s β p) x‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [scalarFiniteGradientSquare_first,norm_mul,norm_mul,norm_mul]
  have hm := Paper.norm_parisiGradient_le_one β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)
  have hh := Paper.norm_parisiHessian_le_one_all β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤‖(2:ℝ)‖)) hh
    (norm_nonneg _) (by norm_num : (0:ℝ)≤‖(2:ℝ)‖*1)
  simpa only [show ‖(2:ℝ)‖=2 from by norm_num,mul_one] using mul_le_mul hb (PiLp.norm_apply_le v p)
    (norm_nonneg _) (by norm_num : (0:ℝ)≤‖(2:ℝ)‖*1*1)

theorem norm_scalarFiniteGaussianWeight_first_le (s : RSBScheme k) (β : ℝ)
    (e : Bool) (x : QuantitativePaper.Field (k+3)) :
    ‖fderiv ℝ (fun y=>Real.exp (scalarFiniteEuclideanExponent s β e y)) x‖≤
      2*Real.exp ‖x‖ := by
  have hd := ((contDiff_scalarFiniteEuclideanExponent s β e).differentiable (by simp) x).hasFDerivAt.exp
  rw [hd.fderiv,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  have hh := mul_le_mul (Real.exp_le_exp.mpr (scalarFiniteEuclideanExponent_le_norm s β e x))
    (norm_scalarFiniteEuclideanExponent_first_le s β e x) (norm_nonneg _) (Real.exp_pos _).le
  simpa only [mul_comm] using hh

theorem norm_scalarFiniteGaussianSquare_first_le (s : RSBScheme k) (β : ℝ)
    (e : Bool) (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    ‖fderiv ℝ (fun y=>Real.exp (scalarFiniteEuclideanExponent s β e y)*
      scalarFiniteGradientSquare s β p y) x‖≤4*Real.exp ‖x‖ := by
  have hd := (((contDiff_scalarFiniteEuclideanExponent s β e).differentiable (by simp) x).hasFDerivAt.exp).mul
    ((contDiff_scalarFiniteGradientSquare s β p).differentiable (by simp) x).hasFDerivAt
  change ‖fderiv ℝ ((fun y=>Real.exp (scalarFiniteEuclideanExponent s β e y)) *
    scalarFiniteGradientSquare s β p) x‖≤_
  rw [hd.fderiv]
  have hV := Real.exp_le_exp.mpr (scalarFiniteEuclideanExponent_le_norm s β e x)
  have he : 0≤Real.exp (scalarFiniteEuclideanExponent s β e x) := (Real.exp_pos _).le
  have h1 := mul_le_mul hV (norm_scalarFiniteGradientSquare_first_le s β p x)
    (norm_nonneg _) (Real.exp_pos _).le
  have hder := mul_le_mul hV (norm_scalarFiniteEuclideanExponent_first_le s β e x)
    (norm_nonneg _) (Real.exp_pos _).le
  have h2 := mul_le_mul (norm_scalarFiniteGradientSquare_le_one s β p x) hder
    (mul_nonneg he (norm_nonneg _)) (by norm_num : (0:ℝ)≤1)
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_of_nonneg he]
  nlinarith

end QuantitativeFollowup
