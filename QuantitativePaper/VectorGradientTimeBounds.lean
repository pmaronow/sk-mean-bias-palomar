module
public import QuantitativePaper.VectorTailAllJets
public import QuantitativePaper.VectorFiniteCellGradientBounds
public import QuantitativePaper.VectorGradientComponentCalculus
public import QuantitativePaper.VectorMeasureGradient

@[expose] public section

/-! Dimension-only time-generator estimates for the genuine finite gradient.
The bounds are uniform in the number and sizes of the profile cells. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem norm_secondJet_gradient_component_le (f : Field n→ℝ) (hf : ContDiff ℝ 3 f)
    (x : Field n) (l : Fin n) :
    ‖iteratedFDeriv ℝ 2 (fun y=>gradient f y l) x‖≤‖iteratedFDeriv ℝ 3 f x‖ := by
  have hg : ContDiff ℝ 2 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Field n)).symm.contDiff.comp (hf.fderiv_right (by norm_num))
  let P : Field n→L[ℝ]ℝ:=EuclideanSpace.proj l
  have hP : ‖P‖≤(1:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖y l‖≤1*‖y‖
    simpa only [Real.norm_eq_abs,one_mul] using PiLp.norm_apply_le y l
  have he:=P.norm_iteratedFDeriv_comp_left (x:=x) hg.contDiffAt (by norm_num : (2:ℕ∞ω)≤2)
  change ‖iteratedFDeriv ℝ 2 (fun y=>gradient f y l) x‖≤_ at he
  exact (he.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))).trans_eq (by
    rw [one_mul,norm_iteratedFDeriv_gradient])

def vectorGradientTimeConstant (n : ℕ) (β t : ℝ) : ℝ :=
  ((1-t)*β^2)*((n:ℝ)*vectorSpatialJetBound n 3/2+(n:ℝ)*Real.sqrt (n:ℝ))

theorem vectorGradientTimeConstant_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) :
    0≤vectorGradientTimeConstant n β t := by
  unfold vectorGradientTimeConstant
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))
    (add_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg n) (vectorSpatialJetBound_nonneg n 3))
      (by norm_num)) (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)))

theorem norm_vectorFiniteCellGradient_timeDerivative_le (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (q : Paper.Overlap) (hq : (q:ℝ)∈Icc (s.q i) (s.q (i+1))) (x : Field n) (l : Fin n) :
    ‖-((1-t)*β^2)*vectorLinearBackwardGenerator
        (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l)
        (vectorFiniteCellPotential s β t p i q) (s.m i) x‖≤vectorGradientTimeConstant n β t := by
  let f:=vectorFiniteCellPotential s β t p i q
  let g:=fun y=>gradient f y l
  let c:=(1-t)*β^2
  have hc:0≤c:=mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)
  have hf : ContDiff ℝ 3 f:=
    (contDiff_vectorColeHopfStep_recursion_field s β t _ _ p (k+1-i)).of_le (by simp)
  have hJ : ‖iteratedFDeriv ℝ 3 f x‖≤vectorSpatialJetBound n 3:=by
    dsimp only [f]
    rw [←vectorTailRecursion_eq_finiteCell s β t q p i hi hq]
    exact norm_vectorTailRecursion_jet_le_uniform s β t q q.property p _ le_rfl 3 (by norm_num) x
  have h₂ : ‖fderiv ℝ (fderiv ℝ g) x‖≤vectorSpatialJetBound n 3:=by
    rw [←norm_iteratedFDeriv_one (fderiv ℝ g),norm_iteratedFDeriv_fderiv]
    exact (norm_secondJet_gradient_component_le f hf x l).trans hJ
  have htrace : |∑j : Fin n,fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single j 1)
      (EuclideanSpace.single j 1)|≤(n:ℝ)*vectorSpatialJetBound n 3:=by
    calc
      _≤∑j : Fin n,|fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1)|:=Finset.abs_sum_le_sum_abs _ _
      _≤∑_j : Fin n,vectorSpatialJetBound n 3:=by
        apply Finset.sum_le_sum
        intro j _
        have hh:=((fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single j 1)).le_opNorm
          (EuclideanSpace.single j 1)).trans
          (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ g) x).le_opNorm
            (EuclideanSpace.single j 1)) (norm_nonneg _))
        simp only [PiLp.norm_single,norm_one,mul_one] at hh
        simpa only [Real.norm_eq_abs] using hh.trans h₂
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hD:‖fderiv ℝ g x‖≤(n:ℝ):=norm_fderiv_vectorFiniteCellGradient_component_le s β t q p i hi hq x l
  have hG:‖gradient f x‖≤Real.sqrt (n:ℝ):=norm_vectorFiniteCellGradient_le s β t q p i hi hq x
  have hm:|s.m i|≤1:=by rw [abs_of_nonneg (s.m_nonneg hi)];exact s.m_le_one hi
  have htransport:|s.m i*fderiv ℝ g x (gradient f x)|≤(n:ℝ)*Real.sqrt (n:ℝ):=by
    rw [abs_mul]
    have hh : |fderiv ℝ g x (gradient f x)|≤(n:ℝ)*Real.sqrt (n:ℝ):=by
      calc
        _≤‖fderiv ℝ g x‖*‖gradient f x‖:=by
          simpa only [Real.norm_eq_abs] using (fderiv ℝ g x).le_opNorm (gradient f x)
        _≤_:=mul_le_mul hD hG (norm_nonneg _) (Nat.cast_nonneg n)
    exact (mul_le_mul hm hh (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  change ‖-c*vectorLinearBackwardGenerator g f (s.m i) x‖≤_
  rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  simp only [vectorLinearBackwardGenerator,vectorBilinearTrace,vectorHessian,map_smul,smul_eq_mul]
  exact (abs_add_le _ _).trans (add_le_add (by
    rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact div_le_div_of_nonneg_right htrace (by norm_num)) htransport)

end QuantitativePaper
