module
public import QuantitativeFollowup.ScalarFiniteObservableDerivatives
public import QuantitativeFollowup.ScalarGaussianPrefix
public import FRSB.ConstantMassGrowth
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

/-! Literal Gaussian integral expectations and normalization of the actual
finite marked scalar law. The normalized weights are derived from the
constructed probability law, rather than assumed in the response calculus. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarFiniteGaussianInput (s : RSBScheme k) (β : ℝ) :
    QuantitativePaper.Field (k+2)→L[ℝ]QuantitativePaper.Field (k+3) :=
  scalarCoefficientHistoryLinear (fun j=>Real.sqrt (β^2*
    ((FRSB.forwardSchemeTime s 1 (j+1):ℝ)-FRSB.forwardSchemeTime s 1 j))) (k+2)

theorem scalarFiniteGaussianInput_eq_history (s : RSBScheme k) (β : ℝ)
    (z : QuantitativePaper.Field (k+2)) :
    WithLp.ofLp (scalarFiniteGaussianInput s β z)=
      scalarGaussianHistoryLinear β (FRSB.forwardSchemeTime s 1) (k+2) z := by
  rw [scalarFiniteGaussianInput,scalarCoefficientHistoryLinear_eq_history]
  rfl

theorem scalarFiniteHistoryDensity_eq_euclidean (s : RSBScheme k) (β : ℝ)
    (p : (Fin (k+3)→ℝ)×Bool) :
    scalarFiniteHistoryDensity s β p=(1/2 : ℝ≥0∞)*
      ENNReal.ofReal (Real.exp (scalarFiniteEuclideanExponent s β p.2 (WithLp.toLp 2 p.1))) := by
  unfold scalarFiniteHistoryDensity scalarFiniteEuclideanExponent
  simp only [WithLp.ofLp_toLp]
  congr 3
  congr 1
  have hs : (∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (i+1),p.1 ⟨i+1,by omega⟩))=
      ∑i∈Finset.range (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),p.1 (Fin.ofNat (k+3) (i+1))) := by
    let f : ℕ→ℝ := fun i=>(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (i+1),p.1 (Fin.ofNat (k+3) (i+1)))
    calc
      _ = ∑i : Fin (k+1),f i := by
        apply Finset.sum_congr rfl
        intro i _
        have he : Fin.ofNat (k+3) (i+1)=(⟨i+1,by omega⟩ : Fin (k+3)) := by
          apply Fin.ext
          simp only [Fin.val_ofNat]
          exact Nat.mod_eq_of_lt (by omega)
        dsimp only [f]
        rw [he]
      _ = _ := Fin.sum_univ_eq_sum_range f (k+1)
  exact hs.symm

theorem scalarFiniteEuclideanExponent_le_norm (s : RSBScheme k) (β : ℝ) (e : Bool)
    (x : QuantitativePaper.Field (k+3)) : scalarFiniteEuclideanExponent s β e x≤‖x‖ := by
  have hsum : 0≤∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (s.m_mono i (by omega)))
      (FRSB.parisiPotential_nonneg β (Paper.parisiSchemeMeasure s) _ _ (FRSB.forwardSchemeTime_le s 1 _))
  have he : ‖Paper.spinSign e‖=1 := by cases e <;> norm_num [Paper.spinSign]
  have hx := PiLp.norm_apply_le x (Fin.last (k+2))
  have hh : Paper.spinSign e*x (Fin.last (k+2))≤‖x‖ := by
    apply (le_abs_self _).trans
    simpa only [abs_mul,←Real.norm_eq_abs,he,one_mul] using hx
  dsimp only [scalarFiniteEuclideanExponent]
  linarith

theorem integral_scalarGaussianMarkedLaw_euclidean (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (f : QuantitativePaper.Field (k+3)×Bool→ℝ)
    (hf : Measurable f) (K : ℝ) (hb : ∀p,‖f p‖≤K) :
    (∫p,f (scalarFiniteGaussianInput s β p.1,p.2) ∂scalarGaussianMarkedLaw s β)=
      (1/2 : ℝ)*∑e : Bool,∫z,Real.exp (scalarFiniteEuclideanExponent s β e
        (scalarFiniteGaussianInput s β z))*f (scalarFiniteGaussianInput s β z,e) ∂fieldGaussian (k+2) := by
  let A:=scalarFiniteGaussianInput s β
  let W : QuantitativePaper.Field (k+2)×Bool→ℝ := fun p=>
    (1/2:ℝ)*Real.exp (scalarFiniteEuclideanExponent s β p.2 (A p.1))*f (A p.1,p.2)
  have hK : 0≤K := (norm_nonneg (f (0,false))).trans (hb _)
  have hmV : Measurable (fun p : QuantitativePaper.Field (k+2)×Bool=>
      scalarFiniteEuclideanExponent s β p.2 (A p.1)) := by
    exact measurable_from_prod_countable_left fun e=>
      ((contDiff_scalarFiniteEuclideanExponent s β e).continuous.comp A.continuous).measurable
  have hmW : Measurable W := (measurable_const.mul hmV.exp).mul
    (hf.comp ((A.measurable.comp measurable_fst).prodMk measurable_snd))
  have hiW : Integrable W ((fieldGaussian (k+2)).prod (Measure.count : Measure Bool)) := by
    apply (((SYK.integrable_exp_mul_norm (ι:=Fin (k+2)) ‖A‖).comp_fst
      (Measure.count : Measure Bool)).const_mul (K/2)).mono' hmW.aestronglyMeasurable
    exact .of_forall fun p=>by
      have he := Real.exp_le_exp.mpr ((scalarFiniteEuclideanExponent_le_norm s β p.2 (A p.1)).trans
        (A.le_opNorm p.1))
      dsimp only [W]
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have hh := mul_le_mul he (hb (A p.1,p.2)) (norm_nonneg _) (Real.exp_pos _).le
      nlinarith
  have hd (p : QuantitativePaper.Field (k+2)×Bool) :
      scalarFiniteHistoryDensity s β (scalarGaussianHistoryMarkMap s β p)=
        (1/2:ℝ≥0∞)*ENNReal.ofReal (Real.exp (scalarFiniteEuclideanExponent s β p.2 (A p.1))) := by
    rw [scalarFiniteHistoryDensity_eq_euclidean]
    congr 3
    exact congrArg (fun y=>scalarFiniteEuclideanExponent s β p.2 y)
      (WithLp.toLp_ofLp _ _ |>.trans (congrArg (WithLp.toLp 2)
        (scalarFiniteGaussianInput_eq_history s β p.1).symm))
  rw [scalarGaussianMarkedLaw]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun p=>scalarFiniteHistoryDensity s β (scalarGaussianHistoryMarkMap s β p))
    ((measurable_scalarFiniteHistoryDensity s β).comp (measurable_scalarGaussianHistoryMarkMap s β))
    (.of_forall fun p=>by rw [hd p]; finiteness)]
  have he : (fun p : QuantitativePaper.Field (k+2)×Bool=>
      (scalarFiniteHistoryDensity s β (scalarGaussianHistoryMarkMap s β p)).toReal •
        f (A p.1,p.2))=W := by
    funext p
    rw [hd p,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le]
    norm_num [W,smul_eq_mul]
  rw [he,integral_prod_symm W hiW,integral_count]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun z=>by dsimp only [W];ring

/-- Normalization is obtained from the actual constructed probability law. -/
theorem scalarFiniteGaussian_normalization (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    (∑e : Bool,∫z,Real.exp (scalarFiniteEuclideanExponent s β e
      (scalarFiniteGaussianInput s β z)) ∂fieldGaussian (k+2))=2 := by
  haveI := isProbabilityMeasure_scalarGaussianMarkedLaw s β hβ
  have hh := integral_scalarGaussianMarkedLaw_euclidean s β hβ (fun _=>1)
    measurable_const 1 (fun _=>by norm_num)
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one] at hh
  linarith

/-- Every measurable Euclidean history observable agrees with the actual
constructed diffusion/spin expectation; boundedness is unnecessary here. -/
theorem integral_scalarGaussianMarkedLaw_euclidean_physical (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (f : QuantitativePaper.Field (k+3)×Bool→ℝ) (hf : Measurable f) :
    (∫p,f (scalarFiniteGaussianInput s β p.1,p.2) ∂scalarGaussianMarkedLaw s β)=
      ∫p,f (WithLp.toLp 2 (scalarSelectedHistory s β hβ p.1),p.2)
        ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s) := by
  have hm : Measurable (fun p : (Fin (k+3)→ℝ)×Bool=>f (WithLp.toLp 2 p.1,p.2)) :=
    hf.comp (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+3)=>ℝ)).symm.continuous.measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hh := integral_scalarGaussianMarkedLaw_history s β hβ
    (fun p=>f (WithLp.toLp 2 p.1,p.2)) hm
  convert hh using 1
  apply integral_congr_ae
  exact .of_forall fun p=>by
    change f (scalarFiniteGaussianInput s β p.1,p.2)=
      f (WithLp.toLp 2 (scalarGaussianHistoryLinear β (FRSB.forwardSchemeTime s 1) (k+2) p.1),p.2)
    rw [←scalarFiniteGaussianInput_eq_history]

end QuantitativeFollowup
