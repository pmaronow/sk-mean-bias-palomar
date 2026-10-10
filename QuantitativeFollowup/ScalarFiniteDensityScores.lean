module
public import QuantitativeFollowup.ScalarFiniteGaussianLaw
public import QuantitativeFollowup.GaussianWeightHessian

@[expose] public section

/-! Genuine first and second spatial scores of the literal scalar finite
marked density. All spatial derivatives are those of the actual PDE solution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

 def scalarFiniteEuclideanExponent (s : RSBScheme k) (β : ℝ) (e : Bool)
    (x : QuantitativePaper.Field (k+3)) : ℝ :=
  Paper.spinSign e*x (Fin.last (k+2))-
    ∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩)

 theorem scalarSchemeHistoryClock_coe (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) :
    (FRSB.forwardSchemeTime s 1 i:ℝ)=s.q i := by
  simp only [FRSB.forwardSchemeTime,min_eq_left hi,NNReal.coe_one,min_eq_left (s.q_le_one hi)]
  rfl

 theorem contDiff_scalarFiniteEuclideanExponent (s : RSBScheme k) (β : ℝ) (e : Bool) :
    ContDiff ℝ ∞ (scalarFiniteEuclideanExponent s β e) := by
  unfold scalarFiniteEuclideanExponent
  apply (contDiff_const.mul ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) (Fin.last (k+2))).contDiff)).sub
  apply ContDiff.sum
  intro i _
  have ht : (FRSB.forwardSchemeTime s 1 (i+1):ℝ)∈Icc (0:ℝ) 1 :=
    ⟨(FRSB.forwardSchemeTime s 1 (i+1)).coe_nonneg,FRSB.forwardSchemeTime_le s 1 _⟩
  exact contDiff_const.mul ((Paper.contDiff_parisiPotential_spatial β (Paper.parisiSchemeMeasure s) _ ht).comp
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩).contDiff)

 theorem hasFDerivAt_scalarFiniteNodePotential (s : RSBScheme k) (β : ℝ)
    (i : Fin (k+1)) (x : QuantitativePaper.Field (k+3)) :
    HasFDerivAt (fun y : QuantitativePaper.Field (k+3) =>
      Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),y ⟨i+1,by omega⟩))
      (Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩) •
        PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩) x := by
  have ht : (FRSB.forwardSchemeTime s 1 (i+1):ℝ)∈Icc (0:ℝ) 1 :=
    ⟨(FRSB.forwardSchemeTime s 1 (i+1)).coe_nonneg,FRSB.forwardSchemeTime_le s 1 _⟩
  have hd := (Paper.hasDerivAt_parisiPotential_spatial_all β (Paper.parisiSchemeMeasure s) _ (x ⟨i+1,by omega⟩) ht).hasFDerivAt.comp x
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩).hasFDerivAt
  convert! hd using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,PiLp.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

 theorem scalarFiniteEuclideanExponent_first (s : RSBScheme k) (β : ℝ) (e : Bool)
    (x v : QuantitativePaper.Field (k+3)) :
    fderiv ℝ (scalarFiniteEuclideanExponent s β e) x v=
      Paper.spinSign e*v (Fin.last (k+2))-
        ∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
          (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩)*v ⟨i+1,by omega⟩ := by
  have hd := ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) (Fin.last (k+2))).hasFDerivAt.const_mul
    (Paper.spinSign e)).sub
      (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hasFDerivAt_scalarFiniteNodePotential s β i x).const_mul
        (s.m (i+1)-s.m i))
  have hh := congrArg (fun D : QuantitativePaper.Field (k+3)→L[ℝ] ℝ => D v) hd.fderiv
  simp only [sub_apply,sum_apply,smul_apply,smul_eq_mul,PiLp.proj_apply,mul_assoc] at hh
  convert! hh using 1 <;> simp only [mul_assoc]

theorem hasFDerivAt_scalarFiniteNodeGradient (s : RSBScheme k) (β : ℝ)
    (i : Fin (k+1)) (x : QuantitativePaper.Field (k+3)) :
    HasFDerivAt (fun y : QuantitativePaper.Field (k+3) =>
      Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),y ⟨i+1,by omega⟩))
      (Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩) •
        PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩) x := by
  have hd := (Paper.hasDerivAt_parisiGradient_spatial_all β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 (i+1))
    (x ⟨i+1,by omega⟩)).hasFDerivAt.comp x
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩).hasFDerivAt
  convert! hd using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,PiLp.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

theorem scalarFiniteEuclideanExponent_second (s : RSBScheme k) (β : ℝ) (e : Bool)
    (x u v : QuantitativePaper.Field (k+3)) :
    FourPapersCommon.vectorHessian (scalarFiniteEuclideanExponent s β e) x u v=
      -∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
          (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩)*u ⟨i+1,by omega⟩*v ⟨i+1,by omega⟩ := by
  have hleft := hasFDerivAt_directional_field (scalarFiniteEuclideanExponent s β e)
    ((contDiff_scalarFiniteEuclideanExponent s β e).of_le (by simp)) x v
  have he : (fun y=>fderiv ℝ (scalarFiniteEuclideanExponent s β e) y v)=
      (fun y : QuantitativePaper.Field (k+3)=>Paper.spinSign e*v (Fin.last (k+2))-
        ∑i : Fin (k+1),(s.m (i+1)-s.m i)*Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
          (FRSB.forwardSchemeTime s 1 (i+1),y ⟨i+1,by omega⟩)*v ⟨i+1,by omega⟩) :=
    funext fun y => scalarFiniteEuclideanExponent_first s β e y v
  rw [he] at hleft
  have hright := (hasFDerivAt_const (Paper.spinSign e*v (Fin.last (k+2))) x).sub
    (HasFDerivAt.fun_sum (u:=Finset.univ) fun i _=>
      ((hasFDerivAt_scalarFiniteNodeGradient s β i x).const_mul (s.m (i+1)-s.m i)).mul_const
        (v ⟨i+1,by omega⟩))
  have hh := congrArg (fun D : QuantitativePaper.Field (k+3)→L[ℝ] ℝ=>D u) (hleft.unique hright)
  simp only [ContinuousLinearMap.flip_apply,zero_sub] at hh
  rw [hh]
  simp only [neg_apply,sum_apply,smul_apply,smul_eq_mul,PiLp.proj_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end QuantitativeFollowup
