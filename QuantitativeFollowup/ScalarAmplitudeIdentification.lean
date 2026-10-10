module
public import QuantitativeFollowup.ScalarAmplitudeRecursion
public import FRSB.ConstantMassEvolution
public import QuantitativePaper.VectorInterpolationNoise

@[expose] public section

/-! Identification of the fixed-noise amplitude recursion with the actual
finite scalar PDE at every retained node. Repeated nodes use the genuine
zero-variance Cole--Hopf identity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem fieldGaussian_coordinate_map (i : Fin n) :
    (fieldGaussian n).map (fun z => z i) = gaussianReal 0 1 := by
  rw [fieldGaussian, SYK.standardGaussianMeasureOnEuclidean,
    Measure.map_map (g := fun z : QuantitativePaper.Field n => z i) (f := WithLp.toLp 2)
      (by fun_prop) (WithLp.measurable_toLp 2 _)]
  change (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (Function.eval i)=_
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq

theorem fieldGaussian_scaled_coordinate_map (i : Fin n) (a : ℝ) :
    (fieldGaussian n).map (fun z => a*z i) = gaussianReal 0 (a^2).toNNReal := by
  have he : (fun z : QuantitativePaper.Field n => a*z i)=(fun y : ℝ => a*y) ∘ (fun z => z i) := rfl
  rw [he, ←Measure.map_map (g := fun y : ℝ => a*y) (f := fun z : QuantitativePaper.Field n => z i) (by fun_prop) (by fun_prop : Measurable (fun z : QuantitativePaper.Field n => z i)),
    fieldGaussian_coordinate_map, gaussianReal_map_const_mul]
  simp only [mul_zero,mul_one]
  congr 1
  exact Subtype.ext (Real.coe_toNNReal _ (sq_nonneg _)).symm

theorem scalarAmplitudeField_cell_shift (w : ScalarAmplitudeState n) (i : Fin n)
    (z : QuantitativePaper.Field n) :
    scalarAmplitudeField (w+scalarAmplitudeCellShift i z)=scalarAmplitudeField w+w.1 i*z i := by
  rw [scalarAmplitudeCellShift, ContinuousLinearMap.comp_apply, scalarAmplitudeField_noise_shift,
    scalarAmplitudeCoordinateProjection_apply, EuclideanSpace.inner_single_right]
  simp only [RCLike.conj_to_real]
  ring

theorem gaussianShiftColeHopf_scalarAmplitude_step (f : ScalarAmplitudeState n → ℝ)
    (h : ℝ → ℝ) (hh : Measurable h) (mass : ℝ) (w : ScalarAmplitudeState n) (i : Fin n)
    (he : ∀ z : QuantitativePaper.Field n,
      f (w+scalarAmplitudeCellShift i z)=h (scalarAmplitudeField w+w.1 i*z i)) :
    gaussianShiftColeHopf (scalarAmplitudeCellShift i) mass f w =
      coleHopf mass ((w.1 i)^2).toNNReal h (scalarAmplitudeField w) := by
  have hmap := fieldGaussian_scaled_coordinate_map i (w.1 i)
  have hi (g : ℝ → ℝ) (hg : Measurable g) :
      (∫ z, g (scalarAmplitudeField w+w.1 i*z i) ∂fieldGaussian n)=
        ∫ y, g (scalarAmplitudeField w+y) ∂gaussianReal 0 ((w.1 i)^2).toNNReal := by
    rw [←hmap]
    symm
    exact integral_map (by fun_prop : AEMeasurable (fun z : QuantitativePaper.Field n => w.1 i*z i) (fieldGaussian n))
      (hg.comp (by fun_prop : Measurable (fun y : ℝ => scalarAmplitudeField w+y))).aestronglyMeasurable
  unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition coleHopf
  simp_rw [he]
  by_cases hm : mass=0
  · simp only [hm, ite_true]
    exact hi h hh
  · simp only [hm,ite_false]
    rw [hi (fun x => Real.exp (mass*h x)) (Real.measurable_exp.comp (hh.const_mul mass))]
    simp only [div_eq_mul_inv,mul_comm,mul_one]

theorem scalarPotential_scheme_node_step (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (j : ℕ) (hj : j≤k+1) (x : ℝ) :
    parisiPotential β (parisiSchemeMeasure s) (s.q (k+1-j),x)=
      coleHopf (s.m (k+1-j)) (β^2*(s.q (k+2-j)-s.q (k+1-j))).toNNReal
        (fun y => parisiPotential β (parisiSchemeMeasure s) (s.q (k+2-j),y)) x := by
  have hi : k+1-j≤k+1 := Nat.sub_le _ _
  have hnext : k+2-j=(k+1-j)+1 := by omega
  have hq := s.q_mono (k+1-j) hi
  by_cases he : s.q (k+1-j)=s.q (k+2-j)
  · simp only [he,sub_self,mul_zero,Real.toNNReal_zero,coleHopf_zero_var]
  · have hlt : s.q (k+1-j)<s.q (k+2-j) := by rw [←hnext] at hq;exact lt_of_le_of_ne hq he
    exact FRSB.parisiPotential_coleHopf_constant_interval β hβ (parisiSchemeMeasure s)
      (s.q_nonneg (by omega)) hlt (s.q_le_one (by omega))
      (fun y hy => parisiCDF_scheme_cell s hi (by simpa only [←hnext] using hy))
      ⟨le_rfl,hlt.le⟩ ⟨hlt.le,le_rfl⟩ x

theorem scalarAmplitudeRecursion_eq_potential (s r : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (hm : ∀ i, s.m i=r.m i)
    (a : QuantitativePaper.Field (k+2))
    (ha : ∀ i : Fin (k+2), (a i)^2=β^2*(r.q (i+1)-r.q i))
    (j : ℕ) (hj : j≤k+2) (z : QuantitativePaper.Field (k+2)) (x : ℝ) :
    scalarAmplitudeRecursion s j (a,z,x)=
      parisiPotential β (parisiSchemeMeasure r) (r.q (k+2-j), scalarAmplitudeField (a,z,x)) := by
  induction j generalizing z x with
  | zero => simp only [scalarAmplitudeRecursion, Nat.sub_zero,r.q_top,parisiPotential_terminal,scalarAmplitudeTerminal]
  | succ j ih =>
    have hj' : j≤k+1 := by omega
    let i := scalarAmplitudeCell k j
    have hi : (i:ℕ)=k+1-j := rfl
    rw [scalarAmplitudeRecursion]
    rw [gaussianShiftColeHopf_scalarAmplitude_step _
      (fun y => parisiPotential β (parisiSchemeMeasure r) (r.q (k+2-j),y))
      (((continuous_parisiPotential β (parisiSchemeMeasure r)).comp
        (continuous_const.prodMk continuous_id)).measurable) _ _ i]
    · rw [ha i,hi,show k+1-j+1=k+2-j by omega,hm]
      simpa only [show k+2-(j+1)=k+1-j by omega] using (scalarPotential_scheme_node_step r β hβ j hj' (scalarAmplitudeField (a,z,x))).symm
    · intro v
      have hadd : ((a,z,x)+scalarAmplitudeCellShift i v)=
          (a,z+scalarAmplitudeCoordinateProjection i v,x) := by
        simp only [scalarAmplitudeCellShift, ContinuousLinearMap.comp_apply, scalarAmplitudeNoiseShift_apply,
          Prod.mk_add_mk, add_zero]
      rw [hadd, ih (by omega)]
      have he := scalarAmplitudeField_cell_shift (a,z,x) i v
      rw [hadd] at he
      rw [he]

end QuantitativeFollowup
