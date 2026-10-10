module
public import FourPapersCommon.GenericFiniteStateCascadeTimeData

@[expose] public section

/-! Dominated joint continuity of actual weighted Gaussian field integrals.
The local Gaussian envelope is proved from the inherited spatial Lipschitz
bound and continuity of the true preceding potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 300000
variable {S I : Type*} [Fintype S] [Fintype I]

private theorem eventually_norm_bound {A V : Type*} [TopologicalSpace A]
    [NormedAddCommGroup V] {f : A → V} {p : A} (hf : ContinuousAt f p) :
    ∀ᶠ q in 𝓝 p, ‖f q‖ ≤ ‖f p‖+1 :=
  (hf.norm.tendsto.eventually (eventually_lt_nhds (by linarith))).mono fun _ h => h.le

private theorem family_local_exp_bound {F : ℝ → FiniteStateField S → ℝ}
    {C B K : ℝ≥0} (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p : ℝ×FiniteStateField S) (hp : p.1 ∈ Ioo 0 1) :
    ∀ᶠ q : ℝ×FiniteStateField S in 𝓝 p,
      q.1 ∈ Ioo 0 1 ∧ ∀ z : FiniteStateGaussianInput I,
        Real.exp (a*F q.1 (q.2+Real.sqrt (1-q.1) • L z)) ≤
          Real.exp (|a| *(|F p.1 p.2|+1+C))*
            Real.exp ((|a| *C*(|Real.sqrt (1-p.1)|+1)*‖L‖)*‖z‖) := by
  have htime : ∀ᶠ q : ℝ×FiniteStateField S in 𝓝 p, q.1 ∈ Ioo 0 1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hp)
  have hF0 : ContinuousAt (fun q : ℝ×FiniteStateField S => F q.1 p.2) p := by
    exact (d.cont.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds ⟨hp, mem_univ _⟩)).comp
      (continuous_fst.prodMk continuous_const).continuousAt
  have hspace : ContinuousAt (fun q : ℝ×FiniteStateField S => q.2-p.2) p := by fun_prop
  have hsqrt : ContinuousAt (fun q : ℝ×FiniteStateField S => Real.sqrt (1-q.1)) p := by fun_prop
  filter_upwards [htime, eventually_norm_bound hF0, eventually_norm_bound hspace,
    eventually_norm_bound hsqrt] with q hq hqF hqH hqS
  refine ⟨hq, fun z => ?_⟩
  simp only [Real.norm_eq_abs] at hqF hqS
  simp only [sub_self, norm_zero, zero_add] at hqH
  have hLip : LipschitzWith C (F q.1) := lipschitzWith_of_nnnorm_fderiv_le
    ((d.spatial_C2 q.1 hq).differentiable (by norm_num))
      (fun H => NNReal.coe_le_coe.mp (d.first_bound q.1 hq H))
  have hfd := hLip.norm_sub_le (q.2+Real.sqrt (1-q.1) • L z) p.2
  rw [Real.norm_eq_abs] at hfd
  have hnorm : ‖q.2+Real.sqrt (1-q.1) • L z-p.2‖ ≤
      1+(|Real.sqrt (1-p.1)|+1)*‖L‖*‖z‖ := by
    rw [show q.2+Real.sqrt (1-q.1) • L z-p.2 = (q.2-p.2)+Real.sqrt (1-q.1) • L z by abel]
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs]
    have hh := mul_le_mul hqS (L.le_opNorm z) (norm_nonneg _) (by positivity)
    calc
      _ ≤ 1+(|Real.sqrt (1-p.1)|+1)*(‖L‖*‖z‖) := add_le_add hqH hh
      _ = _ := by ring
  have hb : |F q.1 (q.2+Real.sqrt (1-q.1) • L z)| ≤
      |F p.1 p.2|+1+C+C*(|Real.sqrt (1-p.1)|+1)*‖L‖*‖z‖ := by
    have htri := abs_add_le
      (F q.1 (q.2+Real.sqrt (1-q.1) • L z)-F q.1 p.2) (F q.1 p.2)
    rw [sub_add_cancel] at htri
    calc
      _ ≤ |F q.1 (q.2+Real.sqrt (1-q.1) • L z)-F q.1 p.2|+|F q.1 p.2| := htri
      _ ≤ C*‖q.2+Real.sqrt (1-q.1) • L z-p.2‖+(|F p.1 p.2|+1) := add_le_add hfd hqF
      _ ≤ C*(1+(|Real.sqrt (1-p.1)|+1)*‖L‖*‖z‖)+(|F p.1 p.2|+1) :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm C.2) le_rfl
      _ = _ := by ring
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg a)
  have hs := le_abs_self (a*F q.1 (q.2+Real.sqrt (1-q.1) • L z))
  rw [abs_mul] at hs
  calc
    _ ≤ |a| * |F q.1 (q.2+Real.sqrt (1-q.1) • L z)| := hs
    _ ≤ |a| *(|F p.1 p.2|+1+C+C*(|Real.sqrt (1-p.1)|+1)*‖L‖*‖z‖) := hh
    _ = _ := by ring

theorem continuousOn_weighted_finiteStateGaussian_family
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (G : ℝ → FiniteStateField S → V)
    (hG : ContinuousOn (fun p : ℝ×FiniteStateField S => G p.1 p.2) (finiteStateGaussianTimeDomain S))
    (R : ℝ≥0) (hR : ∀ t ∈ Ioo 0 1, ∀ H, ‖G t H‖ ≤ R) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      ∫ z, Real.exp (a*F p.1 (p.2+Real.sqrt (1-p.1) • L z)) •
        G p.1 (p.2+Real.sqrt (1-p.1) • L z) ∂stdGaussian (FiniteStateGaussianInput I))
          (finiteStateGaussianTimeDomain S) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hlocal := family_local_exp_bound d a L p hp.1
  have hGc (t : ℝ) (ht : t ∈ Ioo 0 1) : Continuous (G t) := by
    apply continuousOn_univ.mp
    exact hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun H _ => ⟨ht, mem_univ H⟩)
  apply continuousAt_of_dominated
    (bound := fun z => (R*Real.exp (|a| *(|F p.1 p.2|+1+C)))*
      Real.exp ((|a| *C*(|Real.sqrt (1-p.1)|+1)*‖L‖)*‖z‖))
  · filter_upwards [hlocal] with q hq
    have hmap : Continuous (fun z : FiniteStateGaussianInput I => q.2+Real.sqrt (1-q.1) • L z) :=
      continuous_const.add (L.continuous.const_smul (Real.sqrt (1-q.1)))
    have hf : Continuous (fun z : FiniteStateGaussianInput I => F q.1 (q.2+Real.sqrt (1-q.1) • L z)) :=
      (d.spatial_C2 q.1 hq.1).continuous.comp hmap
    have he : Continuous (fun z : FiniteStateGaussianInput I => Real.exp (a*F q.1 (q.2+Real.sqrt (1-q.1) • L z))) :=
      Real.continuous_exp.comp (hf.const_mul a)
    have hg : Continuous (fun z : FiniteStateGaussianInput I => G q.1 (q.2+Real.sqrt (1-q.1) • L z)) :=
      (hGc q.1 hq.1).comp hmap
    exact (he.smul hg).aestronglyMeasurable
  · filter_upwards [hlocal] with q hq
    exact .of_forall fun z => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hh := mul_le_mul (hq.2 z)
        (hR q.1 hq.1 (q.2+Real.sqrt (1-q.1) • L z))
        (norm_nonneg (G q.1 (q.2+Real.sqrt (1-q.1) • L z))) (by positivity)
      convert hh using 1
      ring
  · exact (integrable_exp_mul_norm_gaussian (stdGaussian (FiniteStateGaussianInput I)) _).const_mul _
  · exact .of_forall fun z => by
      have hshift : Continuous (fun q : ℝ×FiniteStateField S =>
          (q.1,q.2+Real.sqrt (1-q.1) • L z)) := by fun_prop
      have hpf : (p.1,p.2+Real.sqrt (1-p.1) • L z) ∈ finiteStateGaussianTimeDomain S := ⟨hp.1, mem_univ _⟩
      have hs : ContinuousAt (fun q : ℝ×FiniteStateField S =>
          (q.1,q.2+Real.sqrt (1-q.1) • L z)) p := hshift.continuousAt
      have hf0 : ContinuousAt (fun q : ℝ×FiniteStateField S => F q.1 q.2)
          (p.1,p.2+Real.sqrt (1-p.1) • L z) :=
        d.cont.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds hpf)
      have hg0 : ContinuousAt (fun q : ℝ×FiniteStateField S => G q.1 q.2)
          (p.1,p.2+Real.sqrt (1-p.1) • L z) :=
        hG.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds hpf)
      have hf : ContinuousAt (fun q : ℝ×FiniteStateField S =>
          F q.1 (q.2+Real.sqrt (1-q.1) • L z)) p :=
        hf0.comp (f := fun q : ℝ×FiniteStateField S =>
          (q.1,q.2+Real.sqrt (1-q.1) • L z)) hs
      have hg : ContinuousAt (fun q : ℝ×FiniteStateField S =>
          G q.1 (q.2+Real.sqrt (1-q.1) • L z)) p :=
        hg0.comp (f := fun q : ℝ×FiniteStateField S =>
          (q.1,q.2+Real.sqrt (1-q.1) • L z)) hs
      exact (Real.continuous_exp.continuousAt.comp (hf.const_mul a)).smul hg

end FourPapersCommon
