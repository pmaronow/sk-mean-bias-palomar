module
public import QuantitativeFollowup.ReflectedNoise

@[expose] public section

/-! Each actual reflected uniform perturbation has Lebesgue density at
most `1/h`. The proof retains both endpoint reflections and works at
q=0 and q=1, rather than dropping atoms by an informal density argument. -/
noncomputable section
open Set MeasureTheory Paper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000

theorem map_volume_abs_le : (volume:Measure ℝ).map abs≤(2:ℝ≥0∞) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply measurable_abs hS,Measure.smul_apply]
  have hsub : abs ⁻¹' S⊆S∪(fun x : ℝ=>-x) ⁻¹' S := by
    intro x hx
    by_cases h : 0≤x
    · exact Or.inl (by simpa only [mem_preimage,abs_of_nonneg h] using hx)
    · exact Or.inr (by simpa only [mem_preimage,abs_of_neg (lt_of_not_ge h)] using hx)
  calc
    volume (abs ⁻¹' S)≤volume (S∪(fun x : ℝ=>-x) ⁻¹' S):=measure_mono hsub
    _≤volume S+volume ((fun x : ℝ=>-x) ⁻¹' S):=measure_union_le _ _
    _=2*volume S:=by
      rw [←Measure.map_apply measurable_neg hS,Measure.map_neg_eq_self]
      ring

theorem map_volume_one_sub (a : ℝ) :
    (volume:Measure ℝ).map (fun x=>a-x)=volume := by
  have he : (fun x : ℝ=>a-x)=(fun x=>a+x)∘(fun x=>-x) := by funext x;simp only [Function.comp_apply,sub_eq_add_neg]
  rw [he,←Measure.map_map (g:=fun x : ℝ=>a+x) (f:=fun x : ℝ=>-x)
    (measurable_const.add measurable_id) measurable_neg,Measure.map_neg_eq_self,map_add_left_eq_self]

theorem map_volume_right_reflection_le :
    (volume:Measure ℝ).map (fun x=>1-|x-1|)≤(2:ℝ≥0∞) • volume := by
  have he : (fun x : ℝ=>1-|x-1|)=
      (fun x=>1-x)∘(abs∘(fun x=>x+(-1))) := by funext x;simp only [Function.comp_apply];ring_nf
  rw [he,←Measure.map_map (g:=fun x : ℝ=>1-x) (f:=abs∘(fun x : ℝ=>x+(-1)))
    (measurable_const.sub measurable_id) (measurable_abs.comp (measurable_id.add_const _)),
    ←Measure.map_map (g:=abs) (f:=fun x : ℝ=>x+(-1)) measurable_abs (measurable_id.add_const _),map_add_right_eq_self]
  calc
    _≤((2:ℝ≥0∞) • volume).map (fun x : ℝ=>1-x):=
      Measure.map_mono map_volume_abs_le (measurable_const.sub measurable_id)
    _=(2:ℝ≥0∞) • volume:=by rw [Measure.map_smul (f:=fun x : ℝ=>1-x) _ (measurable_const.sub measurable_id).aemeasurable,map_volume_one_sub]

theorem symmetricUniformLaw_shift (h q : ℝ) :
    (symmetricUniformLaw h).map (fun u=>q+u)=
      ENNReal.ofReal (1/(2*h)) • volume.restrict (Icc (q-h) (q+h)) := by
  have hm : Measurable (fun u : ℝ=>q+u):=measurable_const.add measurable_id
  have he : (fun u : ℝ=>q+u) ⁻¹' Icc (q-h) (q+h)=Icc (-h) h := by
    ext u;simp only [mem_preimage,mem_Icc]
    constructor <;>rintro ⟨h₁,h₂⟩ <;>constructor <;>linarith
  rw [symmetricUniformLaw,Measure.map_smul _ hm.aemeasurable,←he,←Measure.restrict_map hm measurableSet_Icc,
    map_add_left_eq_self]

theorem abs_uniform_point_density_le (h : ℝ) (hh : 0<h) (q : ℝ) :
    (symmetricUniformLaw h).map (fun u=>|q+u|)≤ENNReal.ofReal (1/h) • volume := by
  have hm : Measurable (fun u : ℝ=>q+u):=measurable_const.add measurable_id
  rw [show (fun u : ℝ=>|q+u|)=abs∘(fun u=>q+u) from rfl,
    ←Measure.map_map measurable_abs hm,symmetricUniformLaw_shift,
    Measure.map_smul _ measurable_abs.aemeasurable]
  have he : ENNReal.ofReal (1/(2*h))*2=ENNReal.ofReal (1/h) := by
    rw [←ENNReal.ofReal_ofNat,←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc
    _≤ENNReal.ofReal (1/(2*h)) • ((2:ℝ≥0∞) • volume):=by
      intro S
      change ENNReal.ofReal (1/(2*h))*_≤ENNReal.ofReal (1/(2*h))*_
      gcongr
      exact (Measure.map_mono Measure.restrict_le_self measurable_abs).trans map_volume_abs_le
    _=_:=by rw [smul_smul,he]

theorem reflected_uniform_point_density_le (h : ℝ) (hh : h∈Ioc (0:ℝ) (1/2))
    (q : ℝ) (_hq : q∈Icc (0:ℝ) 1) :
    (symmetricUniformLaw h).map (fun u=>overlapReflection (q+u))≤
      ENNReal.ofReal (1/h) • volume := by
  let ν : Measure ℝ:=volume.restrict (Icc (q-h) (q+h))
  let c : ℝ≥0∞:=ENNReal.ofReal (1/(2*h))
  have hm : Measurable (fun u : ℝ=>q+u):=measurable_const.add measurable_id
  have hν : ν≤volume:=Measure.restrict_le_self
  have hfold : ν.map overlapReflection≤(2:ℝ≥0∞) • volume := by
    by_cases hqhalf : q≤1/2
    · have he : overlapReflection=ᵐ[ν] abs := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
        simp only [overlapReflection,ite_eq_left_iff]
        intro hn
        exfalso
        linarith [hz.2,hh.2]
      rw [Measure.map_congr he]
      exact (Measure.map_mono hν measurable_abs).trans map_volume_abs_le
    · have he : overlapReflection=ᵐ[ν] (fun z=>1-|z-1|) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
        have hz0 : 0≤z:=by linarith [hz.1,hh.2]
        unfold overlapReflection
        split_ifs with hz1
        · rw [abs_of_nonneg hz0,abs_of_nonpos (by linarith : z-1≤0)];ring
        · rw [abs_of_nonneg (by linarith : 0≤z-1)];ring
      rw [Measure.map_congr he]
      exact (Measure.map_mono hν (measurable_const.sub (measurable_abs.comp
        (measurable_id.sub measurable_const)))).trans map_volume_right_reflection_le
  have hec : c*2=ENNReal.ofReal (1/h) := by
    dsimp only [c]
    rw [←ENNReal.ofReal_ofNat,←ENNReal.ofReal_mul (by exact one_div_nonneg.mpr (mul_nonneg (by norm_num) hh.1.le))]
    congr 1
    field_simp
  rw [show (fun u : ℝ=>overlapReflection (q+u))=overlapReflection∘(fun u=>q+u) from rfl,
    ←Measure.map_map measurable_overlapReflection hm,symmetricUniformLaw_shift,
    Measure.map_smul _ measurable_overlapReflection.aemeasurable]
  change c • ν.map overlapReflection≤_
  calc
    _≤c • ((2:ℝ≥0∞) • volume):=by
      intro S
      change c*_≤c*_
      gcongr
      exact hfold
    _=_:=by rw [smul_smul,hec]

end QuantitativeFollowup
