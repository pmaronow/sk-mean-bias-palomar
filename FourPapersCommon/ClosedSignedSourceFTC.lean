module
public import FourPapersCommon.ClosedNonnegativeSourceFTC
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! A signed cropped source extends to closed endpoints under genuine
integrable domination. No measurability or endpoint value is assumed
outside what follows from the cropped integral identities. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1800000

theorem closed_dominated_source_ftc (F g L : ℝ→ℝ) (a b : ℝ) (hab : a≤b)
    (hF : ContinuousOn F (Icc a b)) (hL : IntegrableOn L (Ioc a b) volume)
    (hbound : ∀q∈Ioo a b,|g q|≤L q)
    (hlocal : ∀l∈Ioo a b,∀u∈Ioo a b,l≤u→
      IntegrableOn g (Ioc l u) volume ∧ F u-F l=∫q in l..u,g q) :
    IntegrableOn g (Ioc a b) volume ∧ F b-F a=∫q in a..b,g q := by
  let Z : ℝ→ℝ:=fun q=>∫r in a..q,L r
  have hLI : IntervalIntegrable L volume a b:=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hL
  have hZ : ContinuousOn Z (Icc a b):=by
    simpa only [uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hLI (a:=a) left_mem_uIcc)
  have hLsub (l u : ℝ) (hl : l∈Icc a b) (hu : u∈Icc a b) :
      IntervalIntegrable L volume l u:=hLI.mono_set
        (by rw [uIcc_of_le hab];exact uIcc_subset_Icc hl hu)
  have hZdiff (l u : ℝ) (hl : l∈Icc a b) (hu : u∈Icc a b) :
      Z u-Z l=∫q in l..u,L q:=
    intervalIntegral.integral_interval_sub_left (hLsub a u ⟨le_rfl,hab⟩ hu)
      (hLsub a l ⟨le_rfl,hab⟩ hl)
  obtain ⟨hTotal,hEq⟩:=closed_nonnegative_source_ftc (fun q=>F q+Z q)
    (fun q=>g q+L q) a b hab (hF.add hZ)
    (fun q hq=>by have hh:=(abs_le.mp (hbound q hq)).1;linarith) (by
      intro l hl u hu hlu
      obtain ⟨hg,he⟩:=hlocal l hl u hu hlu
      have hLc:=hLsub l u ⟨hl.1.le,hl.2.le⟩ ⟨hu.1.le,hu.2.le⟩
      refine ⟨hg.add ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlu).mp hLc),?_⟩
      rw [intervalIntegral.integral_add ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlu).mpr hg) hLc]
      have hz:=hZdiff l u ⟨hl.1.le,hl.2.le⟩ ⟨hu.1.le,hu.2.le⟩
      linarith)
  have hg : IntegrableOn g (Ioc a b) volume:=by
    have he : (fun q=>g q+L q)-L=g:=by funext q;simp
    simpa only [he] using hTotal.sub hL
  refine ⟨hg,?_⟩
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hg) hLI] at hEq
  have hz:=hZdiff a b ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩
  linarith

theorem closed_integrable_source_ftc (F g : ℝ→ℝ) (a b : ℝ) (hab : a≤b)
    (hF : ContinuousOn F (Icc a b)) (hg : IntegrableOn g (Ioc a b) volume)
    (hlocal : ∀l∈Ioo a b,∀u∈Ioo a b,l≤u→
      F u-F l=∫q in l..u,g q) : F b-F a=∫q in a..b,g q := by
  exact (closed_dominated_source_ftc F g (fun q=>|g q|) a b hab hF
    (by simpa only [IntegrableOn,Real.norm_eq_abs] using hg.norm) (fun _ _=>le_rfl)
    (fun l hl u hu hlu=>⟨hg.mono_set (Ioc_subset_Ioc hl.1.le hu.2.le),hlocal l hl u hu hlu⟩)).2

end FourPapersCommon
