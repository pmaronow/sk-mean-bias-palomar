module
public import FourPapersCommon.DyadicQuantileShells
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! Integrating an actual bounded quantile function through its disjoint
dyadic shells and a genuine geometric sum. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1600000

theorem bounded_dyadic_quantile_integral (ψ : ℝ→ℝ) (hψ : Measurable ψ)
    (hb : ∀v,0≤ψ v ∧ ψ v≤1) (s u : ℝ) (hs : s∈Ioo (0:ℝ) 1)
    (hu : u∈Icc s 1) (C ρ : ℝ) (hρ : ρ∈Ico (0:ℝ) 1)
    (hShell : ∀j : ℕ,(∫v in dyadicQuantileShell s u j,ψ v)≤C*ρ^j) :
    (∫v in Ioo (0:ℝ) (1-s),ψ v)≤(u-s)+C/(1-ρ) := by
  let I:=Ioo (0:ℝ) (1-s)
  let L:=Ioo (0:ℝ) (u-s)
  let H:=I∩Ici (u-s)
  have hu0 : 0<u:=hs.1.trans_le hu.1
  have hLI : L⊆I:=fun v hv=>⟨hv.1,hv.2.trans_le (sub_le_sub_right hu.2 s)⟩
  have hHI : H⊆I:=inter_subset_left
  have hsplit : I=L∪H:=by
    ext v
    simp only [I,L,H,mem_union,mem_inter_iff,mem_Ioo,mem_Ici]
    constructor
    · intro hv
      by_cases h:v<u-s
      · exact Or.inl ⟨hv.1,h⟩
      · exact Or.inr ⟨hv,le_of_not_gt h⟩
    · rintro (hv|⟨hv,_⟩)
      · exact ⟨hv.1,hv.2.trans_le (sub_le_sub_right hu.2 s)⟩
      · exact hv
  have hdisj : Disjoint L H:=by
    apply Set.disjoint_left.mpr
    intro v hvL hvH
    exact (not_lt_of_ge hvH.2) hvL.2
  have hi : IntegrableOn ψ I:=by
    let : IsFiniteMeasure (volume.restrict I):=isFiniteMeasure_restrict.mpr (by
      rw [Real.volume_Ioo];exact ENNReal.ofReal_ne_top)
    exact Integrable.of_bound hψ.aestronglyMeasurable 1
      (.of_forall fun v=>by rw [Real.norm_of_nonneg (hb v).1];exact (hb v).2)
  have hlow : (∫v in L,ψ v)≤u-s:=by
    have hh:=integral_mono_ae (hi.mono_set hLI) (integrableOn_const (by
      rw [Real.volume_Ioo];exact ENNReal.ofReal_ne_top))
      (.of_forall fun v=>(hb v).2)
    simpa only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ,
      Real.volume_Ioo,sub_zero,ENNReal.toReal_ofReal (sub_nonneg.mpr hu.1),L] using hh
  have hcover : (⋃j : ℕ,dyadicQuantileShell s u j)=H:=dyadicQuantileShells_cover s u hu0
  have hsum:=hasSum_integral_iUnion
    (fun j=>(dyadicQuantileShell_ordConnected s u j).measurableSet)
    (dyadicQuantileShells_pairwiseDisjoint s u hu0)
    (hcover.symm ▸ hi.mono_set hHI)
  have hgeom : Summable (fun j : ℕ=>C*ρ^j):=
    (summable_geometric_of_abs_lt_one (by rw [abs_of_nonneg hρ.1];exact hρ.2)).mul_left C
  have hhigh : (∫v in H,ψ v)≤C/(1-ρ):=by
    rw [←hcover,←hsum.tsum_eq]
    apply (hsum.summable.tsum_le_tsum hShell hgeom).trans_eq
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg hρ.1];exact hρ.2)]
    exact (div_eq_mul_inv C (1-ρ)).symm
  change (∫v in I,ψ v)≤_
  rw [hsplit,setIntegral_union hdisj (measurableSet_Ioo.inter measurableSet_Ici)
    (hi.mono_set hLI) (hi.mono_set hHI)]
  exact add_le_add hlow hhigh

end FourPapersCommon
