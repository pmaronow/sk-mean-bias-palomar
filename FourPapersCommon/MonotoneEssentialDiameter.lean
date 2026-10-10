module
public import FourPapersCommon.MonotoneBinIntervals
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! The literal essential pair diameter of a monotone function on an
interval bounds its values on the entire interval interior. This recovers
a genuine range from an essential diameter, even at jumps and atoms. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1800000

def intervalEssentialDiameter (f : ℝ→ℝ) (I : Set ℝ) : ℝ :=
  essSup (fun p : ℝ×ℝ=>|f p.1-f p.2|) ((volume.restrict I).prod (volume.restrict I))

theorem monotone_essential_diameter_range (f : ℝ→ℝ) (hf : Monotone f)
    (hfRange : ∀v,f v∈Icc (0:ℝ) 1) (I : Set ℝ) (hI : I.OrdConnected)
    (hb : BddBelow I) (ha : BddAbove I) (hvol : 0<volume.real I) :
    0 ≤ intervalEssentialDiameter f I ∧
      ∃a,∀v∈Ioo (sInf I) (sSup I),f v∈Icc a (a+intervalEssentialDiameter f I) := by
  let P:=volume.restrict I
  have hEq:=ordConnected_ae_eq_open_interval I hI hb ha
  have hfinite : volume I≠∞:=by
    rw [measure_congr hEq,Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  let : IsFiniteMeasure P:=isFiniteMeasure_restrict.mpr hfinite
  have hIpos : volume I≠0:=by intro h;simp only [Measure.real,h,ENNReal.toReal_zero] at hvol;exact (lt_irrefl _ hvol)
  have hPpos : P.prod P≠0:=by
    intro h
    have he:=congrArg (fun μ : Measure (ℝ×ℝ)=>μ univ) h
    rw [←univ_prod_univ,Measure.prod_prod] at he
    dsimp only [P] at he
    simp only [Measure.restrict_apply_univ] at he
    change volume I*volume I=0 at he
    exact mul_ne_zero hIpos hIpos he
  let : NeZero (P.prod P):=⟨hPpos⟩
  have hbF : IsBoundedUnder (· ≤ ·) (ae (P.prod P)) (fun p : ℝ×ℝ=>|f p.1-f p.2|) :=
    isBoundedUnder_of ⟨1,fun p=>by rw [abs_le];constructor <;> linarith [(hfRange p.1).1,(hfRange p.1).2,(hfRange p.2).1,(hfRange p.2).2]⟩
  have hNonneg : 0 ≤ intervalEssentialDiameter f I :=by
    have he:=essSup_mono_ae (μ:=P.prod P)
      (show (fun _ : ℝ×ℝ=>(0:ℝ)) ≤ᵐ[P.prod P](fun p=>|f p.1-f p.2|) from .of_forall fun p=>abs_nonneg _)
      (isCoboundedUnder_le_of_le (ae (P.prod P)) (fun _=>le_rfl)) hbF
    simpa only [essSup_const',intervalEssentialDiameter,P] using he
  have hAE : ∀ᵐx ∂P,∀ᵐy ∂P,|f x-f y| ≤ intervalEssentialDiameter f I :=
    ae_ae_of_ae_prod (ae_le_essSup hbF)
  have hgap : sInf I<sSup I:=by
    rw [volume_ordConnected_eq_endpoints I hI hb ha] at hvol
    by_contra h
    rw [max_eq_right (sub_nonpos.mpr (not_lt.mp h))] at hvol
    exact (lt_irrefl _ hvol)
  have hne : I.Nonempty:=by
    by_contra h
    have he : I=∅:=not_nonempty_iff_eq_empty.mp h
    simp only [he,Measure.real,measure_empty,ENNReal.toReal_zero] at hvol
    exact (lt_irrefl _ hvol)
  have hin : Ioo (sInf I) (sSup I)⊆I :=
    (show IsConnected I from ⟨hne,hI.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
  have hpair (v w : ℝ) (hv : v∈Ioo (sInf I) (sSup I)) (hw : w∈Ioo (sInf I) (sSup I)) :
      f w-f v ≤ intervalEssentialDiameter f I :=by
    have hleft : Ioo (sInf I) v⊆I:=fun x hx=>hin ⟨hx.1,hx.2.trans hv.2⟩
    have hright : Ioo w (sSup I)⊆I:=fun y hy=>hin ⟨hw.1.trans hy.1,hy.2⟩
    have hleftPos : volume (Ioo (sInf I) v)≠0:=by
      rw [Real.volume_Ioo]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hv.1))
    have hrightPos : volume (Ioo w (sSup I))≠0:=by
      rw [Real.volume_Ioo]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hw.2))
    obtain ⟨x,hx,hxe⟩:=exists_mem_of_measure_ne_zero_of_ae hleftPos
      (hAE.filter_mono (ae_mono (Measure.restrict_mono_set volume hleft)))
    obtain ⟨y,hy,hye⟩:=exists_mem_of_measure_ne_zero_of_ae hrightPos
      (hxe.filter_mono (ae_mono (Measure.restrict_mono_set volume hright)))
    have hfx:=hf hx.2.le
    have hfy:=hf hy.1.le
    have habs:=neg_le_abs (f x-f y)
    linarith
  let J:=Ioo (sInf I) (sSup I)
  have hJne : J.Nonempty:=nonempty_Ioo.mpr hgap
  have hImageNe : (f '' J).Nonempty:=hJne.image f
  have hImageB : BddBelow (f '' J):=⟨0,by rintro _ ⟨v,hv,rfl⟩;exact (hfRange v).1⟩
  refine ⟨hNonneg,sInf (f '' J),?_⟩
  intro v hv
  have hl:=csInf_le hImageB (show f v∈f '' J from ⟨v,hv,rfl⟩)
  have hu : f v-intervalEssentialDiameter f I ≤ sInf (f '' J):=by
    apply le_csInf hImageNe
    rintro _ ⟨w,hw,rfl⟩
    have he:=hpair w v hw hv
    linarith
  exact ⟨hl,by linarith⟩

end FourPapersCommon
