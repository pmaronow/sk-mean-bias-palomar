module
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A nonnegative locally integrable source is genuinely integrable up
to closed endpoints when its cropped primitives have finite continuous
endpoint limits. No endpoint bound on the source is assumed. The proof
uses actual a.e. interval covers and nonnegative integral convergence. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1800000

def sourceCropRadius (a b : ℝ) (n : ℕ) : ℝ := (b-a)/((n : ℝ)+3)
def sourceLeftCrop (a b : ℝ) (n : ℕ) : ℝ := a+sourceCropRadius a b n
def sourceRightCrop (a b : ℝ) (n : ℕ) : ℝ := b-sourceCropRadius a b n

theorem sourceCrop_bounds {a b : ℝ} (hab : a<b) (n : ℕ) :
    a<sourceLeftCrop a b n ∧ sourceLeftCrop a b n<sourceRightCrop a b n ∧
      sourceRightCrop a b n<b := by
  have hn : 0<(n : ℝ)+3 := by positivity
  have hn3 : 3≤(n : ℝ)+3 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hd : 0<sourceCropRadius a b n := div_pos (sub_pos.mpr hab) hn
  have htwice : 2*sourceCropRadius a b n<b-a := by
    unfold sourceCropRadius
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hn3 (sub_nonneg.mpr hab.le)]
  dsimp only [sourceLeftCrop,sourceRightCrop]
  constructor
  · linarith
  constructor <;> linarith

theorem tendsto_sourceLeftCrop (a b : ℝ) :
    Tendsto (sourceLeftCrop a b) atTop (𝓝 a) := by
  have hd : Tendsto (sourceCropRadius a b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  change Tendsto (fun n => a+sourceCropRadius a b n) atTop (𝓝 a)
  simpa only [add_zero] using tendsto_const_nhds.add hd

theorem tendsto_sourceRightCrop (a b : ℝ) :
    Tendsto (sourceRightCrop a b) atTop (𝓝 b) := by
  have hd : Tendsto (sourceCropRadius a b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  change Tendsto (fun n => b-sourceCropRadius a b n) atTop (𝓝 b)
  simpa only [sub_zero] using tendsto_const_nhds.sub hd

theorem closed_nonnegative_source_ftc_of_lt (F g : ℝ → ℝ) (a b : ℝ)
    (hab : a<b) (hF : ContinuousOn F (Icc a b))
    (hg : ∀x∈Ioo a b, 0≤g x)
    (hlocal : ∀l∈Ioo a b, ∀u∈Ioo a b, l≤u →
      IntegrableOn g (Ioc l u) volume ∧ F u-F l=∫x in l..u,g x) :
    IntegrableOn g (Ioc a b) volume ∧ F b-F a=∫x in a..b,g x := by
  let l := sourceLeftCrop a b
  let u := sourceRightCrop a b
  have hbds (n : ℕ) := sourceCrop_bounds hab n
  have hlmem (n : ℕ) : l n∈Ioo a b :=
    ⟨(hbds n).1,(hbds n).2.1.trans (hbds n).2.2⟩
  have humem (n : ℕ) : u n∈Ioo a b :=
    ⟨(hbds n).1.trans (hbds n).2.1,(hbds n).2.2⟩
  have hsub (n : ℕ) : Ioc (l n) (u n)⊆Ioc a b :=
    fun x hx => ⟨(hlmem n).1.trans hx.1,hx.2.trans (humem n).2.le⟩
  have hfi (n : ℕ) : IntegrableOn g (Ioc (l n) (u n)) volume :=
    (hlocal (l n) (hlmem n) (u n) (humem n) (hbds n).2.1.le).1
  have heq (n : ℕ) : F (u n)-F (l n)=∫x in l n..u n,g x :=
    (hlocal (l n) (hlmem n) (u n) (humem n) (hbds n).2.1.le).2
  have hl := tendsto_sourceLeftCrop a b
  have hu := tendsto_sourceRightCrop a b
  have hFl : Tendsto (fun n => F (l n)) atTop (𝓝 (F a)) := by
    exact (hF a ⟨le_rfl,hab.le⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hl,.of_forall fun n => ⟨(hlmem n).1.le,(hlmem n).2.le⟩⟩)
  have hFu : Tendsto (fun n => F (u n)) atTop (𝓝 (F b)) := by
    exact (hF b ⟨hab.le,le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hu,.of_forall fun n => ⟨(humem n).1.le,(humem n).2.le⟩⟩)
  have hcover : AECover (volume.restrict (Ioc a b)) atTop (fun n => Ioc (l n) (u n)) :=
    aecover_Ioc_of_Ioc hl hu
  have hfi' (n : ℕ) : IntegrableOn g (Ioc (l n) (u n)) (volume.restrict (Ioc a b)) := by
    rw [IntegrableOn,Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (hsub n)]
    exact hfi n
  have hnonneg : 0≤ᵐ[volume.restrict (Ioc a b)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne b)] with x hx hxb
    exact hg x ⟨hx.1,lt_of_le_of_ne hx.2 hxb⟩
  have hlim : Tendsto (fun n => ∫x in Ioc (l n) (u n),g x ∂volume.restrict (Ioc a b))
      atTop (𝓝 (F b-F a)) := by
    apply (hFu.sub hFl).congr
    intro n
    rw [heq n,intervalIntegral.integral_of_le (hbds n).2.1.le,
      Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (hsub n)]
  have hi := hcover.integrable_of_integral_tendsto_of_nonneg_ae (F b-F a) hfi' hnonneg hlim
  refine ⟨hi,?_⟩
  rw [intervalIntegral.integral_of_le hab.le]
  exact (hcover.integral_eq_of_tendsto (F b-F a) hi hlim).symm

theorem closed_nonnegative_source_ftc (F g : ℝ → ℝ) (a b : ℝ)
    (hab : a≤b) (hF : ContinuousOn F (Icc a b))
    (hg : ∀x∈Ioo a b, 0≤g x)
    (hlocal : ∀l∈Ioo a b, ∀u∈Ioo a b, l≤u →
      IntegrableOn g (Ioc l u) volume ∧ F u-F l=∫x in l..u,g x) :
    IntegrableOn g (Ioc a b) volume ∧ F b-F a=∫x in a..b,g x := by
  rcases hab.eq_or_lt with h | h
  · subst b
    simp
  · exact closed_nonnegative_source_ftc_of_lt F g a b h hF hg hlocal

end FourPapersCommon
