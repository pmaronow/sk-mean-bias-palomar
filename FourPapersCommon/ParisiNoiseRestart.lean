module
public import FourPapersCommon.ParisiStateInitialShift
public import FourPapersCommon.ParisiNoiseContinuity

@[expose] public section

/-! The actual scalar Picard diffusion restarts from its sampled state,
with shifted cumulative mass and shifted PDE gradient. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

def parisiRestartNoiseStatePath (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (W : C(Paper.Overlap,ℝ)) : C(Paper.Overlap,ℝ) :=
  parisiStatePath β x (parisiRestartMeasure μ a ha) (parisiRestartGradient β μ a)
    (continuous_parisiRestartGradient β μ a) (norm_parisiRestartGradient_le_one β μ a)
    (lipschitzWith_parisiRestartGradient β μ a) 1 zero_le_one W

theorem measurable_parisiRestartNoiseStatePath (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (a : ℝ) (ha : 0≤a) :
    Measurable (fun z : ℝ×C(Paper.Overlap,ℝ)=>parisiRestartNoiseStatePath β z.1 μ a ha z.2) :=
  measurable_parisiStatePath_initial_noise β hβ _ _ _ _ _

theorem parisiStateReal_restart (β h : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (W V : ℝ→ℝ) (hW : Continuous W) (hV : Continuous V)
    (hVeq : ∀s∈Icc (0 : ℝ) (1-a),V s=W (a+s)-W a) :
    EqOn (fun s=>parisiStateReal β h μ (fun t x=>parisiGradient β μ (t,x))
      (continuous_parisiGradient β μ) (fun t x=>norm_parisiGradient_le_one β μ (t,x))
      (lipschitzWith_parisiGradient_all β μ) 1 zero_le_one W hW (a+s))
      (parisiStateReal β
        (parisiStateReal β h μ (fun t x=>parisiGradient β μ (t,x))
          (continuous_parisiGradient β μ) (fun t x=>norm_parisiGradient_le_one β μ (t,x))
          (lipschitzWith_parisiGradient_all β μ) 1 zero_le_one W hW a)
        (parisiRestartMeasure μ a ha.1) (parisiRestartGradient β μ a)
        (continuous_parisiRestartGradient β μ a) (norm_parisiRestartGradient_le_one β μ a)
        (lipschitzWith_parisiRestartGradient β μ a) 1 zero_le_one V hV)
      (Icc (0 : ℝ) (1-a)) := by
  let X:=parisiStateReal β h μ (fun t x=>parisiGradient β μ (t,x))
    (continuous_parisiGradient β μ) (fun t x=>norm_parisiGradient_le_one β μ (t,x))
    (lipschitzWith_parisiGradient_all β μ) 1 zero_le_one W hW
  have hX : Continuous X := continuous_parisiStateReal β h μ _ _ _ _ _ _ _ _
  let f:=fun t=>β^2*parisiCDF μ t*parisiGradient β μ (t,X t)
  have hfi (u v : ℝ) : IntervalIntegrable f volume u v :=
    ((parisiCDF_intervalIntegrable μ u v).const_mul (β^2)).mul_continuousOn
      ((continuous_parisiGradient β μ).comp (continuous_id.prodMk hX)).continuousOn
  let R:=parisiStateReal β (X a) (parisiRestartMeasure μ a ha.1)
    (parisiRestartGradient β μ a) (continuous_parisiRestartGradient β μ a)
    (norm_parisiRestartGradient_le_one β μ a) (lipschitzWith_parisiRestartGradient β μ a)
    1 zero_le_one V hV
  have hR : Continuous R := continuous_parisiStateReal β (X a) _ _ _ _ _ _ _ _ _
  have hshift (s : ℝ) (hs : s∈Icc (0 : ℝ) (1-a)) :
      X (a+s)=X a+β*V s+∫r in 0..s,β^2*parisiCDF (parisiRestartMeasure μ a ha.1) r*
        parisiRestartGradient β μ a r (X (a+r)) := by
    have hsa : a+s∈Icc (0 : ℝ) 1 :=
      ⟨add_nonneg ha.1 hs.1,by linarith [hs.2]⟩
    have he:=parisiStateReal_integral_equation β h μ
      (fun t x=>parisiGradient β μ (t,x)) (continuous_parisiGradient β μ)
      (fun t x=>norm_parisiGradient_le_one β μ (t,x))
      (lipschitzWith_parisiGradient_all β μ) 1 zero_le_one W hW hsa
    have hea:=parisiStateReal_integral_equation β h μ
      (fun t x=>parisiGradient β μ (t,x)) (continuous_parisiGradient β μ)
      (fun t x=>norm_parisiGradient_le_one β μ (t,x))
      (lipschitzWith_parisiGradient_all β μ) 1 zero_le_one W hW ha
    change X (a+s)=h+β*W (a+s)+∫r in 0..(a+s),f r at he
    change X a=h+β*W a+∫r in 0..a,f r at hea
    have hi : (∫r in 0..s,β^2*parisiCDF (parisiRestartMeasure μ a ha.1) r*
        parisiRestartGradient β μ a r (X (a+r)))=∫r in a..(a+s),f r := by
      calc
        _ = ∫r in 0..s,f (a+r) := by
          apply intervalIntegral.integral_congr
          intro r hr
          rw [uIcc_of_le hs.1] at hr
          dsimp only [f,parisiRestartGradient]
          rw [parisiCDF_restart μ a ha.1 r hr.1]
        _ = _ := by simpa only [add_zero] using
          intervalIntegral.integral_comp_add_left (a:=(0 : ℝ)) (b:=s) f a
    have hadj:=intervalIntegral.integral_add_adjacent_intervals (hfi 0 a) (hfi a (a+s))
    rw [hi,hVeq s hs]
    linarith
  have hu:=parisiStateReal_unique β (X a) (parisiRestartMeasure μ a ha.1)
    (parisiRestartGradient β μ a) (continuous_parisiRestartGradient β μ a)
    (norm_parisiRestartGradient_le_one β μ a) (lipschitzWith_parisiRestartGradient β μ a)
    (1-a) (by linarith [ha.2]) V hV (fun s=>X (a+s))
    (hX.comp (continuous_const.add continuous_id)) hshift
  have hv:=parisiStateReal_unique β (X a) (parisiRestartMeasure μ a ha.1)
    (parisiRestartGradient β μ a) (continuous_parisiRestartGradient β μ a)
    (norm_parisiRestartGradient_le_one β μ a) (lipschitzWith_parisiRestartGradient β μ a)
    (1-a) (by linarith [ha.2]) V hV R hR (by
      intro s hs
      exact parisiStateReal_integral_equation β (X a) _ _ _ _ _ 1 zero_le_one V hV
        ⟨hs.1,by linarith [hs.2,ha.1]⟩)
  intro s hs
  exact (hu hs).trans (hv hs).symm

def parisiElapsedOverlap (a b : Paper.Overlap) (hab : (a : ℝ)≤b) : Paper.Overlap :=
  ⟨(b : ℝ)-a,sub_nonneg.mpr hab,by linarith [b.property.2,a.property.1]⟩

theorem parisiNoiseStatePath_restart (β h : ℝ) (μ : ParisiMeasure)
    (a b : Paper.Overlap) (hab : (a : ℝ)≤b) (W V : C(Paper.Overlap,ℝ))
    (hVeq : ∀s : Paper.Overlap,∀hs : (s : ℝ)≤1-a,
      V s=W ⟨(a : ℝ)+s,add_nonneg a.property.1 s.property.1,by linarith [hs]⟩-W a) :
    parisiNoiseStatePath β h μ W b=
      parisiRestartNoiseStatePath β (parisiNoiseStatePath β h μ W a) μ a a.property.1 V
        (parisiElapsedOverlap a b hab) := by
  let N:=parisiNoiseExtension zero_le_one W
  let Z:=parisiNoiseExtension zero_le_one V
  have hN : Continuous N := continuous_parisiNoiseExtension zero_le_one W
  have hZ : Continuous Z := continuous_parisiNoiseExtension zero_le_one V
  have he:=parisiStateReal_restart β h μ a a.property N Z hN hZ (by
    intro s hs
    have hs1 : s∈Icc (0 : ℝ) 1 := ⟨hs.1,by linarith [hs.2,a.property.1]⟩
    have has : (a : ℝ)+s∈Icc (0 : ℝ) 1 :=
      ⟨add_nonneg a.property.1 hs.1,by linarith [hs.2]⟩
    simpa only [N,Z,parisiNoiseExtension,projIcc_of_mem zero_le_one hs1,
      projIcc_of_mem zero_le_one has,projIcc_of_mem zero_le_one a.property] using
      hVeq ⟨s,hs1⟩ hs.2)
  have hd : (b : ℝ)-a∈Icc (0 : ℝ) (1-a) :=
    ⟨sub_nonneg.mpr hab,by linarith [b.property.2]⟩
  have hh:=he hd
  dsimp only at hh
  rw [show (a : ℝ)+((b : ℝ)-a)=(b : ℝ) by ring] at hh
  dsimp only [parisiNoiseStatePath,parisiRestartNoiseStatePath]
  erw [parisiStatePath_apply,parisiStatePath_apply,parisiStatePath_apply]
  exact hh

end FourPapersCommon
