module
public import HexagonPaper.VariableScalarClockJoint
public import Paper.ParisiState

@[expose] public section

/-! The clock diffusion is the genuine pathwise Picard state applied to
the original continuous noise. It is a measurable function of that noise,
and agrees with the native constant-clock diffusion on canonical samples. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem continuous_scalarClockPathReindex (τ : Paper.Overlap≃oPaper.Overlap) :
    Continuous (scalarClockPathReindex τ) :=
  (ContinuousMap.compCLM ℝ ℝ ⟨τ,τ.continuous⟩).continuous

def scalarClockUnclockNoise (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (Z : C(Paper.Overlap,ℝ)) : C(Paper.Overlap,ℝ) :=
  β⁻¹ • scalarClockPathReindex τ.symm Z

def scalarClockStateFromNoise (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (Z : C(Paper.Overlap,ℝ)) : C(Paper.Overlap,ℝ) :=
  scalarClockPathReindex τ
    (Paper.parisiStatePath β 0 (scalarClockMeasure τ μ)
      (fun s x=>Paper.parisiGradient β (scalarClockMeasure τ μ) (s,x))
      (Paper.continuous_parisiGradient β (scalarClockMeasure τ μ))
      (fun s x=>Paper.norm_parisiGradient_le_one β (scalarClockMeasure τ μ) (s,x))
      (Paper.lipschitzWith_parisiGradient_all β (scalarClockMeasure τ μ))
      1 zero_le_one (scalarClockUnclockNoise τ β Z))

theorem continuous_scalarClockStateFromNoise (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) :
    Continuous (scalarClockStateFromNoise τ β μ) :=
  (continuous_scalarClockPathReindex τ).comp
    ((Paper.continuous_parisiStatePath β 0 (scalarClockMeasure τ μ) _ _ _ _
      1 zero_le_one).comp
      ((continuous_scalarClockPathReindex τ.symm).const_smul β⁻¹))

theorem scalarClockUnclockNoise_reference (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (sample : Paper.BrownianSample) :
    scalarClockUnclockNoise τ β (scalarClockStoppedReferencePath τ β 1 sample)=
      Paper.canonicalBrownianPath sample := by
  ext q
  change β⁻¹*(β*Paper.canonicalBrownian
    (stoppedOverlapTime (τ (1:Paper.Overlap):ℝ).toNNReal (τ (τ.symm q))) sample)=_
  rw [τ.apply_symm_apply,scalarClock_one]
  simp only [show (((1:Paper.Overlap):ℝ).toNNReal)=1 by norm_num]
  have ht:stoppedOverlapTime 1 q=(q:ℝ).toNNReal:=by
    apply NNReal.eq
    simp only [stoppedOverlapTime,NNReal.coe_mk,NNReal.coe_one,
      min_eq_left q.property.2,Real.coe_toNNReal _ q.property.1]
    rfl
  rw [ht]
  change β⁻¹*(β*Paper.canonicalBrownian (q:ℝ).toNNReal sample)=
    Paper.canonicalBrownian (q:ℝ).toNNReal sample
  rw [←mul_assoc,inv_mul_cancel₀ hβ,one_mul]

theorem scalarClockStateFromNoise_reference (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (sample : Paper.BrownianSample) :
    scalarClockStateFromNoise τ β μ (scalarClockStoppedReferencePath τ β 1 sample)=
      scalarClockStoppedStatePath τ β μ 1 sample := by
  unfold scalarClockStateFromNoise
  rw [scalarClockUnclockNoise_reference τ β hβ]
  ext q
  change Paper.parisiStatePath β 0 (scalarClockMeasure τ μ) _ _ _ _
      1 zero_le_one (Paper.canonicalBrownianPath sample) (τ q)=
    optimalStateReal β (scalarClockMeasure τ μ) sample
      (min (τ q:ℝ) (τ (1:Paper.Overlap):ℝ).toNNReal)
  rw [scalarClock_one,show (((1:Paper.Overlap):ℝ).toNNReal)=1 by norm_num]
  simp only [NNReal.coe_one,min_eq_left (τ q).property.2,Paper.parisiStatePath_apply]
  rfl

theorem scalarClockStateFromNoise_integral_equation
    (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (Z : C(Paper.Overlap,ℝ)) (q : Paper.Overlap) :
    scalarClockStateFromNoise τ β μ Z q=Z q+
      ∫s in (0:ℝ)..(τ q:ℝ),β^2*parisiCDF (scalarClockMeasure τ μ) s*
        parisiGradient β (scalarClockMeasure τ μ)
          (s,scalarClockStateFromNoise τ β μ Z (τ.symm (projIcc 0 1 zero_le_one s))) := by
  let ν:=scalarClockMeasure τ μ
  let W:=scalarClockUnclockNoise τ β Z
  let X:=Paper.parisiStateReal β 0 ν (fun s x=>Paper.parisiGradient β ν (s,x))
    (Paper.continuous_parisiGradient β ν)
    (fun s x=>Paper.norm_parisiGradient_le_one β ν (s,x))
    (Paper.lipschitzWith_parisiGradient_all β ν) 1 zero_le_one
    (Paper.parisiNoiseExtension zero_le_one W)
    (Paper.continuous_parisiNoiseExtension zero_le_one W)
  have he:=Paper.parisiStateReal_integral_equation β 0 ν
    (fun s x=>Paper.parisiGradient β ν (s,x))
    (Paper.continuous_parisiGradient β ν)
    (fun s x=>Paper.norm_parisiGradient_le_one β ν (s,x))
    (Paper.lipschitzWith_parisiGradient_all β ν) 1 zero_le_one
    (Paper.parisiNoiseExtension zero_le_one W)
    (Paper.continuous_parisiNoiseExtension zero_le_one W) (τ q).property
  change X (τ q)=0+β*Paper.parisiNoiseExtension zero_le_one W (τ q)+_ at he
  have hx:scalarClockStateFromNoise τ β μ Z q=X (τ q):=
    Paper.parisiStatePath_apply β 0 ν _ _ _ _ 1 zero_le_one W (τ q)
  have hn:β*Paper.parisiNoiseExtension zero_le_one W (τ q)=Z q:=by
    unfold Paper.parisiNoiseExtension
    rw [projIcc_of_mem zero_le_one (τ q).property]
    change β*(β⁻¹*Z (τ.symm (τ q)))=Z q
    rw [τ.symm_apply_apply,←mul_assoc,mul_inv_cancel₀ hβ,one_mul]
  rw [hx,he,zero_add,hn]
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le (τ q).property.1]
  intro s hs
  have hsi:s∈Icc (0:ℝ) 1:=⟨hs.1.le,hs.2.le.trans (τ q).property.2⟩
  have hxs:scalarClockStateFromNoise τ β μ Z (τ.symm (projIcc 0 1 zero_le_one s))=X s:=by
    change Paper.parisiStatePath β 0 ν _ _ _ _ 1 zero_le_one W
      (τ (τ.symm (projIcc 0 1 zero_le_one s)))=X s
    rw [τ.apply_symm_apply,Paper.parisiStatePath_apply,projIcc_of_mem zero_le_one hsi]
  change β^2*parisiCDF ν s*parisiGradient β ν (s,X s)=
    β^2*parisiCDF ν s*parisiGradient β ν
      (s,scalarClockStateFromNoise τ β μ Z (τ.symm (projIcc 0 1 zero_le_one s)))
  exact congrArg (fun y=>β^2*parisiCDF ν s*parisiGradient β ν (s,y)) hxs.symm

end HexagonPaper
