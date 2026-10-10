module
public import QuantitativeFollowup.AnisotropicWhitenedFiniteState

@[expose] public section

/-! Joint measurability in the true anisotropic disorder and independent
 Wiener sample, obtained from the actual measurable Picard iterates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000

 theorem measurable_anisotropicWhitenedFiniteDrift_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : Measurable (fun z : ℝ≥0×((AnisotropicDisorder n×(Couplings n×ℝ))×Field n)=>
      anisotropicWhitenedFiniteDrift D s z.2.1.1 z.1 z.2.1.2 z.2.2) := by
  have hm := (measurable_anisotropicFiniteTailMagnetization D s).comp
    (show Measurable (fun z : ℝ≥0×((AnisotropicDisorder n×(Couplings n×ℝ))×Field n)=>
      (projIcc (0 : ℝ) 1 zero_le_one z.1,
        anisotropicDisorderInjection n z.2.1.1+anisotropicFieldInjection n (anisotropicNoiseMap D z.2.2))) from by fun_prop)
  exact (((Paper.parisiCDF_monotone (Paper.parisiSchemeMeasure s)).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)).smul
    ((anisotropicNoiseMap D).continuous.measurable.comp hm))

theorem measurable_uncurry_anisotropicWhitenedFiniteState_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : Measurable (fun z : ℝ≥0×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
      anisotropicWhitenedFiniteState D s z.2.1 z.1 z.2.2) := by
  let f:=fun u : AnisotropicDisorder n×VectorDisorderBrownianSample n=>
    vectorNoiseCorrectionDrift (anisotropicWhitenedFiniteDriftData D s u.1) (vectorAdditiveNoiseReal 1) u.2
  have hf (u : AnisotropicDisorder n×VectorDisorderBrownianSample n) :
      IsBoundedVectorDrift (f u) (anisotropicWhitenedFiniteDriftBound D) (anisotropicWhitenedFiniteDriftLip D) :=
    isBounded_vectorNoiseCorrectionDrift (anisotropicWhitenedFiniteDriftData D s u.1)
      (vectorAdditiveNoiseReal 1) (continuous_vectorAdditiveNoiseReal 1) u.2
  have hm : Measurable (fun z : (ℝ×Field n)×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
      f z.2 z.1.1 z.1.2) := by
    have hw : Measurable (fun z : (ℝ×Field n)×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
        vectorAdditiveNoiseReal 1 z.1.1 z.2.2) :=
      (measurable_uncurry_vectorAdditiveNoiseReal 1).comp
        (show Measurable (fun z : (ℝ×Field n)×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
          (z.1.1,z.2.2)) from by fun_prop)
    exact (measurable_anisotropicWhitenedFiniteDrift_parameter D s).comp
      (show Measurable (fun z : (ℝ×Field n)×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
        (z.1.1.toNNReal,((z.2.1,z.2.2.1),z.1.2+vectorAdditiveNoiseReal 1 z.1.1 z.2.2))) from by
          exact (continuous_real_toNNReal.measurable.comp measurable_fst.fst).prodMk
            ((measurable_snd.fst.prodMk measurable_snd.snd.fst).prodMk (measurable_fst.snd.add hw)))
  have hc:=VectorIntegralPicard.measurable_uncurry_solution_compProj
    (T:=1) zero_le_one (0 : Field n) f hf hm
  have hc':=hc.comp
    (show Measurable (fun z : ℝ≥0×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
      ((z.1 : ℝ),z.2)) from by fun_prop)
  have hn : Measurable (fun z : ℝ≥0×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
      (1 : ℝ) • disorderVectorBrownian z.1 z.2.2) :=
    by
      simpa only [one_smul,Function.comp_def,Function.uncurry_def] using
        ((measurable_uncurry_disorderVectorBrownian n).comp
      (show Measurable (fun z : ℝ≥0×(AnisotropicDisorder n×VectorDisorderBrownianSample n)=>
        (z.1,z.2.2)) from by fun_prop))
  exact hc'.add hn

theorem measurable_anisotropicWhitenedFiniteState_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (r : ℝ≥0) :
    Measurable (fun z : AnisotropicDisorder n×VectorDisorderBrownianSample n=>
      anisotropicWhitenedFiniteState D s z.1 r z.2) := by
  simpa only [Function.comp_def] using
    (measurable_uncurry_anisotropicWhitenedFiniteState_parameter D s).comp
      (show Measurable (fun z : AnisotropicDisorder n×VectorDisorderBrownianSample n=>(r,z)) from
        measurable_const.prodMk measurable_id)

end QuantitativeFollowup
