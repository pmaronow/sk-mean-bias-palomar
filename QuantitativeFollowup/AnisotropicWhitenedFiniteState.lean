module
public import QuantitativeFollowup.AnisotropicFiniteCell
public import QuantitativePaper.VectorAdditiveIto
public import QuantitativePaper.VectorAdditiveUniqueness

@[expose] public section

/-! Genuine finite-profile diagonal-whitened Picard diffusion, with the
actual finite Gaussian-tail feedback. No transition law is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000

def anisotropicWhitenedFiniteDrift (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (_p : Couplings n×ℝ) (y : Field n) : Field n :=
  Paper.parisiCDF (Paper.parisiSchemeMeasure s) r • anisotropicNoiseMap D
    (anisotropicFiniteTailMagnetization D s (projIcc (0 : ℝ) 1 zero_le_one r)
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y)))

def anisotropicWhitenedFiniteDriftBound (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖anisotropicNoiseMap D‖₊*(Real.sqrt (n : ℝ)).toNNReal

def anisotropicWhitenedFiniteDriftLip (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖anisotropicNoiseMap D‖₊*(‖anisotropicResponseMap n‖₊*‖anisotropicEnergyMap D‖₊^2)*
    (‖anisotropicFieldInjection n‖₊*‖anisotropicNoiseMap D‖₊)

theorem measurable_anisotropicWhitenedFiniteDrift (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) :
    Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n)=>
      anisotropicWhitenedFiniteDrift D s g z.1 z.2.1 z.2.2) := by
  have hm := (measurable_anisotropicFiniteTailMagnetization D s).comp
    (show Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n)=>
      (projIcc (0 : ℝ) 1 zero_le_one z.1,
        anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D z.2.2))) from by fun_prop)
  exact (((Paper.parisiCDF_monotone (Paper.parisiSchemeMeasure s)).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)).smul
    ((anisotropicNoiseMap D).continuous.measurable.comp hm))

theorem norm_anisotropicWhitenedFiniteDrift_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (p : Couplings n×ℝ) (y : Field n) :
    ‖anisotropicWhitenedFiniteDrift D s g r p y‖≤anisotropicWhitenedFiniteDriftBound D := by
  rw [anisotropicWhitenedFiniteDrift,norm_smul,Real.norm_of_nonneg (Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r)]
  simp only [anisotropicWhitenedFiniteDriftBound,NNReal.coe_mul,coe_nnnorm,
    Real.coe_toNNReal _ (Real.sqrt_nonneg (n : ℝ))]
  calc
    _≤Paper.parisiCDF (Paper.parisiSchemeMeasure s) r*(‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r)
      exact ((anisotropicNoiseMap D).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_anisotropicFiniteTailMagnetization_le D s _ _) (norm_nonneg _))
    _≤_ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one (Paper.parisiSchemeMeasure s) r)

theorem anisotropicWhitenedFiniteDrift_lipschitz (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (p : Couplings n×ℝ) :
    LipschitzWith (anisotropicWhitenedFiniteDriftLip D) (anisotropicWhitenedFiniteDrift D s g r p) := by
  have hp : LipschitzWith (‖anisotropicFieldInjection n‖₊*‖anisotropicNoiseMap D‖₊)
      (fun y : Field n=>anisotropicDisorderInjection n g+
        anisotropicFieldInjection n (anisotropicNoiseMap D y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left,Function.comp_apply] using
      ((anisotropicFieldInjection n).lipschitzWith.comp (anisotropicNoiseMap D).lipschitzWith).dist_le_mul x y
  have hm := (anisotropicFiniteTailMagnetization_lipschitz D s
    (projIcc (0 : ℝ) 1 zero_le_one r)).comp hp
  have hh := (anisotropicNoiseMap D).lipschitzWith.comp hm
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [anisotropicWhitenedFiniteDrift,anisotropicWhitenedFiniteDrift,dist_smul₀,
    Real.norm_of_nonneg (Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r)]
  calc
    _≤Paper.parisiCDF (Paper.parisiSchemeMeasure s) r*((anisotropicWhitenedFiniteDriftLip D : ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [anisotropicWhitenedFiniteDriftLip,Function.comp_apply,mul_assoc] using hh.dist_le_mul x y)
        (Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r)
    _≤_ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one (Paper.parisiSchemeMeasure s) r)

def anisotropicWhitenedFiniteDriftData (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) : VectorAdditiveDriftData n where
  drift := anisotropicWhitenedFiniteDrift D s g
  bound := anisotropicWhitenedFiniteDriftBound D
  spatialLip := anisotropicWhitenedFiniteDriftLip D
  measurable := measurable_anisotropicWhitenedFiniteDrift D s g
  norm_le := norm_anisotropicWhitenedFiniteDrift_le D s g
  lipschitz := anisotropicWhitenedFiniteDrift_lipschitz D s g

def anisotropicWhitenedFiniteState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) : ℝ≥0→VectorDisorderBrownianSample n→Field n :=
  vectorAdditiveState (anisotropicWhitenedFiniteDriftData D s g) 1 0 1

theorem vectorItoCharacteristics_anisotropicWhitenedFiniteState (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) :
    VectorItoCharacteristics (anisotropicWhitenedFiniteState D s g)
      (vectorAdditiveDrift (anisotropicWhitenedFiniteDriftData D s g) 1 0 1) 1 :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

theorem anisotropicWhitenedFinite_actual_cell_drift (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i≤k+1)
    (r : ℝ≥0) (hr : (r : ℝ)∈Ioo (s.q i) (s.q (i+1))) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveDrift (anisotropicWhitenedFiniteDriftData D s g) 1 0 1 r sample=
      s.m i • gradient (vectorColeHopfStep (s.q (i+1)-r) (s.m i)
        (anisotropicWhitenedFinitePotential D s (k+1-i) g))
        (anisotropicWhitenedFiniteState D s g r sample) := by
  have hr1 : (r : ℝ)≤1 := hr.2.le.trans (s.q_le_one (by omega))
  have hrnn : r≤1 := by exact_mod_cast hr1
  rw [vectorAdditiveDrift,if_pos hrnn]
  change anisotropicWhitenedFiniteDrift D s g r sample.1 (anisotropicWhitenedFiniteState D s g r sample)=_
  unfold anisotropicWhitenedFiniteDrift
  rw [Paper.parisiCDF_scheme_cell s hi ⟨hr.1.le,hr.2⟩]
  change s.m i • anisotropicNoiseMap D (anisotropicFiniteTailMagnetization D s _
    (anisotropicDisorderInjection n g+anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample)))=_
  rw [←gradient_anisotropicWhitenedFiniteTailPotential]
  rw [anisotropicWhitenedFiniteTailPotential_eq_cell D s _ i hi]
  · simp only [projIcc_of_mem _ ⟨r.coe_nonneg,hr1⟩]
  · simpa only [projIcc_of_mem _ ⟨r.coe_nonneg,hr1⟩] using ⟨hr.1.le,hr.2.le⟩

end QuantitativeFollowup
