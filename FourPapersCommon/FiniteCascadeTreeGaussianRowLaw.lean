module
public import FourPapersCommon.FiniteCascadeTreeFeatureHeatGrowth
public import FourPapersCommon.ScalarHeatVarianceZero
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! A genuine additional Gaussian terminal-feature coordinate in the
recorded tree law. Its normalized density and Gaussian/record Fubini
identity are proved from the actual cascade numerator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FRSB
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeGaussianRowReference
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :=
  (gaussianReal 0 v.toNNReal).prod (finiteCascadeTreeGaussianReferenceLaw L T R H)

def finiteCascadeTreeGaussianRowLogNumerator (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : ℝ×(FiniteStateField S×Records (FiniteStateField S) S T)) : ℝ :=
  finiteCascadeTreeFeatureLogNumerator V a L s T z.2.1 K z.2.2 z.1

def finiteCascadeTreeGaussianRowNormalizer (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) : ℝ :=
  gaussianHeatFlow (finiteCascadeTreeFeatureNumerator V K a L s T R H (fun _=>1)) v 0

def finiteCascadeTreeGaussianRowLaw (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :=
  (finiteCascadeTreeGaussianRowReference L v T R H).tilted
    (finiteCascadeTreeGaussianRowLogNumerator V K a L s T)

instance finiteCascadeTreeGaussianReferenceLaw_finite
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    IsFiniteMeasure (finiteCascadeTreeGaussianReferenceLaw L T R H) := by
  haveI := isFiniteKernel_finiteCascadeTreeReferenceKernel L T
  unfold finiteCascadeTreeGaussianReferenceLaw
  infer_instance

theorem measurable_finiteCascadeTreeGaussianRowLogNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeTreeGaussianRowLogNumerator V K a L s T) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u:=fun θ (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
      finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
  · intro z
    exact continuous_iff_continuousAt.mpr fun θ=>
      (hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T z.1 K z.2 θ).continuousAt
  · intro θ
    exact measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T

theorem integrable_exp_finiteCascadeTreeGaussianRowLogNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    Integrable (fun z=>Real.exp (finiteCascadeTreeGaussianRowLogNumerator V K a L s T z))
      (finiteCascadeTreeGaussianRowReference L v T R H) := by
  have hd := heatC2Datum_finiteCascadeTreeFeatureNumerator V K a ha hanti h0 L s T hs R H C hC hK
    (fun _=>1) measurable_const 1 (by norm_num) (fun _=>by norm_num)
  have hg : HasExpGrowth (finiteCascadeTreeFeatureNumerator V K a L s T R H (fun _=>1)) := by
    simpa only [iteratedDeriv_zero] using hd.growth 0 (by norm_num)
  have hi := hg.integrable_gaussianReal (μ:=0) (v:=v.toNNReal) hd.smooth.continuous.aestronglyMeasurable
  apply (integrable_prod_iff
    ((measurable_finiteCascadeTreeGaussianRowLogNumerator V K a ha L s T).exp.aestronglyMeasurable)).mpr
  refine ⟨Filter.Eventually.of_forall (fun θ=>integrable_exp_finiteCascadeTreeFeatureLogNumerator
    V K a ha L s θ T R H),?_⟩
  have he : finiteCascadeTreeFeatureNumerator V K a L s T R H (fun _=>1)=
      fun θ=>∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H := by
    funext θ
    simp only [finiteCascadeTreeFeatureNumerator,one_mul]
  rw [he] at hi
  simpa only [finiteCascadeTreeGaussianRowLogNumerator,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hi

theorem integral_exp_finiteCascadeTreeGaussianRowLogNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    (∫z,Real.exp (finiteCascadeTreeGaussianRowLogNumerator V K a L s T z)
      ∂finiteCascadeTreeGaussianRowReference L v T R H)=
        finiteCascadeTreeGaussianRowNormalizer V K a L s v T R H := by
  rw [finiteCascadeTreeGaussianRowReference,integral_prod _ (integrable_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s v T hs R H C hC hK)]
  simp only [finiteCascadeTreeGaussianRowNormalizer,gaussianHeatFlow,
    finiteCascadeTreeFeatureNumerator,finiteCascadeTreeGaussianRowLogNumerator,one_mul,zero_add]

theorem finiteCascadeTreeGaussianRowNormalizer_pos
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    0<finiteCascadeTreeGaussianRowNormalizer V K a L s v T R H := by
  let f := finiteCascadeTreeFeatureNumerator V K a L s T R H (fun _=>1)
  have hp (θ : ℝ) : 0<f θ := by
    have he := integral_exp_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T R H
    simpa only [f,finiteCascadeTreeFeatureNumerator,one_mul,he] using
      finiteCascadeTreeGaussianNormalizer_pos (fun σ=>V σ+θ*K σ) a ha L s j R H
  have hd := heatC2Datum_finiteCascadeTreeFeatureNumerator V K a ha hanti h0 L s T hs R H C hC hK
    (fun _=>1) measurable_const 1 (by norm_num) (fun _=>by norm_num)
  have hg : HasExpGrowth f := by simpa only [iteratedDeriv_zero] using hd.growth 0 (by norm_num)
  have hi := hg.integrable_gaussianReal (μ:=0) (v:=v.toNNReal) hd.smooth.continuous.aestronglyMeasurable
  change 0<∫θ,f (0+θ) ∂gaussianReal 0 v.toNNReal
  simp only [zero_add]
  apply (integral_pos_iff_support_of_nonneg (fun θ=>(hp θ).le) hi).mpr
  have he : Function.support f=univ := by
    ext θ
    simp only [Function.mem_support,Set.mem_univ]
    exact iff_true_intro (hp θ).ne'
  simp [he]

theorem finiteCascadeTreeGaussianRowLaw_probability
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    IsProbabilityMeasure (finiteCascadeTreeGaussianRowLaw V K a L s v T R H) := by
  have hp : 0<∫z,Real.exp (finiteCascadeTreeGaussianRowLogNumerator V K a L s T z)
      ∂finiteCascadeTreeGaussianRowReference L v T R H := by
    rw [integral_exp_finiteCascadeTreeGaussianRowLogNumerator V K a ha hanti h0 L s v T hs R H C hC hK]
    exact finiteCascadeTreeGaussianRowNormalizer_pos V K a ha hanti h0 L s v T hs R H C hC hK
  haveI : NeZero (finiteCascadeTreeGaussianRowReference L v T R H) := ⟨by
    intro he
    simp only [he,integral_zero_measure] at hp
    exact (lt_irrefl 0) hp⟩
  exact isProbabilityMeasure_tilted (integrable_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s v T hs R H C hC hK)

theorem integral_finiteCascadeTreeGaussianRowLaw_eq
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)=
      gaussianHeatFlow (finiteCascadeTreeFeatureNumerator V K a L s T R H F) v 0/
        finiteCascadeTreeGaussianRowNormalizer V K a L s v T R H := by
  have hi := integrable_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s v T hs R H C hC hK
  have hIF : Integrable (fun z=>Real.exp (finiteCascadeTreeGaussianRowLogNumerator V K a L s T z)*F z.2)
      (finiteCascadeTreeGaussianRowReference L v T R H) :=
    (hi.mul_const CF).mono'
      (((measurable_finiteCascadeTreeGaussianRowLogNumerator V K a ha L s T).exp.mul
        (hF.comp measurable_snd)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hFb z.2) (Real.exp_pos _).le)
  unfold finiteCascadeTreeGaussianRowLaw
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div]
  rw [integral_div,integral_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s v T hs R H C hC hK,finiteCascadeTreeGaussianRowReference,integral_prod _ hIF]
  congr 1
  simp only [gaussianHeatFlow,finiteCascadeTreeFeatureNumerator,zero_add,
    finiteCascadeTreeGaussianRowLogNumerator]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ=>integral_congr_ae
    (Filter.Eventually.of_forall fun z=>mul_comm _ _)

end FourPapersCommon
