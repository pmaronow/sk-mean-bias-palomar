module
public import QuantitativePaper.VectorConditionalObservableDensity
public import FourPapersCommon.L2Moments
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

@[expose] public section

/-! Genuine fixed-past L² continuity of conditional covariance square
moments. The probability law in the conditional expectation is fixed;
changing initial-disorder densities are paired only after this contraction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def conditionalCovarianceSquareClip (x : ℝ) : ℝ := (max (-2) (min 2 x))^2

theorem lipschitzWith_conditionalCovarianceSquareClip :
    LipschitzWith 4 conditionalCovarianceSquareClip := by
  let c:ℝ→ℝ:=fun x=>max (-2) (min 2 x)
  have hc:LipschitzWith 1 c:=(LipschitzWith.id.const_min 2).const_max (-2)
  have hb (x : ℝ) : |c x| ≤ 2:=by
    rw [abs_le]
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((c x)^2) ((c y)^2) ≤ (4:ℝ)*dist x y
  simp only [Real.dist_eq]
  have hd:|(c x)^2-(c y)^2|=|c x-c y| * |c x+c y|:=by
    rw [←abs_mul]
    congr 1
    ring
  rw [hd]
  have hs:|c x+c y| ≤ 4:=(abs_add_le _ _).trans (by linarith [hb x,hb y])
  have he:=hc.dist_le_mul x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at he
  exact (mul_le_mul he hs (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem conditionalCovarianceSquareClip_zero : conditionalCovarianceSquareClip 0=0:=by
  norm_num [conditionalCovarianceSquareClip]

theorem conditionalCovarianceSquareClip_eq (x : ℝ) (hx : |x| ≤ 2) :
    conditionalCovarianceSquareClip x=x^2:=by
  rcases abs_le.mp hx with ⟨hl,hu⟩
  simp only [conditionalCovarianceSquareClip,min_eq_right hu,max_eq_right hl]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def conditionalBaseL2 (V : MeasurableSpace Ω) (hV : V ≤ mΩ) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
by
  letI : MeasurableSpace Ω := mΩ
  exact (lpMeas ℝ ℝ V 2 P).subtypeL.comp (condExpL2 ℝ ℝ hV)

theorem conditionalBaseL2_ae (V : MeasurableSpace Ω) (hV : V ≤ mΩ)
    (f : Ω→ℝ) (hf : MemLp f 2 P) :
    (conditionalBaseL2 (mΩ:=mΩ) V hV (hf.toLp f) : Ω→ℝ)=ᵐ[P] P[f|V] :=
  hf.condExpL2_ae_eq_condExp hV

theorem tendsto_conditionalBaseL2 {I : Type*} {L : Filter I}
    (V : MeasurableSpace Ω) (hV : V ≤ mΩ) (f : I→Lp ℝ 2 P) (g : Lp ℝ 2 P)
    (hfg : Tendsto f L (𝓝 g)) :
    Tendsto (fun i=>conditionalBaseL2 (mΩ:=mΩ) V hV (f i)) L (𝓝 (conditionalBaseL2 (mΩ:=mΩ) V hV g)) :=
  ((conditionalBaseL2 (mΩ:=mΩ) V hV).continuous.tendsto g).comp hfg

/-- L²-continuous input observables, known products and initial densities
give true continuity of weighted conditional covariance-square moments. -/
theorem tendsto_weighted_conditional_covariance_square {I : Type*} {L : Filter I}
    (V : MeasurableSpace Ω) (hV : V ≤ mΩ)
    (fj gj wj : I→Ω→ℝ) (f g w : Ω→ℝ)
    (hfj : ∀i,MemLp (fj i) 2 P) (hgj : ∀i,MemLp (gj i) 2 P) (hwj : ∀i,MemLp (wj i) 2 P)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (hw : MemLp w 2 P)
    (hflim : Tendsto (fun i=>(hfj i).toLp (fj i)) L (𝓝 (hf.toLp f)))
    (hglim : Tendsto (fun i=>(hgj i).toLp (gj i)) L (𝓝 (hg.toLp g)))
    (hwlim : Tendsto (fun i=>(hwj i).toLp (wj i)) L (𝓝 (hw.toLp w)))
    (hfjb : ∀i,∀ᵐx ∂P,‖fj i x‖ ≤ 1)
    (hgjb : ∀i,∀ᵐx ∂P,‖gj i x‖ ≤ 1)
    (hfb : ∀ᵐx ∂P,‖f x‖ ≤ 1) (hgb : ∀ᵐx ∂P,‖g x‖ ≤ 1) :
    Tendsto (fun i=>∫x,wj i x*(P[fj i|V] x-gj i x)^2∂P) L
      (𝓝 (∫x,w x*(P[f|V] x-g x)^2∂P)) := by
  letI : MeasurableSpace Ω := mΩ
  let cj:I→Lp ℝ 2 P:=fun i=>conditionalBaseL2 (mΩ:=mΩ) V hV ((hfj i).toLp (fj i))-(hgj i).toLp (gj i)
  let c:Lp ℝ 2 P:=conditionalBaseL2 (mΩ:=mΩ) V hV (hf.toLp f)-hg.toLp g
  let sq:Lp ℝ 2 P→Lp ℝ 2 P:=lipschitzWith_conditionalCovarianceSquareClip.compLp
    conditionalCovarianceSquareClip_zero
  have hc:Tendsto cj L (𝓝 c):=(tendsto_conditionalBaseL2 (mΩ:=mΩ) V hV _ _ hflim).sub hglim
  have hs:Tendsto (fun i=>sq (cj i)) L (𝓝 (sq c)):=
    (lipschitzWith_conditionalCovarianceSquareClip.continuous_compLp
      conditionalCovarianceSquareClip_zero).continuousAt.tendsto.comp hc
  have hpair:=((continuous_fst.inner continuous_snd :
    Continuous (fun z:Lp ℝ 2 P×Lp ℝ 2 P=>inner ℝ z.1 z.2)).tendsto
      (hw.toLp w,sq c)).comp (hwlim.prodMk_nhds hs)
  have hj (i:I):(sq (cj i) : Ω→ℝ)=ᵐ[P]fun x=>(P[fj i|V] x-gj i x)^2:=by
    filter_upwards [lipschitzWith_conditionalCovarianceSquareClip.coeFn_compLp
      conditionalCovarianceSquareClip_zero (cj i),
      Lp.coeFn_sub (conditionalBaseL2 (mΩ:=mΩ) V hV ((hfj i).toLp (fj i))) ((hgj i).toLp (gj i)),
      conditionalBaseL2_ae (mΩ:=mΩ) V hV (fj i) (hfj i),(hgj i).coeFn_toLp,
      ae_bdd_norm_condExp_of_ae_bdd_norm (m:=V) (hfjb i),hgjb i]
      with x hs hsub hce hg hceb hgb
    rw [hs]
    dsimp only [cj,c]
    simp only [Function.comp_def,hsub,Pi.sub_apply,hce,hg]
    apply conditionalCovarianceSquareClip_eq
    simpa only [Real.norm_eq_abs] using
      (norm_sub_le (P[fj i|V] x) (gj i x)).trans (by linarith)
  have he:(sq c : Ω→ℝ)=ᵐ[P]fun x=>(P[f|V] x-g x)^2:=by
    filter_upwards [lipschitzWith_conditionalCovarianceSquareClip.coeFn_compLp
      conditionalCovarianceSquareClip_zero c,
      Lp.coeFn_sub (conditionalBaseL2 (mΩ:=mΩ) V hV (hf.toLp f)) (hg.toLp g),
      conditionalBaseL2_ae (mΩ:=mΩ) V hV f hf,hg.coeFn_toLp,
      ae_bdd_norm_condExp_of_ae_bdd_norm (m:=V) hfb,hgb]
      with x hs hsub hce hg hceb hgb
    rw [hs]
    dsimp only [cj,c]
    simp only [Function.comp_def,hsub,Pi.sub_apply,hce,hg]
    apply conditionalCovarianceSquareClip_eq
    simpa only [Real.norm_eq_abs] using
      (norm_sub_le (P[f|V] x) (g x)).trans (by linarith)
  have hp (A B:Lp ℝ 2 P) : inner ℝ A B=∫x,A x*B x∂P:=by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial,mul_comm]
  have hje (i:I):inner ℝ ((hwj i).toLp (wj i)) (sq (cj i))=
      ∫x,wj i x*(P[fj i|V] x-gj i x)^2∂P:=by
    rw [hp]
    exact integral_congr_ae ((hwj i).coeFn_toLp.mul (hj i))
  have hve:inner ℝ (hw.toLp w) (sq c)=∫x,w x*(P[f|V] x-g x)^2∂P:=by
    rw [hp]
    exact integral_congr_ae (hw.coeFn_toLp.mul he)
  simpa only [Function.comp_def,hje,hve] using hpair

end QuantitativePaper
