module
public import QuantitativeFollowup.AnisotropicFiniteCascade
public import QuantitativeFollowup.ScalarSchemeStieltjesBoundary
public import QuantitativePaper.VectorProfileMeasure
public import FourPapersCommon.FiniteCascadeBinaryFeature
public import FourPapersCommon.FiniteStateCascadeZeroInput

@[expose] public section

/-! The binary terminal-feature Hessian at an actual finite cavity node.
Future squares are genuine conditional cascade moments. Zero-variance
transitions identify repeated levels before the Stieltjes boundary is taken. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def cavityFiniteEnergyInput (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) : FiniteStateGaussianInput (Fin n)→L[ℝ]FiniteStateField (Configuration n) :=
  (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)

def cavityFiniteFutureDepth (s : RSBScheme k) (J : ℕ) (q : Paper.Overlap) : ℕ := by
  classical
  exact Nat.findGreatest (fun d=> (q:ℝ) ≤ s.q (k+2-d)) J

def cavityFiniteFutureSquare (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : ℕ) (H K : FiniteStateField (Configuration n)) (q : Paper.Overlap) : ℝ :=
  let d:=cavityFiniteFutureDepth s J q
  finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) d (J-d) H K K

theorem cavityFiniteFutureDepth_le (s : RSBScheme k) (J : ℕ) (q : Paper.Overlap) :
    cavityFiniteFutureDepth s J q ≤ J := by
  classical
  exact Nat.findGreatest_le J

theorem cavityFiniteFutureDepth_current (s : RSBScheme k) (J : ℕ) (hJ : J ≤ k+2) :
    cavityFiniteFutureDepth s J (scalarSchemeTransportNode s (k+2-J))=J := by
  classical
  apply Nat.findGreatest_eq
  rw [scalarSchemeTransportNode_coe s _ (by omega)]

theorem cavityFiniteFutureSquare_current (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : ℕ) (hJ : J ≤ k+2) (H K : FiniteStateField (Configuration n)) :
    cavityFiniteFutureSquare D s J H K (scalarSchemeTransportNode s (k+2-J))=
      (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J) H K)^2 := by
  simp only [cavityFiniteFutureSquare,cavityFiniteFutureDepth_current s J hJ,Nat.sub_self,
    finiteStateCascadePairMoment,OverlapPaper.sourceKernelExpectation]
  ring

theorem cavityFiniteFutureDepth_node (s : RSBScheme k) (J p : ℕ)
    (hJ : J ≤ k+2) (hp : p ≤ J) :
    p ≤ cavityFiniteFutureDepth s J (scalarSchemeTransportNode s (k+2-p)) ∧
      s.q (k+2-cavityFiniteFutureDepth s J (scalarSchemeTransportNode s (k+2-p)))=
        s.q (k+2-p) := by
  classical
  let d:=cavityFiniteFutureDepth s J (scalarSchemeTransportNode s (k+2-p))
  have hqual : (scalarSchemeTransportNode s (k+2-p):ℝ) ≤ s.q (k+2-p) := by
    rw [scalarSchemeTransportNode_coe s _ (by omega)]
  have hpd : p ≤ d := Nat.le_findGreatest hp hqual
  have hdJ : d ≤ J := cavityFiniteFutureDepth_le s J _
  have hdq : s.q (k+2-p) ≤ s.q (k+2-d) := by
    have hh:=Nat.findGreatest_spec (P:=fun d=>
      (scalarSchemeTransportNode s (k+2-p):ℝ) ≤ s.q (k+2-d)) hp hqual
    change (scalarSchemeTransportNode s (k+2-p):ℝ) ≤ s.q (k+2-d) at hh
    rw [scalarSchemeTransportNode_coe s _ (by omega)] at hh
    exact hh
  exact ⟨hpd,le_antisymm (s.q_mono' (k+2-p) (by omega) (k+2-d) (by omega)) hdq⟩

theorem cavityFiniteEnergyInput_zero_segment (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (p d : ℕ) (hpd : p ≤ d) (hd : d ≤ k+2)
    (he : s.q (k+2-d)=s.q (k+2-p)) (r : ℕ) (hrp : p ≤ r) (hrd : r < d) :
    cavityFiniteEnergyInput D s r=0 := by
  have hlow : s.q (k+2-d) ≤ s.q (k+1-r) :=
    s.q_mono' (k+1-r) (by omega) (k+2-d) (by omega)
  have hhigh : s.q (k+2-r) ≤ s.q (k+2-p) :=
    s.q_mono' (k+2-p) (by omega) (k+2-r) (by omega)
  have hmid : s.q (k+1-r) ≤ s.q (k+2-r) :=
    s.q_mono' (k+2-r) (by omega) (k+1-r) (by omega)
  have hz : s.q (k+2-r)-s.q (k+1-r)=0 := by rw [he] at hlow; linarith
  ext z σ
  simp [cavityFiniteEnergyInput,anisotropicSchemeInput,hz]

theorem cavityFiniteFutureSquare_node (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J p : ℕ) (hJ : J ≤ k+2) (hp : p ≤ J) (H K : FiniteStateField (Configuration n)) :
    cavityFiniteFutureSquare D s J H K (scalarSchemeTransportNode s (k+2-p))=
      finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) p (J-p) H K K := by
  let d:=cavityFiniteFutureDepth s J (scalarSchemeTransportNode s (k+2-p))
  have hd:=cavityFiniteFutureDepth_node s J p hJ hp
  exact (finiteStateCascadePairMoment_zero_segment (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    p d J hd.1 (cavityFiniteFutureDepth_le s J _) (fun r hrp hrd=>
      cavityFiniteEnergyInput_zero_segment D s p d hd.1
        ((cavityFiniteFutureDepth_le s J _).trans hJ) hd.2 r hrp hrd) H K K).symm

theorem cavityFiniteFutureSquare_eq_conditional_integral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (H K : FiniteStateField (Configuration n))
    (q : Paper.Overlap) :
    cavityFiniteFutureSquare D s J H K q=
      let d:=cavityFiniteFutureDepth s J q
      ∫y,(∫σ,K σ ∂finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y)^2
        ∂OverlapPaper.sourceKernelLaw (fun r=>finiteStateGaussianCascadeKernel
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
          (gtStateLogPartition (fun _ : Configuration n=>0)) (d+r)) (J-d) H := by
  unfold cavityFiniteFutureSquare
  rw [finiteStateCascadePairMoment_eq_splitLaw _ _ (anisotropicSchemeMass_nonneg s),
    integral_finiteStateCascadeSplitLaw_mul _ _ (anisotropicSchemeMass_nonneg s)]
  congr 1
  funext y
  ring

theorem cavityFiniteBinaryFeature_node_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (hJ : J ≤ k+2)
    (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J)) H K K=
      1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (k+2-J))*
        (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J) H K)^2-
      ∫q,if scalarSchemeTransportNode s (k+2-J) < q then cavityFiniteFutureSquare D s J H K q else 0
        ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
  have hb:=finiteStateCascadeBinaryFeature_second (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) J H K hK
  have ha0 : anisotropicSchemeMass s 0=1 := by simp [anisotropicSchemeMass,s.m_top]
  rw [ha0] at hb
  simp only [sub_self,zero_mul,sub_zero] at hb
  simp_rw [←finiteStateCascadePairMoment_eq_splitLaw _ _ (anisotropicSchemeMass_nonneg s)] at hb
  have hs:=scalarScheme_stieltjes_boundary s J hJ (cavityFiniteFutureSquare D s J H K)
  rw [cavityFiniteFutureSquare_current D s J hJ H K] at hs
  have he : (∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
      cavityFiniteFutureSquare D s J H K (scalarSchemeTransportNode s (k+1-r)))=
      ∑r∈Finset.range J,(anisotropicSchemeMass s r-anisotropicSchemeMass s (r+1))*
        finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
          (cavityFiniteEnergyInput D s) (r+1) (J-(r+1)) H K K := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrJ:=Finset.mem_range.mp hr
    rw [show k+1-r=k+2-(r+1) by omega,cavityFiniteFutureSquare_node D s J (r+1) hJ (by omega)]
    rfl
  rw [he] at hs
  change anisotropicSchemeMass s J*(_)^2+_= _ at hs
  linarith

theorem cavityFiniteBinaryFeature_node_free_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (hJ : J ≤ k+2)
    (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J)) H K K=
      1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (k+2-J))*
        (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J) H K)^2-
      ∫q,if scalarSchemeTransportNode s (k+2-J) < q then cavityFiniteFutureSquare D s J H K q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  have he : (∫q,if scalarSchemeTransportNode s (k+2-J) < q then cavityFiniteFutureSquare D s J H K q else 0
      ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∫q,if scalarSchemeTransportNode s (k+2-J) < q then cavityFiniteFutureSquare D s J H K q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
    rw [←vectorProfile_free_root_decomposition s a ha has hq,
      integral_add_measure (by apply (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
        (integrable_vectorProfileFreeMeasure s a _)]
    rw [integral_smul_measure,integral_dirac]
    have hz : ¬scalarSchemeTransportNode s (k+2-J) < zeroOverlap :=
      not_lt_of_ge (show zeroOverlap ≤ scalarSchemeTransportNode s (k+2-J) from
        (scalarSchemeTransportNode s _).property.1)
    rw [if_neg hz,smul_zero,zero_add,vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
  rw [cavityFiniteBinaryFeature_node_stieltjes D s J hJ H K hK,he]

theorem hasDerivAt_cavityFiniteFeature_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (H K : FiniteStateField (Configuration n)) (θ : ℝ) :
    HasDerivAt (fun u=>finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J (H+u • K))
      (∫σ,K σ ∂finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J (H+θ • K)) θ :=
  hasDerivAt_finiteStateCascadeFeature_parameter _ _ (anisotropicSchemeMass_nonneg s) _ J H K θ

theorem hasDerivAt_cavityFiniteBinaryFeature_parameter_first (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (hJ : J ≤ k+2)
    (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) (θ : ℝ) :
    HasDerivAt (fun u=>fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J) (H+u • K) K)
      (1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (k+2-J))*
        (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
          (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J) (H+θ • K) K)^2-
      ∫q,if scalarSchemeTransportNode s (k+2-J) < q then cavityFiniteFutureSquare D s J (H+θ • K) K q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) θ := by
  have hU:=contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) J
  have hD : ContDiff ℝ 1 (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J)) := hU.fderiv_right (by norm_num)
  have hh:=(hD.differentiable_one (H+θ • K)).hasFDerivAt
  have hc:=hh.comp_hasDerivAt θ ((hasDerivAt_id θ).smul_const K |>.const_add H)
  have he:=hc.clm_apply (hasDerivAt_const θ K)
  simpa only [Function.comp_def,id_eq,one_smul,map_zero,add_zero,
    cavityFiniteBinaryFeature_node_free_stieltjes D s J hJ a ha has hq (H+θ • K) K hK] using he

def cavityPairFeature (i j : Fin n) : FiniteStateField (Configuration n) :=
  WithLp.toLp 2 (fun σ=>Paper.spinSign (σ i)*Paper.spinSign (σ j))

theorem cavityPairFeature_binary (i j : Fin n) (σ : Configuration n) :
    cavityPairFeature i j σ*cavityPairFeature i j σ=1 := by
  change (Paper.spinSign (σ i)*Paper.spinSign (σ j))*(Paper.spinSign (σ i)*Paper.spinSign (σ j))=1
  rw [←pow_two]
  rw [mul_pow,Paper.spinSign_sq,Paper.spinSign_sq,mul_one]

end QuantitativeFollowup
