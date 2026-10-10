module
public import QuantitativeFollowup.FiniteCascadeAmplitudeCells
public import QuantitativeFollowup.FollowupCavityPathClock
public import QuantitativeFollowup.ExponentialSmoothNonlinearComposition

@[expose] public section

/-! Positive diagonal variance has genuine simultaneous parameter/field
smoothness. Each cell retains its own independent noise coordinates. -/
noncomputable section
open Set
open scoped ContDiff NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def cavityPathSelectedEnergyInput (s : RSBScheme k) (i : Fin n) (j : ℕ) :
    Field n→L[ℝ]FiniteStateField (Configuration n) :=
  cavityPhysicalEdgeCoefficient s j • cavityCoordinateEnergyMap i

theorem cavityFiniteEnergyInput_variance_amplitude (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (b : ℝ) (hb : 0<b) (j : ℕ) :
    cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s j =
      cavityRestEnergyInput D s i j + Real.sqrt b • cavityPathSelectedEnergyInput s i j := by
  apply finiteStateCLM_eq_of_single
  intro l
  ext σ
  change cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s j (EuclideanSpace.single l 1) σ =
    cavityRestEnergyInput D s i j (EuclideanSpace.single l 1) σ +
      Real.sqrt b*(cavityPathSelectedEnergyInput s i j (EuclideanSpace.single l 1) σ)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,PiLp.smul_apply,
    smul_eq_mul,cavityFiniteEnergyInput_single,cavityRestEnergyInput_single,
    cavityPathSelectedEnergyInput,cavityCoordinateEnergyMap_single]
  rw [anisotropicReplaceVariance_variance D i l b hb]
  by_cases hl:l=i
  · simp only [hl,ite_true,cavityPhysicalEdgeCoefficient]
    ring
  · simp only [hl,ite_false,mul_zero,add_zero]

def cavityPathAmplitudePotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (j : ℕ) : ℝ×FiniteStateField (Configuration n)→ℝ :=
  finiteCascadeAmplitudeCellPotential (anisotropicSchemeMass s)
    (cavityRestEnergyInput D s i) (cavityPathSelectedEnergyInput s i) (k+1) j

theorem contDiff_cavityPathAmplitudePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) :
    ContDiff ℝ ∞ (cavityPathAmplitudePotential D s i j) :=
  contDiff_finiteCascadeAmplitudeCellPotential _ (anisotropicSchemeMass_nonneg s) _ _ _ _

theorem cavityPathAmplitudePotential_eq_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) (hj : j≤k+2)
    (b : ℝ) (hb : 0<b) (H : FiniteStateField (Configuration n)) :
    cavityPathAmplitudePotential D s i j (Real.sqrt b,H)=
      finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) j H := by
  unfold cavityPathAmplitudePotential
  rw [finiteCascadeAmplitudeCellPotential_eq_actual _ _ _ _ j (by omega)]
  congr 1
  funext p
  exact (cavityFiniteEnergyInput_variance_amplitude D s i b hb p).symm

theorem contDiffOn_cavityFinitePotential_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) (hj : j≤k+2) :
    ContDiffOn ℝ ∞ (fun w : ℝ×FiniteStateField (Configuration n)=>
      finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) j w.2)
      ((Ioi 0)×ˢ(univ : Set (FiniteStateField (Configuration n)))) := by
  intro w hw
  have hs : ContDiffWithinAt ℝ ∞ (fun z : ℝ×FiniteStateField (Configuration n)=>
      (Real.sqrt z.1,z.2)) ((Ioi 0)×ˢ(univ : Set (FiniteStateField (Configuration n)))) w :=
    (contDiff_fst.contDiffWithinAt.sqrt hw.1.ne').prodMk contDiff_snd.contDiffWithinAt
  have hh := (contDiff_cavityPathAmplitudePotential D s i j).contDiffAt.comp_contDiffWithinAt w hs
  refine hh.congr (fun z hz =>
    (cavityPathAmplitudePotential_eq_variance D s i j hj z.1 hz.1 z.2).symm) ?_
  exact (cavityPathAmplitudePotential_eq_variance D s i j hj w.1 hw.1 w.2).symm

theorem exponentialSmoothOn_cavityFinitePotential_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) (hj : j≤k+2)
    (l u : ℝ) (hl : 0<l) :
    ExponentialSmoothOn (fun w : ℝ×FiniteStateField (Configuration n)=>
      finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) j w.2)
      ((Ioo l u)×ˢ(univ : Set (FiniteStateField (Configuration n)))) := by
  let E:=FiniteStateField (Configuration n)
  let U : Set (ℝ×E):=(Ioo l u)×ˢuniv
  let R : ℝ≥0:=⟨Real.sqrt u+1,by positivity⟩
  let g : ℝ×E→ℝ×E:=fun w=>(Real.sqrt w.1,w.2)
  have hs:=exponentialSmoothOn_sqrt_comp_fst E l u hl
  have hg : ExponentialSmoothOn g U := by
    have hh:=hs.compCLM (ContinuousLinearMap.inl ℝ ℝ E)
    have hz:=exponentialSmoothOn_linear
      ((ContinuousLinearMap.inr ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ E)) U
    convert hh.add hz using 1
    funext w
    simp [g]
  have hmap : MapsTo g U {w : ℝ×E | |w.1|<R} := by
    intro w hw
    change |Real.sqrt w.1|<Real.sqrt u+1
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hm:=Real.sqrt_le_sqrt hw.1.2.le
    linarith
  have hgv (w : ℝ×E) (hw : w∈U) : ‖g w‖≤Real.sqrt u+‖w‖ := by
    change max ‖Real.sqrt w.1‖ ‖w.2‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply max_le
    · exact (Real.sqrt_le_sqrt hw.1.2.le).trans (le_add_of_nonneg_right (norm_nonneg _))
    · exact (norm_snd_le w).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  have hf:=exponentialSmoothOn_finiteCascadeAmplitudeCellPotential (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (cavityRestEnergyInput D s i) (cavityPathSelectedEnergyInput s i)
      (k+1) j R
  have hh:=exponentialSmoothOn_comp_of_linear_growth _ _ hf g U hg hmap
    (Real.sqrt u) 1 (Real.sqrt_nonneg _) (by norm_num) (by simpa only [one_mul] using hgv)
  apply hh.congr
  intro w hw
  have hn : U∈𝓝 w := (isOpen_Ioo.prod isOpen_univ).mem_nhds hw
  filter_upwards [hn] with z hz
  exact cavityPathAmplitudePotential_eq_variance D s i j hj z.1 (hl.trans hz.1.1) z.2

theorem cavityFinitePotential_variance_linear_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) (hj : j≤k+2)
    (l u : ℝ) (hl : 0<l) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀b∈Ioo l u,∀H : FiniteStateField (Configuration n),
      |finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) j H|≤B+L*‖H‖ := by
  let R : ℝ≥0:=⟨Real.sqrt u+1,by positivity⟩
  let L:=finiteCascadeAmplitudeLip (finiteCascadeCellAssembler (K:=k+2) (cavityRestEnergyInput D s i))
    (finiteCascadeCellAssembler (K:=k+2) (cavityPathSelectedEnergyInput s i)) R
  obtain ⟨C,hC,hb⟩:=finiteCascadeAmplitudeCellPotential_value_bound (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (cavityRestEnergyInput D s i) (cavityPathSelectedEnergyInput s i)
      (k+1) j R
  refine ⟨C+L*Real.sqrt u,L,by positivity,L.coe_nonneg,?_⟩
  intro b hb' H
  have hpos : 0<b:=hl.trans hb'.1
  have hR : |Real.sqrt b|<R := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hm:=Real.sqrt_le_sqrt hb'.2.le
    change _<Real.sqrt u+1
    linarith
  rw [←cavityPathAmplitudePotential_eq_variance D s i j hj b hpos H]
  apply (hb (Real.sqrt b,H) hR).trans
  have hn : ‖(Real.sqrt b,H)‖≤Real.sqrt u+‖H‖ := by
    rw [Prod.norm_def,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply max_le
    · exact (Real.sqrt_le_sqrt hb'.2.le).trans (le_add_of_nonneg_right (norm_nonneg _))
    · exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hm:=mul_le_mul_of_nonneg_left hn L.coe_nonneg
  change C+L*‖(Real.sqrt b,H)‖≤_
  nlinarith only [hm]

end QuantitativeFollowup
