module
public import QuantitativeFollowup.FiniteCascadeAmplitudeRecursion
public import FourPapersCommon.FiniteStateCascadePrefix

@[expose] public section

/-! Every physical finite-cell input has its own independent fixed noise
slot. The actual covariance cascade is recovered from those slots. -/
noncomputable section
open scoped BigOperators ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.AT
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {S : Type} [Fintype S] [Nonempty S] {n K : ℕ}

abbrev FiniteCascadeCellNoise (K n : ℕ) := FiniteStateGaussianInput (Fin K × Fin n)

def finiteCascadeCellNoiseProjection (p : Fin K) : FiniteCascadeCellNoise K n→L[ℝ]Field n :=
  LinearMap.toContinuousLinearMap
    {toFun := fun z => WithLp.toLp 2 (fun i => z (p,i))
     map_add' := by intro x y;ext i;simp
     map_smul' := by intro r x;ext i;simp}

def finiteCascadeCellNoiseInjection (p : Fin K) : Field n→L[ℝ]FiniteCascadeCellNoise K n :=
  LinearMap.toContinuousLinearMap
    {toFun := fun z => WithLp.toLp 2 (fun l => if l.1=p then z l.2 else 0)
     map_add' := by intro x y;ext l;by_cases h:l.1=p <;> simp [h]
     map_smul' := by intro r x;ext l;by_cases h:l.1=p <;> simp [h]}

theorem finiteCascadeCellNoiseProjection_injection (p q : Fin K) (z : Field n) :
    finiteCascadeCellNoiseProjection p (finiteCascadeCellNoiseInjection q z) =
      if p=q then z else 0 := by
  ext i
  by_cases h:p=q <;> simp [finiteCascadeCellNoiseProjection,finiteCascadeCellNoiseInjection,h]

def finiteCascadeCellAssembler (L : ℕ→Field n→L[ℝ]FiniteStateField S) :
    FiniteCascadeCellNoise K n→L[ℝ]FiniteStateField S :=
  ∑p : Fin K,(L p).comp (finiteCascadeCellNoiseProjection p)

theorem finiteCascadeCellAssembler_injection (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (q : Fin K) : (finiteCascadeCellAssembler (K:=K) L).comp (finiteCascadeCellNoiseInjection q)=L q := by
  ext z
  simp only [finiteCascadeCellAssembler,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply]
  simp_rw [finiteCascadeCellNoiseProjection_injection]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp; simp [hp]
  · simp

def finiteCascadeNoiseCell (K j : ℕ) : Fin (K+1) := ⟨min j K,by omega⟩

def finiteCascadeAmplitudeCellPotential (a : ℕ→ℝ)
    (A B : ℕ→Field n→L[ℝ]FiniteStateField S) (K : ℕ) (j : ℕ)
    (w : ℝ×FiniteStateField S) : ℝ :=
  finiteGaussianAmplitudeCascade a (finiteCascadeCellAssembler (K:=K+1) A)
    (finiteCascadeCellAssembler (K:=K+1) B)
    (fun p => finiteCascadeCellNoiseInjection (finiteCascadeNoiseCell K p)) j (w.1,0,w.2)

theorem contDiff_finiteCascadeAmplitudeCellPotential (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A B : ℕ→Field n→L[ℝ]FiniteStateField S) (K j : ℕ) :
    ContDiff ℝ ∞ (finiteCascadeAmplitudeCellPotential a A B K j) :=
  (contDiff_finiteGaussianAmplitudeCascade a ha _ _ _ j).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

theorem exponentialSmoothOn_finiteCascadeAmplitudeCellPotential (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A B : ℕ→Field n→L[ℝ]FiniteStateField S) (K j : ℕ) (R : ℝ≥0) :
    ExponentialSmoothOn (finiteCascadeAmplitudeCellPotential a A B K j)
      {w : ℝ×FiniteStateField S | |w.1|<R} := by
  let Z : ℝ×FiniteStateField S→L[ℝ]FiniteCascadeAmplitudeState (FiniteCascadeCellNoise (K+1) n) S :=
    (ContinuousLinearMap.fst ℝ ℝ (FiniteStateField S)).prod
      ((0 : ℝ×FiniteStateField S→L[ℝ]FiniteCascadeCellNoise (K+1) n).prod
        (ContinuousLinearMap.snd ℝ ℝ (FiniteStateField S)))
  exact (finiteGaussianAmplitudeCascade_regular a ha _ _ _ R j).1.precompCLM Z
    (fun w hw=>hw)

theorem finiteCascadeAmplitudeCellPotential_value_bound (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A B : ℕ→Field n→L[ℝ]FiniteStateField S) (K j : ℕ) (R : ℝ≥0) :
    ∃C : ℝ,0≤C ∧ ∀w : ℝ×FiniteStateField S,|w.1|<R→
      |finiteCascadeAmplitudeCellPotential a A B K j w|≤
        C+finiteCascadeAmplitudeLip (finiteCascadeCellAssembler (K:=K+1) A)
          (finiteCascadeCellAssembler (K:=K+1) B) R*‖w‖ := by
  obtain ⟨C,hC,hb⟩:=(finiteGaussianAmplitudeCascade_regular a ha
    (finiteCascadeCellAssembler (K:=K+1) A) (finiteCascadeCellAssembler (K:=K+1) B)
      (fun p=>finiteCascadeCellNoiseInjection (finiteCascadeNoiseCell K p)) R j).2.1
  refine ⟨C,hC,fun w hw=>?_⟩
  have hh:=hb (w.1,0,w.2) hw
  simpa only [finiteCascadeAmplitudeCellPotential,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hh

theorem finiteCascadeAmplitudeCellPotential_eq_actual (a : ℕ→ℝ)
    (A B : ℕ→Field n→L[ℝ]FiniteStateField S) (K j : ℕ) (hj : j≤K+1)
    (w : ℝ×FiniteStateField S) :
    finiteCascadeAmplitudeCellPotential a A B K j w =
      finiteStateGaussianTerminalCascade (fun _ : S=>0) a (fun p => A p+w.1 • B p) j w.2 := by
  unfold finiteCascadeAmplitudeCellPotential
  rw [finiteGaussianAmplitudeCascade_eq_actual]
  have he := finiteStateGaussianTerminalCascade_congr_prefix (fun _ : S=>0) a a
    (fun p => (finiteCascadeCellAssembler (K:=K+1) A).comp
        (finiteCascadeCellNoiseInjection (finiteCascadeNoiseCell K p)) +
      w.1 • (finiteCascadeCellAssembler (K:=K+1) B).comp
        (finiteCascadeCellNoiseInjection (finiteCascadeNoiseCell K p)))
    (fun p => A p+w.1 • B p) j (fun _ _ => rfl) (fun p hp => ?_)
  · rw [he]
    simp [finiteCascadeAmplitudeField]
  · rw [finiteCascadeCellAssembler_injection,finiteCascadeCellAssembler_injection]
    have hval : (finiteCascadeNoiseCell K p : ℕ)=p := Nat.min_eq_left (by omega)
    rw [hval]

end QuantitativeFollowup
