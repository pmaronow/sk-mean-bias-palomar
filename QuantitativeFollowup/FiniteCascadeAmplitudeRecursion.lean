module
public import QuantitativeFollowup.FiniteCascadeAmplitudeTerminal

@[expose] public section

/-! Genuine simultaneous amplitude/field smoothness of a fixed-mass finite
Gaussian cascade, obtained by keeping all noise shifts fixed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.AT
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {S G : Type} [Fintype S] [Nonempty S]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

private theorem gaussianShiftColeHopf_directional_lipschitz_normed
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (U : Set E) (A : Field n→L[ℝ]E) (B : G→L[ℝ]E)
    (hA : ∀x∈U,∀z,x+A z∈U) (hB : ∀x∈U,∀z,x+B z∈U)
    (H K : ℝ≥0) (hLipA : ∀x∈U,∀z,|f (x+A z)-f x|≤H*‖z‖)
    (hLipB : ∀x∈U,∀z,|f (x+B z)-f x|≤K*‖z‖)
    (mass : ℝ) (hmass : 0 ≤ mass) (x : E) (hx : x∈U) (v : G) :
    |gaussianShiftColeHopf A mass f (x+B v)-gaussianShiftColeHopf A mass f x|≤K*‖v‖ := by
  rw [gaussianShiftColeHopf_eq_unitVectorStep,gaussianShiftColeHopf_eq_unitVectorStep]
  apply abs_vectorColeHopfStep_sub_le _ _ H
    (lipschitzWith_gaussian_noise_slice f U A hA H hLipA _ (hB x hx v))
    (lipschitzWith_gaussian_noise_slice f U A hA H hLipA x hx)
    1 mass ((K:ℝ)*‖v‖) hmass _ 0
  intro z
  have hh := hLipB (x+A z) (hA x hx z) v
  have he : x+B v+A z=x+A z+B v := by abel
  rw [he]
  exact hh

def finiteGaussianAmplitudeCascade (a : ℕ→ℝ) (A B : G→L[ℝ]FiniteStateField S)
    (L : ℕ→Field n→L[ℝ]G) : ℕ→FiniteCascadeAmplitudeState G S→ℝ
  | 0 => finiteCascadeAmplitudeTerminal A B
  | j+1 => gaussianShiftColeHopf (finiteCascadeAmplitudeNoiseShift.comp (L j))
      (a j) (finiteGaussianAmplitudeCascade a A B L j)

theorem finiteGaussianAmplitudeCascade_regular (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A B : G→L[ℝ]FiniteStateField S) (L : ℕ→Field n→L[ℝ]G) (R : ℝ≥0) (j : ℕ) :
    ExponentialSmoothOn (finiteGaussianAmplitudeCascade a A B L j) (finiteCascadeAmplitudeDomain R) ∧
    (∃C : ℝ,0≤C ∧ ∀w∈finiteCascadeAmplitudeDomain R,
      |finiteGaussianAmplitudeCascade a A B L j w|≤C+finiteCascadeAmplitudeLip A B R*‖w‖) ∧
    (∀w∈finiteCascadeAmplitudeDomain R,∀z:G,
      |finiteGaussianAmplitudeCascade a A B L j (w+finiteCascadeAmplitudeNoiseShift z)-
        finiteGaussianAmplitudeCascade a A B L j w|≤finiteCascadeAmplitudeLip A B R*‖z‖) := by
  induction j with
  | zero =>
      exact ⟨exponentialSmoothOn_finiteCascadeAmplitudeTerminal A B R,
        ⟨_,abs_nonneg _,finiteCascadeAmplitudeTerminal_value_bound A B R⟩,
        finiteCascadeAmplitudeTerminal_noise_lipschitz A B R⟩
  | succ j ih =>
      obtain ⟨hs,⟨C,hC,hv⟩,hnoise⟩ := ih
      let K := finiteCascadeAmplitudeLip A B R
      let W := finiteCascadeAmplitudeDomain (G:=G) (S:=S) R
      let M := (finiteCascadeAmplitudeNoiseShift (G:=G) (S:=S)).comp (L j)
      have hshift (w : FiniteCascadeAmplitudeState G S) (hw : w∈W) (z : Field n) : w+M z∈W :=
        finiteCascadeAmplitudeDomain_noise_invariant R w hw (L j z)
      have hcell (w : FiniteCascadeAmplitudeState G S) (hw : w∈W) (z : Field n) :
          |finiteGaussianAmplitudeCascade a A B L j (w+M z)-
            finiteGaussianAmplitudeCascade a A B L j w|≤(K*‖L j‖₊)*‖z‖ := by
        apply (hnoise w hw (L j z)).trans
        exact (mul_le_mul_of_nonneg_left ((L j).le_opNorm z) K.coe_nonneg).trans_eq (by
          simp only [NNReal.coe_mul,coe_nnnorm];ring)
      have hsm := exponentialSmoothOn_gaussianShiftColeHopf _ W
        (finiteCascadeAmplitudeDomain_open R) hs M hshift C K K.coe_nonneg hv
        (K*‖L j‖₊) hcell (a j)
      obtain ⟨D,hD,hb⟩ := gaussianShiftColeHopf_value_barrier _ W M hshift
        (K*‖L j‖₊) hcell (a j)
      refine ⟨hsm,⟨C+D,add_nonneg hC hD,?_⟩,?_⟩
      · intro w hw
        change |gaussianShiftColeHopf _ _ _ w|≤_
        linarith [hb w hw,hv w hw]
      · intro w hw z
        exact gaussianShiftColeHopf_directional_lipschitz_normed _ W M finiteCascadeAmplitudeNoiseShift
          hshift (finiteCascadeAmplitudeDomain_noise_invariant R)
          (K*‖L j‖₊) K hcell hnoise (a j) (ha j) w hw z

theorem contDiff_finiteGaussianAmplitudeCascade (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A B : G→L[ℝ]FiniteStateField S) (L : ℕ→Field n→L[ℝ]G) (j : ℕ) :
    ContDiff ℝ ∞ (finiteGaussianAmplitudeCascade a A B L j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  let R : ℝ≥0 := ⟨|w.1|+1,by positivity⟩
  have hw : w∈finiteCascadeAmplitudeDomain R := by
    change |w.1| < |w.1|+1
    linarith
  exact (finiteGaussianAmplitudeCascade_regular a ha A B L R j).1.smooth w hw

theorem finiteGaussianAmplitudeCascade_eq_actual (a : ℕ→ℝ)
    (A B : G→L[ℝ]FiniteStateField S) (L : ℕ→Field n→L[ℝ]G)
    (j : ℕ) (w : FiniteCascadeAmplitudeState G S) :
    finiteGaussianAmplitudeCascade a A B L j w =
      finiteStateGaussianTerminalCascade (fun _ : S=>0) a
        (fun p => A.comp (L p)+w.1 • B.comp (L p)) j (finiteCascadeAmplitudeField A B w) := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih =>
      let F := finiteGaussianAmplitudeCascade a A B L j
      let M := (finiteCascadeAmplitudeNoiseShift (G:=G) (S:=S)).comp (L j)
      let Q := fun p => A.comp (L p)+w.1 • B.comp (L p)
      have he (z : Field n) : F (w+M z)=
          finiteStateGaussianTerminalCascade (fun _ : S=>0) a Q j
            (finiteCascadeAmplitudeField A B w+Q j z) := by
        dsimp only [F]
        rw [ih]
        have hp : (w+M z).1=w.1 := by simp [M,finiteCascadeAmplitudeNoiseShift]
        rw [hp]
        rw [show M z=finiteCascadeAmplitudeNoiseShift (L j z) from rfl,
          finiteCascadeAmplitudeField_noise_shift]
        rfl
      change gaussianShiftColeHopf M (a j) F w =
        finiteStateGaussianStep (a j) (Q j)
          (finiteStateGaussianTerminalCascade (fun _ : S=>0) a Q j) (finiteCascadeAmplitudeField A B w)
      unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition finiteStateGaussianStep
        OverlapPaper.sourceLogAverage
      rw [fieldGaussian_eq_stdGaussian]
      simp_rw [he]

end QuantitativeFollowup
