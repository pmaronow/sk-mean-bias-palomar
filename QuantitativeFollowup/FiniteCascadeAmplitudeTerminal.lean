module
public import QuantitativeFollowup.ExponentialNormedJetComposition
public import QuantitativePaper.FiniteLinearObservableJets
public import FourPapersCommon.FiniteStateCascadeSmoothJets

@[expose] public section

/-! Fixed-noise amplitude coordinates for genuine finite-state Gaussian
cascades. Only the deterministic amplitude is restricted; fields and all
independent noise coordinates remain unbounded. -/
noncomputable section
open Set
open scoped Topology ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.AT
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {S G : Type} [Fintype S] [Nonempty S]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

abbrev FiniteCascadeAmplitudeState (G S : Type) [Fintype S] :=
  ℝ × (G × FiniteStateField S)

def finiteCascadeAmplitudeDomain (R : ℝ) : Set (FiniteCascadeAmplitudeState G S) :=
  {w | |w.1|<R}

def finiteCascadeAmplitudeNoiseShift : G →L[ℝ] FiniteCascadeAmplitudeState G S :=
  (0 : G →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ G).prod 0)

def finiteCascadeAmplitudeField (A B : G →L[ℝ] FiniteStateField S)
    (w : FiniteCascadeAmplitudeState G S) : FiniteStateField S :=
  w.2.2+A w.2.1+w.1 • B w.2.1

def finiteCascadeAmplitudeTerminal (A B : G →L[ℝ] FiniteStateField S)
    (w : FiniteCascadeAmplitudeState G S) : ℝ :=
  gtStateLogPartition (fun _ : S => 0) (finiteCascadeAmplitudeField A B w)

def finiteCascadeAmplitudeLip (A B : G →L[ℝ] FiniteStateField S) (R : ℝ≥0) : ℝ≥0 :=
  1+‖A‖₊+R*‖B‖₊

theorem finiteCascadeAmplitudeDomain_open (R : ℝ) :
    IsOpen (finiteCascadeAmplitudeDomain (G:=G) (S:=S) R) :=
  isOpen_lt (continuous_abs.comp continuous_fst) continuous_const

theorem finiteCascadeAmplitudeDomain_noise_invariant (R : ℝ)
    (w : FiniteCascadeAmplitudeState G S) (hw : w∈finiteCascadeAmplitudeDomain R) (z : G) :
    w+finiteCascadeAmplitudeNoiseShift z∈finiteCascadeAmplitudeDomain R := by
  simpa [finiteCascadeAmplitudeDomain,finiteCascadeAmplitudeNoiseShift] using hw

theorem finiteCascadeAmplitudeField_noise_shift (A B : G →L[ℝ] FiniteStateField S)
    (w : FiniteCascadeAmplitudeState G S) (z : G) :
    finiteCascadeAmplitudeField A B (w+finiteCascadeAmplitudeNoiseShift z)=
      finiteCascadeAmplitudeField A B w+(A z+w.1 • B z) := by
  simp only [finiteCascadeAmplitudeField,finiteCascadeAmplitudeNoiseShift,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,
    Prod.fst_add,Prod.snd_add,add_zero,map_add,smul_add]
  abel

theorem norm_finiteCascadeAmplitudeField_le (A B : G →L[ℝ] FiniteStateField S)
    (R : ℝ≥0) (w : FiniteCascadeAmplitudeState G S) (hw : w∈finiteCascadeAmplitudeDomain R) :
    ‖finiteCascadeAmplitudeField A B w‖ ≤ finiteCascadeAmplitudeLip A B R*‖w‖ := by
  have hz : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have hh : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have hr : |w.1| ≤ R := hw.le
  have ha := (A.le_opNorm w.2.1).trans
    (mul_le_mul_of_nonneg_left hz (norm_nonneg A))
  have hb := (B.le_opNorm w.2.1).trans
    (mul_le_mul_of_nonneg_left hz (norm_nonneg B))
  have hs : ‖w.1 • B w.2.1‖ ≤ (R:ℝ)*‖B‖*‖w‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hr hb (norm_nonneg _) R.coe_nonneg).trans_eq (by ring)
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))).trans
  change _≤((1:ℝ)+‖A‖+(R:ℝ)*‖B‖)*‖w‖
  nlinarith only [ha,hh,hs]

theorem exponentialSmoothOn_finiteCascadeAmplitudeField (A B : G →L[ℝ] FiniteStateField S)
    (R : ℝ) : ExponentialSmoothOn (finiteCascadeAmplitudeField A B)
      (finiteCascadeAmplitudeDomain R) := by
  let U : Set (FiniteCascadeAmplitudeState G S) := finiteCascadeAmplitudeDomain R
  let Z := (ContinuousLinearMap.fst ℝ G (FiniteStateField S)).comp
    (ContinuousLinearMap.snd ℝ ℝ (G×FiniteStateField S))
  have hh := exponentialSmoothOn_linear ((ContinuousLinearMap.snd ℝ G (FiniteStateField S)).comp
    (ContinuousLinearMap.snd ℝ ℝ (G×FiniteStateField S))) U
  have ha := exponentialSmoothOn_linear (A.comp Z) U
  have hb := exponentialSmoothOn_linear (B.comp Z) U
  have hr := exponentialSmoothOn_linear (ContinuousLinearMap.fst ℝ ℝ (G×FiniteStateField S)) U
  have hs := hr.bilinear hb
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ→L[ℝ]FiniteStateField S→L[ℝ]FiniteStateField S)
  exact (hh.add ha).add hs

theorem boundedPositiveJets_finiteStateTerminal_zero :
    BoundedPositiveJets (gtStateLogPartition (fun _ : S => 0)) := by
  have he : gtStateLogPartition (fun _ : S => 0)=
      finiteLinearSoftmax (fun σ : S => EuclideanSpace.proj σ) := by
    funext H
    simp only [gtStateLogPartition,gtStatePartition,finiteLinearSoftmax,finiteLinearPartition,
      EuclideanSpace.coe_proj,add_zero]
  rw [he]
  exact boundedPositiveJets_finiteLinearSoftmax _

theorem finiteStateTerminal_zero_value_bound (H : FiniteStateField S) :
    |gtStateLogPartition (fun _ : S => 0) H| ≤
      |gtStateLogPartition (fun _ : S => 0) 0|+‖H‖ := by
  have hh := (finiteStateGaussianTerminal_lipschitz (fun _ : S => 0)).norm_sub_le H 0
  simp only [NNReal.coe_one,one_mul,sub_zero,Real.norm_eq_abs] at hh
  calc
    _ = |(gtStateLogPartition (fun _ : S => 0) H-
      gtStateLogPartition (fun _ : S => 0) 0)+gtStateLogPartition (fun _ : S => 0) 0| := by
      rw [sub_add_cancel]
    _ ≤ |gtStateLogPartition (fun _ : S => 0) H-gtStateLogPartition (fun _ : S => 0) 0|+
      |gtStateLogPartition (fun _ : S => 0) 0| := abs_add_le _ _
    _ ≤ ‖H‖+|gtStateLogPartition (fun _ : S => 0) 0| := add_le_add hh (le_refl _)
    _ = _ := add_comm _ _

theorem exponentialSmoothOn_finiteCascadeAmplitudeTerminal
    (A B : G →L[ℝ] FiniteStateField S) (R : ℝ≥0) :
    ExponentialSmoothOn (finiteCascadeAmplitudeTerminal A B) (finiteCascadeAmplitudeDomain R) := by
  exact exponentialSmoothOn_comp_boundedPositiveJets_normed
    _ boundedPositiveJets_finiteStateTerminal_zero
    |gtStateLogPartition (fun _ : S => 0) 0| 1 (abs_nonneg _) zero_le_one
    (fun y => by simpa only [one_mul] using finiteStateTerminal_zero_value_bound y)
    _ _ (exponentialSmoothOn_finiteCascadeAmplitudeField A B R)
    0 (finiteCascadeAmplitudeLip A B R) le_rfl (NNReal.coe_nonneg _)
    (fun w hw => by simpa only [zero_add] using norm_finiteCascadeAmplitudeField_le A B R w hw)

theorem finiteCascadeAmplitudeTerminal_value_bound (A B : G →L[ℝ] FiniteStateField S)
    (R : ℝ≥0) (w : FiniteCascadeAmplitudeState G S) (hw : w∈finiteCascadeAmplitudeDomain R) :
    |finiteCascadeAmplitudeTerminal A B w| ≤ |gtStateLogPartition (fun _ : S => 0) 0|+
      finiteCascadeAmplitudeLip A B R*‖w‖ :=
  (finiteStateTerminal_zero_value_bound _).trans (add_le_add (le_refl _)
    (norm_finiteCascadeAmplitudeField_le A B R w hw))

theorem finiteCascadeAmplitudeTerminal_noise_lipschitz (A B : G →L[ℝ] FiniteStateField S)
    (R : ℝ≥0) (w : FiniteCascadeAmplitudeState G S) (hw : w∈finiteCascadeAmplitudeDomain R) (z : G) :
    |finiteCascadeAmplitudeTerminal A B (w+finiteCascadeAmplitudeNoiseShift z)-
      finiteCascadeAmplitudeTerminal A B w| ≤ finiteCascadeAmplitudeLip A B R*‖z‖ := by
  have hh := (finiteStateGaussianTerminal_lipschitz (fun _ : S => 0)).norm_sub_le
    (finiteCascadeAmplitudeField A B (w+finiteCascadeAmplitudeNoiseShift z)) (finiteCascadeAmplitudeField A B w)
  simp only [NNReal.coe_one,one_mul,Real.norm_eq_abs,finiteCascadeAmplitudeField_noise_shift,
    add_sub_cancel_left] at hh
  simp only [finiteCascadeAmplitudeTerminal,finiteCascadeAmplitudeField_noise_shift]
  apply hh.trans
  have hn := norm_add_le (A z) (w.1 • B z)
  rw [norm_smul,Real.norm_eq_abs] at hn
  have hr : |w.1| ≤ R := hw.le
  have hs := mul_le_mul hr (B.le_opNorm z) (norm_nonneg _) R.coe_nonneg
  change ‖A z+w.1 • B z‖≤((1:ℝ)+‖A‖+(R:ℝ)*‖B‖)*‖z‖
  nlinarith only [hn,hs,A.le_opNorm z,norm_nonneg z]

end QuantitativeFollowup
