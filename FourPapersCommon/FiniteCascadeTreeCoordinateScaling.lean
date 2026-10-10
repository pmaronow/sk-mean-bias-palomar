module
public import FourPapersCommon.FiniteCascadeTreeReferenceSpins

@[expose] public section

/-! Exact scaling of every independent edge coordinate in the genuine
finite-tree reference realization. Root disorder is retained unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]

def finiteGaussianDiagonal {A : Type} [Fintype A] (c : A → ℝ) :
    FiniteStateGaussianInput A →L[ℝ] FiniteStateGaussianInput A :=
  LinearMap.toContinuousLinearMap
    {toFun := fun z => WithLp.toLp 2 (fun i => c i*z i)
     map_add' := by intro x y; ext i; simp [mul_add]
     map_smul' := by intro r x; ext i; simp; ring}

@[simp] theorem finiteGaussianDiagonal_apply {A : Type} [Fintype A]
    (c : A → ℝ) (z : FiniteStateGaussianInput A) (i : A) :
    finiteGaussianDiagonal c z i = c i*z i := rfl

theorem finiteGaussianDiagonal_single {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (i : A) :
    finiteGaussianDiagonal c (EuclideanSpace.single i 1) =
      c i • EuclideanSpace.single i 1 := by
  classical
  ext l
  by_cases hl : l=i <;> simp [finiteGaussianDiagonal_apply,hl]

theorem finiteStateCLM_eq_of_single {A E : Type} [Fintype A] [DecidableEq A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : FiniteStateGaussianInput A →L[ℝ] E)
    (h : ∀i,L (EuclideanSpace.single i 1)=M (EuclideanSpace.single i 1)) : L=M := by
  classical
  ext z
  have hz : z=∑i : A,z i • EuclideanSpace.single i 1 := by
    ext i; simp [Pi.single_apply]
  rw [hz]
  simp only [map_sum,map_smul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => z i • x) (h i))

@[reducible] def finiteCascadeEdgeMultiplier (c : I → ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → GaussianCoordinateIndex I T → ℝ
  | _, .leaf => Empty.elim
  | _, .advance T => Sum.elim c (finiteCascadeEdgeMultiplier c T)
  | _, .fork T U => Sum.elim (finiteCascadeEdgeMultiplier c T) (finiteCascadeEdgeMultiplier c U)

theorem finiteGaussianLeft_diagonal {A B : Type} [Fintype A] [Fintype B]
    (c : A → ℝ) (d : B → ℝ) (z : FiniteStateGaussianInput (A ⊕ B)) :
    finiteGaussianLeft (finiteGaussianDiagonal (Sum.elim c d) z) =
      finiteGaussianDiagonal c (finiteGaussianLeft z) := by ext i; rfl

theorem finiteGaussianRight_diagonal {A B : Type} [Fintype A] [Fintype B]
    (c : A → ℝ) (d : B → ℝ) (z : FiniteStateGaussianInput (A ⊕ B)) :
    finiteGaussianRight (finiteGaussianDiagonal (Sum.elim c d) z) =
      finiteGaussianDiagonal d (finiteGaussianRight z) := by ext i; rfl

theorem finiteCascadeTreeReferenceFlatRecord_coordinate_scaling
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (c : I → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) (σ : TerminalSpins S T) :
    finiteCascadeTreeReferenceFlatRecord (fun p => (L p).comp (finiteGaussianDiagonal c)) T H (z,σ) =
      finiteCascadeTreeReferenceFlatRecord L T H
        (finiteGaussianDiagonal (finiteCascadeEdgeMultiplier c T) z,σ) := by
  induction T generalizing H with
  | leaf => rfl
  | @advance j T ih =>
      change (H + L j (finiteGaussianDiagonal c (finiteGaussianLeft z)),
        finiteCascadeTreeReferenceFlatRecord _ T
          (H + L j (finiteGaussianDiagonal c (finiteGaussianLeft z))) (finiteGaussianRight z,σ)) =
        (H + L j (finiteGaussianLeft (finiteGaussianDiagonal
          (Sum.elim c (finiteCascadeEdgeMultiplier c T)) z)),
        finiteCascadeTreeReferenceFlatRecord L T _
          (finiteGaussianRight (finiteGaussianDiagonal
            (Sum.elim c (finiteCascadeEdgeMultiplier c T)) z),σ))
      rw [finiteGaussianLeft_diagonal,finiteGaussianRight_diagonal,ih]
      rfl
  | fork T U ihT ihU =>
      change (finiteCascadeTreeReferenceFlatRecord _ T H (finiteGaussianLeft z,σ.1),
          finiteCascadeTreeReferenceFlatRecord _ U H (finiteGaussianRight z,σ.2)) =
        (finiteCascadeTreeReferenceFlatRecord L T H
          (finiteGaussianLeft (finiteGaussianDiagonal
            (Sum.elim (finiteCascadeEdgeMultiplier c T) (finiteCascadeEdgeMultiplier c U)) z),σ.1),
        finiteCascadeTreeReferenceFlatRecord L U H
          (finiteGaussianRight (finiteGaussianDiagonal
            (Sum.elim (finiteCascadeEdgeMultiplier c T) (finiteCascadeEdgeMultiplier c U)) z),σ.2))
      rw [finiteGaussianLeft_diagonal,finiteGaussianRight_diagonal,ihT,ihU]

theorem finiteCascadeTreeReferenceRootFlatRecord_coordinate_scaling
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (c : I → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T)) (σ : TerminalSpins S T) :
    finiteCascadeTreeReferenceRootFlatRecord (fun p => (L p).comp (finiteGaussianDiagonal c)) T R H (z,σ) =
      finiteCascadeTreeReferenceRootFlatRecord L T R H
        (finiteGaussianDiagonal (Sum.elim (fun _ : J => 1) (finiteCascadeEdgeMultiplier c T)) z,σ) := by
  unfold finiteCascadeTreeReferenceRootFlatRecord
  dsimp only
  rw [finiteGaussianLeft_diagonal,finiteGaussianRight_diagonal]
  have he : finiteGaussianDiagonal (fun _ : J => (1:ℝ)) (finiteGaussianLeft z) = finiteGaussianLeft z := by
    ext i; simp
  rw [he,finiteCascadeTreeReferenceFlatRecord_coordinate_scaling]

end FourPapersCommon
