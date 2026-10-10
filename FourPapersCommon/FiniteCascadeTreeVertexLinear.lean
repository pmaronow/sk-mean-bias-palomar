module
public import FourPapersCommon.FiniteCascadeTreePathCovariance

@[expose] public section

/-! Every charge vertex, including shared fork roots and terminal vertices,
is an actual linear function of the retained independent edge inputs. -/
noncomputable section
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {S I : Type} [Fintype S] [Fintype I]

@[reducible] def finiteCascadeRecordVertexCLM
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → FiniteCascadeRecordVertex T →
      (FiniteStateField S × FiniteStateGaussianInput (GaussianCoordinateIndex I T) →L[ℝ]
        FiniteStateField S)
  | _, _, .root _ => ContinuousLinearMap.fst ℝ _ _
  | _, @FiniteTerminalGenealogy.advance j T, .child v =>
      let hmap := ContinuousLinearMap.fst ℝ (FiniteStateField S) _ +
        (L j).comp (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _))
      (finiteCascadeRecordVertexCLM L T v).comp
        (hmap.prod (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _)))
  | _, .fork T _, .left v => (finiteCascadeRecordVertexCLM L T v).comp
      ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _).prod
        (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _)))
  | _, .fork _ U, .right v => (finiteCascadeRecordVertexCLM L U v).comp
      ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _).prod
        (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _)))

theorem finiteCascadeReference_vertex_field_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T))
    (σ : TerminalSpins S T) :
    v.field H (finiteCascadeTreeReferenceFlatRecord L T H (z,σ)) =
      finiteCascadeRecordVertexCLM L T v (H,z) := by
  induction v generalizing H with
  | root T => rfl
  | @child j T v ih => exact ih (H+L j (finiteGaussianLeft z)) (finiteGaussianRight z) σ
  | left v ih => exact ih H (finiteGaussianLeft z) σ.1
  | right v ih => exact ih H (finiteGaussianRight z) σ.2

theorem finiteCascadeRecordVertexCLM_initial (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) (H : FiniteStateField S) :
    finiteCascadeRecordVertexCLM L T v (H,0)=H := by
  induction v generalizing H with
  | root T => rfl
  | @child j T v ih => simpa [finiteCascadeRecordVertexCLM] using ih H
  | left v ih => simpa [finiteCascadeRecordVertexCLM] using ih H
  | right v ih => simpa [finiteCascadeRecordVertexCLM] using ih H

theorem finiteCascadeRecordVertexCLM_split (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) :
    finiteCascadeRecordVertexCLM L T v (H,z)=H+finiteCascadeRecordVertexCLM L T v (0,z) := by
  have he : (H,z)=(H,0)+(0,z) := by simp
  rw [he,map_add,finiteCascadeRecordVertexCLM_initial]

theorem finiteCascadeRecordVertexCLM_coordinate_scaling
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (c : I → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) :
    finiteCascadeRecordVertexCLM (fun p => (L p).comp (finiteGaussianDiagonal c)) T v (H,z) =
      finiteCascadeRecordVertexCLM L T v
        (H,finiteGaussianDiagonal (finiteCascadeEdgeMultiplier c T) z) := by
  induction v generalizing H with
  | root T => rfl
  | @child j T v ih =>
      change finiteCascadeRecordVertexCLM _ T v
        (H+L j (finiteGaussianDiagonal c (finiteGaussianLeft z)),finiteGaussianRight z)=
          finiteCascadeRecordVertexCLM L T v
            (H+L j (finiteGaussianLeft (finiteGaussianDiagonal
              (Sum.elim c (finiteCascadeEdgeMultiplier c T)) z)),
              finiteGaussianRight (finiteGaussianDiagonal
                (Sum.elim c (finiteCascadeEdgeMultiplier c T)) z))
      rw [finiteGaussianLeft_diagonal,finiteGaussianRight_diagonal,ih]
  | left v ih =>
      change finiteCascadeRecordVertexCLM _ _ v (H,finiteGaussianLeft z)=
        finiteCascadeRecordVertexCLM L _ v
          (H,finiteGaussianLeft (finiteGaussianDiagonal (finiteCascadeEdgeMultiplier c _) z))
      rw [finiteGaussianLeft_diagonal,ih]
  | right v ih =>
      change finiteCascadeRecordVertexCLM _ _ v (H,finiteGaussianRight z)=
        finiteCascadeRecordVertexCLM L _ v
          (H,finiteGaussianRight (finiteGaussianDiagonal (finiteCascadeEdgeMultiplier c _) z))
      rw [finiteGaussianRight_diagonal,ih]

theorem finiteCascadeRecordVertexCLM_rank_one [DecidableEq I]
    (d : ℕ → ℝ) (i : I) (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) :
    finiteCascadeRecordVertexCLM
      (fun p => (d p) • (EuclideanSpace.proj i).smulRight K) T v (H,z) =
      H + (∑e : GaussianCoordinateIndex I T, finiteCascadePathCoefficient d i v e*z e) • K := by
  classical
  induction v generalizing H with
  | root T => simp [finiteCascadeRecordVertexCLM,finiteCascadePathCoefficient]
  | @child j T v ih =>
      change finiteCascadeRecordVertexCLM _ T v
        (H+(d j) • (z (Sum.inl i) • K),finiteGaussianRight z)=_
      rw [smul_smul]
      rw [ih]
      simp only [finiteCascadePathCoefficient,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
      have he : (∑l : I,(if l=i then d j else 0)*z (Sum.inl l))=d j*z (Sum.inl i) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro l _ hli; simp [hli]
        · simp
      rw [he,add_smul]
      exact add_assoc _ _ _
  | left v ih =>
      change finiteCascadeRecordVertexCLM _ _ v (H,finiteGaussianLeft z)=_
      rw [ih]
      simp [finiteCascadePathCoefficient,Fintype.sum_sum_type,finiteGaussianLeft]
  | right v ih =>
      change finiteCascadeRecordVertexCLM _ _ v (H,finiteGaussianRight z)=_
      rw [ih]
      simp [finiteCascadePathCoefficient,Fintype.sum_sum_type,finiteGaussianRight]

end FourPapersCommon
