module
public import HexagonPaper.PathHeatTreeBernsteinReconstructionMixedCovariance
public import HexagonPaper.PathHeatSignedGeneratorLimits
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section

/-! Measurability of actual covariance contractions requires only weak
scalar measurability of signed jets. Finite-rank Bernstein contractions
are genuine finite Hessian sums; their pointwise limit is the original
unchanged signed-measure contraction. Auxiliary TV continuity is unused. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators unitInterval BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Θ : Type*} [MeasurableSpace Θ] {L : ℕ}

theorem measurable_signedContraction_mixedKernel
    (M : Θ→SignedMeasure ((Fin L×I)×(Fin L×I)))
    (hM : ∀h k : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedHessian (M θ) h k))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (K : C(Fin L×I,C(Fin L×I,ℝ))) :
    Measurable (fun θ=>signedContraction
      (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W K)) (M θ)) := by
  let kernelN := fun n=>pathHeatTreeKernelBCF L
    (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L K))
  have hfinite (n : ℕ) : Measurable (fun θ=>signedContraction (kernelN n) (M θ)) := by
    have heq : (fun θ=>signedContraction (kernelN n) (M θ))=
        fun θ=>∑p : Fin L×Fin (n+1),∑q : Fin L×Fin (n+1),
          K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2)*
            pathHeatSignedHessian (M θ)
              (pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single p 1)))
              (pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single q 1))) := by
      funext θ
      exact (pathHeatTreeMixedBernstein_signed_covariance_contraction n L δ W K (M θ)).symm
    rw [heq]
    apply Finset.measurable_sum
    intro p hp
    apply Finset.measurable_sum
    intro q hq
    exact (hM _ _).const_mul _
  have hk : Tendsto kernelN atTop
      (𝓝 (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W K))) :=
    (pathHeatTreeKernelBCF L).continuous.continuousAt.tendsto.comp
      (tendsto_pathHeatTreeMixedKernelSample (L:=L) δ W K)
  apply measurable_of_tendsto_metrizable hfinite
  rw [tendsto_pi_nhds]
  intro θ
  exact tendsto_signedContraction kernelN _ (fun _=>M θ) (M θ) (signedTV (M θ))
    (signedTV_nonneg _) (fun _=>le_rfl) hk (by simpa [signedTV] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0)))

theorem measurable_signedContraction_mixedTensor
    (S P : Θ→SignedMeasure (Fin L×I))
    (hS : ∀h : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedScore (S θ) h))
    (hP : ∀h : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedScore (P θ) h))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (K : C(Fin L×I,C(Fin L×I,ℝ))) :
    Measurable (fun θ=>signedContraction
      (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W K))
      (pathHeatSignedTensor (S θ) (P θ))) := by
  apply measurable_signedContraction_mixedKernel _ _ δ W K
  intro h k
  simp only [pathHeatSignedHessian_tensor]
  exact (hS h).mul (hP k)

theorem measurable_pathHeatDensityGenerator_mixedKernel
    (S : Θ→SignedMeasure (Fin L×I)) (M : Θ→SignedMeasure ((Fin L×I)×(Fin L×I)))
    (dotell : Θ→ℝ)
    (hS : ∀h : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedScore (S θ) h))
    (hM : ∀h k : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedHessian (M θ) h k))
    (hdt : Measurable dotell)
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (K : C(Fin L×I,C(Fin L×I,ℝ))) :
    Measurable (fun θ=>pathHeatDensityGenerator
      (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W K))
      (S θ) (M θ) (dotell θ)) := by
  have hm := measurable_signedContraction_mixedKernel M hM δ W K
  have ht := measurable_signedContraction_mixedTensor S S hS hS δ W K
  simp only [pathHeatDensityGenerator,pathHeatDensityDerivativeMeasure,signedContraction_add]
  exact hdt.add ((hm.add ht).const_mul (1/2:ℝ))

theorem measurable_pathHeatObservableGenerator_mixedKernel
    (S P : Θ→SignedMeasure (Fin L×I)) (Q : Θ→SignedMeasure ((Fin L×I)×(Fin L×I)))
    (dotphi : Θ→ℝ)
    (hS : ∀h : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedScore (S θ) h))
    (hP : ∀h : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedScore (P θ) h))
    (hQ : ∀h k : C(Fin L×I,ℝ),Measurable (fun θ=>pathHeatSignedHessian (Q θ) h k))
    (hdt : Measurable dotphi)
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (K : C(Fin L×I,C(Fin L×I,ℝ))) :
    Measurable (fun θ=>pathHeatObservableGenerator
      (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W K))
      (S θ) (P θ) (Q θ) (dotphi θ)) := by
  have hq := measurable_signedContraction_mixedKernel Q hQ δ W K
  have hsp := measurable_signedContraction_mixedTensor S P hS hP δ W K
  have hps := measurable_signedContraction_mixedTensor P S hP hS δ W K
  simp only [pathHeatObservableGenerator,pathHeatObservableDerivativeMeasure,signedContraction_add]
  exact hdt.add (((hq.add hsp).add hps).const_mul (1/2:ℝ))

end HexagonPaper
