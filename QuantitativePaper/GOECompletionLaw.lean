module
public import QuantitativePaper.GOECompletionMatrix
public import FourPapersCommon.GaussianAbsoluteMoment

@[expose] public section

/-! The independent GOE diagonal entries compress to the actual common
completion Gaussian with variance exactly one half. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology RealInnerProductSpace
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1000000

def goeRawLaw (n : ℕ) : Measure (Couplings n×(Fin n→ℝ)) :=
  (couplingLaw n).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 1))

instance goeRawLaw_probability (n : ℕ) : IsProbabilityMeasure (goeRawLaw n) := by
  unfold goeRawLaw
  infer_instance

def goeDiagonalVector (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _=>Real.sqrt (2/(n : ℝ))/2)

theorem goeDiagonalVector_norm_sq (n : ℕ) (hn : 0 < n) :
    ‖goeDiagonalVector n‖^2=(1/2 : ℝ) := by
  have hN : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [goeDiagonalVector,WithLp.ofLp_toLp,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,div_pow]
  rw [Real.sq_sqrt (show 0 ≤ 2/(n : ℝ) by positivity)]
  field_simp
  <;> ring

theorem goeDiagonalTrace_inner (n : ℕ) (p : Couplings n×(Fin n→ℝ)) :
    goeDiagonalTrace n p=inner ℝ (goeDiagonalVector n) (WithLp.toLp 2 p.2) := by
  rw [goeDiagonalTrace_eq]
  simp only [PiLp.inner_apply,goeDiagonalVector,WithLp.ofLp_toLp,Real.inner_apply,
    ←Finset.mul_sum]

 theorem goeDiagonalTrace_gaussian_map (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n=>gaussianReal 0 1)).map
      (fun z=>Real.sqrt (2/(n : ℝ))/2*(∑i,z i))=gaussianReal 0 (1/2) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (goeDiagonalVector n)
  have hLaw := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian (EuclideanSpace ℝ (Fin n)))).map L
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L=
      gaussianReal 0 (‖L‖^2).toNNReal := by
    simpa only [Function.comp_def,id_eq,integral_strongDual_stdGaussian,
      variance_dual_stdGaussian] using hLaw.map_eq_gaussianReal
  have hnL : ‖L‖^2=(1/2 : ℝ) := by
    rw [show ‖L‖=‖goeDiagonalVector n‖ from
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).norm_map _]
    exact goeDiagonalVector_norm_sq n hn
  rw [hnL] at hm
  have hhalf : ((1/2 : ℝ).toNNReal : ℝ≥0)=(1/2 : ℝ≥0) := by
    ext
    norm_num
  rw [hhalf] at hm
  have hs : stdGaussian (EuclideanSpace ℝ (Fin n))=
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 1)).map (WithLp.toLp 2) := by
    exact (map_pi_eq_stdGaussian (ι:=Fin n)).symm
  rw [hs,Measure.map_map L.continuous.measurable (by fun_prop)] at hm
  simpa only [L,Function.comp_def,InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply,goeDiagonalVector,WithLp.ofLp_toLp,Real.inner_apply,
    ←Finset.mul_sum] using hm

 theorem measurable_goeDiagonalTrace (n : ℕ) : Measurable (goeDiagonalTrace n) := by
  have he : goeDiagonalTrace n=(fun p=>Real.sqrt (2/(n : ℝ))/2*(∑i,p.2 i)) :=
    funext (goeDiagonalTrace_eq n)
  rw [he]
  fun_prop

def goeCompression (n : ℕ) (p : Couplings n×(Fin n→ℝ)) : Couplings n×ℝ :=
  (p.1,goeDiagonalTrace n p)

 theorem measurable_goeCompression (n : ℕ) : Measurable (goeCompression n) :=
  measurable_fst.prodMk (measurable_goeDiagonalTrace n)

 theorem goeRawLaw_compression (n : ℕ) (hn : 0 < n) :
    (goeRawLaw n).map (goeCompression n)=completionLaw n := by
  have hD : Measurable (fun z : Fin n→ℝ=>Real.sqrt (2/(n : ℝ))/2*(∑i,z i)) := by fun_prop
  have he : goeCompression n=Prod.map id
      (fun z : Fin n→ℝ=>Real.sqrt (2/(n : ℝ))/2*(∑i,z i)) := by
    funext p
    change (p.1,goeDiagonalTrace n p)=(p.1,Real.sqrt (2/(n : ℝ))/2*(∑i,p.2 i))
    rw [goeDiagonalTrace_eq]
  rw [goeRawLaw,he,←Measure.map_prod_map _ _ measurable_id hD,
    Measure.map_id,goeDiagonalTrace_gaussian_map n hn]
  rfl

 theorem hasLaw_goeDiagonalTrace (n : ℕ) (hn : 0 < n) :
    HasLaw (goeDiagonalTrace n) (gaussianReal 0 (1/2)) (goeRawLaw n) := by
  have hh : HasLaw (goeCompression n) (completionLaw n) (goeRawLaw n) :=
    ⟨(measurable_goeCompression n).aemeasurable,goeRawLaw_compression n hn⟩
  simpa only [Function.comp_def,goeCompression] using
    (measurePreserving_snd (μ:=couplingLaw n) (ν:=gaussianReal 0 (1/2))).hasLaw.comp hh

 theorem indep_goeLogPartition_diagonalTrace (n : ℕ) (β : ℝ) :
    IndepFun (fun p : Couplings n×(Fin n→ℝ)=>logPartition n β p.1)
      (goeDiagonalTrace n) (goeRawLaw n) := by
  have hd : Measurable (fun z : Fin n→ℝ=>Real.sqrt (2/(n : ℝ))/2*(∑i,z i)) := by fun_prop
  have he : goeDiagonalTrace n=(fun p=>Real.sqrt (2/(n : ℝ))/2*(∑i,p.2 i)) :=
    funext (goeDiagonalTrace_eq n)
  rw [he,goeRawLaw]
  exact
    (indepFun_prod (X:=logPartition n β)
      (Y:=fun z : Fin n→ℝ=>Real.sqrt (2/(n : ℝ))/2*(∑i,z i))
      (continuous_logPartition n β).measurable hd
      (μ:=couplingLaw n) (ν:=Measure.pi (fun _ : Fin n=>gaussianReal 0 1)))

 theorem goeCompletedLogPartition_eq_compressed (n : ℕ) (β : ℝ)
    (p : Couplings n×(Fin n→ℝ)) :
    goeCompletedLogPartition n β p=completedLogPartition n β (goeCompression n p) := by
  rw [goeCompletedLogPartition_eq]
  rfl

 theorem goeGroundState_eq_compressed (n : ℕ) (p : Couplings n×(Fin n→ℝ)) :
    goeGroundState n p=completedGroundState n (goeCompression n p) := by
  rw [goeGroundState_eq]
  rfl

end QuantitativePaper
