module
public import QuantitativePaper.VariableGaussianShiftJets
public import QuantitativePaper.LocalSmoothIntegral

@[expose] public section

/-! Joint smoothness of a genuine Gaussian average with variable positive
variance, from actual local exponential derivative bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

 theorem variableGaussianAverage_contDiffOn (N : ℕ) (f : G→ℝ) (U : Set G) (hU : IsOpen U)
    (hf : ∀ x∈U,ContDiffAt ℝ ∞ f x) (B : (ℝ×E)→L[ℝ]G) (A : Field n→L[ℝ]G)
    (l : ℝ→ℝ) (V : Set ℝ) (hV : IsOpen V) (hl : ∀ q∈V,ContDiffAt ℝ ∞ l q)
    (W : Set (ℝ×E)) (hW : IsOpen W) (a b : ℝ) (hv : Icc a b⊆V)
    (htime : ∀ x∈W,x.1∈Icc a b)
    (hshift : ∀ x∈W,∀ z,variableGaussianEvaluation B A l z x∈U)
    (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ j,j ≤ N→∀ x∈U,‖iteratedFDeriv ℝ j f x‖ ≤ K*Real.exp (D*‖x‖)) :
    ContDiffOn ℝ N (fun x : ℝ×E=>∫ z,f (variableGaussianEvaluation B A l z x) ∂fieldGaussian n) W := by
  have hLam : ContDiffOn ℝ N l V:=fun q hq=>(hl q hq).of_le (by simp) |>.contDiffWithinAt
  obtain ⟨L,hL,hLjets⟩:=exists_scalar_cylinder_jet_bound (E:=E) N l V hV hLam a b hv
  obtain ⟨M,hM,hMjets⟩:=variableGaussianEvaluation_jet_bound N B A l V hV hLam a b hv
  have hEval (x : ℝ×E) (hx : x∈W) (z : Field n) :
      ContDiffAt ℝ ∞ (variableGaussianEvaluation B A l z) x:=
    variableGaussianEvaluation_smooth B A l x (hl x.1 (hv (htime x hx))) z
  have hSmooth (z : Field n) : ContDiffOn ℝ N (fun x=>f (variableGaussianEvaluation B A l z x)) W:=by
    intro x hx
    exact ((hf _ (hshift x hx z)).comp x (hEval x hx z)).of_le (by simp) |>.contDiffWithinAt
  have hJoint (x : ℝ×E) (hx : x∈W) (z : Field n) :
      ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>
        f (variableGaussianEvaluation B A l w.2 w.1)) (x,z):=by
    have hq : ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>l w.1.1) (x,z):=
      (hl x.1 (hv (htime x hx))).comp (x,z) (contDiff_fst.contDiffAt.comp (x,z) contDiff_fst.contDiffAt)
    have hB : ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>B w.1) (x,z):=
      B.contDiff.contDiffAt.comp (x,z) contDiff_fst.contDiffAt
    have hA : ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>A w.2) (x,z):=
      A.contDiff.contDiffAt.comp (x,z) contDiff_snd.contDiffAt
    exact (hf _ (hshift x hx z)).comp (x,z) (hB.add (hq.smul hA))
  have hm (j : ℕ) (x : ℝ×E) (hx : x∈W) : Continuous
      (fun z=>iteratedFDeriv ℝ j (fun y=>f (variableGaussianEvaluation B A l z y)) x):=by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hJ:=contDiffAt_partial_iteratedFDeriv j
      (fun w : (ℝ×E)×Field n=>f (variableGaussianEvaluation B A l w.2 w.1)) (x,z) (hJoint x hx z)
    exact (ContDiffAt.comp (f := fun w : Field n=>(x,w))
      (g := fun w : (ℝ×E)×Field n=>iteratedFDeriv ℝ j
        (fun y=>f (variableGaussianEvaluation B A l w.2 y)) w.1) z hJ
      (contDiffAt_const.prodMk contDiffAt_id)).continuousAt
  apply contDiffOn_integral_of_dominated_derivatives N (fieldGaussian n) _ W hW hSmooth
    (fun j _ x hx=>(hm j x hx).aestronglyMeasurable)
  intro x hx
  let R:=‖x‖+1
  let J : ℕ→Field n→ℝ:=fun j z=>
    (j.factorial:ℝ)*K*Real.exp (D*‖B‖*R)*M^j*
      Real.exp ((D*L*‖A‖+(j:ℝ))*‖z‖)
  refine ⟨Metric.ball x 1∩W,inter_mem (Metric.ball_mem_nhds x (by norm_num))
    (hW.mem_nhds hx),inter_subset_right,J,?_,?_⟩
  · intro j _
    exact (SYK.integrable_exp_mul_norm (ι:=Fin n) (D*L*‖A‖+(j:ℝ))).const_mul _
  · intro j hj y hy z
    have hyR : ‖y‖ ≤ R:=norm_le_norm_add_const_of_dist_le hy.1.le
    have hLamY : |l y.1| ≤ L:=by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hLjets 0 (Nat.zero_le _) y (htime y hy.2)
    have heval : ‖variableGaussianEvaluation B A l z y‖ ≤ ‖B‖*R+L*‖A‖*‖z‖:=by
      have hn:=norm_add_le (B y) (l y.1 • A z)
      have hny:‖B y‖ ≤ ‖B‖*R:=(B.le_opNorm y).trans (mul_le_mul_of_nonneg_left hyR (norm_nonneg _))
      have hns:‖l y.1 • A z‖ ≤ L*‖A‖*‖z‖:=by
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul hLamY (A.le_opNorm z) (norm_nonneg _) (zero_le_one.trans hL)).trans_eq (by ring)
      exact hn.trans (add_le_add hny hns)
    have hDmap (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
        ‖iteratedFDeriv ℝ i (variableGaussianEvaluation B A l z) y‖ ≤ 
          (M*Real.exp ‖z‖)^i:=by
      have hbase:=hMjets i hi (hij.trans hj) y (htime y hy.2) z
      have he : 1+‖z‖ ≤ Real.exp ‖z‖:=by linarith [Real.add_one_le_exp ‖z‖]
      have hpow : M*Real.exp ‖z‖ ≤ (M*Real.exp ‖z‖)^i:=
        le_self_pow₀ (one_le_mul_of_one_le_of_one_le hM
          (Real.one_le_exp_iff.mpr (norm_nonneg z))) (by omega)
      exact (hbase.trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans hM))).trans hpow
    have hsource (i : ℕ) (hij : i ≤ j) :
        ‖iteratedFDeriv ℝ i f (variableGaussianEvaluation B A l z y)‖ ≤ 
          K*Real.exp (D*(‖B‖*R+L*‖A‖*‖z‖)):=
      (hjets i (hij.trans hj) _ (hshift y hy.2 z)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left heval hD)) hK)
    have hh:=DepthPaper.norm_iteratedFDeriv_comp_le_at
      (hf _ (hshift y hy.2 z)) (hEval y hy.2 z) j
      (K*Real.exp (D*(‖B‖*R+L*‖A‖*‖z‖))) (M*Real.exp ‖z‖) hsource hDmap
    apply hh.trans_eq
    dsimp only [J]
    rw [mul_pow,←Real.exp_nat_mul]
    rw [show D*(‖B‖*R+L*‖A‖*‖z‖)=D*‖B‖*R+D*L*‖A‖*‖z‖ by ring,Real.exp_add]
    rw [show (D*L*‖A‖+(j:ℝ))*‖z‖=D*L*‖A‖*‖z‖+(j:ℝ)*‖z‖ by ring,Real.exp_add]
    ring

end QuantitativePaper
