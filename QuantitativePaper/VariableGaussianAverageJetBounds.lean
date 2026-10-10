module
public import QuantitativePaper.VariableGaussianAverageSmooth
public import QuantitativePaper.LocalSmoothIntegralJets

@[expose] public section

/-! Genuine averaged-jet bounds for a variable-overlap Gaussian integral.
The derivative-integral equality and exponential envelopes are both derived
from local dominated differentiation and true Gaussian norm moments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem variableGaussianAverage_iteratedFDeriv_bound (N : ℕ) (f : G→ℝ) (U : Set G) (hU : IsOpen U)
    (hf : ∀ x ∈ U,ContDiffAt ℝ ∞ f x) (B : (ℝ×E)→L[ℝ]G) (A : Field n→L[ℝ]G)
    (l : ℝ→ℝ) (V : Set ℝ) (hV : IsOpen V) (hl : ∀ q ∈ V,ContDiffAt ℝ ∞ l q)
    (W : Set (ℝ×E)) (hW : IsOpen W) (a b : ℝ) (hv : Icc a b⊆V)
    (htime : ∀ x ∈ W,x.1 ∈ Icc a b)
    (hshift : ∀ x ∈ W,∀ z,variableGaussianEvaluation B A l z x ∈ U)
    (K D : ℝ) (hK : 0  ≤  K) (hD : 0  ≤  D)
    (hjets : ∀ j,j  ≤  N→∀ x ∈ U,‖iteratedFDeriv ℝ j f x‖  ≤  K*Real.exp (D*‖x‖)) :
    ∀ j, j  ≤  N → ∃ C R : ℝ, 0  ≤  C ∧ 0  ≤  R ∧ ∀ x ∈ W,
      iteratedFDeriv ℝ j (fun y : ℝ×E => ∫ z,f (variableGaussianEvaluation B A l z y) ∂fieldGaussian n) x =
        ∫ z,iteratedFDeriv ℝ j (fun y => f (variableGaussianEvaluation B A l z y)) x ∂fieldGaussian n ∧
      ‖iteratedFDeriv ℝ j (fun y : ℝ×E => ∫ z,f (variableGaussianEvaluation B A l z y) ∂fieldGaussian n) x‖  ≤ 
        C*Real.exp (R*‖x‖) := by
  have hLam : ContDiffOn ℝ N l V:=fun q hq=>(hl q hq).of_le (by simp) |>.contDiffWithinAt
  obtain ⟨L,hL,hLjets⟩:=exists_scalar_cylinder_jet_bound (E:=E) N l V hV hLam a b hv
  obtain ⟨M,hM,hMjets⟩:=variableGaussianEvaluation_jet_bound N B A l V hV hLam a b hv
  have hEval (x : ℝ×E) (hx : x ∈ W) (z : Field n) :
      ContDiffAt ℝ ∞ (variableGaussianEvaluation B A l z) x:=
    variableGaussianEvaluation_smooth B A l x (hl x.1 (hv (htime x hx))) z
  have hSmooth (z : Field n) : ContDiffOn ℝ N (fun x=>f (variableGaussianEvaluation B A l z x)) W:=by
    intro x hx
    exact ((hf _ (hshift x hx z)).comp x (hEval x hx z)).of_le (by simp) |>.contDiffWithinAt
  have hJoint (x : ℝ×E) (hx : x ∈ W) (z : Field n) :
      ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>
        f (variableGaussianEvaluation B A l w.2 w.1)) (x,z):=by
    have hq : ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>l w.1.1) (x,z):=
      (hl x.1 (hv (htime x hx))).comp (x,z) (contDiff_fst.contDiffAt.comp (x,z) contDiff_fst.contDiffAt)
    have hB : ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>B w.1) (x,z):=
      B.contDiff.contDiffAt.comp (x,z) contDiff_fst.contDiffAt
    have hA : ContDiffAt ℝ ∞ (fun w : (ℝ×E)×Field n=>A w.2) (x,z):=
      A.contDiff.contDiffAt.comp (x,z) contDiff_snd.contDiffAt
    exact (hf _ (hshift x hx z)).comp (x,z) (hB.add (hq.smul hA))
  have hm (j : ℕ) (x : ℝ×E) (hx : x ∈ W) : Continuous
      (fun z=>iteratedFDeriv ℝ j (fun y=>f (variableGaussianEvaluation B A l z y)) x):=by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hJ:=contDiffAt_partial_iteratedFDeriv j
      (fun w : (ℝ×E)×Field n=>f (variableGaussianEvaluation B A l w.2 w.1)) (x,z) (hJoint x hx z)
    exact (ContDiffAt.comp (f := fun w : Field n=>(x,w))
      (g := fun w : (ℝ×E)×Field n=>iteratedFDeriv ℝ j
        (fun y=>f (variableGaussianEvaluation B A l w.2 y)) w.1) z hJ
      (contDiffAt_const.prodMk contDiffAt_id)).continuousAt
  let J : ℕ→(ℝ×E)→Field n→ℝ := fun j x z =>
    (j.factorial:ℝ)*K*Real.exp (D*‖B‖*‖x‖)*M^j*
      Real.exp ((D*L*‖A‖+(j:ℝ))*‖z‖)
  have hpoint (j : ℕ) (hj : j ≤ N) (x : ℝ×E) (hx : x ∈ W) (z : Field n) :
      ‖iteratedFDeriv ℝ j (fun y => f (variableGaussianEvaluation B A l z y)) x‖  ≤  J j x z := by
    have hLamX : |l x.1|  ≤  L := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        hLjets 0 (Nat.zero_le _) x (htime x hx)
    have heval : ‖variableGaussianEvaluation B A l z x‖  ≤  ‖B‖*‖x‖+L*‖A‖*‖z‖ := by
      have hn := norm_add_le (B x) (l x.1 • A z)
      have hns : ‖l x.1 • A z‖  ≤  L*‖A‖*‖z‖ := by
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul hLamX (A.le_opNorm z) (norm_nonneg _) (zero_le_one.trans hL)).trans_eq (by ring)
      exact hn.trans (add_le_add (B.le_opNorm x) hns)
    have hDmap (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
        ‖iteratedFDeriv ℝ i (variableGaussianEvaluation B A l z) x‖  ≤  (M*Real.exp ‖z‖)^i := by
      have hbase := hMjets i hi (hij.trans hj) x (htime x hx) z
      have he : 1+‖z‖  ≤  Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
      have hpow : M*Real.exp ‖z‖  ≤  (M*Real.exp ‖z‖)^i :=
        le_self_pow₀ (one_le_mul_of_one_le_of_one_le hM
          (Real.one_le_exp_iff.mpr (norm_nonneg z))) (by omega)
      exact (hbase.trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans hM))).trans hpow
    have hsource (i : ℕ) (hij : i ≤ j) :
        ‖iteratedFDeriv ℝ i f (variableGaussianEvaluation B A l z x)‖  ≤ 
          K*Real.exp (D*(‖B‖*‖x‖+L*‖A‖*‖z‖)) :=
      (hjets i (hij.trans hj) _ (hshift x hx z)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left heval hD)) hK)
    have hh := DepthPaper.norm_iteratedFDeriv_comp_le_at
      (hf _ (hshift x hx z)) (hEval x hx z) j
      (K*Real.exp (D*(‖B‖*‖x‖+L*‖A‖*‖z‖))) (M*Real.exp ‖z‖) hsource hDmap
    apply hh.trans_eq
    dsimp only [J]
    rw [mul_pow,←Real.exp_nat_mul]
    rw [show D*(‖B‖*‖x‖+L*‖A‖*‖z‖)=D*‖B‖*‖x‖+D*L*‖A‖*‖z‖ by ring,Real.exp_add]
    rw [show (D*L*‖A‖+(j:ℝ))*‖z‖=D*L*‖A‖*‖z‖+(j:ℝ)*‖z‖ by ring,Real.exp_add]
    ring
  have hi (j : ℕ) (x : ℝ×E) : Integrable (J j x) (fieldGaussian n) :=
    (SYK.integrable_exp_mul_norm (ι:=Fin n) (D*L*‖A‖+(j:ℝ))).const_mul _
  have hbound : ∀ x ∈ W,∃ s ∈ 𝓝 x,s⊆W ∧ ∃ H : ℕ→Field n→ℝ,
      (∀ j,j ≤ N → Integrable (H j) (fieldGaussian n)) ∧
      ∀ j,j ≤ N → ∀ y ∈ s,∀ z,
        ‖iteratedFDeriv ℝ j (fun u => f (variableGaussianEvaluation B A l z u)) y‖  ≤  H j z := by
    intro x hx
    let x' : ℝ×E := (‖x‖+1,0)
    refine ⟨Metric.ball x 1∩W,inter_mem (Metric.ball_mem_nhds x (by norm_num))
      (hW.mem_nhds hx),inter_subset_right,(fun j => J j x'),fun j _ => hi j x',?_⟩
    intro j hj y hy z
    refine (hpoint j hj y hy.2 z).trans ?_
    have hn : ‖y‖  ≤  ‖x‖+1 := norm_le_norm_add_const_of_dist_le hy.1.le
    have hxnonneg : 0 ≤ ‖x‖+1 := by positivity
    have hx' : ‖x'‖=‖x‖+1 := by
      change max |‖x‖+1| ‖(0:E)‖ = ‖x‖+1
      rw [abs_of_nonneg hxnonneg,norm_zero,max_eq_left hxnonneg]
    dsimp only [J]
    gcongr
    rw [hx']
    exact hn
  intro j hj
  let c := D*L*‖A‖+(j:ℝ)
  let C := (j.factorial:ℝ)*K*M^j*(∫ z,Real.exp (c*‖z‖) ∂fieldGaussian n)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hK) (pow_nonneg (zero_le_one.trans hM) _))
      (integral_nonneg (fun z => (Real.exp_pos _).le))
  refine ⟨C,D*‖B‖,hC,mul_nonneg hD (norm_nonneg _),?_⟩
  intro x hx
  have heq := iteratedFDeriv_integral_of_locally_dominated_derivatives N (fieldGaussian n)
    (fun y z => f (variableGaussianEvaluation B A l z y)) W hW hSmooth
    (fun j _ x hx => (hm j x hx).aestronglyMeasurable) hbound j hj x hx
  refine ⟨heq,?_⟩
  rw [heq]
  have hnormi : Integrable (fun z =>
      ‖iteratedFDeriv ℝ j (fun y => f (variableGaussianEvaluation B A l z y)) x‖) (fieldGaussian n) :=
    (hi j x).mono' (hm j x hx).norm.aestronglyMeasurable (.of_forall fun z => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hpoint j hj x hx z)
  refine (norm_integral_le_integral_norm _).trans ((integral_mono hnormi (hi j x)
    (hpoint j hj x hx)).trans_eq ?_)
  dsimp only [J,C,c]
  rw [integral_const_mul]
  ring

end QuantitativePaper
