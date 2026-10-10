module
public import QuantitativeFollowup.FollowupCavityPathNumeratorRegularity
public import QuantitativeFollowup.FollowupCavityNodeBFieldDerivative

@[expose] public section

/-! The parameter part of the physical path-variance generator is the
actual finite covariance response at every charged retained vertex. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2200000
variable {n k : ℕ}

def cavityPathParameterCharge (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (y : CavityPathGaussianSpace T n) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
    c.1*cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s c.2.depth
      (cavityPathVertexField D s i T c.2 y) (cavityCoordinateFeature i))).sum

private theorem hasDerivAt_weighted_list {A : Type} (cs : List (ℝ×A)) (f d : A→ℝ→ℝ)
    (b : ℝ) (hf : ∀c,HasDerivAt (f c) (d c b) b) :
    HasDerivAt (fun u=>(cs.map (fun c=>c.1*f c.2 u)).sum)
      ((cs.map (fun c=>c.1*d c.2 b)).sum) b := by
  induction cs with
  | nil => exact hasDerivAt_const b 0
  | cons c cs ih =>
    convert! ((hf c.2).const_mul c.1).add ih using 1 <;>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply]

theorem hasDerivAt_cavityPathLogNumerator_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) (y : CavityPathGaussianSpace T n) :
    HasDerivAt (fun u=>cavityPathLogNumerator D s a i T σ (u,y))
      (-cavityPathParameterCharge D s a i T b y) b := by
  have hh:=hasDerivAt_weighted_list (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T)
    (fun v u=>cavityPathVertexPotential D s i T v (u,y))
    (fun v u=>cavityFiniteNodeBResponse (anisotropicReplaceVariance D i u) s v.depth
      (cavityPathVertexField D s i T v y) (cavityCoordinateFeature i)) b
    (fun v=>hasDerivAt_cavityFinitePotential_variance_field D s i b hb v.depth
      (cavityPathVertexField D s i T v y))
  convert! (hasDerivAt_const b (cavityPathTerminalEnergy D s i T σ y)).sub hh using 1 <;>
    simp only [cavityPathLogNumerator, cavityPathChargePotential, cavityPathParameterCharge,
      zero_sub, Pi.sub_apply]

theorem fderiv_cavityPathLogNumerator_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b)
    (y : CavityPathGaussianSpace T n) :
    fderiv ℝ (cavityPathLogNumerator D s a i T σ) (b,y) (1,0)=
      -cavityPathParameterCharge D s a i T b y := by
  have hs:=exponentialSmoothOn_cavityPathLogNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
  have hh:=(hs.smooth (b,y) ⟨⟨by linarith,by linarith⟩,mem_univ y⟩).differentiableAt (by simp)
  have hd:=hh.hasFDerivAt.comp_hasDerivAt b ((hasDerivAt_id b).prodMk (hasDerivAt_const b y))
  exact hd.unique (hasDerivAt_cavityPathLogNumerator_parameter D s a i T σ b hb y)

theorem fderiv_cavityPathNumerator_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b)
    (y : CavityPathGaussianSpace T n) :
    fderiv ℝ (cavityPathNumerator D s a i T σ) (b,y) (1,0)=
      -cavityPathNumerator D s a i T σ (b,y)*cavityPathParameterCharge D s a i T b y := by
  have hs:=exponentialSmoothOn_cavityPathLogNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
  have hh:=(hs.smooth (b,y) ⟨⟨by linarith,by linarith⟩,mem_univ y⟩).differentiableAt (by simp)
  unfold cavityPathNumerator
  rw [hh.hasFDerivAt.exp.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [fderiv_cavityPathLogNumerator_parameter D s a i T hj σ b hb y]
  change Real.exp _ * (-cavityPathParameterCharge D s a i T b y)=_
  ring

end QuantitativeFollowup
