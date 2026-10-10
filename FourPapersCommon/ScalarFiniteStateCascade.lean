module
public import FourPapersCommon.QuadraticMixture
public import FourPapersCommon.FiniteStateCascadeLinearTransport
public import OverlapPaper.ReplicaSourceChronologicalBaseline

@[expose] public section

/-! The actual one-spin finite Gaussian cascade is the actual scalar Parisi
solution for its finite overlap probability law. This bridge uses the literal
spin terminal partition function and includes repeated overlap levels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1600000

def scalarSpinPotential (h : ℝ) (ε : Configuration 1) : ℝ :=
  h*∑l : Fin 1,spin (ε l)

def scalarSchemeMass {k : ℕ} (s : RSBScheme k) (j : ℕ) : ℝ := s.m (k+1-j)

def scalarSchemeVariance {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) : ℝ :=
  β^2*(s.q (k+2-j)-s.q (k+1-j))

def scalarSchemeSpinInput {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    FiniteStateGaussianInput (Fin 1)→L[ℝ]FiniteStateField (Configuration 1) :=
  (replicaSingleSiteSpinCLM (d:=1)).comp
    (replicaSiteCopyGaussianCLM (scalarSchemeVariance s β j) (id : Fin 1→Fin 1))

theorem scalarSchemeMass_nonneg {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    0 ≤ scalarSchemeMass s j := s.m_nonneg (Nat.sub_le _ _)

/-- The complete finite cascade is literally the selected finite-measure PDE
potential. Its additive log(2) is the one-spin partition normalization. -/
theorem scalarGaussianTerminalCascade_scheme {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (j : ℕ) (hj : j≤k+2)
    (H : FiniteStateField (Fin 1)) :
    finiteStateGaussianTerminalCascade (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) j (replicaSingleSiteSpinCLM H) =
      Real.log 2+Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-j),h+H 0) := by
  classical
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  let L:=fun i=>replicaSiteCopyGaussianCLM (scalarSchemeVariance s β i) (id : Fin 1→Fin 1)
  have hF : (fun y=>gtStateLogPartition (scalarSpinPotential h) (replicaSingleSiteSpinCLM y))=
      replicaSourceSingleSite h 0 (∅ : Finset (Fin 1)) := by
    funext y
    rw [replicaSourceSingleSite_eq_terminal]
    simp only [zero_mul,add_zero]
    rfl
  change finiteStateGaussianCascade (scalarSchemeMass s)
    (fun i=>(replicaSingleSiteSpinCLM (d:=1)).comp (L i))
    (gtStateLogPartition (scalarSpinPotential h)) j (replicaSingleSiteSpinCLM H)=_
  rw [finiteStateGaussianCascade_comp_linear,hF]
  have hcomp (i : ℕ) (_ : i<k+2) :
      ∃ b : ℕ,∃ group : Fin 1→Fin b,∃ rep : Fin b→Fin 1,
        (∀q,group (rep q)=q) ∧
        (∀q,(Finset.univ.filter (fun l=>group l=q)).card=1) ∧
        (∀l m,(id : Fin 1→Fin 1) l=id m↔group l=group m) := by
    refine ⟨1,id,id,fun _=>rfl,?_,fun _ _=>Iff.rfl⟩
    intro q
    have hq : q=0 := Subsingleton.elim _ _
    rw [hq]
    decide
  have he:=replicaSourceSiteCascade_baseline ξ s h (∅ : Finset (Fin 1))
    (fun _=>id) (fun _=>1) (fun _ _=>by norm_num) hcomp
    (fun _ _ _ _ he=>he) j hj H (fun _ _ he=>congrArg H he)
  have hL : (fun i=>replicaSiteCopyGaussianCLM
      (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i))) (id : Fin 1→Fin 1))=L := by
    funext i
    dsimp only [L,scalarSchemeVariance,ξ]
    simp only [AdmissibleEvenMixture.quadratic_first]
    congr 1
    ring
  rw [hL] at he
  simp only [div_one,Nat.cast_one,one_mul,Fin.sum_univ_one] at he
  change finiteStateGaussianCascade (fun i=>s.m (k+1-i)) L
    (replicaSourceSingleSite h 0 (∅ : Finset (Fin 1))) j H=_
  simpa only [ξ,mixedPotential_quadratic,Real.sqrt_sq_eq_abs,abs_of_pos hβ] using he

end FourPapersCommon
