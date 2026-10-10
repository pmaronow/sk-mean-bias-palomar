module
public import QuantitativeFollowup.AnisotropicProcessEnergy

@[expose] public section

/-! Genuine unit-coupling coordinates expose every spin-pair feature even
when the original deterministic Gaussian coupling scale vanishes. The
potential and terminal posterior are transported by an explicit linear map. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def anisotropicUnitCouplings (D : AnisotropicSpinModel n) : AnisotropicSpinModel n where
  variance:=D.variance
  variance_pos:=D.variance_pos
  coupling:=fun _=>1

def anisotropicCouplingRescaling (D : AnisotropicSpinModel n) :
    AnisotropicParameter n→L[ℝ]AnisotropicParameter n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun P=>WithLp.toLp 2 (Sum.elim (fun e=>D.coupling e*P (Sum.inl e)) (fun i=>P (Sum.inr i)))
      map_add':=by intro P Q;ext i;cases i <;> simp [mul_add]
      map_smul':=by intro c P;ext i;cases i <;> simp [mul_left_comm] }

theorem anisotropicCouplingRescaling_field (D : AnisotropicSpinModel n) (x : Field n) :
    anisotropicCouplingRescaling D (anisotropicFieldInjection n x)=anisotropicFieldInjection n x := by
  ext i
  cases i <;> simp [anisotropicCouplingRescaling,anisotropicFieldInjection]

theorem anisotropicEnergyMap_unitCouplings (D : AnisotropicSpinModel n) (P : AnisotropicParameter n) :
    anisotropicEnergyMap (anisotropicUnitCouplings D) (anisotropicCouplingRescaling D P)=anisotropicEnergyMap D P := by
  ext σ
  simp only [anisotropicEnergyMap_apply,anisotropicTerminalLinear,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change (∑e : AnisotropicCouplingIndex n,
    1*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)*(D.coupling e*P (Sum.inl e)))+
    (∑i : Fin n,Paper.spinSign (σ i)*P (Sum.inr i))=_
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  change 1*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)*(D.coupling e*P (Sum.inl e))=
    D.coupling e*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)*P (Sum.inl e)
  ring

theorem anisotropicEnergyInputs_unitCouplings (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    (anisotropicEnergyMap (anisotropicUnitCouplings D)).comp (anisotropicSchemeInput (anisotropicUnitCouplings D) s j)=
      (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j) := by
  ext z σ
  simp only [ContinuousLinearMap.comp_apply,anisotropicSchemeInput_apply,anisotropicEnergyMap_field]
  rfl

theorem anisotropicFinitePotential_unitCouplings (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) :
    anisotropicFinitePotential (anisotropicUnitCouplings D) s j (anisotropicCouplingRescaling D P)=
      anisotropicFinitePotential D s j P := by
  unfold anisotropicFinitePotential
  rw [show (fun l=>(anisotropicEnergyMap (anisotropicUnitCouplings D)).comp
      (anisotropicSchemeInput (anisotropicUnitCouplings D) s l))=
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) from
        funext (anisotropicEnergyInputs_unitCouplings D s)]
  rw [anisotropicEnergyMap_unitCouplings]

theorem anisotropicFiniteSpinKernel_unitCouplings (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) :
    anisotropicFiniteSpinKernel (anisotropicUnitCouplings D) s j (anisotropicCouplingRescaling D P)=
      anisotropicFiniteSpinKernel D s j P := by
  simp only [anisotropicFiniteSpinKernel,Kernel.comap_apply]
  rw [show (fun l=>(anisotropicEnergyMap (anisotropicUnitCouplings D)).comp
      (anisotropicSchemeInput (anisotropicUnitCouplings D) s l))=
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) from
        funext (anisotropicEnergyInputs_unitCouplings D s)]
  rw [anisotropicEnergyMap_unitCouplings]

def anisotropicCouplingDirection (e : AnisotropicCouplingIndex n) : AnisotropicParameter n :=
  EuclideanSpace.single (Sum.inl e) 1

theorem anisotropicTerminalLinear_unitCoupling (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (σ : Configuration n) :
    anisotropicTerminalLinear (anisotropicUnitCouplings D) σ (anisotropicCouplingDirection e)=
      Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2) := by
  classical
  simp [anisotropicTerminalLinear,anisotropicCouplingDirection,EuclideanSpace.single_apply,
    anisotropicUnitCouplings]

theorem anisotropicFinitePairMean_unitCoupling (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (anisotropicFinitePotential (anisotropicUnitCouplings D) s j)
      (anisotropicCouplingRescaling D P) (anisotropicCouplingDirection e)=
      ∫σ,Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2) ∂anisotropicFiniteSpinKernel D s j P := by
  rw [fderiv_anisotropicFinitePotential,anisotropicFiniteSpinKernel_unitCouplings]
  simp_rw [anisotropicTerminalLinear_unitCoupling]

end QuantitativeFollowup
