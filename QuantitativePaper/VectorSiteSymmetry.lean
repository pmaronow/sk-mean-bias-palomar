module
public import QuantitativePaper.VectorSpinDiagonalBounds
public import FourPapersCommon.GaussianSignFlips
public import FourPapersCommon.BinaryPrefixMass

@[expose] public section

/-! The genuine single-site spin symmetry of the finite vector recursion.
The incident couplings and the corresponding field coordinate are reflected
together; Gaussian future fields are changed by their actual isometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def siteSign {n:ℕ} (i j:Fin n):ℝ:=if j=i then -1 else 1

theorem abs_siteSign {n:ℕ} (i j:Fin n):|siteSign i j|=1 := by
  simp [siteSign];split_ifs <;> norm_num

def siteFieldReflection {n:ℕ} (i:Fin n):Field n≃ₗᵢ[ℝ]Field n:=
  coordinateSignEquiv (siteSign i) (abs_siteSign i)

@[simp] theorem siteFieldReflection_apply {n:ℕ} (i:Fin n) (x:Field n) (j:Fin n):
    siteFieldReflection i x j=siteSign i j*x j:=rfl

def siteDisorderReflection {n:ℕ} (i:Fin n) (p:Couplings n×ℝ):Couplings n×ℝ:=
  (fun e=>siteSign i e.val.1*siteSign i e.val.2*p.1 e,p.2)

theorem spinSign_flipSpin {n:ℕ} (i j:Fin n) (σ:Configuration n):
    Paper.spinSign (flipSpin i σ j)=siteSign i j*Paper.spinSign (σ j):=by
  by_cases hj:j=i
  · subst j;cases hσ:σ i <;> simp [hσ,siteSign,Paper.spinSign]
  · rw [flipSpin_away i j σ hj]
    simp [siteSign,hj]

theorem energy_site_reflection {n:ℕ} (i:Fin n) (p:Couplings n×ℝ)
    (σ:Configuration n):
    energy n (siteDisorderReflection i p).1 σ=energy n p.1 (flipSpin i σ):=by
  unfold energy Paper.skHamiltonian
  simp only [zero_mul,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  simp only [siteDisorderReflection,spinSign_flipSpin]
  ring

theorem fieldDot_site_reflection {n:ℕ} (i:Fin n) (x:Field n) (σ:Configuration n):
    fieldDot (siteFieldReflection i x) σ=fieldDot x (flipSpin i σ):=by
  unfold fieldDot
  apply Finset.sum_congr rfl
  intro j _
  rw [siteFieldReflection_apply,spinSign_flipSpin]
  ring

theorem vectorTerminalExponent_site_reflection {n:ℕ} (i:Fin n) (β t:ℝ)
    (p:Couplings n×ℝ) (x:Field n) (σ:Configuration n):
    vectorTerminalExponent n β t (siteDisorderReflection i p) (siteFieldReflection i x) σ=
      vectorTerminalExponent n β t p x (flipSpin i σ):=by
  unfold vectorTerminalExponent
  rw [energy_site_reflection,fieldDot_site_reflection]
  rfl

theorem terminalPartition_reindex {n:ℕ} (E:Configuration n→ℝ)
    (e:Configuration n≃Configuration n):terminalPartition (E∘e)=terminalPartition E:=by
  exact e.sum_comp (fun σ=>Real.exp (E σ))

theorem terminalMean_reindex {n:ℕ} (E d:Configuration n→ℝ)
    (e:Configuration n≃Configuration n):
    terminalMean (E∘e) (d∘e)=terminalMean E d:=by
  unfold terminalMean terminalWeight
  rw [terminalPartition_reindex]
  exact e.sum_comp (fun σ=>Real.exp (E σ)/terminalPartition E*d σ)

theorem fieldShift_site_reflection {n:ℕ} (i:Fin n) (c:ℝ) (x z:Field n):
    fieldShift c (siteFieldReflection i x) (siteFieldReflection i z)=
      siteFieldReflection i (fieldShift c x z):=by
  simp only [fieldShift,map_add,map_smul]

theorem integral_siteFieldReflection {n:ℕ} (i:Fin n) (f:Field n→ℝ):
    (∫z,f (siteFieldReflection i z) ∂fieldGaussian n)=∫z,f z ∂fieldGaussian n:=by
  exact (measurePreserving_coordinateSign (siteSign i) (abs_siteSign i)).integral_comp
    (siteFieldReflection i).toHomeomorph.measurableEmbedding f

theorem vectorColeHopfStep_site_reflection {n:ℕ} (i:Fin n) (c m:ℝ)
    (f g:Field n→ℝ) (hfg:∀x,f (siteFieldReflection i x)=g x) (x:Field n):
    vectorColeHopfStep c m f (siteFieldReflection i x)=vectorColeHopfStep c m g x:=by
  have hi (h:ℝ→ℝ):
      (∫z,h (f (fieldShift c (siteFieldReflection i x) z)) ∂fieldGaussian n)=
        ∫z,h (g (fieldShift c x z)) ∂fieldGaussian n:=by
    rw [←integral_siteFieldReflection i (fun z=>h (f (fieldShift c (siteFieldReflection i x) z)))]
    simp_rw [fieldShift_site_reflection,hfg]
  unfold vectorColeHopfStep vectorStepPartition
  split_ifs
  · exact hi id
  · rw [hi (fun a=>Real.exp (m*a))]

theorem vectorStepResponse_site_reflection {n:ℕ} (i:Fin n) (c m:ℝ)
    (f g v w:Field n→ℝ) (hfg:∀x,f (siteFieldReflection i x)=g x)
    (hvw:∀x,v (siteFieldReflection i x)=w x) (x:Field n):
    vectorStepResponse c m f v (siteFieldReflection i x)=vectorStepResponse c m g w x:=by
  have hp:vectorStepPartition c m f (siteFieldReflection i x)=vectorStepPartition c m g x:=by
    unfold vectorStepPartition
    rw [←integral_siteFieldReflection i (fun z=>Real.exp (m*f (fieldShift c (siteFieldReflection i x) z)))]
    simp_rw [fieldShift_site_reflection,hfg]
  unfold vectorStepResponse vectorStepWeight
  rw [hp,←integral_siteFieldReflection i
    (fun z=>Real.exp (m*f (fieldShift c (siteFieldReflection i x) z))/
      vectorStepPartition c m g x*v (fieldShift c (siteFieldReflection i x) z))]
  simp_rw [fieldShift_site_reflection,hfg,hvw]

theorem vectorRecursion_site_reflection {n k:ℕ} (s:RSBScheme k) (i:Fin n)
    (β t:ℝ) (p:Couplings n×ℝ) (j:ℕ) (x:Field n):
    vectorRecursion s β t (siteDisorderReflection i p) j (siteFieldReflection i x)=
      vectorRecursion s β t p j x:=by
  induction j generalizing x with
  | zero =>
    unfold vectorRecursion vectorTerminalPotential terminalPotential
    have he:vectorTerminalExponent n β t (siteDisorderReflection i p) (siteFieldReflection i x)=
        (vectorTerminalExponent n β t p x)∘flipSpinEquiv i:=by
      funext σ;exact vectorTerminalExponent_site_reflection i β t p x σ
    rw [he,terminalPartition_reindex]
  | succ j ih =>
    simp only [vectorRecursion]
    exact vectorColeHopfStep_site_reflection i _ _ _ _ ih x

theorem vectorSpinMean_site_reflection {n k:ℕ} (s:RSBScheme k) (i l:Fin n)
    (β t:ℝ) (p:Couplings n×ℝ) (j:ℕ) (x:Field n):
    vectorMagnetization s β t (siteDisorderReflection i p) j (siteFieldReflection i x) l=
      siteSign i l*vectorMagnetization s β t p j x l:=by
  have hm (j:ℕ) (x:Field n):
      vectorConditionalMean s β t (siteDisorderReflection i p) (fun _=>0)
        (fun σ=>Paper.spinSign (flipSpin i σ l)) j 0 (siteFieldReflection i x)=
      vectorConditionalMean s β t p (fun _=>0) (fun σ=>Paper.spinSign (σ l)) j 0 x:=by
    induction j generalizing x with
    | zero =>
      simp only [vectorConditionalMean,terminalTilt_zero]
      have he:vectorTerminalExponent n β t (siteDisorderReflection i p) (siteFieldReflection i x)=
          (vectorTerminalExponent n β t p x)∘flipSpinEquiv i:=by
        funext σ;exact vectorTerminalExponent_site_reflection i β t p x σ
      rw [he]
      exact terminalMean_reindex (vectorTerminalExponent n β t p x)
        (fun σ:Configuration n=>Paper.spinSign (σ l)) (flipSpinEquiv i)
    | succ j ih =>
      simp only [vectorConditionalMean,vectorPerturbedRecursion_zero]
      exact vectorStepResponse_site_reflection i _ _ _ _ _ _
        (vectorRecursion_site_reflection s i β t p j) ih x
  have hh:=hm j x
  simp_rw [spinSign_flipSpin] at hh
  rw [vectorConditionalMean_const_mul,
    vectorConditionalMean_zero_eq_response,vectorConditionalMean_zero_eq_response] at hh
  change siteSign i l*vectorMagnetization s β t (siteDisorderReflection i p) j
    (siteFieldReflection i x) l=vectorMagnetization s β t p j x l at hh
  by_cases hl:l=i
  · subst l;simp only [siteSign,ite_true] at hh ⊢;linarith
  · simpa only [siteSign,hl,ite_false,one_mul] using hh

end QuantitativePaper
