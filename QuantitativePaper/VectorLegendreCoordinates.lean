module
public import QuantitativePaper.VectorFiniteLegendreInverse
public import QuantitativePaper.VectorFiniteOpenCube
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

/-! Smooth genuine Legendre coordinates for the actual finite recursion.
The selected field is the unique preimage under the actual magnetization. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def vectorLegendreField {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) : Field n:=by
  classical
  exact if hm:m∈vectorOpenSpinCube n then
    (vectorMagnetization_surjective_openCube s β t p j m hm).choose else 0

theorem vectorMagnetization_legendreField {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    vectorMagnetization s β t p j (vectorLegendreField s β t p j m)=m:=by
  unfold vectorLegendreField
  rw [dif_pos hm]
  exact (vectorMagnetization_surjective_openCube s β t p j m hm).choose_spec

theorem vectorLegendreField_magnetization {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    vectorLegendreField s β t p j (vectorMagnetization s β t p j x)=x:=by
  apply vectorMagnetization_injective s β t p j
  apply vectorMagnetization_legendreField
  exact fun i=>vectorMagnetization_component_abs_lt_one s β t p j x i

theorem contDiff_vectorMagnetization {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (vectorMagnetization s β t p j):=by
  have he:vectorMagnetization s β t p j=gradient (vectorRecursion s β t p j):=
    funext (vectorMagnetization_eq_gradient s β t p j)
  rw [he]
  exact (InnerProductSpace.toDual ℝ (Field n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
    ((contDiff_vectorRecursion_field s β t p j).fderiv_right (by simp))

theorem hasFDerivAt_vectorMagnetization {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    HasFDerivAt (vectorMagnetization s β t p j) (vectorFieldHessian s β t p j x) x:=by
  have he:vectorMagnetization s β t p j=gradient (vectorRecursion s β t p j):=
    funext (vectorMagnetization_eq_gradient s β t p j)
  rw [he]
  exact hasFDerivAt_gradient_hessianOperator _
    ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)) x

def vectorFieldHessianEquiv {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) : Field n≃L[ℝ]Field n:=
  ContinuousLinearEquiv.ofUnit (vectorFieldHessian_isUnit s β t p j x).unit

theorem vectorFieldHessianEquiv_coe {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    (vectorFieldHessianEquiv s β t p j x : Field n→L[ℝ]Field n)=
      vectorFieldHessian s β t p j x:=by
  change ↑(vectorFieldHessian_isUnit s β t p j x).unit=vectorFieldHessian s β t p j x
  exact IsUnit.unit_spec _

theorem contDiffAt_vectorLegendreField {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (vectorLegendreField s β t p j) m:=by
  let x:=vectorLegendreField s β t p j m
  have hx:vectorMagnetization s β t p j x=m:=vectorMagnetization_legendreField s β t p j m hm
  let e:=vectorFieldHessianEquiv s β t p j x
  have hd:HasFDerivAt (vectorMagnetization s β t p j) (e : Field n→L[ℝ]Field n) x:=by
    rw [show (e : Field n→L[ℝ]Field n)=vectorFieldHessian s β t p j x from
      vectorFieldHessianEquiv_coe s β t p j x]
    exact hasFDerivAt_vectorMagnetization s β t p j x
  have hf:ContDiffAt ℝ ∞ (vectorMagnetization s β t p j) x:=
    (contDiff_vectorMagnetization s β t p j).contDiffAt
  have hs:=hf.hasStrictFDerivAt' hd (by simp)
  have he:=hs.localInverse_unique
    (Eventually.of_forall (vectorLegendreField_magnetization s β t p j))
  have hi:=hf.to_localInverse hd (by simp)
  have hc:ContDiffAt ℝ ∞ (vectorLegendreField s β t p j) (vectorMagnetization s β t p j x):=
    hi.congr_of_eventuallyEq he
  rwa [hx] at hc

theorem hasFDerivAt_vectorLegendreField {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    HasFDerivAt (vectorLegendreField s β t p j)
      ((vectorFieldHessianEquiv s β t p j (vectorLegendreField s β t p j m)).symm :
        Field n→L[ℝ]Field n) m:=by
  let x:=vectorLegendreField s β t p j m
  have hx:vectorMagnetization s β t p j x=m:=vectorMagnetization_legendreField s β t p j m hm
  let e:=vectorFieldHessianEquiv s β t p j x
  have hd:HasFDerivAt (vectorMagnetization s β t p j) (e : Field n→L[ℝ]Field n) x:=by
    rw [show (e : Field n→L[ℝ]Field n)=vectorFieldHessian s β t p j x from
      vectorFieldHessianEquiv_coe s β t p j x]
    exact hasFDerivAt_vectorMagnetization s β t p j x
  have hf:ContDiffAt ℝ ∞ (vectorMagnetization s β t p j) x:=
    (contDiff_vectorMagnetization s β t p j).contDiffAt
  have hs:=hf.hasStrictFDerivAt' hd (by simp)
  have hi:HasStrictFDerivAt (vectorLegendreField s β t p j) (e.symm : Field n→L[ℝ]Field n)
      (vectorMagnetization s β t p j x):=
    hs.to_local_left_inverse (Eventually.of_forall (vectorLegendreField_magnetization s β t p j))
  simpa only [hx,x,e] using hi.hasFDerivAt

end QuantitativePaper
