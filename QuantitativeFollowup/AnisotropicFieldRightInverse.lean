module
public import QuantitativeFollowup.AnisotropicHistoryLinear
public import QuantitativePaper.VectorFieldRightInverse

@[expose] public section

/-! An actual right inverse of each anisotropic revealed field map.
Every revealed increment is used, so repeated levels and zero variances
are retained. Positive diagonal entries are inverted explicitly. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

def anisotropicPhysicalFieldIncrement (s : RSBScheme k) (j : Fin (k+2)) : ℝ :=
  Real.sqrt (s.q (j+1)-s.q j)

theorem anisotropicSchemeInput_physical (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : Fin (k+2)) (w : Field n) :
    anisotropicSchemeInput D s (k+1-j) w=
      anisotropicPhysicalFieldIncrement s j • anisotropicFieldInjection n (anisotropicNoiseMap D w) := by
  rw [anisotropicSchemeInput_apply]
  have h1 : k+2-(k+1-j.val)=j.val+1 := by omega
  have h2 : k+1-(k+1-j.val)=j.val := by omega
  rw [h1,h2,map_smul]
  rfl

theorem anisotropicCoordinateHistory_sum (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p : AnisotropicGaussianCoordinates n k) (i : Fin (k+3)) :
    anisotropicCoordinateHistory D s p i=anisotropicDisorderInjection n p.1+
      ∑j : Fin (k+2),if j.val < i.val then
        anisotropicPhysicalFieldIncrement s j • anisotropicFieldInjection n (anisotropicNoiseMap D (p.2 j)) else 0 := by
  classical
  refine Fin.induction ?_ (fun j ih => ?_) i
  · change independentHistory (anisotropicCoordinateUpdate D s) (k+2)
      (anisotropicDisorderInjection n p.1,p.2) 0 = _
    rw [independentHistory_initial]
    simp
  · change independentHistory (anisotropicCoordinateUpdate D s) (k+2)
      (anisotropicDisorderInjection n p.1,p.2) j.succ = _
    rw [independentHistory_next]
    change anisotropicCoordinateHistory D s p j.castSucc+
      anisotropicSchemeInput D s (k+1-j.val) (p.2 j)=_
    rw [ih,anisotropicSchemeInput_physical,fin_prefix_sum_succ]
    abel

def anisotropicEuclideanFieldInsert (n k : ℕ) (j : Fin (k+2)) :
    Field n→L[ℝ]AnisotropicGaussianSpace n k :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : AnisotropicGaussianIndex n k => ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun a => match a with
      | .inl _ => 0
      | .inr (l,i) => if l=j then EuclideanSpace.proj i else 0)

theorem anisotropicEuclideanCoordinates_fieldInsert (j : Fin (k+2)) (w : Field n) :
    anisotropicEuclideanCoordinates n k (anisotropicEuclideanFieldInsert n k j w)=
      (0,fun l => if l=j then w else 0) := by
  apply Prod.ext
  · ext e
    simp [anisotropicEuclideanCoordinates,anisotropicRawGaussianCoordinates,anisotropicEuclideanFieldInsert]
  · funext l
    ext i
    by_cases hl : l=j <;> simp [anisotropicEuclideanCoordinates,anisotropicRawGaussianCoordinates,
      flatFieldCoordinates,anisotropicEuclideanFieldInsert,hl]

theorem anisotropicEuclideanStateLinear_fieldInsert (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin (k+3)) (j : Fin (k+2)) (w : Field n) :
    anisotropicEuclideanStateLinear D s i (anisotropicEuclideanFieldInsert n k j w)=
      if j.val < i.val then anisotropicPhysicalFieldIncrement s j •
        anisotropicFieldInjection n (anisotropicNoiseMap D w) else 0 := by
  classical
  rw [anisotropicEuclideanStateLinear_apply,anisotropicEuclideanCoordinates_fieldInsert]
  have hi : Fin.ofNat (k+3) i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  change anisotropicCoordinateHistory D s _ (Fin.ofNat (k+3) i.val)=_
  rw [hi,anisotropicCoordinateHistory_sum]
  simp only [map_zero,zero_add,Prod.fst,Prod.snd]
  have he (l : Fin (k+2)) :
      (if l.val < i.val then anisotropicPhysicalFieldIncrement s l •
        anisotropicFieldInjection n (anisotropicNoiseMap D (if l=j then w else 0)) else 0)=
      if l=j then (if j.val < i.val then anisotropicPhysicalFieldIncrement s j •
        anisotropicFieldInjection n (anisotropicNoiseMap D w) else 0) else 0 := by
    by_cases hl : l=j
    · subst l
      simp
    · simp [hl]
  simp_rw [he]
  simp

def anisotropicNoiseInverse (D : AnisotropicSpinModel n) : Field n→L[ℝ]Field n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun l => (Real.sqrt (D.variance l))⁻¹*w l)
      map_add' := by intro w z;ext l;simp only [PiLp.add_apply,mul_add]
      map_smul' := by intro c w;ext l;simp only [PiLp.smul_apply,smul_eq_mul,RingHom.id_apply];ring }

theorem anisotropicNoiseMap_inverse (D : AnisotropicSpinModel n) (w : Field n) :
    anisotropicNoiseMap D (anisotropicNoiseInverse D w)=w := by
  ext l
  change Real.sqrt (D.variance l)*((Real.sqrt (D.variance l))⁻¹*w l)=w l
  rw [←mul_assoc,mul_inv_cancel₀ (Real.sqrt_pos.mpr (D.variance_pos l)).ne',one_mul]

theorem anisotropicPhysicalFieldIncrement_prefix_sq (s : RSBScheme k) (i : Fin (k+3)) :
    (∑j : Fin (k+2),if j.val < i.val then (anisotropicPhysicalFieldIncrement s j)^2 else 0)=s.q i := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp [s.q_zero]
  · rw [fin_prefix_sum_succ,ih]
    rw [anisotropicPhysicalFieldIncrement,Real.sq_sqrt (sub_nonneg.mpr (s.q_mono j (by omega)))]
    simp only [Fin.val_succ,Fin.val_castSucc]
    ring

def anisotropicEuclideanFieldRightInverse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin (k+3)) : Field n→L[ℝ]AnisotropicGaussianSpace n k :=
  ∑j : Fin (k+2),(if j.val < i.val then anisotropicPhysicalFieldIncrement s j/s.q i else 0) •
    (anisotropicEuclideanFieldInsert n k j).comp (anisotropicNoiseInverse D)

theorem anisotropicEuclideanStateLinear_rightInverse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin (k+3)) (hi : 0 < s.q i) (w : Field n) :
    anisotropicEuclideanStateLinear D s i (anisotropicEuclideanFieldRightInverse D s i w)=
      anisotropicFieldInjection n w := by
  classical
  rw [anisotropicEuclideanFieldRightInverse,sum_apply,map_sum]
  simp_rw [smul_apply,map_smul,ContinuousLinearMap.comp_apply,
    anisotropicEuclideanStateLinear_fieldInsert,anisotropicNoiseMap_inverse]
  have he (j : Fin (k+2)) :
      (if j.val < i.val then anisotropicPhysicalFieldIncrement s j/s.q i else 0) •
        (if j.val < i.val then anisotropicPhysicalFieldIncrement s j • anisotropicFieldInjection n w else 0)=
      ((if j.val < i.val then (anisotropicPhysicalFieldIncrement s j)^2 else 0)/s.q i) •
        anisotropicFieldInjection n w := by
    by_cases hj : j.val < i.val
    · simp only [ite_eq_left hj,smul_smul]
      congr 1
      ring
    · simp [hj]
  simp_rw [he]
  rw [←Finset.sum_smul,←Finset.sum_div,anisotropicPhysicalFieldIncrement_prefix_sq,
    div_self hi.ne',one_smul]

end QuantitativeFollowup
