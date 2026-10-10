module
public import FourPapersCommon.GaussianSignFlips
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-! Genuine independent standard Gaussian coordinates on a finite subset
and its complement. The coordinate splitting is an actual linear map. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {ι:Type*} [Fintype ι] (p:ι→Prop) [DecidablePred p]

def gaussianCoordinateSplit:
    EuclideanSpace ℝ ι→L[ℝ]
      (EuclideanSpace ℝ {i//p i}×EuclideanSpace ℝ {i//¬p i}):=
  LinearMap.toContinuousLinearMap
    {toFun:=fun z=>(WithLp.toLp 2 (fun i=>z i.val),WithLp.toLp 2 (fun i=>z i.val))
     map_add':=by intro x y;ext i <;> rfl
     map_smul':=by intro a x;ext i <;> rfl}

@[simp] theorem gaussianCoordinateSplit_fst (z:EuclideanSpace ℝ ι) (i:{i//p i}):
    (gaussianCoordinateSplit p z).1 i=z i.val:=rfl

@[simp] theorem gaussianCoordinateSplit_snd (z:EuclideanSpace ℝ ι) (i:{i//¬p i}):
    (gaussianCoordinateSplit p z).2 i=z i.val:=rfl

def gaussianCoordinateJoin:
    (EuclideanSpace ℝ {i//p i}×EuclideanSpace ℝ {i//¬p i})→L[ℝ]
      EuclideanSpace ℝ ι:=
  LinearMap.toContinuousLinearMap
    {toFun:=fun z=>WithLp.toLp 2 (fun i=>if hi:p i then z.1 ⟨i,hi⟩ else z.2 ⟨i,hi⟩)
     map_add':=by
       intro x y
       ext i
       change (if h:p i then x.1 ⟨i,h⟩+y.1 ⟨i,h⟩ else x.2 ⟨i,h⟩+y.2 ⟨i,h⟩)=
         (if h:p i then x.1 ⟨i,h⟩ else x.2 ⟨i,h⟩)+(if h:p i then y.1 ⟨i,h⟩ else y.2 ⟨i,h⟩)
       split_ifs <;> rfl
     map_smul':=by intro a x;ext i;change (if h:p i then _ else _)=_;split_ifs <;> simp_all}

@[simp] theorem gaussianCoordinateJoin_split (z:EuclideanSpace ℝ ι):
    gaussianCoordinateJoin p (gaussianCoordinateSplit p z)=z:=by
  ext i
  change (if hi:p i then z i else z i)=z i
  split_ifs <;> rfl

@[simp] theorem gaussianCoordinateSplit_join
    (z:EuclideanSpace ℝ {i//p i}×EuclideanSpace ℝ {i//¬p i}):
    gaussianCoordinateSplit p (gaussianCoordinateJoin p z)=z:=by
  apply Prod.ext <;> ext i
  · change (if hi:p i.val then z.1 ⟨i.val,hi⟩ else z.2 ⟨i.val,hi⟩)=z.1 i
    simp only [dif_pos i.property]
  · change (if hi:p i.val then z.1 ⟨i.val,hi⟩ else z.2 ⟨i.val,hi⟩)=z.2 i
    simp only [dif_neg i.property]

theorem standardGaussianMeasure_gaussianCoordinateSplit_map:
    (SYK.standardGaussianMeasureOnEuclidean ι).map (gaussianCoordinateSplit p)=
      (SYK.standardGaussianMeasureOnEuclidean {i//p i}).prod
        (SYK.standardGaussianMeasureOnEuclidean {i//¬p i}):=by
  let e:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:ι=>ℝ) p
  have he:=measurePreserving_piEquivPiSubtypeProd (fun _:ι=>gaussianReal 0 1) p
  have hs:gaussianCoordinateSplit p∘(WithLp.toLp 2: (ι→ℝ)→EuclideanSpace ℝ ι)=
      (Prod.map (WithLp.toLp 2) (WithLp.toLp 2))∘e:=rfl
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map (gaussianCoordinateSplit p).measurable (by fun_prop),hs,
    ←Measure.map_map (by fun_prop) e.measurable,he.map_eq,
    ←Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

end FourPapersCommon
