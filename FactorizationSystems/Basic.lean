import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Composition

namespace CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The predicate that a class of morphism contains the isomorphisms -/
def contains_isos (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ≅ Y) , W f.hom

/-- The predicate of a class of morphisms being closed under compositin -/
class is_closed_comp (W : MorphismProperty C) extends W.Respects W where

/-- The structure of a factorization system on a category C with specified classes of morphisms -/
structure FactorizationSystem {C : Type u} [Category.{v} C] (L R : MorphismProperty C) where
  /-- The left class contains isomorphism -/
  contains_isos_left_class : contains_isos L
  /-- The right class contains isomorphism -/
  contains_isos_right_class : contains_isos R
  /-- The left class is closed under composition -/
  is_closed_comp_left_class : is_closed_comp L
  /-- The right class is closed under composition -/
  is_closed_comp_right_class : is_closed_comp R
  /-- The midpoint/image of the factorization-/
  image  : {X Y : C} → (f : X ⟶ Y) → C
  /-- The left map of the factorization -/
  left_map : {X Y : C} → (f : X ⟶ Y) → X ⟶ image f
  /-- The left map of the factorization is contained in the left class-/
  left_map_in_left_class : {X Y : C} → (f : X ⟶ Y) → L (left_map f)
  /-- The right map of the factorization -/
  right_map : {X Y : C} → (f : X ⟶ Y) → image f ⟶ Y
  /-- The left map of the factorization is contained in the left class-/
  right_map_in_right_class : {X Y : C} → (f : X ⟶ Y) → R (right_map f)
  /-- The factorization-/
  factorization : {X Y : C} → (f : X ⟶ Y) → left_map f ≫ right_map f = f := by aesop_cat
  /-- The factorization is unique up to isomorphism -/
  factorization_iso :
    {X Y : C} → (f : X ⟶ Y) → (im : C) → (left : X ⟶ im) → L left→ (right : im ⟶ Y) → R right →
    (fact : left ≫ right = f) →
    Σ' i : image f ≅ im, left_map f ≫ i.hom = left ∧ i.hom ≫ right = right_map f
  /-- The factorization is unique up toa unique isomorphism -/
  factorization_iso_is_unique :
    {X Y : C} → (f : X ⟶ Y) → (im : C) → (left : X ⟶ im)→ (p : L left) → (right : im ⟶ Y) →
    (q : R right) → (fact : left ≫ right = f) → (i : image f ≅ im) →
    (comm₁ : left_map f ≫ i.hom = left) → (comm₂ : i.hom ≫ right = right_map f) →
    i = (factorization_iso f im left p right q fact).fst

/-- A class of morphisms in C defines a class of morphism in the slice C/X for every X ∈ C -/
def MorphismPropertySlice (W : MorphismProperty C) (X : C) : MorphismProperty (Over X) := by
  rintro _ _ f
  exact W ((Over.forget X).map f)

/-- If a class of morphisms contains isomorphisms,
then so does the class of morphisms in the slice -/
lemma contains_isos_slice : {W : MorphismProperty C} → {X : C} →  contains_isos W →
    contains_isos (MorphismPropertySlice W X) := by
  intro _ X h _ _ i
  exact h (asIso ((Over.forget X).map i.hom))

/-- If a class of morphisms is closed under composition,
then so does the class of morphisms in the slice -/
lemma is_closed_comp_slice {W : MorphismProperty C} {X : C} (h : is_closed_comp W) :
    is_closed_comp (MorphismPropertySlice W X) where
  precomp f hf g hg := by
    unfold MorphismPropertySlice
    rw [(Over.forget X).map_comp]
    exact h.precomp _ hf _ hg
  postcomp f hf g hg := by
    unfold MorphismPropertySlice
    rw [(Over.forget X).map_comp]
    exact h.postcomp _ hf _ hg

namespace Over

/-- If a triangle commutes in the slice C/X, then it commutes in C -/
lemma forget_map_comp :
    {X : C} → {p q r : Over X} → (F : p ⟶ q) → (G : q ⟶ r) → (H : p ⟶ r) →
    (hyp : F ≫ G = H) → (F.left ≫ G.left = H.left) := by
  rintro X _ _ _ ⟨f,_,u⟩ ⟨g,_,v⟩ ⟨h,_,w⟩ _
  calc
    f ≫ g = ((Over.forget X).map ⟨f,_,u⟩) ≫ ((Over.forget X).map ⟨g,_,v⟩) := by
      simp
    _ = ((Over.forget X).map (⟨f,_,u⟩ ≫ ⟨g,_,v⟩)) := by simp
    _ = ((Over.forget X).map ⟨h,_,w⟩) := by aesop_cat
    _ = h := by simp

/-- The forgetful functor C/X ⟶ X preserves isomorphisms -/
def forget_preserves_isos : {X : C} → {f g : Over X} → (i : f ≅ g) → f.left ≅ g.left := by
  rintro X _ _ i
  exact
  {
    hom := by exact i.hom.left,
    inv := by exact i.inv.left,
    hom_inv_id := by exact forget_map_comp _ _ _ i.hom_inv_id,
    inv_hom_id := by exact forget_map_comp _ _ _ i.inv_hom_id
  }

end Over

def image_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → Over X := by
  rintro _ _ _ F _ ⟨_,_,g⟩ ⟨φ,_,_⟩
  apply Over.mk ((F.right_map φ) ≫ g)

def left_map_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → (f ⟶ image_slice F φ) := by
  rintro _ _ _ F ⟨_,_,f⟩ ⟨_,_,g⟩ ⟨φ,_,w⟩
  have comm : F.left_map φ ≫ F.right_map φ ≫ g = f := by
    calc
      F.left_map φ ≫ F.right_map φ ≫ g =  (F.left_map φ ≫ F.right_map φ) ≫ g := by simp
      _ = φ ≫ g := by exact (F.factorization φ) =≫ g
      _ = f := by simp at w ; exact w
  exact Over.homMk (F.left_map φ) comm

def left_map_in_left_class_slice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) → {f g : Over X} → (φ : f ⟶ g) →
    (MorphismPropertySlice L X) (left_map_slice F φ) := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  have el := F.left_map_in_left_class φ
  aesop_cat

def right_map_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → (image_slice F φ ⟶ g) := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  exact Over.homMk (F.right_map φ) (by aesop_cat)

def right_map_in_right_class_slice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) → {f g : Over X} → (φ : f ⟶ g) →
    (MorphismPropertySlice R X) (right_map_slice F φ) := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  have el := F.right_map_in_right_class φ
  aesop_cat

def factorization_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → left_map_slice F φ ≫ right_map_slice F φ = φ := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  have fact := F.factorization φ
  aesop_cat

def factorization_iso_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → (im : Over X) → (left : f ⟶ im) →
    (p : (MorphismPropertySlice L X) left) → (right : im ⟶ g) →
    (q : (MorphismPropertySlice R X) right) → (fact : left ≫ right = φ) →
      Σ' i : image_slice F φ ≅ im,
        left_map_slice F φ ≫ i.hom = left ∧ i.hom ≫ right = right_map_slice F φ := by
  rintro _ _ _ F _ ⟨_,_,g⟩ ⟨φ,_,_⟩ ⟨_,_,h⟩ ⟨l,_,_⟩ _ ⟨r,_,w⟩ _ fact
  have ⟨i,⟨P,Q⟩⟩ :=
    F.factorization_iso φ _ l (by aesop_cat) r (by aesop_cat) (Over.forget_map_comp _ _ _ fact)
  exact {
    fst := by
      have comm : i.hom ≫ h = (F.right_map φ) ≫ g := by
        calc
          i.hom ≫ h = i.hom ≫ r ≫ g := by simp at w ; rw [←w]
          _ = (F.right_map φ) ≫ g := by rw [←Q] ; simp
      exact Over.isoMk i (by simp ; exact comm)
    snd := by aesop_cat
  }


def factorization_iso_is_unique_slice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) → {f g : Over X} → (φ : f ⟶ g) → (im : Over X) → (left : f ⟶ im) →
    (p : (MorphismPropertySlice L X) left) → (right : im ⟶ g) →
    (q : (MorphismPropertySlice R X) right) → (fact : left ≫ right = φ) →
    (i : image_slice F φ ≅ im) → (comm₁ : left_map_slice F φ ≫ i.hom = left) →
    (comm₂ : i.hom ≫ right = right_map_slice F φ) →
    i = (factorization_iso_slice F φ im left p right q fact).fst := by
  rintro _ _ _ F ⟨A,_,f⟩ ⟨B,_,g⟩ ⟨φ,_,u⟩ ⟨C,_,h⟩ ⟨l,_,v⟩ p ⟨r,_,w⟩ q fact i comm₁ comm₂
  have uniqueness := F.factorization_iso_is_unique φ C l p r q
    (Over.forget_map_comp _ _ _ fact)
    (Over.forget_preserves_isos i)
    (Over.forget_map_comp _ _ _ comm₁)
    (Over.forget_map_comp _ _ _ comm₂)
  ext
  have this_is_obvious : (Over.forget_preserves_isos i).hom = i.hom.left := by rfl
  rw [←this_is_obvious]
  have why_do_you_not_know_this_you_stupid_machine :
      (F.factorization_iso φ C l p r q (Over.forget_map_comp _ _ _ fact)).fst.hom =
      (factorization_iso_slice F ⟨φ,_,u⟩ ⟨C,_,h⟩ ⟨l,_,v⟩ p ⟨r,_,w⟩ q fact).fst.hom.left := by
    simp
    unfold factorization_iso_slice
    aesop_cat
  rw [←why_do_you_not_know_this_you_stupid_machine]
  aesop_cat

/-- A factorization system in C determines descends to a factorization system in the slice -/
def FactorizationSystemSlice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) →
    FactorizationSystem (MorphismPropertySlice L X) (MorphismPropertySlice R X) := by
  intro X L R F
  exact
  {
    contains_isos_left_class := contains_isos_slice F.contains_isos_left_class
    contains_isos_right_class := contains_isos_slice F.contains_isos_right_class
    is_closed_comp_left_class := is_closed_comp_slice F.is_closed_comp_left_class
    is_closed_comp_right_class := is_closed_comp_slice F.is_closed_comp_right_class
    image := image_slice F
    left_map := left_map_slice F
    left_map_in_left_class := left_map_in_left_class_slice F
    right_map := right_map_slice F
    right_map_in_right_class := right_map_in_right_class_slice F
    factorization := factorization_slice F
    factorization_iso := factorization_iso_slice F
    factorization_iso_is_unique := factorization_iso_is_unique_slice F
  }
