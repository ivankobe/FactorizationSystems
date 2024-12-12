import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Basic
import FactorizationSystems.Basic

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

/-
We construct some examples of factorization systems:
  - (Mono,Epi) on Set
-/

/- Every iso is an epi -/
lemma isIsoIsEpi : {X Y : C} → (f : X ⟶ Y) →
      MorphismProperty.isomorphisms _ f → MorphismProperty.epimorphisms _ f := by
  intro X Y f hf
  simp at hf
  exact {left_cancellation := by exact (IsIso.epi_of_iso f).left_cancellation}


/- Iso ⊆ Epi -/
lemma epimorphismsContainsIsos : contains_isos (MorphismProperty.epimorphisms C) := by
    intro X Y isof
    exact isIsoIsEpi isof.hom (Iso.isIso_hom isof)

/- Epimorphisms are closed under composition -/
lemma epimorphismsClosedUnderComp : is_closed_comp (MorphismProperty.epimorphisms C) where
    precomp := by exact epi_comp
    postcomp := by
        intro _ _ _ f hf g hg
        simp at hf
        simp at hg
        exact epi_comp g f

/- Every iso is a mono -/
lemma isIsoIsMono : {X Y : C} → (f : X ⟶ Y) →
        MorphismProperty.isomorphisms _ f → MorphismProperty.monomorphisms _ f := by
    intro X Y f hf
    simp at hf
    exact {right_cancellation := by exact (IsIso.mono_of_iso f).right_cancellation}

/- Mono ⊆ Iso -/
lemma monomorphismsContainsIsos : contains_isos (MorphismProperty.monomorphisms C) := by
    intro X Y isof
    exact isIsoIsMono isof.hom (Iso.isIso_hom isof)

/- Monomorphisms are closed under composition -/
lemma monomorphismsClosedUnderComp : is_closed_comp (MorphismProperty.monomorphisms C) where
    precomp := by exact mono_comp
    postcomp := by
        intro _ _ _ f hf g hg
        simp at hf
        simp at hg
        exact mono_comp g f

/- The image of a function of sets -/
def image_set {X Y : Type u} (f : X → Y) : Type u := {y : Y // ∃ x : X , f x = y}

/- Left map of the image factorization of a map -/
def left_map_set : {X Y : Type u} → (f : X → Y) → (X ⟶ image_set f) := by
    intro X Y f x
    exact ⟨f x, by simp⟩

/- Right map of the image factorization of a map -/
def right_map_set : {X Y : Type u} → (f : X → Y) → (image_set f ⟶ Y) := by
    intro X Y f y
    exact y.1

/- The image factorization of a map-/
def factorization_set :
        {X Y : Type u} → (f : X → Y) → left_map_set f ≫ right_map_set f = f:= by
    intro X Y f
    ext x
    rfl

/- The left map of the image factorization of a map is epi -/
def left_map_in_left_class_set : {X Y : Type u} → (f : X ⟶ Y) →
        MorphismProperty.epimorphisms _ (left_map_set f) := by
    intro X Y f
    apply (epi_iff_surjective (left_map_set f)).mpr
    intro a
    let ⟨fx, ⟨x,p⟩⟩ := a
    use x
    aesop

/- The right map of the image factorization of a map is mono -/
def right_map_in_right_class_set : {X Y : Type u} → (f : X ⟶ Y) →
        MorphismProperty.monomorphisms _ (right_map_set f) := by
    intro X Y f
    apply (mono_iff_injective (right_map_set f)).mpr
    rintro ⟨fx, ⟨x,p⟩⟩ ⟨fy, ⟨y,q⟩⟩ h
    aesop

/- Given another (Epi,Mono) factorization of a map, there
is a unique way solve the corresponding lifting problem -/
lemma factorization_iso_set_hom' {X Y : Type u} (f : X ⟶ Y) (im : Type u)
    (left : X ⟶ im) (p : MorphismProperty.epimorphisms _ left) (right : im ⟶ Y)
    (q : MorphismProperty.monomorphisms _ right) (fact : left ≫ right = f) (y : image_set f) :
    ∃! y' : im, right y' = (right_map_set f) y := by
  let ⟨fx,P⟩ := y
  have injectiveRight : Function.Injective right := by
    exact (mono_iff_injective right).mp q
  have existence : ∃ y : im, right y = fx := by aesop
  have uniqueness : ∃! y : im, right y = fx := by
    let ⟨y,Q⟩ := existence
    apply Exists.intro y
    simp
    apply And.intro
    exact Q
    intro y'
    aesop
  exact uniqueness

/- A (unique) way of solving the lifting problem, i.e. a diagonal filler -/
noncomputable
def factorization_iso_set_hom : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) → image_set f ⟶ im := by
  intro X Y f im left p right q fact ⟨fx,P⟩
  exact (factorization_iso_set_hom' f im left p right q fact ⟨fx,P⟩).choose

/- The commutiativity of the right triangle with the diagonal filler -/
def factorization_iso_set_hom_comm_right : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    factorization_iso_set_hom f im left p right q fact ≫ right = right_map_set f := by
  rintro X Y f im left p right q fact
  ext ⟨fx,P⟩
  let i := factorization_iso_set_hom f im left p right q fact
  let i' := factorization_iso_set_hom' f im left p right q fact
  have comm : right (i ⟨fx,P⟩) = fx := by
    unfold i
    unfold factorization_iso_set_hom
    exact (Exists.choose_spec (i' ⟨fx,P⟩)).left
  aesop

/- The commutiativity of the left triangle with the diagonal filler -/
def factorization_iso_set_hom_comm_left : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    left_map_set f ≫ factorization_iso_set_hom f im left p right q fact = left := by
  intro X Y f im left p right q fact
  apply q.right_cancellation
  let i := factorization_iso_set_hom f im left p right q fact
  calc
    (left_map_set f ≫ i) ≫ right = left_map_set f ≫ (i ≫ right) := by simp
    _  = left_map_set f ≫ right_map_set f :=
      by rw [factorization_iso_set_hom_comm_right f im left p right q fact]
    _ = f := by exact factorization_set f
    _ = left ≫ right := by rw [←fact]

/- The inverse of the solution to the lifting problem -/
def factorization_iso_set_inv : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) → (left : X ⟶ im) →
    (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) → im ⟶ image_set f := by
  intro X Y f im left p right q fact y
  have existence : ∃ x : X, f x = right y := by
    simp at p
    have surjectiveLeft : Function.Surjective left := by
      exact (epi_iff_surjective left).mp p
    rw [←fact]
    simp
    have triv : ∃ x : X, left x = y := by apply surjectiveLeft
    aesop
  unfold image_set
  exact ⟨right y,existence⟩

/- The commutiativity of the right triangle with the inverse to the diagonal filler -/
def factorization_iso_set_inv_comm_right : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    factorization_iso_set_inv f im left p right q fact ≫ right_map_set f = right := by
  aesop_cat

/- The commutiativity of the left triangle with the inverse to the diagonal filler -/
def factorization_iso_set_inv_comm_left : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    left ≫ factorization_iso_set_inv f im left p right q fact = left_map_set f := by
  aesop_cat

/- The factorization isomorphism -/
noncomputable
def factorization_iso_set : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) → (left : X ⟶ im) →
    (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (left ≫ right = f) →
    Σ' i : image_set f ≅ im,
      left_map_set  f ≫ i.hom = left ∧ i.hom ≫ right = right_map_set f := by
  intro X Y f im left p right q fact
  exact {
    fst := by exact {
      hom := factorization_iso_set_hom f im left p right q fact
      inv := factorization_iso_set_inv f im left p right q fact
      hom_inv_id := by
        let hom := factorization_iso_set_hom f im left p right q fact
        let inv := factorization_iso_set_inv f im left p right q fact
        apply (left_map_in_left_class_set f).left_cancellation
        apply (right_map_in_right_class_set f).right_cancellation
        calc
          left_map_set f ≫ hom ≫ inv ≫ right_map_set f =
            (left_map_set f ≫ hom) ≫ (inv ≫ right_map_set f) := by simp
          _ = left ≫ right := by
            rw [factorization_iso_set_hom_comm_left, factorization_iso_set_inv_comm_right]
          _ = f := fact
      inv_hom_id := by
        let hom := factorization_iso_set_hom f im left p right q fact
        let inv := factorization_iso_set_inv f im left p right q fact
        apply p.left_cancellation
        apply q.right_cancellation
        simp
        calc
          left ≫ inv ≫ hom ≫ right = (left ≫ inv) ≫ (hom ≫ right) := by rfl
          _ = left_map_set f ≫ right_map_set f := by
            rw [factorization_iso_set_inv_comm_left, factorization_iso_set_hom_comm_right]
          _ = f := factorization_set f
          _ = left ≫ right := by rw [fact]
    }
    snd := by exact {
      left := factorization_iso_set_hom_comm_left f im left p right q fact
      right := factorization_iso_set_hom_comm_right f im left p right q fact
    }
  }

/- The uniqueness of the factorization isomorphism -/
def factorization_iso_is_unique_set : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    (i : image_set f ≅ im) → (left_map_set f ≫ i.hom = left) → (i.hom ≫ right = right_map_set f) →
    i = (factorization_iso_set f im left p right q fact).fst := by
  intro X Y f im left p right q fact i comm_left comm_right
  let hom := factorization_iso_set_hom f im left p right q fact
  let hom' := i.hom
  apply Iso.ext
  apply (left_map_in_left_class_set f).left_cancellation
  calc
    left_map_set f ≫ hom' = left := comm_left
    _ = left_map_set f ≫ hom := by rw [factorization_iso_set_hom_comm_left]

/- The (Epi,Mono) factorization system on Set -/
noncomputable
instance EpiMonoSet : FactorizationSystem
        (MorphismProperty.epimorphisms (Type u))
        (MorphismProperty.monomorphisms (Type u)) := by
    exact
    {
        contains_isos_left_class := epimorphismsContainsIsos
        contains_isos_right_class := monomorphismsContainsIsos
        is_closed_comp_left_class := epimorphismsClosedUnderComp
        is_closed_comp_right_class:= monomorphismsClosedUnderComp
        image := image_set
        left_map := left_map_set
        right_map := right_map_set
        factorization := factorization_set
        left_map_in_left_class := left_map_in_left_class_set
        right_map_in_right_class := right_map_in_right_class_set
        factorization_iso := factorization_iso_set
        factorization_iso_is_unique := factorization_iso_is_unique_set
    }
