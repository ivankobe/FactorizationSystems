import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Composition

-- set_option diagnostics true

namespace CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

def contains_isos (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ≅ Y) , W f.hom

class is_closed_comp (W : MorphismProperty C) extends W.Respects W where

structure FactorizationSystem (L R : MorphismProperty C) where
  contains_isos_left_class : contains_isos L
  contains_isos_right_class : contains_isos R
  is_closed_comp_left_class : is_closed_comp L
  is_closed_comp_right_class : is_closed_comp R
  image  : {X Y : C} → (f : X ⟶ Y) → C
  left_map : {X Y : C} → (f : X ⟶ Y) → X ⟶ image f
  right_map : {X Y : C} → (f : X ⟶ Y) → image f ⟶ Y
  factorization : {X Y : C} → (f : X ⟶ Y) → left_map f ≫ right_map f = f := by aesop_cat
  iso :
    {X Y : C} → (f : X ⟶ Y) → (im : C) → (left : X ⟶ im) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) →
    Σ' i : image f ≅ im, left_map f ≫ i.hom = left ∧ i.hom ≫ right = right_map f
  is_unique_iso :
    {X Y : C} → (f : X ⟶ Y) → (im : C) → (left : X ⟶ im) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) → (i : image f ≅ im) → (comm₁ : left_map f ≫ i.hom = left) →
    (comm₂ : i.hom ≫ right = right_map f) → i = (iso f im left right fact).fst

def MorphismPropertySlice (W : MorphismProperty C) (X : C) : MorphismProperty (Over X) := by
  rintro _ _ f
  exact W ((Over.forget X).map f)

lemma contains_isos_slice : {W : MorphismProperty C} → {X : C} →  contains_isos W →
    contains_isos (MorphismPropertySlice W X) := by
  intro _ X h _ _ i
  exact h (asIso ((Over.forget X).map i.hom))

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

lemma forget_map_comm :
    {X : C} → {p q r : Over X} → (F : p ⟶ q) → (G : q ⟶ r) → (H : p ⟶ r) →
    (hyp : F ≫ G = H) → (F.left ≫ G.left = H.left) := by
  rintro X _ _ _ ⟨f,_,u⟩ ⟨g,_,v⟩ ⟨h,_,w⟩ _
  calc
    f ≫ g = ((Over.forget X).map ⟨f,_,u⟩) ≫ ((Over.forget X).map ⟨g,_,v⟩) := by
      simp
    _ = ((Over.forget X).map (⟨f,_,u⟩ ≫ ⟨g,_,v⟩)) := by simp
    _ = ((Over.forget X).map ⟨h,_,w⟩) := by aesop_cat
    _ = h := by simp

def forget_preserves_isos : {X : C} → {f g : Over X} → (i : f ≅ g) → f.left ≅ g.left := by
  rintro X _ _ i
  exact
  {
    hom := by exact i.hom.left,
    inv := by exact i.inv.left,
    hom_inv_id := by exact forget_map_comm _ _ _ i.hom_inv_id,
    inv_hom_id := by exact forget_map_comm _ _ _ i.inv_hom_id
  }

end Over

def FactorizationSystemSlice : {X : C} → {L R : MorphismProperty C} → FactorizationSystem L R →
    FactorizationSystem (MorphismPropertySlice L X) (MorphismPropertySlice R X) := by
  intro X L R F
  exact
  {
    contains_isos_left_class := contains_isos_slice F.contains_isos_left_class,
    contains_isos_right_class := contains_isos_slice F.contains_isos_right_class,
    is_closed_comp_left_class := is_closed_comp_slice F.is_closed_comp_left_class,
    is_closed_comp_right_class := is_closed_comp_slice F.is_closed_comp_right_class,
    image := by
      rintro _ ⟨_,_,b⟩ ⟨f,_,_⟩
      apply Over.mk ((F.right_map f) ≫ b),
    left_map := by
      rintro ⟨_,_,a⟩ ⟨_,_,b⟩ ⟨f,_,w⟩
      have comm : F.left_map f ≫ F.right_map f ≫ b = a := by
        calc
          F.left_map f ≫ F.right_map f ≫ b =
          (F.left_map f ≫ F.right_map f) ≫ b := by simp
          _ = f ≫ b := by exact (F.factorization f) =≫ b
          _ = a := by simp at w ; exact w
      exact Over.homMk (F.left_map f) comm,
    right_map := by
      rintro _ _ ⟨f,_,_⟩
      exact Over.homMk (F.right_map f) (by aesop_cat),
    factorization := by
      rintro _ _ ⟨f,_,_⟩
      have fact : (F.left_map f) ≫ (F.right_map f) = f := F.factorization f
      aesop_cat,
    iso := by
      rintro ⟨_,_,a⟩ ⟨_,_,b⟩ ⟨g,_,u⟩ ⟨_,_,im⟩ ⟨l,_,v⟩ ⟨r,_,w⟩ fact
      have ⟨i,⟨P,Q⟩⟩ := F.iso g _ l r (Over.forget_map_comm _ _ _ fact)
      exact
      {
        fst := by
          have comm : i.hom ≫ im = (F.right_map g) ≫ b := by
            calc
              i.hom ≫ im = i.hom ≫ r ≫ b := by simp at w ; rw [←w]
              _ = (F.right_map g) ≫ b := by rw [←Q] ; simp
          simp
          apply Over.isoMk i (by simp ; exact comm)
        snd := by aesop_cat
      }
    is_unique_iso := by
      rintro ⟨A,_,a⟩ ⟨B,_,b⟩ ⟨g,_,u⟩ ⟨Im,_,im⟩ ⟨l,_,v⟩ ⟨r,_,w⟩
      rintro fact i comm₁ comm₂
      have duh := F.is_unique_iso g Im l r
        (Over.forget_map_comm _ _ _ fact)
        (Over.forget_preserves_isos i)
        (Over.forget_map_comm _ _ _ comm₁)
        (Over.forget_map_comm _ _ _ comm₂)
      aesop_cat
  }
