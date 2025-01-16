import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Comma

import FactorizationSystems.Basic
import FactorizationSystems.Orthogonality
import FactorizationSystems.OrthogonalComplements

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

def is_replete (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y X' Y' : C⦄ (l : X ⟶ Y) (l' : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
  (_ : i.hom ≫ l' = l ≫ j.hom) (_: W l) , W l'

lemma is_replete_left_class
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : is_replete L := by
  intro X Y X' Y' l l' i j c p
  let i' := i.symm
  have eq : l' = i'.hom ≫ l ≫ j.hom := by calc
    l' = i.inv ≫ i.hom ≫ l' := by simp
    _ = i'.hom ≫ i.hom ≫ l' := by rfl
    _ = i'.hom ≫ l ≫ j.hom := by rw [c]
  rw [eq]
  apply  F.is_closed_comp_left_class.precomp
  apply F.contains_isos_left_class
  apply  F.is_closed_comp_left_class.precomp
  exact p
  apply F.contains_isos_left_class

lemma is_replete_right_class
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : is_replete R := by
  intro X Y X' Y' r r' i j c p
  let i' := i.symm
  have eq : r' = i'.hom ≫ r ≫ j.hom := by calc
    r' = i.inv ≫ i.hom ≫ r' := by simp
    _ = i'.hom ≫ i.hom ≫ r' := by rfl
    _ = i'.hom ≫ r ≫ j.hom := by rw [c]
  rw [eq]
  apply  F.is_closed_comp_right_class.precomp
  apply F.contains_isos_right_class
  apply  F.is_closed_comp_right_class.precomp
  exact p
  apply F.contains_isos_right_class

/- Note that this terminology is non-standart -/
structure WeakFactorizationSystem (L R : MorphismProperty C) where
  image : {X Y : C} → (f : X ⟶ Y) → C
  left_map : {X Y : C} → (f : X ⟶ Y) → X ⟶ image f
  left_map_in_left_class : {X Y : C} → (f : X ⟶ Y) → L (left_map f)
  right_map : {X Y : C} → (f : X ⟶ Y) → image f ⟶ Y
  right_map_in_right_class : {X Y : C} → (f : X ⟶ Y) → R (right_map f)
  factorization : {X Y : C} → (f : X ⟶ Y) → left_map f ≫ right_map f = f := by aesop_cat

def WFS_of_FS (L R : MorphismProperty C) (F : FactorizationSystem L R) :
  WeakFactorizationSystem L R := {
    image := F.image
    left_map := F.left_map
    left_map_in_left_class := F.left_map_in_left_class
    right_map := F.right_map
    right_map_in_right_class := F.right_map_in_right_class
    factorization := F.factorization
  }

def orthogonal_class (L R : MorphismProperty C) :=
  ∀ ⦃A B X Y : C⦄ (l : A ⟶ B) (_ : L l) (r : X ⟶ Y) (_ : R r) , orthogonal l r

lemma apd (A : Type u) (B : A → Type v) (a b : A) (p : b = a) (f : ∀ x, B x) : p ▸ f a = f b := by
  cases p ; rfl

lemma comm_square_right_map_apd {L R : MorphismProperty C} (F : FactorizationSystem L R)
  {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) :
  (S.comm ▸ F.right_map (S.top ≫ r)) = F.right_map (l ≫ S.bot) :=
  apd (A ⟶ Y) (fun f => F.image f ⟶ Y) (S.top ≫ r) (l ≫ S.bot) S.comm F.right_map

lemma rw_eq_apd {A : Type u} {B : A → Type v} {a b : A} (p : b = a) (f : ∀ x, B x) :
  p ▸ f a = ( by rw [p] ; exact (f a)) := by aesop

def FactorizationSystem_diagonal
  {L R : MorphismProperty C} (F : FactorizationSystem L R) {A B X Y : C} (l : A ⟶ B) (hl : L l)
  (r : X ⟶ Y) (hr : R r) (S : l □ r) : diagonal_filler S := by
  let s := F.left_map S.top
  let p := F.right_map S.top
  let s' := F.left_map S.bot
  let p' := F.right_map S.bot
  let I := F.factorization_iso (l ≫ S.bot) (F.image S.bot) (l ≫ (F.left_map S.bot))
    (F.is_closed_comp_left_class.precomp l hl (F.left_map S.bot) (F.left_map_in_left_class S.bot))
    (F.right_map S.bot) ( F.right_map_in_right_class S.bot)
    (by have fact := F.factorization S.bot ; aesop_cat)
  let fact : (F.left_map S.top) ≫ (F.right_map S.top) ≫ r = S.top ≫ r := by calc
    (F.left_map S.top) ≫ (F.right_map S.top) ≫ r =
      ((F.left_map S.top) ≫ (F.right_map S.top)) ≫ r := by simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
  let J := F.factorization_iso (S.top ≫ r) (F.image S.top) s (F.left_map_in_left_class S.top)
    ((F.right_map S.top) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.right_map S.top) (F.right_map_in_right_class S.top) r hr) fact
  exact {
    map := s' ≫ I.fst.inv ≫ (by rw [S.comm] ; exact J.fst.hom) ≫ p
    comm_top := by calc
      l ≫ s' ≫ I.fst.inv ≫ (by rw [S.comm] ; exact J.fst.hom) ≫ p =
        (l ≫ s') ≫ I.fst.inv ≫ (by rw [S.comm] ; exact J.fst.hom) ≫ p := by simp
      _ = (F.left_map (l ≫ S.bot) ≫ I.fst.hom) ≫ I.fst.inv ≫
        ( by rw [S.comm] ; exact J.fst.hom) ≫ p := by rw [I.snd.left]
      _ = F.left_map (l ≫ S.bot) ≫ (I.fst.hom ≫ I.fst.inv) ≫
        ( by rw [S.comm] ; exact J.fst.hom) ≫ p := by simp
      _ = F.left_map (l ≫ S.bot) ≫ ( by rw [S.comm] ; exact J.fst.hom) ≫ p :=
        by rw [I.fst.hom_inv_id] ; simp
      _ = F.left_map (S.top ≫ r) ≫ J.fst.hom ≫ p := by have comm := S.comm ; aesop_cat
      _ = (F.left_map (S.top ≫ r) ≫ J.fst.hom) ≫ p := by simp
      _ = s ≫ p := by rw [J.snd.left]
      _ = S.top := F.factorization S.top
    comm_bot := by calc
      (s' ≫ I.fst.inv ≫ (by rw [S.comm] ; exact J.fst.hom) ≫ p) ≫ r =
        s' ≫ I.fst.inv ≫ ((by rw [S.comm] ; exact J.fst.hom) ≫ p ≫ r) := by simp
      _ = s' ≫ I.fst.inv ≫ (by rw [S.comm] ; exact F.right_map (S.top ≫ r)) :=
        by have comm := S.comm ; have comm' := J.snd.right ; aesop_cat
      _ = s' ≫ I.fst.inv ≫ (S.comm ▸ F.right_map (S.top ≫ r)) :=
        by rw [← rw_eq_apd S.comm F.right_map]
      _ = s' ≫ I.fst.inv ≫ F.right_map (l ≫ S.bot) :=
        by rw [comm_square_right_map_apd F l r S]
      _ = s' ≫ I.fst.inv ≫ I.fst.hom ≫ p' := by rw [I.snd.right]
      _ = s' ≫ (I.fst.inv ≫ I.fst.hom) ≫ p' := by simp
      _ = s' ≫ p' := by rw [I.fst.inv_hom_id] ; simp
      _ = S.bot := F.factorization S.bot
  }

def FactorizationSystem_diagonal_canonicity
  {L R : MorphismProperty C} (F : FactorizationSystem L R) {A B X Y : C} (l : A ⟶ B) (hl : L l)
  (r : X ⟶ Y) (hr : R r) (S : l □ r) (d : diagonal_filler S) :
  d.map = (FactorizationSystem_diagonal F l hl r hr S).map := by
  let comm : (l ≫ F.left_map d.map) ≫ F.right_map d.map = S.top := by calc
    (l ≫ F.left_map d.map) ≫ F.right_map d.map = l ≫ F.left_map d.map ≫ F.right_map d.map :=
      by simp
    _ = l ≫ d.map := by rw [F.factorization d.map]
    _ = S.top := d.comm_top
  let K := F.factorization_iso S.top (F.image d.map) (l ≫ F.left_map d.map)
    (F.is_closed_comp_left_class.precomp l hl (F.left_map d.map) (F.left_map_in_left_class d.map))
    (F.right_map d.map) (F.right_map_in_right_class d.map) comm
  let comm' : F.left_map d.map ≫ F.right_map d.map ≫ r = S.bot := by calc
    F.left_map d.map ≫ F.right_map d.map ≫ r = (F.left_map d.map ≫ F.right_map d.map) ≫ r :=
      by simp
    _ = d.map ≫ r := by rw [F.factorization d.map]
    _ = S.bot := d.comm_bot
  let K' := F.factorization_iso S.bot (F.image d.map) (F.left_map d.map)
    (F.left_map_in_left_class d.map) ((F.right_map d.map) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.right_map d.map) (F.right_map_in_right_class d.map) r hr) comm'
  let I := F.factorization_iso (l ≫ S.bot) (F.image S.bot) (l ≫ (F.left_map S.bot))
    (F.is_closed_comp_left_class.precomp l hl (F.left_map S.bot) (F.left_map_in_left_class S.bot))
    (F.right_map S.bot) ( F.right_map_in_right_class S.bot)
    (by have fact := F.factorization S.bot ; aesop_cat)
  let fact : F.left_map S.top ≫ F.right_map S.top ≫ r = l ≫ S.bot := by calc
    F.left_map S.top ≫ F.right_map S.top ≫ r = (F.left_map S.top ≫ F.right_map S.top) ≫ r := by
      simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
    _ = l ≫ S.bot := by rw [← S.comm]
  let I' := F.factorization_iso (l ≫ S.bot) (F.image S.top) (F.left_map S.top)
    (F.left_map_in_left_class S.top) ((F.right_map S.top) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.right_map S.top) (F.right_map_in_right_class S.top) r hr) fact
  let kk := K'.fst ≪≫ K.fst.symm
  let ii := I.fst.symm ≪≫ I'.fst
  let fact' : (l ≫ F.left_map S.bot) ≫ F.right_map S.bot = l ≫ S.bot := by calc
    (l ≫ F.left_map S.bot) ≫ F.right_map S.bot = l ≫ (F.left_map S.bot ≫ F.right_map S.bot) := by
      simp
    _ = l ≫ S.bot := by rw [F.factorization S.bot]
  let fact'' : F.left_map S.top ≫ F.right_map S.top ≫ r = l ≫ S.bot := by calc
    F.left_map S.top ≫ F.right_map S.top ≫ r = (F.left_map S.top ≫ F.right_map S.top) ≫ r := by
      simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
    _ = l ≫ S.bot := by rw [← S.comm]
  let comm₀ : (l ≫ F.left_map S.bot) ≫ ii.hom = F.left_map S.top := by calc
    (l ≫ F.left_map S.bot) ≫ ii.hom =
      (l ≫ F.left_map S.bot ≫ I.fst.inv) ≫ I'.fst.hom := by simp ; rfl
    _ = F.left_map (l ≫ S.bot) ≫ I'.fst.hom := by
      have c : l ≫ F.left_map S.bot ≫ I.fst.inv = F.left_map (l ≫ S.bot) := by calc
        l ≫ F.left_map S.bot ≫ I.fst.inv = (l ≫ F.left_map S.bot) ≫ I.fst.inv := by simp
        _ = (F.left_map (l ≫ S.bot) ≫ I.fst.hom) ≫ I.fst.inv := by rw [I.snd.left]
        _ = F.left_map (l ≫ S.bot) ≫ (I.fst.hom ≫ I.fst.inv) := by simp
        _ = F.left_map (l ≫ S.bot) := by rw [I.fst.hom_inv_id] ; simp
      rw [ c ]
    _ = F.left_map S.top := I'.snd.left
  let comm₁ : ii.hom ≫ F.right_map S.top ≫ r = F.right_map S.bot := by calc
    ii.hom ≫ F.right_map S.top ≫ r = (I.fst.inv ≫ I'.fst.hom) ≫ F.right_map S.top ≫ r := by
      simp ; aesop_cat
    _ = I.fst.inv ≫ (I'.fst.hom ≫ F.right_map S.top ≫ r) := by simp
    _ = I.fst.inv ≫ F.right_map (l ≫ S.bot) := by rw [I'.snd.right]
    _ = I.fst.inv ≫ (I.fst.hom ≫ F.right_map S.bot) := by rw [I.snd.right]
    _ = (I.fst.inv ≫ I.fst.hom) ≫ F.right_map S.bot := by simp
    _ = F.right_map S.bot := by rw [I.fst.inv_hom_id] ; simp
  let comm₀' : (l ≫ F.left_map S.bot) ≫ kk.hom = F.left_map S.top := by calc
    (l ≫ F.left_map S.bot) ≫ kk.hom = l ≫ (F.left_map S.bot ≫ K'.fst.hom) ≫ K.fst.inv := by
      simp ; rfl
    _ = l ≫ F.left_map d.map ≫ K.fst.inv := by rw [K'.snd.left]
    _ = (l ≫ F.left_map d.map) ≫ K.fst.inv := by simp
    _ = (F.left_map S.top ≫ K.fst.hom) ≫ K.fst.inv := by rw [K.snd.left]
    _ = F.left_map S.top ≫ (K.fst.hom ≫ K.fst.inv) := by simp
    _ = F.left_map S.top := by rw [K.fst.hom_inv_id] ; simp
  let comm₁' : kk.hom ≫ F.right_map S.top ≫ r = F.right_map S.bot := by calc
    kk.hom ≫ F.right_map S.top ≫ r = K'.fst.hom ≫ K.fst.inv ≫ F.right_map S.top ≫ r := by simp
    _ = K'.fst.hom ≫ K.fst.inv ≫ (K.fst.hom ≫ F.right_map d.map) ≫ r := by rw [K.snd.right]
    _ = K'.fst.hom ≫ (K.fst.inv ≫ K.fst.hom) ≫ F.right_map d.map ≫ r := by simp
    _ = K'.fst.hom ≫ F.right_map d.map ≫ r := by rw [K.fst.inv_hom_id] ; simp
    _ = F.right_map S.bot := K'.snd.right
  let uniq := factorization_iso_is_unique' F (l ≫ S.bot) (F.image S.bot) (F.image S.top)
    (l ≫ F.left_map S.bot) (F.is_closed_comp_left_class.precomp l hl (F.left_map S.bot)
    (F.left_map_in_left_class S.bot)) (F.right_map S.bot) (F.right_map_in_right_class S.bot)
    fact' (F.left_map S.top) (F.left_map_in_left_class S.top) (F.right_map S.top ≫ r)
    (F.is_closed_comp_right_class.precomp (F.right_map S.top) (F.right_map_in_right_class S.top)
    r hr) fact'' ii kk comm₀ comm₁ comm₀' comm₁'
  sorry


def FactorizationSystem_orthogonal
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : orthogonal_class L R := by
  intro A B X Y l hl r hr
  exact {
    diagonal := fun S => FactorizationSystem_diagonal F l hl r hr S
    diagonal_unique := fun S d d' => by sorry
  }
