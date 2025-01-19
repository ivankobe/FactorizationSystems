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

/- The predicate of a class of morphisms being replete -/
def is_replete (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y X' Y' : C⦄ (l : X ⟶ Y) (l' : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
    (_ : i.hom ≫ l' = l ≫ j.hom) (_: W l) , W l'

/- The left class of a factorization system is replete -/
lemma is_replete_left_class
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : is_replete L := by
  intro X Y X' Y' l l' i j c p
  let i' := i.symm
  have eq : l' = i'.hom ≫ l ≫ j.hom := by calc
    l' = i.inv ≫ i.hom ≫ l' := by simp
    _ = i'.hom ≫ i.hom ≫ l' := by rfl
    _ = i'.hom ≫ l ≫ j.hom := by rw [c]
  rw [ eq ]
  apply  F.is_closed_comp_left_class.precomp
  apply F.contains_isos_left_class
  apply  F.is_closed_comp_left_class.precomp
  exact p
  apply F.contains_isos_left_class

/- The right class of a factorization system is replete -/
lemma is_replete_right_class
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : is_replete R := by
  intro X Y X' Y' r r' i j c p
  let i' := i.symm
  have eq : r' = i'.hom ≫ r ≫ j.hom := by calc
    r' = i.inv ≫ i.hom ≫ r' := by simp
    _ = i'.hom ≫ i.hom ≫ r' := by rfl
    _ = i'.hom ≫ r ≫ j.hom := by rw [c]
  rw [ eq ]
  apply  F.is_closed_comp_right_class.precomp
  apply F.contains_isos_right_class
  apply  F.is_closed_comp_right_class.precomp
  exact p
  apply F.contains_isos_right_class

/- The type of weak factorization systems (NB : the terminology here isn't completely standard) -/
structure WeakFactorizationSystem (L R : MorphismProperty C) where
  image : {X Y : C} → (f : X ⟶ Y) → C
  left_map : {X Y : C} → (f : X ⟶ Y) → X ⟶ image f
  left_map_in_left_class : {X Y : C} → (f : X ⟶ Y) → L (left_map f)
  right_map : {X Y : C} → (f : X ⟶ Y) → image f ⟶ Y
  right_map_in_right_class : {X Y : C} → (f : X ⟶ Y) → R (right_map f)
  factorization : {X Y : C} → (f : X ⟶ Y) → left_map f ≫ right_map f = f := by aesop_cat

/- A factorization system determines a weak factorization system -/
def WFS_of_FS (L R : MorphismProperty C) (F : FactorizationSystem L R) :
  WeakFactorizationSystem L R := {
    image := F.image
    left_map := F.left_map
    left_map_in_left_class := F.left_map_in_left_class
    right_map := F.right_map
    right_map_in_right_class := F.right_map_in_right_class
    factorization := F.factorization }

/- The predicate of classes of morphisms being orthogonal -/
def orthogonal_class (L R : MorphismProperty C) :=
  ∀ ⦃A B X Y : C⦄ (l : A ⟶ B) (_ : L l) (r : X ⟶ Y) (_ : R r) , orthogonal l r

/- Towards the proof that the two classes of a factorization system are orthogonal -/

/- If (L,R) is a factorization system, then every (L,R)-square has a diagonal filler -/
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
  let fact : F.left_map S.top ≫ F.right_map S.top ≫ r = l ≫ S.bot := by calc
    F.left_map S.top ≫ F.right_map S.top ≫ r = (F.left_map S.top ≫ F.right_map S.top) ≫ r := by
      simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
    _ = l ≫ S.bot := by rw [← S.comm]
  let J := F.factorization_iso (l ≫ S.bot) (F.image S.top) (F.left_map S.top)
    (F.left_map_in_left_class S.top) ((F.right_map S.top) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.right_map S.top) (F.right_map_in_right_class S.top) r hr) fact
  exact {
    map := s' ≫ I.fst.inv ≫ J.fst.hom ≫ p
    comm_top := by calc
      l ≫ s' ≫ I.fst.inv ≫ J.fst.hom ≫ p = (l ≫ s') ≫ I.fst.inv ≫ J.fst.hom ≫ p := by simp
      _ = (F.left_map (l ≫ S.bot) ≫ I.fst.hom) ≫ I.fst.inv ≫ J.fst.hom ≫ p := by rw [I.snd.left]
      _ = F.left_map (l ≫ S.bot) ≫ (I.fst.hom ≫ I.fst.inv) ≫ J.fst.hom ≫ p := by simp
      _ = F.left_map (l ≫ S.bot) ≫ J.fst.hom ≫ p := by rw [I.fst.hom_inv_id] ; simp
      _ = (F.left_map (l ≫ S.bot) ≫ J.fst.hom) ≫ p := by simp
      _ = s ≫ p := by rw [J.snd.left]
      _ = S.top := F.factorization S.top
    comm_bot := by calc
      (s' ≫ I.fst.inv ≫ J.fst.hom ≫ p) ≫ r = s' ≫ I.fst.inv ≫ (J.fst.hom ≫ p ≫ r) := by simp
      _ = s' ≫ I.fst.inv ≫ F.right_map (l ≫ S.bot) := by rw [J.snd.right]
      _ = s' ≫ I.fst.inv ≫ I.fst.hom ≫ p' := by rw [I.snd.right]
      _ = s' ≫ (I.fst.inv ≫ I.fst.hom) ≫ p' := by simp
      _ = s' ≫ p' := by rw [I.fst.inv_hom_id] ; simp
      _ = S.bot := F.factorization S.bot}

/- An auxiliary lemma for uniqueness of diagonal fillers -/
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
    kk.hom ≫ F.right_map S.top ≫ r = K'.fst.hom ≫ K.fst.inv ≫ F.right_map S.top ≫ r := by
      aesop_cat
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
  calc
    d.map = F.left_map d.map ≫ F.right_map d.map := by rw [F.factorization d.map]
    _ = (F.left_map S.bot ≫ K'.fst.hom) ≫ (K.fst.inv ≫ F.right_map S.top) := by
      rw [K'.snd.left] ; congr ; calc
      F.right_map d.map = (K.fst.inv ≫ K.fst.hom) ≫ F.right_map d.map := by
        rw [K.fst.inv_hom_id] ; simp
      _ = K.fst.inv ≫ (K.fst.hom ≫ F.right_map d.map) := by simp
      _ = K.fst.inv ≫ F.right_map S.top := by rw [K.snd.right]
    _ = F.left_map S.bot ≫ (K'.fst ≪≫ K.fst.symm).hom ≫ F.right_map S.top := by simp
    _ = F.left_map S.bot ≫ kk.hom ≫ F.right_map S.top := by rfl
    _ = F.left_map S.bot ≫ ii.hom ≫ F.right_map S.top := by rw [ uniq ]
    _ = (FactorizationSystem_diagonal F l hl r hr S).map := by aesop_cat

/- The two classes of a factorization system are orthogonal -/
def FactorizationSystem_orthogonal
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : orthogonal_class L R := by
  intro A B X Y l hl r hr
  exact {
    diagonal := fun S => FactorizationSystem_diagonal F l hl r hr S
    diagonal_unique := fun S d d' => by calc
      d.map = (FactorizationSystem_diagonal F l hl r hr S).map :=
        FactorizationSystem_diagonal_canonicity F l hl r hr S d
      _ = d'.map := Eq.symm (FactorizationSystem_diagonal_canonicity F l hl r hr S d') }

/- If (L,R) is a weak factorization system, R is replete and L⊥R,
then R is the right orthogonal complement of L-/
def left_determinacy (L R : MorphismProperty C) (H₁R : is_replete R)
  (H₂ : WeakFactorizationSystem L R) (H₃ : orthogonal_class L R) :
  R = right_orthogonal_complement L := by
  ext X Y r
  apply Iff.intro
  . intro Rr A B l Ll
    exact orthogonal_implies_hom_orthogonal l r (H₃ l Ll r Rr)
  . intro L_orthogonal_r
    let S : H₂.left_map r □ r :=
      { top := 𝟙 X , bot := H₂.right_map r , comm := by have f := H₂.factorization r ; aesop_cat }
    let d : diagonal_filler S :=
      ( hom_orthogonal_implies_orthogonal
        ( L_orthogonal_r (H₂.left_map r) (H₂.left_map_in_left_class r))).diagonal S
    let S' : H₂.left_map r □ H₂.right_map r := { top := H₂.left_map r , bot := H₂.right_map r }
    let δ : diagonal_filler S' := {
      map := d.map ≫ H₂.left_map r
      comm_top := by calc
        H₂.left_map r ≫ d.map ≫ H₂.left_map r =
          (H₂.left_map r ≫ d.map) ≫ H₂.left_map r := by simp
        _ = H₂.left_map r := by rw [d.comm_top] ; simp
      comm_bot := by calc
        (d.map ≫ H₂.left_map r) ≫ H₂.right_map r =
          d.map ≫ (H₂.left_map r ≫ H₂.right_map r) := by simp
        _ = d.map ≫ r := by rw [H₂.factorization r]
        _ = S'.bot := d.comm_bot }
    let δ' : diagonal_filler S' := { map := 𝟙 (H₂.image r) }
    let u : X ≅ H₂.image r := {
      hom := H₂.left_map r
      inv := d.map
      hom_inv_id := d.comm_top
      inv_hom_id := (H₃ (H₂.left_map r) (H₂.left_map_in_left_class r) (H₂.right_map r)
        (H₂.right_map_in_right_class r)).diagonal_unique S' δ δ' }
    exact H₁R (H₂.right_map r) r u.symm (Iso.refl _) (by simp ; exact d.comm_bot)
      (H₂.right_map_in_right_class r)

/- If (L,R) is a weak factorization system, L is replete and L⊥R,
then L is the right orthogonal complement of R-/
def right_determinacy (L R : MorphismProperty C) (H₁L : is_replete L)
  (H₂ : WeakFactorizationSystem L R) (H₃ : orthogonal_class L R) :
  L = left_orthogonal_complement R := by
  ext A B l
  constructor
  case mp =>
    intro Ll X Y r Rr
    exact orthogonal_implies_hom_orthogonal l r (H₃ l Ll r Rr)
  case mpr =>
    intro l_orthogonal_R
    let S : l □ H₂.right_map l :=
      { top := H₂.left_map l , bot := 𝟙 B , comm := by have f := H₂.factorization l ; aesop_cat }
    let d : diagonal_filler S :=
      ( hom_orthogonal_implies_orthogonal
        ( l_orthogonal_R (H₂.right_map l) (H₂.right_map_in_right_class l))).diagonal S
    let S' : H₂.left_map l □ H₂.right_map l := { top := H₂.left_map l , bot := H₂.right_map l }
    let δ : diagonal_filler S' := {
      map := H₂.right_map l ≫ d.map
      comm_top := by calc
        H₂.left_map l ≫ H₂.right_map l ≫ d.map =
          (H₂.left_map l ≫ H₂.right_map l) ≫ d.map := by simp
        _ = l ≫ d.map := by rw [H₂.factorization l]
        _ = H₂.left_map l := d.comm_top
      comm_bot := by have cb := d.comm_bot ; aesop_cat }
    let δ' : diagonal_filler S' := { map := 𝟙 _ }
    let p : H₂.image l ≅ B := {
      hom := H₂.right_map l
      inv := d.map
      hom_inv_id := (H₃ (H₂.left_map l) (H₂.left_map_in_left_class l) (H₂.right_map l)
        (H₂.right_map_in_right_class l)).diagonal_unique S' δ δ'
      inv_hom_id := d.comm_bot }
    exact H₁L (H₂.left_map l) l (Iso.refl _) p (by have f := H₂.factorization l ; aesop_cat)
      (H₂.left_map_in_left_class l)

/- A characterization theorem for factorization systems. (L,R) is a factorization system iff both
L and R are replete, L is orthogonal to R and (L,R) is a weak factorization system. -/
noncomputable
def FactorizationSystem_characterization (L R : MorphismProperty C) (H₁L : is_replete L)
  (H₁R : is_replete R) (H₂ : WeakFactorizationSystem L R) (H₃ : orthogonal_class L R) :
  FactorizationSystem L R := {
    image := H₂.image
    left_map := H₂.left_map
    left_map_in_left_class := H₂.left_map_in_left_class
    right_map := H₂.right_map
    right_map_in_right_class := H₂.right_map_in_right_class
    factorization := H₂.factorization
    contains_isos_left_class := by
      rw [ right_determinacy L R H₁L H₂ H₃ ]
      exact Arrow.contains_isos_left_ort_complement R
    contains_isos_right_class := by
      rw [ left_determinacy L R H₁R H₂ H₃ ]
      exact Arrow.contains_isos_right_ort_complement L
    is_closed_comp_left_class := {
      precomp := fun l Ll l' Ll' => (Eq.symm (right_determinacy L R H₁L H₂ H₃)) ▸
        Arrow.is_closed_under_comp_l_ort_complement
          R l ((right_determinacy L R H₁L H₂ H₃) ▸ Ll) l' ((right_determinacy L R H₁L H₂ H₃) ▸ Ll')
      postcomp := fun l' Ll' l Ll => (Eq.symm (right_determinacy L R H₁L H₂ H₃)) ▸
        Arrow.is_closed_under_comp_l_ort_complement
          R l ((right_determinacy L R H₁L H₂ H₃) ▸ Ll) l' ((right_determinacy L R H₁L H₂ H₃) ▸ Ll')}
    is_closed_comp_right_class := {
      precomp := fun r Rr r' Rr' => (Eq.symm (left_determinacy L R H₁R H₂ H₃)) ▸
        Arrow.is_closed_under_comp_r_ort_complement
          L r ((left_determinacy L R H₁R H₂ H₃) ▸ Rr) r' ((left_determinacy L R H₁R H₂ H₃) ▸ Rr')
      postcomp := fun r' Rr' r Rr => (Eq.symm (left_determinacy L R H₁R H₂ H₃)) ▸
        Arrow.is_closed_under_comp_r_ort_complement
          L r ((left_determinacy L R H₁R H₂ H₃) ▸ Rr) r' ((left_determinacy L R H₁R H₂ H₃) ▸ Rr') }
    factorization_iso := fun f E u Lu p Rp fact => by
      have orth₀' : left_orthogonal_complement R (H₂.left_map f) :=
        (right_determinacy L R H₁L H₂ H₃) ▸ (H₂.left_map_in_left_class f)
      let orth₀ : orthogonal (H₂.left_map f) p := hom_orthogonal_implies_orthogonal (orth₀' p Rp)
      let S₀ : (H₂.left_map f) □ p := {
        top := u
        bot := H₂.right_map f
        comm := by have c₀ := H₂.factorization f ; have c₁ := fact ; aesop_cat }
      let d : H₂.image f ⟶ E := (orth₀.diagonal S₀).map
      let orth₁' : left_orthogonal_complement R u := (right_determinacy L R H₁L H₂ H₃) ▸ Lu
      let orth₁ : orthogonal u (H₂.right_map f) :=
        hom_orthogonal_implies_orthogonal (orth₁' (H₂.right_map f) (H₂.right_map_in_right_class f))
      let S₁ : u □ (H₂.right_map f) :=
        { top := H₂.left_map f , bot := p , comm := have c := S₀.comm ; by aesop_cat}
      let r : E ⟶ H₂.image f := (orth₁.diagonal S₁).map
      let I : H₂.image f ≅ E := {
        hom := d
        inv := r
        hom_inv_id := by
          let T : H₂.left_map f □  H₂.right_map f := {top := H₂.left_map f , bot := H₂.right_map f}
          let δ : diagonal_filler T := {
            map := d ≫ r
            comm_top := by calc
              H₂.left_map f ≫ d ≫ r = (H₂.left_map f ≫ d) ≫ r := by simp
              _ = u ≫ r := by rw [ (orth₀.diagonal S₀).comm_top ]
              _ = H₂.left_map f := by rw [ (orth₁.diagonal S₁).comm_top ]
            comm_bot := by calc
              (d ≫ r) ≫ H₂.right_map f = d ≫ r ≫ H₂.right_map f := by simp
              _ = d ≫ p := by rw [ (orth₁.diagonal S₁).comm_bot ]
              _ = H₂.right_map f := by rw [ (orth₀.diagonal S₀).comm_bot ] }
          let δ' : diagonal_filler T := { map := 𝟙 _ }
          exact (H₃ (H₂.left_map f) (H₂.left_map_in_left_class f) (H₂.right_map f)
            (H₂.right_map_in_right_class f)).diagonal_unique T δ δ'
        inv_hom_id := by
          let T : u □ p := {top := u , bot := p}
          let δ : diagonal_filler T := {
            map := r ≫ d
            comm_top := by calc
              u ≫ r ≫ d = (u ≫ r) ≫ d := by simp
              _ = H₂.left_map f ≫ d := by rw [ (orth₁.diagonal S₁).comm_top ]
              _ = u := by rw [ (orth₀.diagonal S₀).comm_top ]
            comm_bot := by calc
              (r ≫ d) ≫ p = r ≫ d ≫ p := by simp
              _ = r ≫ H₂.right_map f := by rw [ (orth₀.diagonal S₀).comm_bot ]
              _ = p := by rw [ (orth₁.diagonal S₁).comm_bot ] }
          let δ' : diagonal_filler T := { map := 𝟙 _ }
          exact (H₃ u Lu p Rp).diagonal_unique T δ δ' }
      apply PSigma.mk I
      apply And.intro
      . exact (orth₀.diagonal S₀).comm_top
      . exact (orth₀.diagonal S₀).comm_bot
    factorization_iso_is_unique := fun f E u Lu p Rp fact I c c' => by
      ext
      have orth₀' : left_orthogonal_complement R (H₂.left_map f) :=
        (right_determinacy L R H₁L H₂ H₃) ▸ (H₂.left_map_in_left_class f)
      let orth₀ : orthogonal (H₂.left_map f) p := hom_orthogonal_implies_orthogonal (orth₀' p Rp)
      let S₀ : (H₂.left_map f) □ p := {
        top := u
        bot := H₂.right_map f
        comm := by have c₀ := H₂.factorization f ; have c₁ := fact ; aesop_cat }
      let δ : diagonal_filler S₀ := orth₀.diagonal S₀
      let δ' : diagonal_filler S₀ := { map := I.hom , comm_top := c , comm_bot := c' }
      have eq := (H₃ (H₂.left_map f) (H₂.left_map_in_left_class f) p Rp).diagonal_unique S₀ δ δ'
      aesop_cat }
