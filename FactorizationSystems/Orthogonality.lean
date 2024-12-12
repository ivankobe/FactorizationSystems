import FactorizationSystems.Examples
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-
Given two morphisms l: A ⟶ B and r: X ⟶ Y in a category C, we say that l is left orthogonal to r
or that r is right orthogonal to l, if for every commuting square of the form

    A ----f----> X
    |            |
  l |            |
    |            |
    v            v
    B ----g----> Y,

there exists a unique diagonal filler d: B ⟶ X making both triangles commute.
-/

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]
variable [HasPullbacks : Limits.HasPullbacks C]


/- The sort of commuting squares in a category C -/
structure square (A B X Y : C) where
  left : A ⟶ B
  right : X ⟶ Y
  top : A ⟶ X
  bot : B ⟶ Y
  comm : left ≫ bot = top ≫ right := by aesop_cat

/- The sort of commuting squares in a category C with specified vertical maps -/
structure square_completion {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) where
  top : A ⟶ X
  bot : B ⟶ Y
  comm : l ≫ bot = top ≫ r := by aesop_cat

infixl:75 " □ " => square_completion

/- Forgetting the specification of vertical maps -/
@[reducible]
def square_of_square_completion
    {A B X Y : C} {l : A ⟶ B} {r : X ⟶ Y} (S' : l □ r) :
    square A B X Y where
  left := l
  right := r
  top := S'.top
  bot := S'.bot
  comm := S'.comm

variable {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

/- The sort of diagonal fillers of a square with specified vertical maps -/
structure diagonal_filler
    {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} (S : f □ g) where
  map : B ⟶ X
  comm_top : f ≫ map = S.top
  comm_bot : map ≫ g = S.bot

/- The sort of proofs that morphisms f and g are orthogonal -/
structure orthogonal {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) where
  diagonal : (S : f □ g) → diagonal_filler S
  diagonal_unique :
    (S : f □ g) → (d : diagonal_filler S) → (d' : diagonal_filler S) → d.map = d'.map

/- We now start working towards an alternative characterization of orthogonality: morphisms l and r
are orthogonal iff the commuting square
                l^*
    Hom(B,X)--------->Hom(A,X)
      |                 |
  r_* |                 |r_*
      |                 |
      v                 V
    Hom(B,Y)--------->Hom(A,Y)  is a pullback square in Set.
                l^*
-/

/- We first construct this commuting square in Set-/

@[reducible]
def hom_square_left : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ X) ⟶ (A ⟶ X)) :=
  fun l _ f => l ≫ f

@[reducible]
def hom_square_right : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ Y) ⟶ (A ⟶ Y)) :=
  fun l _ f => l ≫ f

@[reducible]
def hom_square_top : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ X) ⟶ (B ⟶ Y)) :=
  fun _ r f => f ≫ r

@[reducible]
def hom_square_bot : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((A ⟶ X) ⟶ (A ⟶ Y)) :=
  fun _ r f => f ≫ r

@[reducible]
def hom_square : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) →
    square (B ⟶ X) (A ⟶ X) (B ⟶ Y) (A ⟶ Y) := fun l r =>
  {
    left := hom_square_left l r
    right := hom_square_right l r
    top := hom_square_top l r
    bot := hom_square_bot l r
    comm := by aesop_cat
  }

/- The canonical pullback of the cospan given by the right and bottom maps in the hom square -/
def hom_cospan_pullback : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → Type v := by
  intro A B X Y l r
  exact Limits.pullback (hom_square_right l r) (hom_square_bot l r)

noncomputable
/- The associated pullback cone -/
def hom_cospan_pullback_cone : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) →
    Limits.PullbackCone (hom_square_right l r) (hom_square_bot l r) := by
  intro A B X Y l r
  exact Limits.pullback.cone (hom_square_right l r) (hom_square_bot l r)


@[reducible]
noncomputable
/- The first projection of the hom pullback -/
def hom_cospan_pullback_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_cospan_pullback l r) → (B ⟶ Y) :=
  Limits.pullback.fst (hom_square_right l r) (hom_square_bot l r)

@[reducible]
noncomputable
/- The second projection of the hom pullback -/
def hom_cospan_pullback_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_cospan_pullback l r) → (A ⟶ X) :=
  Limits.pullback.snd (hom_square_right l r) (hom_square_bot l r)

@[reducible]
noncomputable
/- The universal property of the hom pullback -/
def hom_cospan_pullback_lift {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (hom_square_right l r) = ψ ≫ (hom_square_bot l r) := by aesop_cat) :
    W ⟶ hom_cospan_pullback l r :=
  Limits.pullback.lift φ ψ comm

def hom_cospan_pullback_lift_fst {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (hom_square_right l r) = ψ ≫ (hom_square_bot l r) := by aesop_cat) :
    hom_cospan_pullback_lift l r φ ψ comm ≫ hom_cospan_pullback_fst l r = φ :=
  Limits.pullback.lift_fst φ ψ comm

def hom_cospan_pullback_lift_snd {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (hom_square_right l r) = ψ ≫ (hom_square_bot l r) := by aesop_cat) :
    hom_cospan_pullback_lift l r φ ψ comm ≫ hom_cospan_pullback_snd l r = ψ :=
  Limits.pullback.lift_snd φ ψ comm

@[reducible]
noncomputable
/- The hom pullback square is in particular commutative -/
def hom_cospan_pullback_condition {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_cospan_pullback_fst l r) ≫ (hom_square_right l r) =
    (hom_cospan_pullback_snd l r) ≫ (hom_square_bot l r) :=
  Limits.pullback.condition

@[reducible]
/- The property of a commuting square being Cartesian -/
def is_cartesian_square {A B X Y : C} (S : square A B X Y) : Prop :=
  IsIso (Limits.pullback.lift S.top S.left (by rw [S.comm]))

@[reducible]
/- The second characterization of orthogonality via the hom square in Set -/
def hom_orthogonal {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Prop :=
  is_cartesian_square (hom_square l r)

/- We construct a map from Hom(B,X) into the pullback
of the hom square via the universal mapping property -/
noncomputable
def diagonals_hom_cospan_pullback_top {A B X  Y: C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ (A ⟶ X) := fun f => l ≫ f

noncomputable
def diagonals_hom_cospan_pullback_bot {A B X Y: C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ (B ⟶ Y) := fun f => f ≫ r

def diagonals_hom_cospan_pullback_lift_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (diagonals_hom_cospan_pullback_bot l r) ≫ (hom_square_right l r) =
    (diagonals_hom_cospan_pullback_top l r) ≫ (hom_square_bot l r) := by
  ext d
  calc
    (diagonals_hom_cospan_pullback_bot l r ≫ hom_square_right l r) d = l ≫ d ≫ r := by aesop_cat
    _ = (hom_square_bot l r) (l ≫ d) := by simp
    _ = (hom_square_bot l r) ((diagonals_hom_cospan_pullback_top l r ) d) := by rfl
    _ = (diagonals_hom_cospan_pullback_top l r ≫ hom_square_bot l r) d := by rfl

noncomputable
def diagonals_hom_cospan_pullback_lift {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ hom_cospan_pullback l r := by
  intro f
  exact hom_cospan_pullback_lift l r
    (diagonals_hom_cospan_pullback_bot l r)
    (diagonals_hom_cospan_pullback_top l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)
    f

def diagonals_hom_cospan_pullback_lift_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_pullback_lift l r ≫ hom_cospan_pullback_fst l r =
    (diagonals_hom_cospan_pullback_bot l r) :=
  Limits.pullback.lift_fst
    (diagonals_hom_cospan_pullback_bot l r)
    (diagonals_hom_cospan_pullback_top l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

def diagonals_hom_cospan_pullback_lift_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_pullback_lift l r ≫ hom_cospan_pullback_snd l r =
    (diagonals_hom_cospan_pullback_top l r) :=
  Limits.pullback.lift_snd
    (diagonals_hom_cospan_pullback_bot l r)
    (diagonals_hom_cospan_pullback_top l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

/- Given an element in the pullback of the hom
square in Set, we construct a commuting square in C -/
noncomputable
def hom_cospan_pullback_to_square_completion
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (x : hom_cospan_pullback l r) :
    l □ r := by
  let x'  := (hom_cospan_pullback_fst l r) x
  let x'' := (hom_cospan_pullback_snd l r)  x
  have S : l □ r := {
      top := x''
      bot := x'
      comm := by calc
        l ≫ x' = hom_square_right l r x' := by simp
        _ = ((hom_cospan_pullback_fst l r) ≫ (hom_square_right l r)) x := by simp
        _ = ((hom_cospan_pullback_snd l r) ≫ (hom_square_bot l r)) x := by rw [Limits.pullback.condition]
        _ = hom_square_bot l r x'' := by simp
        _ = x'' ≫ r := by simp
  }
  exact S

noncomputable
/- With the assumption that l and r are orthognal, we can construct from an
element in the pullback of the hom square a diagonal filler of this square -/
def hom_cospan_pullback_to_diagonal_filler
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (hom_square_right l r) (hom_square_bot l r)) :
    diagonal_filler (hom_cospan_pullback_to_square_completion l r x) := by
  let ⟨d,S⟩ := h
  exact d (hom_cospan_pullback_to_square_completion l r x)

noncomputable
def hom_cospan_pullback_to_diagonal_filler_map
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r) :
    (Limits.pullback (hom_square_right l r) (hom_square_bot l r)) ⟶ (B ⟶ X) := by
  intro x
  let ⟨d,S⟩ := h
  exact (hom_cospan_pullback_to_diagonal_filler l r h x).map

noncomputable
def hom_cospan_pullback_to_diagonal_filler_map_comm_top
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (hom_square_right l r) (hom_square_bot l r)) :
    l ≫ (hom_cospan_pullback_to_diagonal_filler_map l r h x) =
    (hom_cospan_pullback_to_square_completion l r x).top :=
  (hom_cospan_pullback_to_diagonal_filler l r h x).comm_top

noncomputable
def hom_cospan_pullback_to_diagonal_filler_map_comm_bot
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (hom_square_right l r) (hom_square_bot l r)) :
    (hom_cospan_pullback_to_diagonal_filler_map l r h x) ≫ r =
    (hom_cospan_pullback_to_square_completion l r x).bot :=
  (hom_cospan_pullback_to_diagonal_filler l r h x).comm_bot

omit HasPullbacks

/- If morphisms l and r in C are orthogonal, then the hom square is cartesian -/
lemma orthogonal_implies_hom_orthogonal :
    {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → (orthogonal l r) → (hom_orthogonal l r) := by
  intro A B X Y l r ⟨d,u⟩
  unfold hom_orthogonal
  unfold is_cartesian_square
  use hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩
  constructor
  . ext δ
    simp
    let i := hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩
    let j := Limits.pullback.lift
      (hom_square l r).top (hom_square l r).left (is_cartesian_square.proof_2 (hom_square l r))
    let S : l □ r := { top := l ≫ δ , bot := δ ≫ r }
    let Δ : diagonal_filler S := {
      map := δ
      comm_top := by aesop_cat
      comm_bot := by aesop_cat
    }
    let comm_snd :=  Limits.pullback.lift_snd
      (hom_square l r).top (hom_square l r).left (is_cartesian_square.proof_2 (hom_square l r))
    let comm_fst :=  Limits.pullback.lift_fst
      (hom_square l r).top (hom_square l r).left (is_cartesian_square.proof_2 (hom_square l r))
    let Δ' : diagonal_filler S := {
      map := i (j δ)
      comm_top := by calc
        l ≫ i (j δ) = (hom_cospan_pullback_to_square_completion l r (j δ)).top :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_top l r ⟨d,u⟩ (j δ)
        _ = Limits.pullback.snd (hom_square_right l r) (hom_square_bot l r) (j δ) := by aesop_cat
        _ = (Limits.pullback.lift (hom_square l r).top (hom_square l r).left
            (is_cartesian_square.proof_2 (hom_square l r)) ≫
            Limits.pullback.snd (hom_square l r).right (hom_square l r).bot) δ := by rfl
        _ = (hom_square l r).left δ := by rw [comm_snd]
      comm_bot := by calc
        i (j δ) ≫ r = (hom_cospan_pullback_to_square_completion l r (j δ)).bot :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_bot l r ⟨d,u⟩ (j δ)
        _ = Limits.pullback.fst (hom_square_right l r) (hom_square_bot l r) (j δ) := by aesop_cat
        _ = (Limits.pullback.lift (hom_square l r).top (hom_square l r).left
            (is_cartesian_square.proof_2 (hom_square l r)) ≫
            Limits.pullback.fst (hom_square l r).right (hom_square l r).bot) δ := by rfl
        _ = (hom_square l r).top δ := by rw [comm_fst]
      }
    calc
      i (j δ) = Δ'.map := by rfl
      _ = Δ.map := by rw [← u _ Δ Δ']
      _ = δ := by rfl
  . apply Limits.pullback.hom_ext
    simp
    ext x
    let g := Limits.pullback.fst (hom_square l r).right (hom_square l r).bot x
    let δ := (hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩)
    calc
      (δ ≫ (hom_square l r).top) x = (hom_square l r).top (δ x) := by simp
      _ = (δ x) ≫ r := by aesop_cat
      _ = (hom_cospan_pullback_to_square_completion l r x).bot :=
        hom_cospan_pullback_to_diagonal_filler_map_comm_bot l r ⟨d,u⟩ x
      _ = g := by aesop_cat
    simp
    ext x
    let f := Limits.pullback.snd (hom_square l r).right (hom_square l r).bot x
    let δ := (hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩)
    calc
      (δ ≫ (hom_square l r).left) x = (hom_square l r).left (δ x) := by simp
      _ = l ≫ (δ x) := by aesop_cat
      _ = (hom_cospan_pullback_to_square_completion l r x).top :=
        hom_cospan_pullback_to_diagonal_filler_map_comm_top l r ⟨d,u⟩ x
      _ = f := by aesop_cat

/- We now start working towards the proof of the implication in the other direction -/

noncomputable
/- The cone associated to the pullback of the hom square -/
def hom_pullback_cone
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.PullbackCone (hom_square l r).right (hom_square l r).bot :=
  Limits.pullback.cone (hom_square l r).right (hom_square l r).bot

noncomputable
/- The proof that this cone is a limit cone-/
def hom_pullback_cone_isLimit
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.IsLimit (hom_pullback_cone l r) :=
  Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot

/- The components of this limit cone-/

def hom_pullback_cone_point {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Type v :=
  (hom_pullback_cone l r).pt

noncomputable
def hom_pullback_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : hom_pullback_cone_point l r ⟶ (B ⟶ Y) :=
  Limits.pullback.fst (hom_square l r).right (hom_square l r).bot

noncomputable
def hom_pullback_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : hom_pullback_cone_point l r ⟶ (A ⟶ X) :=
  Limits.pullback.snd (hom_square l r).right (hom_square l r).bot

/- We construct a cone over the same cospan with apex Hom(B,X) -/

def diagonals_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_square l r).top ≫ (hom_square l r).right = (hom_square l r).left ≫ (hom_square l r).bot
    := by rw [(hom_square l r).comm]

def diagonals_cone
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.PullbackCone (hom_square l r).right (hom_square l r).bot :=
  Limits.PullbackCone.mk (hom_square l r).top (hom_square l r).left (diagonals_comm l r)

def diagonals_cone_point
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Type v :=
  (diagonals_cone l r).pt

def diagonals_cone_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_cone_point l r ⟶ (B ⟶ Y) :=
  Limits.PullbackCone.fst (diagonals_cone l r)

def diagonals_cone_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_cone_point l r ⟶ (A ⟶ X) :=
  Limits.PullbackCone.snd (diagonals_cone l r)

noncomputable
/- The map from Hom(B,X) into the canonical pullback -/
def diagonals_hom_cospan_lift
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_cone_point l r ⟶ hom_pullback_cone_point l r :=
  (hom_pullback_cone_isLimit l r).lift (diagonals_cone l r)

noncomputable
def diagonals_hom_cospan_lift_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_lift l r ≫ hom_pullback_fst l r = (hom_square l r).top :=
  (hom_pullback_cone_isLimit l r).fac (diagonals_cone l r) Limits.WalkingCospan.left

noncomputable
def diagonals_hom_cospan_lift_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_lift l r ≫ hom_pullback_snd l r = (hom_square l r).left :=
  (hom_pullback_cone_isLimit l r).fac (diagonals_cone l r) Limits.WalkingCospan.right

@[reducible]
/- An auxiliary definition of orthogonality that behaves much better -/
def hom_orthogonal_aux {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Prop :=
  IsIso (diagonals_hom_cospan_lift l r)

def hom_orthogonal_implies_hom_orthogonal_aux
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal l r) :
    hom_orthogonal l r := h

def hom_orthogonal_aux_implies_hom_orthogonal
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    hom_orthogonal l r := h

noncomputable
/- The isomorphism from Hom(B,X) into the canonical pullback -/
def hom_orthogonal_aux_hom {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
      (B ⟶ X) ⟶ (hom_cospan_pullback l r) :=
  (asIso (diagonals_hom_cospan_lift l r)).hom

noncomputable
/-The inverse of the isomorphism from Hom(B,X) into the canonical pullback -/
def hom_orthogonal_aux_inv {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (hom_cospan_pullback l r) ⟶ (B ⟶ X) :=
  (asIso (diagonals_hom_cospan_lift l r)).inv

def hom_orthogonal_aux_hom_inv_id
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (hom_orthogonal_aux_hom l r h) ≫ (hom_orthogonal_aux_inv l r h) = 𝟙 (B ⟶ X) :=
  (asIso (diagonals_hom_cospan_lift l r)).hom_inv_id

def hom_orthogonal_aux_inv_hom_id
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (hom_orthogonal_aux_inv l r h) ≫ (hom_orthogonal_aux_hom l r h) =
    𝟙 (hom_cospan_pullback l r) :=
  (asIso (diagonals_hom_cospan_lift l r)).inv_hom_id

/- We now prove that the cone with apex Hom(B,X) is a limit cone -/

@[reducible]
noncomputable
def hom_orthogonal_aux_lift
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    ∀ s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot,
    s.pt ⟶ diagonals_cone_point l r := by
  intro s
  let lift : s.pt ⟶ hom_pullback_cone_point l r
    := (Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot).lift s
  exact lift ≫ hom_orthogonal_aux_inv l r h

@[reducible]
def hom_orthogonal_aux_fac_left
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    ∀ s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot,
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_fst l r = s.fst := by
  intro s
  let lift : s.pt ⟶ hom_pullback_cone_point l r :=
    (Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot).lift s
  calc
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_fst l r =
    lift ≫ (hom_orthogonal_aux_inv l r h ≫ diagonals_cone_fst l r) := by rfl
    _ = lift ≫ hom_cospan_pullback_fst l r := by
      have triangle_comm :
        (diagonals_hom_cospan_pullback_lift l r) ≫ hom_cospan_pullback_fst l r =
        (hom_square l r).top := diagonals_hom_cospan_pullback_lift_fst l r
      apply whisker_eq lift
      calc
        hom_orthogonal_aux_inv l r h ≫ (hom_square l r).top =
        hom_orthogonal_aux_inv l r h ≫
          ((diagonals_hom_cospan_pullback_lift l r) ≫ hom_cospan_pullback_fst l r) :=
          by rw [triangle_comm]
        _ = (hom_orthogonal_aux_inv l r h ≫ diagonals_hom_cospan_pullback_lift l r) ≫
          hom_cospan_pullback_fst l r := by aesop_cat
        _ = (hom_orthogonal_aux_inv l r h ≫ hom_orthogonal_aux_hom l r h) ≫
          hom_cospan_pullback_fst l r := by rfl
        _ = hom_cospan_pullback_fst l r := by rw [hom_orthogonal_aux_inv_hom_id l r h] ; simp
    _ = s.fst := by aesop_cat

noncomputable
def hom_orthogonal_aux_fac_right
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    ∀ s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot,
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_snd l r = s.snd := by
  intro s
  let lift : s.pt ⟶ (hom_cospan_pullback l r) :=
    (Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot).lift s
  calc
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_snd l r =
    lift ≫ (hom_orthogonal_aux_inv l r h ≫ diagonals_cone_snd l r) := by rfl
    _ = lift ≫ hom_cospan_pullback_snd l r := by
      have triangle_comm :
        (diagonals_hom_cospan_pullback_lift l r) ≫ hom_cospan_pullback_snd l r =
        (hom_square l r).left := diagonals_hom_cospan_pullback_lift_snd l r
      apply whisker_eq lift
      calc
        hom_orthogonal_aux_inv l r h ≫ (hom_square l r).left =
        hom_orthogonal_aux_inv l r h ≫
          (diagonals_hom_cospan_pullback_lift l r ≫ hom_cospan_pullback_snd l r) :=
          by rw [triangle_comm]
        _ = (hom_orthogonal_aux_inv l r h ≫ hom_orthogonal_aux_hom l r h) ≫
          hom_cospan_pullback_snd l r := by rfl
        _ = hom_cospan_pullback_snd l r := by rw [hom_orthogonal_aux_inv_hom_id l r] ; simp
    _ = s.snd := by aesop_cat

noncomputable
def hom_orthogonal_aux_uniq
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (∀ (s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot) (m : s.pt ⟶ B ⟶ X),
      m ≫ (hom_square l r).top = s.fst →
      m ≫ (hom_square l r).left = s.snd →
      m = hom_orthogonal_aux_lift l r h s) := by
  intro s m comm₁ comm₂
  unfold hom_orthogonal_aux_lift
  have comm₁' := by calc
    m ≫ ((hom_orthogonal_aux_hom l r h) ≫ (hom_pullback_fst l r)) = m ≫ hom_square_top l r := by
      apply whisker_eq m
      exact diagonals_hom_cospan_lift_fst l r
    _ = s.fst := comm₁
    _ = s.π.app Limits.WalkingCospan.left := by rfl
    _ = (hom_pullback_cone_isLimit l r).lift s ≫
        (hom_pullback_cone l r).π.app Limits.WalkingCospan.left := by
      rw [←(hom_pullback_cone_isLimit l r).fac s Limits.WalkingCospan.left]
    _ = (hom_pullback_cone_isLimit l r).lift s ≫ (hom_pullback_fst l r) := by rfl
  have comm₂' : m ≫ (hom_orthogonal_aux_hom l r h) ≫ (hom_pullback_snd l r) =
      (hom_pullback_cone_isLimit l r).lift s ≫ (hom_pullback_snd l r) := by calc
    m ≫ ((hom_orthogonal_aux_hom l r h) ≫ (hom_pullback_snd l r)) = m ≫ hom_square_left l r := by
      apply whisker_eq m
      exact diagonals_hom_cospan_lift_snd l r
    _ = s.snd := comm₂
    _ = s.π.app Limits.WalkingCospan.right := by rfl
    _ = (hom_pullback_cone_isLimit l r).lift s ≫
        (hom_pullback_cone l r).π.app Limits.WalkingCospan.right := by
      rw [←(hom_pullback_cone_isLimit l r).fac s Limits.WalkingCospan.right]
    _ = (hom_pullback_cone_isLimit l r).lift s ≫ (hom_pullback_snd l r) := by rfl
  have whee : m ≫ hom_orthogonal_aux_hom l r h = (hom_pullback_cone_isLimit l r).lift s :=
    Limits.pullback.hom_ext comm₁' comm₂'
  calc
    m = m ≫ (hom_orthogonal_aux_hom l r h ≫ hom_orthogonal_aux_inv l r h) :=
      by rw [hom_orthogonal_aux_hom_inv_id l r h] ; aesop_cat
    _ = (m ≫ hom_orthogonal_aux_hom l r h) ≫ hom_orthogonal_aux_inv l r h := by rfl
    _ = (hom_pullback_cone_isLimit l r).lift s ≫ hom_orthogonal_aux_inv l r h := by rw [whee]

noncomputable
def hom_orthogonal_aux_implies_is_pullback_diagonals
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    Limits.IsLimit (diagonals_cone l r) :=
  Limits.PullbackCone.IsLimit.mk
    (diagonals_comm l r)
    (hom_orthogonal_aux_lift l r h)
    (hom_orthogonal_aux_fac_left l r h)
    (hom_orthogonal_aux_fac_right l r h)
    (hom_orthogonal_aux_uniq l r h)

/- Given a commuting square in C with vertical morphisms l and r, we construct a cone over the
hom-cospan in Set with apex the terminal object -/

def square_completion_cone_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S :  l □ r)
    : PUnit ⟶ (A ⟶ X) :=
  fun _ => S.top

def square_completion_cone_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S :  l □ r)
    : PUnit ⟶ (B ⟶ Y) :=
  fun _ => S.bot

def square_completion_cone_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S :  l □ r) :
    square_completion_cone_fst l r S ≫ (hom_square l r).right =
    square_completion_cone_snd l r S ≫ (hom_square l r).bot := by
  have comm := S.comm
  aesop_cat

def square_completion_cone {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S :  l □ r) :
    Limits.PullbackCone (hom_square l r).right (hom_square l r).bot :=
  Limits.PullbackCone.mk
    (square_completion_cone_fst l r S)
    (square_completion_cone_snd l r S)
    (square_completion_cone_comm l r S)

/- Given a diagonal filler of a square S, we construct a map in Set
from the terminal object into the apex Hom(B,X) of the pullback cone -/
def diagonal_filler_to_pullback
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S :  l □ r) (δ : diagonal_filler S) :
    PUnit ⟶ diagonals_cone_point l r :=
  fun _ => δ.map

noncomputable
/- If the hom square is cartesian, then l and r are orthogonal -/
def is_hom_orthogonal_aux_implies_is_orthogonal
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) : orthogonal l r where
  diagonal := by
    intro S
    exact {
      map := (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
        (square_completion_cone l r S) PUnit.unit
      comm_top := by
        have comm : (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
            (square_completion_cone l r S) ≫
            (hom_square l r).left =
            (fun _ => S.top) :=
          (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).fac
          (square_completion_cone l r S) Limits.WalkingCospan.right
        calc
          l ≫ ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) PUnit.unit) =
          ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) ≫ (hom_square l r).left) PUnit.unit := by rfl
          _ = (fun _ : PUnit.{v} => S.top) PUnit.unit := by rw [comm]
          _ = S.top := by rfl
      comm_bot := by
        have comm : (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
            (square_completion_cone l r S) ≫
            (hom_square l r).top =
            (fun _ => S.bot) :=
          (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).fac
          (square_completion_cone l r S) Limits.WalkingCospan.left
        calc
          ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) PUnit.unit) ≫ r =
          ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) ≫ (hom_square l r).top) PUnit.unit := by rfl
          _ = (fun _ : PUnit.{v} => S.bot) PUnit.unit := by rw [comm]
          _ = S.bot := by rfl
    }
  diagonal_unique := by
    intro S d d'
    have comm₁ :
        (diagonal_filler_to_pullback l r S d) ≫ diagonals_cone_fst l r =
        (diagonal_filler_to_pullback l r S d') ≫ diagonals_cone_fst l r:= by
      apply (homOfElement_eq_iff
        ((diagonal_filler_to_pullback l r S d ≫ diagonals_cone_fst l r) PUnit.unit)
        ((diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_fst l r) PUnit.unit)).mpr
      calc
        (diagonal_filler_to_pullback l r S d ≫ diagonals_cone_fst l r) PUnit.unit =
        d.map ≫ r:= by rfl
        _ = S.bot := by rw [d.comm_bot]
        _ = d'.map ≫ r := by rw [d'.comm_bot]
        _ = (diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_fst l r) PUnit.unit := by rfl
    have comm₂ :
        (diagonal_filler_to_pullback l r S d) ≫ diagonals_cone_snd l r =
        (diagonal_filler_to_pullback l r S d') ≫ diagonals_cone_snd l r:= by
      apply (homOfElement_eq_iff
        ((diagonal_filler_to_pullback l r S d ≫ diagonals_cone_snd l r) PUnit.unit)
        ((diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_snd l r) PUnit.unit)).mpr
      calc
        (diagonal_filler_to_pullback l r S d ≫ diagonals_cone_snd l r) PUnit.unit =
        l ≫ d.map:= by rfl
        _ = S.top := by rw [d.comm_top]
        _ = l ≫ d'.map := by rw [d'.comm_top]
        _ = (diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_snd l r) PUnit.unit := by rfl
    have unique := Limits.PullbackCone.IsLimit.hom_ext
      (hom_orthogonal_aux_implies_is_pullback_diagonals l r h) comm₁ comm₂
    calc
      d.map = diagonal_filler_to_pullback l r S d PUnit.unit := by rfl
      _ = diagonal_filler_to_pullback l r S d' PUnit.unit := by rw [unique]
      _ = d'.map := by rfl
