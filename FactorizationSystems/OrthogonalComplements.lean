import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Comma

import FactorizationSystems.Basic
import FactorizationSystems.Orthogonality

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]


/- We use hom_orthogonality here not because we want to but because it is a proposition -/
def right_orthogonal_complement : (W: MorphismProperty C) → MorphismProperty C := by
  intro W _ _ f
  exact ∀ ⦃A B : C ⦄ (g : A ⟶ B) (p : W g) , (hom_orthogonal g f)

namespace Arrow

/- We haven't found this in the library, so we first show that the forgetfull functor
U : [I,C] ⥤ C ; U : (f : X ⟶ Y) ↦ X ; preserves limits. -/

/- A cone over f : J ⥤ Arrow C determines a cone over f ⋙ leftFunc -/
@[reducible]
def source_cone_arrow_cone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (Cf : Limits.Cone f) :
  Limits.Cone (f ⋙ leftFunc) := {
    pt := leftFunc.obj Cf.pt
    π := {
      app := fun i => leftFunc.map (Cf.π.app i)
      naturality := by
        intro i j α
        have naturality' := Cf.π.naturality α
        calc
          ((Functor.const J).obj (leftFunc.obj Cf.pt)).map α ≫ leftFunc.map (Cf.π.app j) =
          leftFunc.map (((Functor.const J).obj Cf.pt).map α ≫ Cf.π.app j) := by aesop_cat
          _ = leftFunc.map (Cf.π.app i ≫ f.map α) := by rw [naturality']
          _ = leftFunc.map (Cf.π.app i) ≫ leftFunc.map (f.map α) := by apply leftFunc.map_comp
          _ = leftFunc.map (Cf.π.app i) ≫ (f ⋙ leftFunc).map α := by aesop_cat
    }
  }

@[reducible]
def cone_source_triv_cone_arrow {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C)
  (s : Limits.Cone (f ⋙ leftFunc)) : Limits.Cone f := {
    pt := Arrow.mk (𝟙 s.pt)
    π := {
      app := fun i => by
        apply Arrow.homMk
        let l := s.π.app i
        let r := (s.π.app i) ≫ (f.obj i).hom
        have comm : l ≫ (f.obj i).hom =
          (((Functor.const J).obj (mk (𝟙 s.pt))).obj i).hom ≫ r := by aesop_cat
        exact comm
      naturality := fun i j α => by
        have naturality' := s.π.naturality α
        ext
        . aesop_cat
        . aesop_cat}
        }

@[reducible]
def map_triv_map_arrow_source (f : Arrow C) (X : C) (m : X ⟶ f.left) : Arrow.mk (𝟙 X) ⟶ f := by
  apply Arrow.homMk
  have l := m
  have r := m ≫ f.hom
  aesop_cat

/- The domain functor dom : [I,C] ⥤ C preserves limits -/
def source_limit_cone_arrow_limit_cone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C)
  (Cf : Limits.LimitCone f) : Limits.LimitCone (f ⋙ leftFunc) :=
  {
    cone := source_cone_arrow_cone f Cf.cone
    isLimit := {
      lift := fun s => leftFunc.map (Cf.isLimit.lift (cone_source_triv_cone_arrow f s))
      fac := fun s j => by
        have fac' := Cf.isLimit.fac (cone_source_triv_cone_arrow f s) j
        calc
          (Cf.isLimit.lift (cone_source_triv_cone_arrow f s)).left ≫
          (source_cone_arrow_cone f Cf.cone).π.app j =
          (Cf.isLimit.lift (cone_source_triv_cone_arrow f s)).left ≫ (Cf.cone.π.app j).left :=
            by aesop_cat
          _ = (Cf.isLimit.lift (cone_source_triv_cone_arrow f s) ≫ Cf.cone.π.app j).left :=
            by apply leftFunc.map_comp
          _ = ((cone_source_triv_cone_arrow f s).π.app j).left := by rw [fac']
          _ = s.π.app j := by aesop_cat
      uniq := fun s m p => by
        let m_triv := map_triv_map_arrow_source Cf.cone.pt s.pt m
        let p' : ∀ (j : J), m_triv ≫ Cf.cone.π.app j = (cone_source_triv_cone_arrow f s).π.app j :=
          fun j => by
          ext
          . aesop_cat
          . simp
            calc
              m_triv.right ≫ (Cf.cone.π.app j).right =
                m ≫ (Cf.cone.pt.hom ≫ (Cf.cone.π.app j).right) := by aesop_cat
              _ =  m ≫ ((Cf.cone.π.app j).left ≫ (f.obj j).hom) := by aesop_cat
              _ =  m ≫ ((source_cone_arrow_cone f Cf.cone).π.app j ≫ (f.obj j).hom) := by aesop_cat
              _ = (m ≫ (source_cone_arrow_cone f Cf.cone).π.app j) ≫ (f.obj j).hom := by simp
              _ = s.π.app j ≫ (f.obj j).hom := by rw [p j]
        have uniq' := Cf.isLimit.uniq (cone_source_triv_cone_arrow f s) m_triv p'
        calc
          m = m_triv.left := by rfl
          _ = (Cf.isLimit.lift (cone_source_triv_cone_arrow f s)).left := by rw [uniq']
          }
        }

/- If the category C has a terminal object, then the functor cod : [I,C] ⥤ C is continuous as well-/

/- A cone over f : J ⥤ Arrow C determines a cone over f ⋙ rightFunc -/
@[reducible]
def target_cone_arrow_cone {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (Cf : Limits.Cone f) :
  Limits.Cone (f ⋙ rightFunc) := {
    pt := rightFunc.obj Cf.pt
    π := {
      app := fun i => rightFunc.map (Cf.π.app i)
      naturality := by
        intro i j α
        have naturality' := Cf.π.naturality α
        calc
          ((Functor.const J).obj (rightFunc.obj Cf.pt)).map α ≫ rightFunc.map (Cf.π.app j) =
          rightFunc.map (((Functor.const J).obj Cf.pt).map α ≫ Cf.π.app j) := by aesop_cat
          _ = rightFunc.map (Cf.π.app i ≫ f.map α) := by rw [naturality']
          _ = rightFunc.map (Cf.π.app i) ≫ rightFunc.map (f.map α) := by apply rightFunc.map_comp
          _ = rightFunc.map (Cf.π.app i) ≫ (f ⋙ rightFunc).map α := by aesop_cat
    }
  }

@[reducible]
noncomputable
def cone_target_triv_cone_arrow {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C]
  (f : J ⥤ Arrow C) (s : Limits.Cone (f ⋙ rightFunc)) : Limits.Cone f := {
    pt := Arrow.mk (Limits.initial.to s.pt)
    π := {
      app := fun i => by
        apply Arrow.homMk
        let l := Limits.initial.to (leftFunc.obj (f.obj i))
        let r := s.π.app i
        have comm : l ≫ (f.obj i).hom =
          (((Functor.const J).obj (mk (Limits.initial.to s.pt))).obj i).hom ≫ r := by ext
        exact comm
      naturality := fun j i α => by
        ext
        . apply Limits.initial.hom_ext
        . have nat := s.π.naturality α
          aesop_cat}
  }

@[reducible]
noncomputable
def map_triv_map_arrow_target [CategoryTheory.Limits.HasInitial C]
  (f : Arrow C) (B : C) (m : B ⟶ f.right) : (Arrow.mk (Limits.initial.to B)) ⟶ f := by
  apply Arrow.homMk
  let l := Limits.initial.to f.left
  let r := m
  have comm : l ≫ f.hom = (mk (Limits.initial.to B)).hom ≫ r := by ext
  exact comm

/- If C has an initial object, then the codomain functor cod : [I,C] ⥤ C preserves limits -/
noncomputable
def target_limit_cone_arrow_limit_cone {J : Type u} [Category.{v} J]
  [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (Cf : Limits.LimitCone f) :
  Limits.LimitCone (f ⋙ rightFunc) := {
    cone := target_cone_arrow_cone f Cf.cone
    isLimit := {
      lift := fun s => rightFunc.map (Cf.isLimit.lift (cone_target_triv_cone_arrow f s))
      fac := fun s j => by
        have fac' := Cf.isLimit.fac (cone_target_triv_cone_arrow f s) j
        calc
          (Cf.isLimit.lift (cone_target_triv_cone_arrow f s)).right ≫
            (target_cone_arrow_cone f Cf.cone).π.app j =
            (Cf.isLimit.lift (cone_target_triv_cone_arrow f s)).right ≫ (Cf.cone.π.app j).right :=
              by aesop_cat
          _ = (Cf.isLimit.lift (cone_target_triv_cone_arrow f s) ≫ (Cf.cone.π.app j)).right :=
            by apply rightFunc.map_comp
          _ = ((cone_target_triv_cone_arrow f s).π.app j).right := by rw [fac']
          _ = s.π.app j := by aesop_cat
      uniq := fun s m p => by
        let p' : ∀ (j : J), Cf.cone.pt.map_triv_map_arrow_target s.pt m ≫ Cf.cone.π.app j =
          (cone_target_triv_cone_arrow f s).π.app j := fun j => by
          ext
          . aesop_cat
          . aesop_cat
        have uniq' := Cf.isLimit.uniq (cone_target_triv_cone_arrow f s)
            (map_triv_map_arrow_target Cf.cone.pt s.pt m) p'
        calc
          m = (map_triv_map_arrow_target Cf.cone.pt s.pt m).right := by rfl
          _ = (Cf.isLimit.lift (cone_target_triv_cone_arrow f s)).right := by rw [uniq']}
  }

/- We now proceed to prove that the right orthogonal complement of a class of morphisms is closed
  under limits. -/


/- Given a functor f : J ⥤ Arrow C together with a choice of a limit s : X ⟶ Y, a map m : A ⟶ B
and a commuting square

      A ---------> X
      |            |
    m |            |s       (*)
      |            |
      v            v
      B ---------> Y,

we obtain for every object i : J a commuting square

      A -------> dom(fi)
      |            |
    m |            |fi
      |            |
      v            v
      B -------> cod(fi).                          -/
@[reducible]
def square_completion_is_closed_under_limits_r_ort_complement
  {A B : C} {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f) (m : A ⟶ B)
  (sq_lim : square_completion m s.cone.pt.hom) :
  (i : J) → square_completion m (f.obj i).hom := fun i => {
    top := sq_lim.top ≫ (s.cone.π.app i).left
    bot := sq_lim.bot ≫ (s.cone.π.app i).right
    comm := by calc
      m ≫ sq_lim.bot ≫ (s.cone.π.app i).right = (m ≫ sq_lim.bot) ≫ (s.cone.π.app i).right
        := by simp
      _ =  (sq_lim.top ≫ s.cone.pt.hom) ≫ (s.cone.π.app i).right := by rw [sq_lim.comm]
      _ = (sq_lim.top ≫ (s.cone.π.app i).left) ≫ (f.obj i).hom := by aesop_cat
  }

/- Given a square (*) as above, we construct a cone over (U ∘ f) with apex B. -/
@[reducible]
noncomputable
def cone_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C) {A B : C}
  {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) : Limits.Cone (f ⋙ leftFunc) := {
    pt := B
    π := {
      app := fun i => by
        let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
        let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
        exact (m_ort_fi.diagonal sq_i).map
      naturality := fun i j α => by
        let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
        let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
        let m_ort_fj : orthogonal m (f.obj j).hom := hom_orthogonal_implies_orthogonal ((p j) m Wm)
        let sq_j := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim j
        simp
        let d : diagonal_filler sq_j := {
          map := (m_ort_fj.diagonal sq_j).map
          comm_top := (m_ort_fj.diagonal sq_j).comm_top
          comm_bot := (m_ort_fj.diagonal sq_j).comm_bot}
        let d' : diagonal_filler sq_j := {
          map := (m_ort_fi.diagonal sq_i).map ≫ (f.map α).left
          comm_top := by calc
            m ≫ (m_ort_fi.diagonal sq_i).map ≫ (f.map α).left =
              (m ≫ (m_ort_fi.diagonal sq_i).map) ≫ (f.map α).left := by simp
            _ = (sq_lim.top ≫ (s.cone.π.app i).left) ≫ (f.map α).left :=
              by rw [(m_ort_fi.diagonal sq_i).comm_top]
            _ = sq_lim.top ≫ ((s.cone.π.app i).left ≫ (f.map α).left) := by simp
            _ = sq_lim.top ≫ (s.cone.π.app j).left := by
              have naturality := s.cone.π.naturality α
              have naturality' : s.cone.π.app i ≫ f.map α = s.cone.π.app j := by aesop_cat
              calc
                sq_lim.top ≫ (leftFunc.map (s.cone.π.app i) ≫ leftFunc.map (f.map α)) =
                  sq_lim.top ≫ leftFunc.map (s.cone.π.app i ≫ f.map α) := by rw [leftFunc.map_comp]
                _ = sq_lim.top ≫ leftFunc.map (s.cone.π.app j) := by rw [naturality']
            _ = sq_j.top := by rfl
          comm_bot := by calc
            ((m_ort_fi.diagonal sq_i).map ≫ (f.map α).left) ≫ (f.obj j).hom =
              ((m_ort_fi.diagonal sq_i).map ≫ (f.obj i).hom) ≫ (f.map α).right := by simp
            _ = (sq_lim.bot ≫ (s.cone.π.app i).right) ≫ (f.map α).right :=
              by rw [(m_ort_fi.diagonal sq_i).comm_bot]
            _ = sq_lim.bot ≫ ((s.cone.π.app i).right ≫ (f.map α).right) := by simp
            _ = sq_lim.bot ≫ (s.cone.π.app j).right := by
              have naturality := s.cone.π.naturality α
              have naturality' : s.cone.π.app i ≫ f.map α = s.cone.π.app j := by aesop_cat
              calc
                sq_lim.bot ≫ (rightFunc.map (s.cone.π.app i) ≫ rightFunc.map (f.map α)) =
                  sq_lim.bot ≫ rightFunc.map (s.cone.π.app i ≫ f.map α) :=
                    by rw [rightFunc.map_comp]
                _ = sq_lim.bot ≫ rightFunc.map (s.cone.π.app j) := by rw [naturality']
            _ = sq_j.bot := by rfl}
        apply (m_ort_fj.diagonal_unique sq_j) d d'}
  }

/- By the universal property of the limit cone, the cone from the previous construction gives rise
  to a morphism B → X. -/
@[reducible]
noncomputable
def diagonal_map_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C) {A B : C}
  {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) : B ⟶ s.cone.pt.left := by
  let this_is_what_we_want :=
    ( source_limit_cone_arrow_limit_cone f s).isLimit.lift
      ( cone_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p)
  let do_the_magic : B ⟶ s.cone.pt.left := by aesop_cat
  exact do_the_magic

/- The diagonal constructed in the previous lemma makes the upper triangle commute -/
noncomputable
def diagonal_comm_top_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) :
  m ≫ (diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p) = sq_lim.top
  := by
  apply Limits.IsLimit.hom_ext (source_limit_cone_arrow_limit_cone f s).isLimit
  intro i
  let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
  let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
  let d := diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
  let di := (m_ort_fi.diagonal sq_i).map
  calc
    (m ≫ d) ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i =
      m ≫ (d ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i) := by simp
    _ = m ≫ di := by aesop_cat
    _ = sq_lim.top ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i :=
      (m_ort_fi.diagonal sq_i).comm_top

/- The bottom triangle commutes as well -/
noncomputable
def diagonal_comm_bot_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) :
  (diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p) ≫ s.cone.pt.hom
    = sq_lim.bot := by
  apply Limits.IsLimit.hom_ext (target_limit_cone_arrow_limit_cone f s).isLimit
  intro i
  let m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
  let sq_i := square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i
  let d := diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
  let di := (m_ort_fi.diagonal sq_i).map
  calc
    (d ≫ s.cone.pt.hom) ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i =
      d ≫ s.cone.pt.hom ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i := by simp
    _ = d ≫ (s.cone.π.app i).left ≫ (f.obj i).hom := by aesop_cat
    _ = (d ≫ (s.cone.π.app i).left) ≫ (f.obj i).hom := by simp
    _ = (d ≫ (source_limit_cone_arrow_limit_cone f s).cone.π.app i) ≫ (f.obj i).hom := by rfl
    _ = di ≫ (f.obj i).hom := by aesop_cat
    _ = sq_i.bot := (m_ort_fi.diagonal sq_i).comm_bot
    _ = sq_lim.bot ≫ (target_limit_cone_arrow_limit_cone f s).cone.π.app i := by rfl

noncomputable
def diagonal_filler_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m) (sq_lim : square_completion m s.cone.pt.hom)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) : diagonal_filler sq_lim := {
    map := diagonal_map_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
    comm_top := diagonal_comm_top_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
    comm_bot := diagonal_comm_bot_limit_is_closed_under_limits_r_ort_complement W f s m Wm sq_lim p
  }

/- Uniqueness of lifts -/

/- If f: J ⥤ Arrow C is a functor with limit cone λᵢ : lim f ⇒ fᵢ, and d is a diagonal filler
of the square
        a
  A ----------> dom(lim f)
  |               |
 m|               |lim f
  |               |
  V               V
  B ----------> cod(lim f),
        b
then for every object i of J, dom(λᵢ) ∘ d is a diagonal filler of the square
      dom(λᵢ)∘a
  A ----------> dom(fᵢ)
  |               |
 m|               |fᵢ
  |               |
  V               V
  B ----------> cod(fᵢ).
      cod(λᵢ)∘b                         -/
@[reducible]
def diagonal_postcomp_is_diagonal {J : Type u}
  [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  {A B : C} (m : A ⟶ B) (S : square_completion m s.cone.pt.hom) (d : diagonal_filler S) (i : J) :
  diagonal_filler (square_completion_is_closed_under_limits_r_ort_complement f s m S i) := {
    map := d.map ≫ (s.cone.π.app i).left
    comm_top := by calc
      m ≫ d.map ≫ (s.cone.π.app i).left = (m ≫ d.map) ≫ (s.cone.π.app i).left := by simp
      _ =  S.top ≫ (s.cone.π.app i).left := by rw [d.comm_top]
      _ = (square_completion_is_closed_under_limits_r_ort_complement f s m S i).top := by aesop_cat
    comm_bot := by calc
      (d.map ≫ (s.cone.π.app i).left) ≫ (f.obj i).hom =
        d.map ≫ ((s.cone.π.app i).left ≫ (f.obj i).hom) := by simp
      _ = d.map ≫ (s.cone.pt.hom ≫ (s.cone.π.app i).right) := by aesop_cat
      _ = (d.map ≫ s.cone.pt.hom) ≫ (s.cone.π.app i).right := by simp
      _ = (square_completion_is_closed_under_limits_r_ort_complement f s m S i).bot :=
        by rw [d.comm_bot]
  }

def diagonal_unique_limit_is_closed_under_limits_r_ort_complement (W : MorphismProperty C)
  {A B : C} {J : Type u} [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C)
  (s : Limits.LimitCone f) (m : A ⟶ B) (Wm : W m)
  (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom)
  (sq_lim : square_completion m s.cone.pt.hom) (d d' : diagonal_filler sq_lim) :
  d.map = d'.map := by
  apply Limits.IsLimit.hom_ext (source_limit_cone_arrow_limit_cone f s).isLimit
  intro i
  let D := diagonal_postcomp_is_diagonal f s m sq_lim d i
  let D' := diagonal_postcomp_is_diagonal f s m sq_lim d' i
  have m_ort_fi : orthogonal m (f.obj i).hom := hom_orthogonal_implies_orthogonal ((p i) m Wm)
  exact m_ort_fi.diagonal_unique
    (square_completion_is_closed_under_limits_r_ort_complement f s m sq_lim i) D D'

/- Putting everything together -/
noncomputable
def is_closed_under_limits_r_ort_complement (W : MorphismProperty C) {A B : C} {J : Type u}
  [Category.{v} J] [CategoryTheory.Limits.HasInitial C] (f : J ⥤ Arrow C) (s : Limits.LimitCone f)
  (m : A ⟶ B) (Wm : W m) (p : ∀ i : J , (right_orthogonal_complement W) (f.obj i).hom) :
  orthogonal m s.cone.pt.hom := {
    diagonal := fun S =>
      diagonal_filler_limit_is_closed_under_limits_r_ort_complement W f s m Wm S p
    diagonal_unique := fun S d d' =>
      diagonal_unique_limit_is_closed_under_limits_r_ort_complement W f s m Wm p S d d'
  }

/- We now proceed to show that the right orthogonal complement is closed under composition -/

lemma is_closed_under_comp_r_ort_complement (W : MorphismProperty C) {X Y Z : C} (r : X ⟶ Y)
  (hr : (right_orthogonal_complement W) r) (r' : Y ⟶ Z) (hr' : (right_orthogonal_complement W) r') :
  (right_orthogonal_complement W) (r ≫ r') := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ r
        bot := b
        comm := by have comm' := S.comm ; aesop_cat}
      let d := (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal S'
      let S'' : l □ r := {
        top := a
        bot := d.map
        comm := d.comm_top}
      let d' := (hom_orthogonal_implies_orthogonal (hr l hl)).diagonal S''
      exact {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by
          let comm_bot' := d'.comm_bot
          let comm_bot'' := d.comm_bot
          calc
            d'.map ≫ r ≫ r' = (d'.map ≫ r) ≫ r' := by simp
            _ = d.map ≫ r' := by rw [comm_bot']
            _ = b := comm_bot''}
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ r
        bot := b
        comm := by have comm' := S.comm ; aesop_cat}
      let D : diagonal_filler S' := {
        map := d.map ≫ r
        comm_top := by calc
          l ≫ d.map ≫ r = S.top ≫ r := by rw [←d.comm_top] ; simp
          _ = a ≫ r := by rfl
        comm_bot := by have comm_bot' := d.comm_bot ; aesop_cat}
      let D' : diagonal_filler S' := {
        map := d'.map ≫ r
        comm_top := by calc
          l ≫ d'.map ≫ r = S.top ≫ r := by rw [←d'.comm_top] ; simp
          _ = a ≫ r := by rfl
        comm_bot := by have comm_bot' := d'.comm_bot ; aesop_cat}
      let eq : d.map ≫ r = d'.map ≫ r :=
        (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal_unique S' D D'
      let S'' : l □ r := {
        top := a
        bot := d.map ≫ r
        comm := by calc
          l ≫ d.map ≫ r = (l ≫ d.map) ≫ r := by simp
          _ = S'.top := by rw [d.comm_top]
          _ = a ≫ r := by rfl}
      let Δ : diagonal_filler S'' := {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by aesop_cat}
      let Δ' : diagonal_filler S'' := {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by aesop_cat}
      exact (hom_orthogonal_implies_orthogonal (hr l hl)).diagonal_unique S'' Δ Δ'}

/- We now prove that the right orthogonal complement of any class of morphism has the left
  cancellation property. -/

lemma left_cancellation_r_ort_complement (W : MorphismProperty C) {X Y Z : C} (r : X ⟶ Y)
  (r' : Y ⟶ Z) (hr' : (right_orthogonal_complement W) r')
  (hr'r : (right_orthogonal_complement W) (r ≫ r')): (right_orthogonal_complement W) r := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r ≫ r' := {
        top := a
        bot := b ≫ r'
        comm := by calc
          l ≫ b ≫ r' = (l ≫ b) ≫ r' := by simp
          _ = (a ≫ r) ≫ r' := by rw [S.comm]
          _ = a ≫ r ≫ r' := by simp}
      let d := (hom_orthogonal_implies_orthogonal (hr'r l hl)).diagonal S'
      exact {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by
          let S'' : l □ r' := {
            top := a ≫ r
            bot := b ≫ r'
            comm := by have comm' := S'.comm ; aesop_cat}
          let D : diagonal_filler S'' := {
            map := d.map ≫ r
            comm_top := by calc
              l ≫ d.map ≫ r = (l ≫ d.map) ≫ r := by simp
              _ = S'.top ≫ r := by rw [d.comm_top]
              _ = S''.top := by rfl
            comm_bot := by have comm_bot' := d.comm_bot ; aesop_cat}
          let D' : diagonal_filler S'' := {
            map := S.bot
            comm_top := S.comm
            comm_bot := by simp}
          exact (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal_unique S'' D D'}
    diagonal_unique := fun S d d' => by
      let a := S.top
      let b := S.bot
      let S' : l □ r ≫ r' := {
        top := a
        bot := b ≫ r'
        comm := by calc
          l ≫ b ≫ r' = (l ≫ b) ≫ r' := by simp
          _ = (a ≫ r) ≫ r' := by rw [S.comm]
          _ = a ≫ r ≫ r' := by simp}
      let Δ : diagonal_filler S' := {
        map := d.map
        comm_top := d.comm_top
        comm_bot := by calc
          d.map ≫ r ≫ r' = (d.map ≫ r) ≫ r' := by simp
          _ = b ≫ r' := by rw [d.comm_bot]}
      let Δ' : diagonal_filler S' := {
        map := d'.map
        comm_top := d'.comm_top
        comm_bot := by calc
          d'.map ≫ r ≫ r' = (d'.map ≫ r) ≫ r' := by simp
          _ = b ≫ r' := by rw [d'.comm_bot]}
      exact (hom_orthogonal_implies_orthogonal (hr'r l hl)).diagonal_unique S' Δ Δ'
  }

/- Moreover, the right orthogonal complement of any class of morphisms is closed under base change-/

lemma base_change_r_ort_complement [Limits.HasPullbacks C] (W : MorphismProperty C) {Y X' Y' : C}
  (r' : X' ⟶ Y') (hr' : (right_orthogonal_complement W) r') (f : Y ⟶ Y') :
  (right_orthogonal_complement W) (Limits.pullback.snd r' f) := by
  intro A B l hl
  apply orthogonal_implies_hom_orthogonal
  let r := Limits.pullback.snd r' f
  exact {
    diagonal := fun S => by
      let a := S.top
      let b := S.bot
      let S' : l □ r' := {
        top := a ≫ Limits.pullback.fst r' f
        bot := b ≫ f
        comm := by calc
          l ≫ b ≫ f = (l ≫ b) ≫ f := by simp
          _ = a ≫ r ≫ f := by rw [S.comm] ; aesop_cat
          _ = a ≫ Limits.pullback.fst r' f ≫ r' := by rw [Limits.pullback.condition]
          _ = (a ≫ Limits.pullback.fst r' f) ≫ r' := by simp}
      let d := (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal S'
      let comm' : d.map ≫ r' =  b ≫ f := by have comm_bot' := d.comm_bot ; aesop_cat
      exact {
        map := Limits.pullback.lift d.map b comm'
        comm_top := by
          apply Limits.pullback.hom_ext
          . calc
            (l ≫ Limits.pullback.lift d.map b comm') ≫ Limits.pullback.fst r' f =
              l ≫ (Limits.pullback.lift d.map b comm' ≫ Limits.pullback.fst r' f) := by simp
            _ = l ≫ d.map := by rw [Limits.pullback.lift_fst]
            _ = a ≫ Limits.pullback.fst r' f := d.comm_top
          . calc
            (l ≫ Limits.pullback.lift d.map b comm') ≫ Limits.pullback.snd r' f =
              l ≫ (Limits.pullback.lift d.map b comm' ≫ Limits.pullback.snd r' f) := by simp
            _ = l ≫ b := by rw [Limits.pullback.lift_snd]
            _ = a ≫ r := S.comm
        comm_bot := by apply Limits.pullback.lift_snd}
    diagonal_unique := fun S d d' => by
      apply Limits.pullback.hom_ext
      . let a := S.top
        let b := S.bot
        let S' : l □ r' := {
          top := a ≫ Limits.pullback.fst r' f
          bot := b ≫ f
          comm := by calc
            l ≫ b ≫ f = (l ≫ b) ≫ f := by simp
            _ = a ≫ r ≫ f := by rw [S.comm] ; aesop_cat
            _ = a ≫ Limits.pullback.fst r' f ≫ r' := by rw [Limits.pullback.condition]
            _ = (a ≫ Limits.pullback.fst r' f) ≫ r' := by simp}
        let D : diagonal_filler S' := {
          map := d.map ≫ Limits.pullback.fst r' f
          comm_top := by calc
            l ≫ d.map ≫ Limits.pullback.fst r' f = (l ≫ d.map) ≫ Limits.pullback.fst r' f :=
              by simp
            _ = a ≫ Limits.pullback.fst r' f := by rw [d.comm_top]
          comm_bot := by calc
            (d.map ≫ Limits.pullback.fst r' f) ≫ r' = d.map ≫ (Limits.pullback.fst r' f ≫ r') :=
              by simp
            _ = d.map ≫ (r ≫ f) := by rw [Limits.pullback.condition]
            _ = (d.map ≫ r) ≫ f := by simp
            _ = b ≫ f := by rw [d.comm_bot]}
        let D' : diagonal_filler S' := {
          map := d'.map ≫ Limits.pullback.fst r' f
          comm_top := by calc
            l ≫ d'.map ≫ Limits.pullback.fst r' f = (l ≫ d'.map) ≫ Limits.pullback.fst r' f :=
              by simp
            _ = a ≫ Limits.pullback.fst r' f := by rw [d'.comm_top]
          comm_bot := by calc
            (d'.map ≫ Limits.pullback.fst r' f) ≫ r' = d'.map ≫ (Limits.pullback.fst r' f ≫ r')
              := by simp
            _ = d'.map ≫ (r ≫ f) := by rw [Limits.pullback.condition]
            _ = (d'.map ≫ r) ≫ f := by simp
            _ = b ≫ f := by rw [d'.comm_bot]}
        exact (hom_orthogonal_implies_orthogonal (hr' l hl)).diagonal_unique S' D D'
      . calc
        d.map ≫ Limits.pullback.snd r' f = S.bot := d.comm_bot
        _ = d'.map ≫ Limits.pullback.snd r' f := by rw [←d'.comm_bot]}
