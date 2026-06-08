import HoTTLean.ForMathlib
import Mathlib.CategoryTheory.Widesubcategory
import HoTTLean.ForMathlib.CategoryTheory.Functor.Iso
import HoTTLean.ForMathlib.CategoryTheory.FreeGroupoid
import HoTTLean.ForMathlib.CategoryTheory.Grpd
import Mathlib.Tactic.DepRewrite

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

@[simp]
lemma WideSubcategory.coe_eqToHom {C : Type u} [Category.{v} C]
    {P : MorphismProperty C} [P.IsMultiplicative] {X Y : WideSubcategory P} (h : X = Y) :
    (eqToHom h).1 = eqToHom (by subst h; rfl) := by
  subst h
  rfl

@[simp]
lemma WideSubcategory.hom_eqToHom {C : Type u} [Category.{v} C]
    {P : MorphismProperty C} [P.IsMultiplicative] {X Y : WideSubcategory P} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

@[simp]
lemma WideSubcategory.comp_hom {C : Type u} [Category.{v} C]
    {P : MorphismProperty C} [P.IsMultiplicative] {X Y Z : WideSubcategory P}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
lemma ObjectProperty.FullSubcategory.hom_eqToHom {C : Type u} [Category.{v} C]
    {P : ObjectProperty C} {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

end CategoryTheory


/-!
## Strict (meta-theoretic) 1-pullbacks of categories
* Due to universe level complications, it is convenient to have
  a version of pullbacks of categories that is agnostic to universe levels,
  providing a universal property for cones with apex of any universe size.
  This is essentially the same as asking for a pullback in `Cat.{max ⋯, max ⋯}`,
  (where all the categories are adjusted by `ULift`).
* However, since Lean cannot express quantification of universe variables,
  we state `CategoryTheory.Functor.IsPullback` via being isomorphic
  to a chosen pullback
  `CategoryTheory.Functor.IsPullback.Chosen`.

## Main definitions
* `CategoryTheory.Functor.IsPullback.Chosen` a construction of the
  strict 1-pullback of categories as a (non-full)
  subcategory of the product.
* `CategoryTheory.Functor.IsPullback` being a pullback of a functor
  is to be isomorphic (functors to and from that compose to identity)
  to the chosen pullback `CategoryTheory.Functor.IsPullback.Chosen`.
* Pullback pasting, in `pasteHoriz` and `ofRight` and `ofRight'`.
-/

namespace CategoryTheory.Functor

namespace IsPullback

section east_south

variable {Egypt : Type*} [Category Egypt]
  {Chad : Type*} [Category Chad]
  {Sudan : Type*} [Category Sudan]
  (east : Egypt ⥤ Sudan) (south : Chad ⥤ Sudan)

/--
  The chosen pullback category `Chosen` is a wide subcategory
  of this intermediate category `ChosenObjects`,
  which itself is a full subcategory of the product `Egypt × Chad`.
  Objects in this full subcategory are those whose two components are
  sent to equal objects in the base category `Sudan`.
-/
def ChosenObjects := ObjectProperty.FullSubcategory (
  fun p : Egypt × Chad => east.obj p.1 = south.obj p.2 )

namespace ChosenObjects

instance : Category (ChosenObjects east south) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

end ChosenObjects

/--
  Morphisms in `Chosen` are morphisms from `ChosenObjects`
  whose two components are sent to equal maps in the base category `Sudan`.
-/
def morphismProperty : MorphismProperty (ChosenObjects east south) :=
  fun {x y} f => east.map f.hom.1
    = eqToHom x.property ≫ south.map f.hom.2 ≫ eqToHom y.property.symm

instance : MorphismProperty.IsMultiplicative (morphismProperty east south) where
  id_mem x := by
    change east.map (𝟙 x.obj.1) =
      eqToHom x.property ≫ south.map (𝟙 x.obj.2) ≫ eqToHom x.property.symm
    simp
  comp_mem {X Y Z} f g hf hg := by
    change east.map (f.hom.1 ≫ g.hom.1) =
      eqToHom X.property ≫ south.map (f.hom.2 ≫ g.hom.2) ≫ eqToHom Z.property.symm
    rw [east.map_comp, south.map_comp, hf, hg]
    simp [Category.assoc]

/--
  The chosen pullback category `Chosen` is a wide subcategory
  of `ChosenObjects`,
  consisting of pairs of maps from `Egypt` and `Chad`
  that are equal in the base category `Sudan`.
-/
def Chosen := WideSubcategory (morphismProperty east south)

instance : Category (Chosen east south) :=
  inferInstanceAs (Category (WideSubcategory _))

end east_south

namespace Chosen

section
/-
       north
  Chosen ----> Egypt
    |          |
  west         |east
    |          |
    V          V
  Chad ----> Sudan
       south
-/
variable {Egypt : Type*} [Category Egypt]
  {Chad : Type*} [Category Chad]
  {Sudan : Type*} [Category Sudan]
  {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}

def north : Chosen east south ⥤ Egypt :=
  wideSubcategoryInclusion _ ⋙ ObjectProperty.ι _ ⋙ Prod.fst _ _

def west : Chosen east south ⥤ Chad :=
  wideSubcategoryInclusion _ ⋙ ObjectProperty.ι _ ⋙ Prod.snd _ _

theorem comm_sq : @north _ _ _ _ _ _ east south ⋙ east = west ⋙ south := by
  fapply Functor.ext
  · intro x
    exact x.obj.property
  · intro x y f
    exact f.property

end

variable {Egypt Chad Sudan : Type*}
  [Category Egypt] [Category Chad] [Category Sudan]
  {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}

variable {C : Type u} [Category.{v} C] (Cn : C ⥤ Egypt) (Cw : C ⥤ Chad)
    (hC : Cn ⋙ east = Cw ⋙ south)

/--
The universal lift of the chosen pullback `Chosen`.
-/
def lift : C ⥤ Chosen east south where
  obj x := ⟨ ⟨ Cn.obj x , Cw.obj x ⟩ , congr_obj hC x ⟩
  map {X Y} f := ⟨ ⟨ ⟨ Cn.map f , Cw.map f ⟩ ⟩ , by
    change (Cn ⋙ east).map f =
      eqToHom (congr_obj hC X) ≫ (Cw ⋙ south).map f ≫ eqToHom (congr_obj hC Y).symm
    exact congr_hom hC f ⟩

/--
The universal lift of the chosen pullback `Chosen` commutes with projections.
-/
theorem fac_left : lift Cn Cw hC ⋙ north = Cn :=
  rfl

/--
The universal lift of the chosen pullback `Chosen` commutes with projections.
-/
theorem fac_right : lift Cn Cw hC ⋙ west = Cw :=
  rfl

/--
Lifts of the chosen pullback `Chosen` are unique.
-/
theorem hom_ext {l0 l1 : C ⥤ Chosen east south} (hnorth : l0 ⋙ north = l1 ⋙ north)
   (hwest : l0 ⋙ west = l1 ⋙ west) : l0 = l1 := by
  let objEq : ∀ x, l0.obj x = l1.obj x := fun x => by
    apply WideSubcategory.ext
    apply ObjectProperty.FullSubcategory.ext
    apply Prod.ext
    · exact congr_obj hnorth x
    · exact congr_obj hwest x
  fapply Functor.ext
  · intro x
    exact objEq x
  · intro x y f
    apply (wideSubcategory.faithful _).map_injective
    apply (ObjectProperty.faithful_ι _).map_injective
    apply Prod.ext
    · change north.map (l0.map f) = north.map (eqToHom (objEq x) ≫ l1.map f ≫ eqToHom (objEq y).symm)
      rw [Functor.map_comp, Functor.map_comp]
      convert congr_hom hnorth f using 1
      all_goals simp [eqToHom_map]
    · change west.map (l0.map f) = west.map (eqToHom (objEq x) ≫ l1.map f ≫ eqToHom (objEq y).symm)
      rw [Functor.map_comp, Functor.map_comp]
      convert congr_hom hwest f using 1
      all_goals simp [eqToHom_map]

end Chosen

end IsPullback


open IsPullback

/--
A pullback structure on a type `Libya` over a pair of functors
`east` and `south` with the same codomain consists of an isomorphism
with the chosen pullback `CategoryTheory.Functor.IsPullback.Chosen east south`.
This is a strict isomorphism in the sense of having functors back and forth
that compose to *equal* the identity,
but since the universe levels are variable these are not the same it does not fit
into mathlib's definition of an isomorphism.
-/
structure IsPullback {Libya Egypt Chad Sudan : Type*}
    [Category Libya] [Category Egypt] [Category Chad] [Category Sudan]
    (north : Libya ⥤ Egypt) (west : Libya ⥤ Chad)
    (east : Egypt ⥤ Sudan) (south : Chad ⥤ Sudan) where
  (comm_sq : north ⋙ east = west ⋙ south)
  (toChosen : Libya ⥤ Chosen east south)
  (fromChosen : Chosen east south ⥤ Libya)
  (to_from_id : toChosen ⋙ fromChosen = 𝟭 _)
  (from_to_id : fromChosen ⋙ toChosen = 𝟭 _)
  (from_north : fromChosen ⋙ north = Chosen.north)
  (from_west : fromChosen ⋙ west = Chosen.west)

namespace IsPullback

section
variable {Libya Egypt Chad Sudan : Type*} [Category Libya]
  [Category Egypt] [Category Chad] [Category Sudan]
  (north : Libya ⥤ Egypt) (west : Libya ⥤ Chad)
  (east : Egypt ⥤ Sudan) (south : Chad ⥤ Sudan)

section
variable {Libya'} [Category Libya']
  (h : IsPullback north west east south)

/--
We can construct a pullback by only providing an isomorphism to the chosen pullback.
-/
def ofIso (to' : Libya' ⥤ Libya)
    (from' : Libya ⥤ Libya')
    (htf : to' ⋙ from' = 𝟭 _) (hft: from' ⋙ to' = 𝟭 _) :
    IsPullback (to' ⋙ north) (to' ⋙ west) east south where
  comm_sq := by rw [Functor.assoc, h.comm_sq, Functor.assoc]
  toChosen := to' ⋙ h.toChosen
  fromChosen := h.fromChosen ⋙ from'
  to_from_id := calc to' ⋙ (h.toChosen ⋙ h.fromChosen) ⋙ from'
    _ = to' ⋙ from' := by rw [h.to_from_id, Functor.id_comp]
    _ = 𝟭 _ := htf
  from_to_id := calc h.fromChosen ⋙ (from' ⋙ to') ⋙ h.toChosen
    _ = h.fromChosen ⋙ h.toChosen := by rw [hft, Functor.id_comp]
    _ = 𝟭 _ := h.from_to_id
  from_north := calc h.fromChosen ⋙ (from' ⋙ to') ⋙ north
    _ = h.fromChosen ⋙ north := by rw [hft, Functor.id_comp]
    _ = Chosen.north := h.from_north
  from_west := calc h.fromChosen ⋙ (from' ⋙ to') ⋙ west
    _ = h.fromChosen ⋙ west := by rw [hft, Functor.id_comp]
    _ = Chosen.west := h.from_west

end

def Chosen.isPullback : IsPullback (@Chosen.north _ _ _ _ _ _ east south)
    Chosen.west east south where
  comm_sq := Chosen.comm_sq
  toChosen := 𝟭 _
  fromChosen := 𝟭 _
  to_from_id := rfl
  from_to_id := rfl
  from_north := rfl
  from_west := rfl

/--
We can construct a pullback by only providing an isomorphism to the chosen pullback.
-/
def ofIsoChosen (toChosen : Libya ⥤ Chosen east south)
    (fromChosen : Chosen east south ⥤ Libya)
    (htf : toChosen ⋙ fromChosen = 𝟭 _) (hft: fromChosen ⋙ toChosen = 𝟭 _) :
    IsPullback (toChosen ⋙ Chosen.north) (toChosen ⋙ Chosen.west) east south :=
  ofIso _ _ _ _ (Chosen.isPullback east south) toChosen fromChosen htf hft

variable {north} {east} {south} {west} (P : IsPullback north west east south)
/--
Commuting conditions between a general pullback `P` and the chosen pullback.
-/
theorem toChosen_north : P.toChosen ⋙ Chosen.north = north := by
  simp [← P.from_north, ← Functor.assoc, P.to_from_id, Functor.id_comp]

/--
Commuting conditions between a general pullback `P` and the chosen pullback.
-/
theorem toChosen_west : P.toChosen ⋙ Chosen.west = west := by
  simp [← P.from_west, ← Functor.assoc, P.to_from_id, Functor.id_comp]

variable {C : Type u} [Category.{v} C] (Cn : C ⥤ Egypt) (Cw : C ⥤ Chad)
    (hC : Cn ⋙ east = Cw ⋙ south)

/--
The universal lift of the pullback `P`.
-/
def lift : C ⥤ Libya := Chosen.lift Cn Cw hC ⋙ P.fromChosen

/--
Commuting conditions for the universal lift of the pullback `P`.
-/
theorem fac_left : lift P Cn Cw hC ⋙ north = Cn := by
  simp [lift, Functor.assoc, P.from_north, Chosen.fac_left]


/--
Commuting conditions for the universal lift of the pullback `P`.
-/
theorem fac_right : lift P Cn Cw hC ⋙ west = Cw := by
  simp [lift, Functor.assoc, P.from_west, Chosen.fac_right]

include P in
/--
Uniqueness of universal lifts for the pullback `P`.
-/
theorem hom_ext {l0 l1 : C ⥤ Libya} (hnorth : l0 ⋙ north = l1 ⋙ north)
    (hwest : l0 ⋙ west = l1 ⋙ west) : l0 = l1 :=
  calc l0
    _ = l0 ⋙ P.toChosen ⋙ P.fromChosen := by
      rw [P.to_from_id, Functor.comp_id]
    _ = l1 ⋙ P.toChosen ⋙ P.fromChosen := by
      dsimp only [← Functor.assoc]
      congr 1
      apply Chosen.hom_ext
      · simp [Functor.assoc, toChosen_north, hnorth]
      · simp [Functor.assoc, toChosen_west, hwest]
    _ = l1 := by rw [P.to_from_id, Functor.comp_id]

/--
Uniqueness of universal lifts for the pullback `P`.
-/
theorem lift_uniq {l : C ⥤ Libya} (hnorth : l ⋙ north = Cn)
    (hwest : l ⋙ west = Cw) : l = lift P Cn Cw hC := by
  apply hom_ext P
  · simp [hnorth, fac_left]
  · simp [hwest, fac_right]
end

section
variable {Libya : Type u} {Egypt : Type u₁} {Chad : Type u₂} {Sudan : Type u₃}
  [Category.{v} Libya] [Category.{v₁} Egypt]
  [Category.{v₂} Chad] [Category.{v₃} Sudan]
  (north : Libya ⥤ Egypt) (west : Libya ⥤ Chad)
  (east : Egypt ⥤ Sudan) (south : Chad ⥤ Sudan)
  (comm_sq : north ⋙ east = west ⋙ south)

variable (lChosen :
  ∀ {C : Type (max u₁ u₂)} [Category.{max v₁ v₂} C]
    (Cn : C ⥤ Egypt) (Cw : C ⥤ Chad),
    Cn ⋙ east = Cw ⋙ south →
    (lift : C ⥤ Libya) ×'
    (lift ⋙ north = Cn) ∧
    (lift ⋙ west = Cw) ∧
    (∀ {l0 l1 : C ⥤ Libya}, l0 ⋙ north = l1 ⋙ north → l0 ⋙ west = l1 ⋙ west → l0 = l1))

variable (lLibya :
  ∀ {C : Type u} [Category.{v} C]
    (Cn : C ⥤ Egypt) (Cw : C ⥤ Chad),
    Cn ⋙ east = Cw ⋙ south →
    (lift : C ⥤ Libya) ×'
    (lift ⋙ north = Cn) ∧
    (lift ⋙ west = Cw) ∧
    (∀ {l0 l1 : C ⥤ Libya}, l0 ⋙ north = l1 ⋙ north →
      l0 ⋙ west = l1 ⋙ west → l0 = l1))
/--
  To define a pullback structure on a category,
  rather than showing a category is isomorphic to the chosen pullback,
  we can instead show its universal property.

  Unfortunately, because we cannot quantify over universe level `u`
  we cannot state the general universal property as a hypothesis.
  Instead, one should on an ad-hoc basis state and prove a more general universal property
  (i.e. using a fresh universe variable)
  and then specialize it to these two choices of universe levels.
  For an example of this see `Category.Functor.IsPullback.pasteHoriz`.

  Note that when we *use* the universal property of a pullback
  this problem does not arise.
  See `CategoryTheory.Functor.IsPullback.lift` etc.
-/
def ofUniversal : IsPullback north west east south := {
  comm_sq := comm_sq
  toChosen := Chosen.lift north west comm_sq
  fromChosen := (lChosen Chosen.north Chosen.west Chosen.comm_sq).1
  to_from_id := by
    apply (lLibya north west comm_sq).2.2.2
    · rw [Functor.assoc, (lChosen _ _ Chosen.comm_sq).2.1,
        Chosen.fac_left, Functor.id_comp]
    · rw [Functor.assoc, (lChosen _ _ Chosen.comm_sq).2.2.1,
        Chosen.fac_right, Functor.id_comp]
  from_to_id := by
    apply Chosen.hom_ext
    · rw [Functor.assoc, Chosen.fac_left, Functor.id_comp,
        (lChosen _ _ Chosen.comm_sq).2.1]
    · rw [Functor.assoc, Chosen.fac_right, Functor.id_comp,
        (lChosen _ _ Chosen.comm_sq).2.2.1]
  from_north := (lChosen _ _ Chosen.comm_sq).2.1
  from_west := (lChosen _ _ Chosen.comm_sq).2.2.1
}


end

section

variable {Libya Egypt Chad Sudan : Type*} [Category Libya]
  [Category Egypt] [Category Chad] [Category Sudan]
  (north : Libya ⥤ Egypt) (west : Libya ⥤ Chad)
  (east : Egypt ⥤ Sudan) (south : Chad ⥤ Sudan)
  (pb : IsPullback north west east south)

variable {north} in
lemma Iso.inv_comp_eq_comp_inv {north'} (lib : Iso Chad Libya) (egy : Iso Sudan Egypt)
(hnorth : north' ⋙ egy.hom = lib.hom ⋙ north): lib.inv ⋙ north' = north ⋙ egy.inv
    ↔ north' ⋙ egy.hom = lib.hom ⋙ north := by
    rw [lib.inv_comp_eq, ← Functor.assoc, egy.eq_comp_inv, hnorth]

variable {Libya' Egypt' Chad' Sudan' : Type*} [Category Libya']
  [Category Egypt'] [Category Chad'] [Category Sudan']
  (north' : Libya' ⥤ Egypt') (west' : Libya' ⥤ Chad')
  (east' : Egypt' ⥤ Sudan') (south' : Chad' ⥤ Sudan')
  (lib : Iso Libya' Libya) (egy : Iso Egypt' Egypt)
  (cha : Iso Chad' Chad) (sud : Iso Sudan' Sudan)
  (hnorth : north' ⋙ egy.hom = lib.hom ⋙ north) (hwest : lib.hom ⋙ west = west' ⋙ cha.hom)
  (heast : egy.hom ⋙ east = east' ⋙ sud.hom) (hsouth : south' ⋙ sud.hom = cha.hom ⋙ south)

include hnorth in

include north west east south pb north' west' east' south' lib egy cha
  sud hnorth hwest heast hsouth in
theorem ofIso'_comm_sq : north' ⋙ east' = west' ⋙ south' :=
  calc north' ⋙ east'
  _ = lib.hom ⋙ north ⋙ egy.inv ⋙ east' := by rw [egy.eq_comp_inv.mpr hnorth]; rfl
  _ = lib.hom ⋙ (north ⋙ east) ⋙ sud.inv := by
    rw [egy.eq_inv_comp.mpr heast]; simp [Functor.comp_id, Functor.assoc]
  _ = lib.hom ⋙ (west ⋙ south) ⋙ sud.inv := by rw [pb.comm_sq]
  _ = west' ⋙ (cha.hom ⋙ south) ⋙ sud.inv := by
    rw [lib.eq_inv_comp.mpr hwest]; simp [Functor.id_comp, ← Functor.assoc]
  _ = west' ⋙ south' := by rw [sud.eq_comp_inv.mpr hsouth]

def ofIso'Lift {C : Type*} [Category C] (Cn : C ⥤ Egypt') (Cw : C ⥤ Chad')
    (hC : Cn ⋙ east' = Cw ⋙ south') : C ⥤ Libya' :=
  pb.lift (Cn ⋙ egy.hom) (Cw ⋙ cha.hom) (by simp [Functor.assoc, heast, ← hsouth, hC])
  ⋙ lib.inv

def ofIso'Universal {C : Type*} [Category C]
    (Cn : C ⥤ Egypt') (Cw : C ⥤ Chad') (hC : Cn ⋙ east' = Cw ⋙ south')
    : (lift : C ⥤ Libya') ×' lift ⋙ north' = Cn ∧ lift ⋙ west' = Cw ∧
    ∀ {l0 l1 : C ⥤ Libya'}, l0 ⋙ north' = l1 ⋙ north' → l0 ⋙ west' = l1 ⋙ west'
    → l0 = l1 :=
  ⟨ ofIso'Lift north west east south pb east' south' lib egy cha sud heast hsouth Cn Cw hC,
    by rw [ofIso'Lift, Functor.assoc, (Iso.inv_comp_eq_comp_inv lib egy hnorth).mpr hnorth,
        ← Functor.assoc, pb.fac_left, Functor.assoc, egy.hom_inv_id, Functor.comp_id],
    by rw [ofIso'Lift, Functor.assoc, (Iso.inv_comp_eq_comp_inv lib cha hwest.symm).mpr hwest.symm,
        ← Functor.assoc, pb.fac_right, Functor.assoc, cha.hom_inv_id, Functor.comp_id],
    by
      intro l0 l1 hn hw
      have : l0 ⋙ lib.hom = l1 ⋙ lib.hom := by
        apply pb.hom_ext
        · rw [Functor.assoc, ← hnorth, ← Functor.assoc, hn, Functor.assoc, hnorth, Functor.assoc]
        · rw [Functor.assoc, hwest, ← Functor.assoc, hw, Functor.assoc, ← hwest, Functor.assoc]
      calc l0
        _ = l0 ⋙ lib.hom ⋙ lib.inv := by aesop_cat
        _ = l1 ⋙ lib.hom ⋙ lib.inv := by rw [← Functor.assoc, this, Functor.assoc]
        _ = l1 := by aesop_cat
  ⟩

/--
Libya' --------------------------> Egypt'
  |    \∨                       v/   |
  |        Libya -------->Egypt      |
  |          |              |        |
  |          |              |        |
  |          |              |        |
  |          v              v        |
  |        Chad ---------> Sudan     |
  v      /^                     ^\   v
Chad' ---------------------------> Sudan

If the inner square is a pullback and all corners are isomorphic to the outer square,
then the outer square is also a pullback.
-/
def ofIso' : IsPullback north' west' east' south' :=
  ofUniversal north' west' east' south'
  (ofIso'_comm_sq north west east south pb north' west' east' south' lib egy cha
    sud hnorth hwest heast hsouth)
  (fun Cn Cw hC => ofIso'Universal north west east south pb north' west' east' south' lib egy cha
      sud hnorth hwest heast hsouth Cn Cw hC)
  (fun Cn Cw hC => ofIso'Universal north west east south pb north' west' east' south' lib egy cha
      sud hnorth hwest heast hsouth Cn Cw hC)

end

def isoIsPullback {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤ Y} {f : X ⥤ Z} {g : Y ⥤ Z}
    {fst' : P' ⥤ X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) : P ≅≅ P' where
  hom := h.toChosen ⋙ h'.fromChosen
  inv := h'.toChosen ⋙ h.fromChosen
  hom_inv_id := by
    conv => lhs; rw [Functor.assoc]; rhs; rw [← Functor.assoc]; rw [from_to_id]
    simp [Functor.id_comp, to_from_id]
  inv_hom_id := by
    conv => lhs; rw [Functor.assoc]; rhs; rw [← Functor.assoc]; rw [from_to_id]
    simp [Functor.id_comp, to_from_id]

lemma isoIsPullback.inv_comp_left {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤ Y} {f : X ⥤ Z} {g : Y ⥤ Z}
    {fst' : P' ⥤ X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) :
    (isoIsPullback h h').inv ⋙ fst = fst' := by
  simp [isoIsPullback, Functor.assoc, from_north, toChosen_north]

lemma isoIsPullback.inv_comp_right {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤  Y} {f : X ⥤  Z} {g : Y ⥤  Z}
    {fst' : P' ⥤ X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) :
    (isoIsPullback h h').inv ⋙ snd = snd' := by
  simp [isoIsPullback, Functor.assoc, from_west, toChosen_west]

lemma isoIsPullback.hom_comp_left {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤  Y} {f : X ⥤ Z} {g : Y ⥤ Z}
    {fst' : P' ⥤ X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) :
    (isoIsPullback h h').hom ⋙ fst' = fst := by
  simp [isoIsPullback, Functor.assoc, from_north, toChosen_north]

lemma isoIsPullback.hom_comp_left' {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤  Y} {f : X ⥤  Z} {g : Y ⥤  Z}
    {fst' : P' ⥤  X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) {hom} (e: hom = (isoIsPullback h h').hom) :
    hom ⋙ fst' = fst := by
  rw [e]
  apply isoIsPullback.hom_comp_left

lemma isoIsPullback.hom_comp_right {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤  Y} {f : X ⥤ Z} {g : Y ⥤  Z}
    {fst' : P' ⥤  X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) :
    (isoIsPullback h h').hom ⋙ snd' = snd := by
  simp [isoIsPullback, Functor.assoc, from_west, toChosen_west]

lemma isoIsPullback.hom_comp_right' {P P' X Y Z : Type*} [Category P] [Category P']
    [Category X] [Category Y] [Category Z]
    {fst : P ⥤ X} {snd : P ⥤  Y} {f : X ⥤ Z} {g : Y ⥤  Z}
    {fst' : P' ⥤  X} {snd' : P' ⥤ Y} (h : Functor.IsPullback fst snd f g)
    (h' : Functor.IsPullback fst' snd' f g) {hom} (e: hom = (isoIsPullback h h').hom) :
    hom ⋙ snd' = snd := by
  rw[e]
  apply isoIsPullback.hom_comp_right

def ofBotId {A A' B : Type*} [Category A] [Category A']
    [Category B]
    {i : A ≅≅ A'} {F1: A ⥤ B} {F2 : A' ⥤ B}
    (h' : F1 = i.hom ⋙ F2) : IsPullback i.hom F1 F2 (Functor.id B) := by
  fapply ofUniversal
  · aesop
  · intro C inst Cn Cw h
    simp only [Iso.cancel_iso_hom_right, forall_eq', imp_self, implies_true, and_true]
    have hinv : Cn ⋙ i.inv ⋙ i.hom = Cn ∧ Cn ⋙ i.inv ⋙ F1 = Cw := by
      aesop_cat
    exact ⟨ Cn ⋙ i.inv, hinv⟩
  · intro C inst Cn Cw h
    simp only [Iso.cancel_iso_hom_right, forall_eq', imp_self, implies_true, and_true]
    have hinv : Cn ⋙ i.inv ⋙ i.hom = Cn ∧ Cn ⋙ i.inv ⋙ F1 = Cw := by
      aesop_cat
    exact ⟨ Cn ⋙ i.inv, hinv⟩

namespace Paste
variable {Algeria Libya Egypt Niger Chad Sudan : Type*} [Category Algeria]
  [Category Libya] [Category Egypt] [Category Niger] [Category Chad] [Category Sudan]

section no_rth

/-
           no           rth
  Algeria -----> Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
variable
  {no : Algeria ⥤ Libya} {rth : Libya ⥤ Egypt}
  {west : Algeria ⥤ Niger} {sah : Libya ⥤ Chad} {east : Egypt ⥤ Sudan}
  {so : Niger ⥤ Chad} {uth : Chad ⥤ Sudan}
  (wsah : no ⋙ sah = west ⋙ so) (esah : rth ⋙ east = sah ⋙ uth)

include esah wsah in
theorem outer_comm_sq : no ⋙ rth ⋙ east = west ⋙ so ⋙ uth := by
  rw [esah, ← Functor.assoc, wsah, Functor.assoc]

section horiz

variable (wsah_pb : IsPullback no west sah so) (esah_pb : IsPullback rth sah east uth)

namespace horiz

variable {C : Type u} [Category.{v} C] (Cn : C ⥤ Egypt) (Cw : C ⥤ Niger)
  (hC : Cn ⋙ east = Cw ⋙ so ⋙ uth)

def lift : C ⥤ Algeria :=
  wsah_pb.lift (esah_pb.lift Cn (Cw ⋙ so) hC) Cw (esah_pb.fac_right _ _ _)

def universal : (lift : C ⥤ Algeria) ×'
    lift ⋙ no ⋙ rth = Cn ∧
    lift ⋙ west = Cw ∧
    ∀ {l0 l1 : C ⥤ Algeria}, l0 ⋙ no ⋙ rth = l1 ⋙ no ⋙ rth →
    l0 ⋙ west = l1 ⋙ west → l0 = l1 :=
  ⟨ lift wsah_pb esah_pb Cn Cw hC,
    by rw [lift, ← Functor.assoc, wsah_pb.fac_left, esah_pb.fac_left],
    wsah_pb.fac_right _ _ _,
    by
      intro l0 l1 hnorth hwest
      apply wsah_pb.hom_ext
      · apply esah_pb.hom_ext
        · exact hnorth
        · conv => right; rw [Functor.assoc, wsah, ← Functor.assoc]
          conv => left; rw [Functor.assoc, wsah, ← Functor.assoc, hwest]
      · exact hwest
  ⟩

end horiz

/--
Pullback pasting =>.
The outer square is a pullback when the two inner squares
are both pullbacks.
           no           rth
  Algeria -----> Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
def horiz : IsPullback (no ⋙ rth) west east (so ⋙ uth) :=
  IsPullback.ofUniversal (no ⋙ rth) west east (so ⋙ uth)
    (outer_comm_sq wsah esah)
    (fun _ _ hC => horiz.universal wsah wsah_pb esah_pb _ _ hC)
    (fun _ _ hC => horiz.universal wsah wsah_pb esah_pb _ _ hC)

end horiz

section ofRight

/-
           no           rth
  Algeria -----> Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
variable (esah_pb : IsPullback rth sah east uth)
  (outer_pb : IsPullback (no ⋙ rth) west east (so ⋙ uth))

namespace ofRight

variable {C : Type u} [Category.{v} C] (Cn : C ⥤ Libya) (Cw : C ⥤ Niger)
  (hC : Cn ⋙ sah = Cw ⋙ so)

def hCLeft : (Cn ⋙ rth) ⋙ east = Cw ⋙ so ⋙ uth :=
  by calc
    (Cn ⋙ rth) ⋙ east = Cn ⋙ (sah ⋙ uth) := by rw [Functor.assoc, esah]
    _ = (Cn ⋙ sah) ⋙ uth := by rw[← Functor.assoc]
    _ = (Cw ⋙ so) ⋙ uth := by rw [hC]
    _ = Cw ⋙ so ⋙ uth := by rw [Functor.assoc]

def lift : C ⥤ Algeria :=
  outer_pb.lift (Cn ⋙ rth) Cw (hCLeft esah Cn Cw hC)

def universal : (lift : C ⥤ Algeria) ×'
    lift ⋙ no = Cn ∧ lift ⋙ west = Cw ∧
    ∀ {l0 l1 : C ⥤ Algeria}, l0 ⋙ no = l1 ⋙ no → l0 ⋙ west = l1 ⋙ west → l0 = l1 :=
  ⟨ lift esah_pb.comm_sq outer_pb Cn Cw hC, by
     constructor
     . apply esah_pb.hom_ext
       . exact outer_pb.fac_left _ _ _
       . rw [Functor.assoc, wsah, ← Functor.assoc, hC]
         conv => rhs; rw! [← outer_pb.fac_right (Cn⋙rth) Cw (hCLeft esah Cn Cw hC)]
         rfl
     . constructor
       . exact outer_pb.fac_right (Cn⋙rth) Cw (hCLeft esah Cn Cw hC)
       . intro l0 l1 hln hlw
         apply outer_pb.hom_ext
         . rw[← Functor.assoc, ← Functor.assoc, hln]
         . exact hlw
    ⟩

end ofRight

/--
Pullback pasting <=.
The left square is a pullback when the right and outer squares
are both pullbacks.
           no           rth
  Algeria -----> Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
def ofRight : IsPullback no west sah so :=
  IsPullback.ofUniversal no west sah so
  wsah
  (fun Cn Cw hC => ofRight.universal wsah esah esah_pb outer_pb Cn Cw hC)
  (fun Cn Cw hC => ofRight.universal wsah esah esah_pb outer_pb Cn Cw hC)



end ofRight

end no_rth

section north
/-
               north
    ⌐-------------------------¬
    |                  rth    V
  Algeria        Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
variable {north : Algeria ⥤ Egypt} {rth : Libya ⥤ Egypt}
  {west : Algeria ⥤ Niger} {sah : Libya ⥤ Chad} {east : Egypt ⥤ Sudan}
  {so : Niger ⥤ Chad} {uth : Chad ⥤ Sudan}
  (outer : north ⋙ east = west ⋙ so ⋙ uth) (esah : rth ⋙ east = sah ⋙ uth)

section ofRight'

variable (esah_pb : IsPullback rth sah east uth)
  (outer_pb : IsPullback north west east (so ⋙ uth))

namespace ofRight'

variable {C : Type u} [Category.{v} C] (Cn : C ⥤ Libya) (Cw : C ⥤ Niger)
  (hC : Cn ⋙ sah = Cw ⋙ so)

def universal : (lift : C ⥤ Algeria) ×'
  lift ⋙ esah_pb.lift north (west ⋙ so) outer = Cn ∧
  lift ⋙ west = Cw ∧
  ∀ {l0 l1 : C ⥤ Algeria},
    l0 ⋙ esah_pb.lift north (west ⋙ so) outer = l1 ⋙ esah_pb.lift north (west ⋙ so) outer →
      l0 ⋙ west = l1 ⋙ west → l0 = l1 :=
  ⟨ lift outer_pb (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC),
  by constructor
     . apply esah_pb.hom_ext
       . calc
          (outer_pb.lift (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC) ⋙ esah_pb.lift north (west ⋙ so) outer) ⋙ rth =
            outer_pb.lift (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC) ⋙ esah_pb.lift north (west ⋙ so) outer ⋙ rth := by rw[Functor.assoc]
          _ = outer_pb.lift (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC) ⋙ north := by rw[esah_pb.fac_left north (west ⋙ so) outer]
          _ = Cn ⋙ rth := by rw[outer_pb.fac_left (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC)]
       . calc
          (outer_pb.lift (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC) ⋙ esah_pb.lift north (west ⋙ so) outer) ⋙ sah =
            outer_pb.lift (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC) ⋙ esah_pb.lift north (west ⋙ so) outer ⋙ sah := by rw[Functor.assoc]
          _ = outer_pb.lift (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC) ⋙ (west ⋙ so) := by rw[esah_pb.fac_right north (west ⋙ so) outer]
          _ = Cw ⋙ so := by rw[← Functor.assoc, outer_pb.fac_right (Cn ⋙ rth) Cw (ofRight.hCLeft esah Cn Cw hC)]
          _ = Cn ⋙ sah := by rw[hC]
     . constructor
       . exact outer_pb.fac_right (Cn⋙rth) Cw (ofRight.hCLeft esah Cn Cw hC)
       . intro l0 l1 hll hlw
         apply outer_pb.hom_ext
         . calc
            l0 ⋙ north = l0 ⋙ (esah_pb.lift north (west ⋙ so) outer ⋙ rth) :=
              by rw [esah_pb.fac_left north (west ⋙ so) outer ]
            _ = (l0 ⋙ esah_pb.lift north (west ⋙ so) outer) ⋙ rth := by rw [Functor.assoc]
            _ = (l1 ⋙ esah_pb.lift north (west ⋙ so) outer) ⋙ rth := by rw [hll]
            _ = l1 ⋙ north := by rw [Functor.assoc, esah_pb.fac_left north (west ⋙ so) outer]
         . exact hlw
    ⟩

end ofRight'

/--
Pullback pasting <=,
where the map `Algeria ⥤ Libya` is generated by the universal property of the right square
and the top map `north : Algberia ⥤ Egypt`.
The left square is a pullback when the right and outer squares
are both pullbacks.
               north
    ⌐-------------------------¬
    |                  rth    V
  Algeria        Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
def ofRight' {north : Algeria ⥤ Egypt} {rth : Libya ⥤ Egypt}
  {west : Algeria ⥤ Niger} {sah : Libya ⥤ Chad} {east : Egypt ⥤ Sudan}
  {so : Niger ⥤ Chad} {uth : Chad ⥤ Sudan}
  (outer : north ⋙ east = west ⋙ so ⋙ uth)
  (outer_pb : IsPullback north west east (so ⋙ uth))
  (esah : rth ⋙ east = sah ⋙ uth)
  (esah_pb : IsPullback rth sah east uth)
  (no : Algeria ⥤ Libya := esah_pb.lift north (west ⋙ so) outer)
  (no_eq : no = esah_pb.lift north (west ⋙ so) outer)
  :
  IsPullback no west sah so :=
  no_eq ▸
  IsPullback.ofUniversal (esah_pb.lift north (west ⋙ so) outer) west sah so
  (esah_pb.fac_right _ _ _)
  (fun Cn Cw hC => ofRight'.universal outer esah esah_pb outer_pb Cn Cw hC)
  (fun Cn Cw hC => ofRight'.universal outer esah esah_pb outer_pb Cn Cw hC)

end ofRight'
end north

end Paste

section

variable {Libya Egypt Chad Sudan : Type*} [Category Libya]
  [Category Egypt] [Category Chad] [Category Sudan]
  (north : Libya ≅≅ Egypt) (west : Libya ⥤ Chad)
  (east : Egypt ⥤ Sudan) (south : Chad ≅≅ Sudan)
  (comm_sq : north.hom ⋙ east = west ⋙ south.hom)

def ofHorizIso.lift {C : Type*} [Category C] (Cn : C ⥤ Egypt) : C ⥤ Libya :=
  Cn ⋙ north.inv

include comm_sq in
lemma ofHorizIso.inv_comm_sq : east ⋙ south.inv = north.inv ⋙ west := by
  rw [Functor.Iso.eq_inv_comp, ← Functor.assoc, Functor.Iso.comp_inv_eq, comm_sq]

def ofHorizIso.universal {C : Type*} [Category C] (Cn : C ⥤ Egypt) (Cw : C ⥤ Chad)
    (hC : Cn ⋙ east = Cw ⋙ south.hom) :
    (lift : C ⥤ Libya) ×' lift ⋙ north.hom = Cn ∧ lift ⋙ west = Cw ∧
    ∀ {l0 l1 : C ⥤ Libya}, l0 ⋙ north.hom = l1 ⋙ north.hom →
    l0 ⋙ west = l1 ⋙ west → l0 = l1 :=
  ⟨ofHorizIso.lift north Cn, by simp [lift, Functor.assoc, Functor.comp_id],
    calc _
    _ = (Cw ⋙ south.hom) ⋙ south.inv := by
      rw [← hC, Functor.assoc, ofHorizIso.inv_comm_sq _ _ _ _ comm_sq, lift, Functor.assoc]
    _ = Cw := by
      simp [Functor.assoc, Functor.comp_id],
    by
      intro _ _ h0 _
      simpa [Functor.Iso.cancel_iso_hom_right] using h0 ⟩

def ofHorizIso : IsPullback north.hom west east south.hom :=
  ofUniversal _ _ _ _ comm_sq
  (fun Cn Cw hC => ofHorizIso.universal _ _ _ _ comm_sq Cn Cw hC)
  (fun Cn Cw hC => ofHorizIso.universal _ _ _ _ comm_sq Cn Cw hC)

end

end IsPullback

end Functor
end CategoryTheory

namespace CategoryTheory.Cat

open Functor Limits

/-- Compatibility alias: morphisms in `Cat` are bundled functors. -/
abbrev homOf {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := F.toCatHom

section
variable {Libya Egypt Chad Sudan : Type u} [Category.{v} Libya]
  [Category.{v} Egypt] [Category.{v} Chad] [Category.{v} Sudan]
  {north : Libya ⥤ Egypt} {west : Libya ⥤ Chad}
  {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}
  {comm_sq : north ⋙ east = west ⋙ south}
  (h : Functor.IsPullback north west east south)
  (s : Limits.PullbackCone (homOf east) (homOf south))

private def coneCondition : s.fst.toFunctor ⋙ east = s.snd.toFunctor ⋙ south :=
  congrArg Cat.Hom.toFunctor s.condition

def lift : s.pt ⟶ of Libya := homOf (h.lift s.fst.toFunctor s.snd.toFunctor (coneCondition s))

def fac_left : lift h s ≫ homOf north = s.fst := by
  apply Cat.ext
  exact h.fac_left s.fst.toFunctor s.snd.toFunctor (coneCondition s)

def fac_right : lift h s ≫ homOf west = s.snd := by
  apply Cat.ext
  exact h.fac_right s.fst.toFunctor s.snd.toFunctor (coneCondition s)

def uniq (m : s.pt ⟶ of Libya) (hl : m ≫ homOf north = s.fst)
    (hr : m ≫ homOf west = s.snd) : m = lift h s := by
  apply Cat.ext
  apply h.hom_ext
  · exact (by
      have hl' := congrArg Cat.Hom.toFunctor hl
      have fl' := congrArg Cat.Hom.toFunctor (fac_left h s)
      exact hl'.trans fl'.symm)
  · exact (by
      have hr' := congrArg Cat.Hom.toFunctor hr
      have fr' := congrArg Cat.Hom.toFunctor (fac_right h s)
      exact hr'.trans fr'.symm)

variable (comm_sq) in
def isPullback : IsPullback (homOf north) (homOf west) (homOf east)
    (homOf south) := by
  have commSqCat : homOf north ≫ homOf east = homOf west ≫ homOf south := by
    apply Cat.ext
    exact comm_sq
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    commSqCat (lift h) (fac_left _) (fac_right _) (uniq _))

noncomputable def functorIsPullback
    (h : IsPullback (homOf north) (homOf west) (homOf east) (homOf south)) :
    Functor.IsPullback north west east south := by
  have hChosen : IsPullback (P := Cat.of (Functor.IsPullback.Chosen east south))
    (homOf IsPullback.Chosen.north) (homOf IsPullback.Chosen.west) (homOf east)
    (homOf south) :=
    Cat.isPullback (comm_sq := Functor.IsPullback.Chosen.comm_sq)
      (Functor.IsPullback.Chosen.isPullback east south)
  let i := IsPullback.isoIsPullback _ _ h hChosen
  convert Functor.IsPullback.ofIsoChosen east south i.hom.toFunctor i.inv.toFunctor ?_ ?_ using 1
  · exact congrArg Cat.Hom.toFunctor (IsPullback.isoIsPullback_hom_fst _ _ h hChosen).symm
  · exact congrArg Cat.Hom.toFunctor (IsPullback.isoIsPullback_hom_snd _ _ h hChosen).symm
  · exact congrArg Cat.Hom.toFunctor i.hom_inv_id
  · exact congrArg Cat.Hom.toFunctor i.inv_hom_id

end
end Cat

namespace Grpd

open Functor Limits

/-- Compatibility alias for unbundled functors as morphisms in `Grpd`. -/
abbrev homOf' {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D] (F : C ⥤ D) :
    Grpd.of C ⟶ Grpd.of D := F

variable {Libya Egypt Chad Sudan : Type u} [Groupoid.{v} Libya]
  [Groupoid.{v} Egypt] [Groupoid.{v} Chad] [Groupoid.{v} Sudan]
  {north : Libya ⥤ Egypt} {west : Libya ⥤ Chad}
  {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}
  (h : Functor.IsPullback north west east south)
  (s : Limits.PullbackCone (homOf' east) (homOf' south))

def lift : s.pt ⟶ of Libya := h.lift s.fst s.snd s.condition

def fac_left : lift h s ≫ homOf' north = s.fst :=
  h.fac_left _ _ _

def fac_right : lift h s ≫ homOf' west = s.snd :=
  h.fac_right _ _ _

def uniq (m : s.pt ⟶ of Libya) (hl : m ≫ homOf' north = s.fst)
    (hr : m ≫ homOf' west = s.snd) : m = lift h s := by
  apply h.hom_ext
  · convert (fac_left h s).symm
  · convert (fac_right h s).symm

def isPullback : IsPullback (homOf' north) (homOf' west) (homOf' east) (homOf' south) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    h.comm_sq (lift h) (fac_left _) (fac_right _) (uniq _))

noncomputable def functorIsPullback {Libya Egypt Chad Sudan : Type v} [Groupoid.{v} Libya]
    [Groupoid.{v} Egypt] [Groupoid.{v} Chad] [Groupoid.{v} Sudan]
    {north : Libya ⥤ Egypt} {west : Libya ⥤ Chad}
    {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}
    (h : IsPullback (homOf' north) (homOf' west) (homOf' east) (homOf' south)) :
    Functor.IsPullback north west east south :=
  Cat.functorIsPullback <|
    @Functor.map_isPullback _ _ _ _ Grpd.forgetToCat (Grpd.of Libya) (Grpd.of Egypt) (Grpd.of Chad)
    (Grpd.of Sudan) (homOf' north) (homOf' west) (homOf' east) (homOf' south) _ h

end Grpd

/--
The following square is a pullback

 AsSmall C ------- ≅ ------> C
        |                    |
        |                    |
 AsSmall F                   F
        |                    |
        |                    |
        v                    v
 AsSmall D  ------- ≅ -----> D

-/
def AsSmall.isPullback {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D) :
    Functor.IsPullback AsSmall.down (AsSmall.down ⋙ F ⋙ AsSmall.up) F AsSmall.down :=
  Functor.IsPullback.ofHorizIso AsSmall.downIso _ _ AsSmall.downIso rfl

end CategoryTheory
