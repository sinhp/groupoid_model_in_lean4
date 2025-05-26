import GroupoidModel.ForMathlib

universe v u v₁ u₁

namespace CategoryTheory.Functor

section
variable {Libya Egypt Chad Sudan : Type*}
  [Category Libya] [Category Egypt] [Category Chad] [Category Sudan]

/-
       north
  Libya ----> Egypt
    |          |
  west         |east
    |          |
    V          V
  Chad ----> Sudan
       south
-/

structure PullbackCone (C : Type*) [Category C] (east : Egypt ⥤ Sudan) (south : Chad ⥤ Sudan) where
  (north : C ⥤ Egypt)
  (west : C ⥤ Chad)
  (comm_sq : north ⋙ east = west ⋙ south)

structure Pullback {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}
    (P : PullbackCone Libya east south)
    {C : Type u} [Category.{v} C] (cone : PullbackCone C east south) where
  (lift : C ⥤ Libya)
  (fac_left : lift ⋙ P.north = cone.north)
  (fac_right : lift ⋙ P.west = cone.west)
  (hom_ext {l0 l1 : C ⥤ Libya} : l0 ⋙ P.north = l1 ⋙ P.north →
    l0 ⋙ P.west = l1 ⋙ P.west → l0 = l1)

namespace Pullback

section
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
variable {Algeria Niger : Type*} [Category Algeria] [Category Niger]
  {no : Algeria ⥤ Libya} {rth : Libya ⥤ Egypt}
  {west : Algeria ⥤ Niger} {sah : Libya ⥤ Chad} {east : Egypt ⥤ Sudan}
  {so : Niger ⥤ Chad} {uth : Chad ⥤ Sudan}
  (wsah : no ⋙ sah = west ⋙ so) (esah : rth ⋙ east = sah ⋙ uth)
  (esah_pb : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C east uth),
    Pullback (PullbackCone.mk _ _ esah) cone)
  (wsah_pb : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C sah so),
    Pullback (PullbackCone.mk _ _ wsah) cone)

variable {C : Type u} [Category.{v} C] (cone : PullbackCone C east (so ⋙ uth))

@[simps] def pasteHorizEastCone : PullbackCone C east uth where
  north := cone.north
  west := cone.west ⋙ so
  comm_sq := cone.comm_sq

@[simps] def pasteHorizWestCone : PullbackCone C sah so where
  north := (esah_pb (pasteHorizEastCone cone)).lift
  west := cone.west
  comm_sq := (esah_pb (pasteHorizEastCone cone)).fac_right

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
def pasteHoriz : Pullback (PullbackCone.mk (no ⋙ rth) west (by
    rw [Functor.assoc, esah, ← Functor.assoc, wsah, Functor.assoc])) cone where
  lift := (wsah_pb (pasteHorizWestCone esah esah_pb cone)).lift
  fac_left := by
    rw [← Functor.assoc, (wsah_pb _).fac_left]
    exact (esah_pb _).fac_left
  fac_right := (wsah_pb _).fac_right
  hom_ext hleft hright := by
    apply (wsah_pb (pasteHorizWestCone esah esah_pb cone)).hom_ext
    · apply (esah_pb (pasteHorizEastCone cone)).hom_ext
      · exact hleft
      · simp only [Functor.assoc, wsah]
        simp only [← Functor.assoc, hright]
    · exact hright
end

section
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
variable {Algeria Niger : Type*} [Category Algeria] [Category Niger]
  {no : Algeria ⥤ Libya} {rth : Libya ⥤ Egypt}
  {west : Algeria ⥤ Niger} {sah : Libya ⥤ Chad} {east : Egypt ⥤ Sudan}
  {so : Niger ⥤ Chad} {uth : Chad ⥤ Sudan}
  (wsah : no ⋙ sah = west ⋙ so) (esah : rth ⋙ east = sah ⋙ uth)
  (esah_pb : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C east uth),
    Pullback (PullbackCone.mk _ _ esah) cone)
  (outer_pb : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C east (so ⋙ uth)),
    Pullback (PullbackCone.mk (no ⋙ rth) west (by
      rw [Functor.assoc, esah, ← Functor.assoc, wsah, Functor.assoc]))
      cone)

variable {C : Type u} [Category.{v} C] (cone : PullbackCone C sah so)

@[simps] def ofRightOuterCone : PullbackCone C east (so ⋙ uth) where
  north := cone.north ⋙ rth
  west := cone.west
  comm_sq := by
    rw [Functor.assoc, esah, ← Functor.assoc, cone.comm_sq, Functor.assoc]

def ofRightRightCone : PullbackCone C east uth where
  north := cone.north ⋙ rth
  west := cone.west ⋙ so
  comm_sq := by rw [Functor.assoc, esah, ← Functor.assoc, cone.comm_sq]

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
def ofRight : Pullback (PullbackCone.mk no west wsah) cone where
  lift := (outer_pb (ofRightOuterCone esah cone)).lift
  fac_left := by
    apply (esah_pb (ofRightRightCone esah cone)).hom_ext
    · exact (outer_pb (ofRightOuterCone esah cone)).fac_left
    · rw! [Functor.assoc, wsah, ← Functor.assoc,
        (outer_pb (ofRightOuterCone esah cone)).fac_right, cone.comm_sq]
      simp
  fac_right := (outer_pb (ofRightOuterCone esah cone)).fac_right
  hom_ext hleft hright := by
    apply (outer_pb (ofRightOuterCone esah cone)).hom_ext
    · rw [← Functor.assoc, hleft, Functor.assoc]
    · exact hright

end

section
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
variable {Algeria : Type u} {Niger : Type*} [Category.{v} Algeria] [Category Niger]
  {north : Algeria ⥤ Egypt} {rth : Libya ⥤ Egypt}
  {west : Algeria ⥤ Niger} {sah : Libya ⥤ Chad} {east : Egypt ⥤ Sudan}
  {so : Niger ⥤ Chad} {uth : Chad ⥤ Sudan}
  (outer : north ⋙ east = west ⋙ so ⋙ uth) (esah : rth ⋙ east = sah ⋙ uth)
  (esah_pb : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C east uth),
    Pullback (PullbackCone.mk _ _ esah) cone)
  (outer_pb : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C east (so ⋙ uth)),
    Pullback (PullbackCone.mk north west outer) cone)

variable {C : Type u} [Category.{v} C] (cone : PullbackCone C sah so)

@[simps] def ofRight'Outer : PullbackCone Algeria east uth where
  north := north
  west := west ⋙ so
  comm_sq := outer

def ofRight'Lift : Algeria ⥤ Libya := (esah_pb (ofRight'Outer outer)).lift

@[simps] def ofRight'OuterCone : PullbackCone Algeria east (so ⋙ uth) where
  north := (ofRight'Lift outer esah esah_pb ⋙ rth)
  west := west
  comm_sq := by
    convert outer
    convert (esah_pb (ofRight'Outer outer)).fac_left

def outer_pb' {C : Type u} [Category.{v} C] (cone : PullbackCone C east (so ⋙ uth)) :
    Pullback (ofRight'OuterCone outer esah esah_pb) cone where
  lift := (outer_pb cone).lift
  fac_left := by
    convert (outer_pb cone).fac_left
    exact (esah_pb (ofRight'Outer outer)).fac_left
  fac_right := (outer_pb cone).fac_right
  hom_ext hl hr := by
    apply (outer_pb cone).hom_ext _ hr
    convert hl
    convert (esah_pb (ofRight'Outer outer)).fac_left.symm
    convert (esah_pb (ofRight'Outer outer)).fac_left.symm

/--
      ofRight'Lift
  Algeria -----> Libya
    |              |
  west         sah |
    |              |
    V              V
  Niger   -----> Chad
           so
-/
def ofRight'CommSq : (ofRight'Lift outer esah esah_pb) ⋙ sah = west ⋙ so :=
  (esah_pb (ofRight'Outer outer)).fac_right

/--
Pullback pasting <=,
where the map `no` is generated by the universal property of the right square
and the top map `north : Algberia ⥤ Egypt`.
The left square is a pullback when the right and outer squares
are both pullbacks.
        ofRight'Lift    rth
  Algeria -----> Libya ----> Egypt
    |              |          |
  west         sah |          | east
    |              |          |
    V              V          V
  Niger   -----> Chad  ----> Sudan
           so           uth
-/
def ofRight' : Pullback (PullbackCone.mk (ofRight'Lift outer esah esah_pb) west
    (esah_pb (ofRight'Outer outer)).fac_right) cone :=
  ofRight _ esah esah_pb (outer_pb' _ _ _ outer_pb) cone

end

end Pullback

end


end CategoryTheory.Functor

namespace CategoryTheory.Cat

open Functor Limits

section
variable {Libya Egypt Chad Sudan : Type u} [Category.{v} Libya]
  [Category.{v} Egypt] [Category.{v} Chad] [Category.{v} Sudan]
  {north : Libya ⥤ Egypt} {west : Libya ⥤ Chad}
  {east : Egypt ⥤ Sudan} {south : Chad ⥤ Sudan}
  {comm_sq : north ⋙ east = west ⋙ south}
  (h : Π {C : Type u} [Category.{v} C] (cone : PullbackCone C east south),
      Pullback (PullbackCone.mk north west comm_sq) cone)
  (s : Limits.PullbackCone (homOf east) (homOf south))

def pullbackCone :
    Functor.PullbackCone s.pt east south where
  north := s.fst
  west := s.snd
  comm_sq := s.condition

def lift : s.pt ⟶ of Libya := (h (pullbackCone s)).lift

def fac_left : lift h s ≫ (homOf north) = s.fst :=
  (h (pullbackCone s)).fac_left

def fac_right : lift h s ≫ (homOf west) = s.snd :=
  (h (pullbackCone s)).fac_right

def uniq (m : s.pt ⟶ of Libya) (hl : m ≫ homOf north = s.fst)
    (hr : m ≫ homOf west = s.snd) : m = lift h s := by
  apply (h (pullbackCone s)).hom_ext
  · convert (fac_left h s).symm
  · convert (fac_right h s).symm

variable (comm_sq) in
def isPullback :
    IsPullback (homOf north) (homOf west) (homOf east)
    (homOf south) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    comm_sq (lift h) (fac_left _) (fac_right _) (uniq _))

end

end CategoryTheory.Cat
