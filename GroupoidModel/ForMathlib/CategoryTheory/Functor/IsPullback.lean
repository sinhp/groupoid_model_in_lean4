import GroupoidModel.ForMathlib

universe v u

namespace CategoryTheory.Functor

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
    {C : Type*} [Category C] (cone : PullbackCone C east south) where
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

def pasteHorizEastCone : PullbackCone C east uth where
  north := cone.north
  west := cone.west ⋙ so
  comm_sq := cone.comm_sq

def pasteHorizWestCone : PullbackCone C sah so where
  north := (esah_pb (pasteHorizEastCone cone)).lift
  west := cone.west
  comm_sq := sorry

def pasteHoriz : Pullback (PullbackCone.mk (no ⋙ rth) west (by
        rw [Functor.assoc, esah, ← Functor.assoc, wsah, Functor.assoc]
        )) cone where
  lift := sorry
  fac_left := sorry
  fac_right := sorry
  hom_ext := sorry
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

end Pullback

end CategoryTheory.Functor
