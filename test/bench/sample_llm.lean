import GroupoidModel.Syntax.Frontend.Prelude

noncomputable section

namespace sample1

def benchDef_0 : Type 1 := Type 0 → Type 0

def benchDef_1 : Type 1 := Type 0 → Type 0

def benchDef_2 : Type _ := (A : Type 0) → A → A

def benchDef_3 : Type 1 := (A : Type 0) → (B : Type 0) → (A → B) → A → B

def benchDef_4 : Type _ := (A : Type 0) → Identity A A

def benchDef_5 : Type 1 := Sigma (fun (A : Type 0) => A → A)

def benchDef_6 : Type _ := (A : Type 0) → (a : A) → (b : A) → Identity a b → Identity b a

def benchDef_7 : Type _ := (A : Type 0) → (B : A → Type 0) → ((a : A) → B a) → Sigma B

def benchDef_8 : Type _ := (A : Type 0) → (B : Type 0) → Sigma (fun (_ : A → B) => Sigma (fun (_ : B → A) => Type 0))

def benchDef_9 : Type _ := (A : Type 0) → (a : A) → (b : A) → (c : A) → Identity a b → Identity b c → Identity a c

end sample1

namespace sample2

def benchDef_0 : Type 1 := Type 0 → Type 0

def benchDef_1 : (A : Type 0) → A → A := fun _ a => a

def benchDef_2 : (A : Type 0) → (B : Type 0) → A → B → A := fun _ _ a _ => a
def benchDef_3 : (A : Type 0) → Identity A A := fun A => Identity.refl A
def benchDef_4 : Sigma (fun (A : Type 1) => A → A) := Sigma.mk (Type 0 → Type 0) (fun f => f)
def benchDef_5 : (A : Type 0) → (a : A) → (b : A) → Identity a b → Identity b a :=
  fun A a b p => match p with | Identity.refl _ => Identity.refl a
-- def benchDef_6 : (A : Type 0) → (B : A → Type 0) → ((a : A) → B a) → Sigma B :=
--   fun A B f => Sigma.mk (f (Sigma.mk (Type 0) Type).fst) (f (Sigma.mk (Type 0) Type).fst)
def benchDef_7 : (A : Type 0) → (B : Type 0) → (C : Type 0) →
  (f : A → B) → (g : B → C) → (a : A) → Identity (g (f a)) (g (f a)) :=
  fun A B C f g a => Identity.refl (g (f a))
def benchDef_8 : (A : Type 0) → (a : A) → (b : A) → (c : A) →
  Identity a b → Identity b c → Sigma (fun (_ : Identity a c) => Identity a a) :=
  fun A a b c p q =>
    match p, q with
    | Identity.refl _, Identity.refl _ => Sigma.mk (Identity.refl a) (Identity.refl a)
def benchDef_9 : (A : Type 1) → (B : A → Type 1) → (C : (a : A) → B a → Type 1) →
  ((a : A) → (b : B a) → C a b) → (s : Sigma B) → C s.fst s.snd :=
  fun A B C f s => f s.fst s.snd

end sample2

namespace sample3

def benchDef_10 : Type 2 := (A : Type 1) → (B : Type 0) → (A → B) → A → B

def benchDef_11 : Type 1 := Sigma (fun (A : Type 0) => Sigma (fun (_ : A) => A))

def benchDef_12 : Type 1 := (A : Type 0) → (P : A → Type 0) → ((a : A) → P a) → (a : A) → P a

-- def benchDef_13 : Type 1 := (A : Type 0) → Identity (A → A) (fun (x : A) => x)

def benchDef_14 : Type _ := (A : Type 0) → (B : Type 0) → (f : A → B) → (g : A → B) → ((a : A) → Identity (f a) (g a)) → Type 0

def benchDef_15 : Type _ := Sigma (fun (A : Type 0) => Sigma (fun (a : A) => Identity a a))

def benchDef_16 : Type _ := (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) → ((a : A) → (b : B a) → C a b) → Type 0

def benchDef_17 : Type _ := (A : Type 0) → (a : A) → Identity (Identity.refl a) (Identity.refl a)

def benchDef_18 : Type _ := (A : Type 0) → (B : Type 0) → (A → B) → (B → A) → Sigma (fun (_ : A) => B)

def benchDef_19 : Type _ := (A : Type 0) → (B : Type 0) → (C : Type 0) → (A → B) → (B → C) → A → C

def benchDef_20 : Type _ := (A : Type 0) → (x : A) → (y : A) → (p : Identity x y) → (q : Identity x y) → Identity p q → Type 0

def benchDef_21 : Type _ := Sigma (fun (A : Type 0) => Sigma (fun (B : A → Type 0) => (a : A) → B a))

def benchDef_22 : Type 2 := (A : Type 0) → (B : Type 0) → Identity Type Type → A → B → Type 0

def benchDef_23 : Type _ := (A : Type 1) → (B : Type 0) → (C : Type 0) → ((A → B) → C) → (A → B → C)

-- def benchDef_24 : Type _ := (A : Type 0) → (a : A) → (b : A) → (c : A) → (d : A) → Identity a b → Identity c d → Identity (Sigma.mk a c) (Sigma.mk b d)

def benchDef_25 : Type _ := Sigma (fun (f : Type 0 → Type 0) => (A : Type 0) → A → f A)

def benchDef_26 : Type _ := (A : Type 0) → (B : A → Type 1) → Sigma B → Sigma (fun (a : A) => Type 0)

def benchDef_27 : Type _ := (A : Type 0) → (B : Type 0) → (f : A → B) → (a1 : A) → (a2 : A) → Identity a1 a2 → Identity (f a1) (f a2)

def benchDef_28 : Type _ := (P : Type 0 → Type 0) → ((A : Type 0) → P A) → Sigma P

def benchDef_29 : Type _ := Sigma (fun (A : Type 0) => Sigma (fun (B : Type 0) => Sigma (fun (_ : A → B) => B → A)))

def benchDef_30 : Type _ := (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) → (f : (a : A) → (b : B a) → C a b) → (g : (a : A) → (b : B a) → C a b) → ((a : A) → (b : B a) → Identity (f a b) (g a b)) → Type 0

def benchDef_31 : Type _ := (A : Type 0) → (B : Type 0) → (C : Type 0) → Identity A B → Identity B C → Identity A C

def benchDef_32 : Type _ := (A : Type 0) → (P : A → Type 1) → (Q : A → Type 0) → ((a : A) → P a → Q a) → Sigma P → Sigma Q

def benchDef_33 : Type _ := Sigma (fun (A : Type 0) => Sigma (fun (a : A) => Sigma (fun (b : A) => Identity a b)))

def benchDef_34 : Type _ := (A : Type 0) → (B : A → Type 0) → (p : Sigma B) → Identity p (Sigma.mk p.fst p.snd)

def benchDef_35 : Type _ := (F : Type 0 → Type 0) → (A : Type 0) → Identity (F (F A)) (F (F A))

def benchDef_36 : Type _ := (A : Type 0) → (B : Type 0) → (C : Type 0) → (f : A → B → C) → (a1 : A) → (a2 : A) → (b1 : B) → (b2 : B) → Identity a1 a2 → Identity b1 b2 → Identity (f a1 b1) (f a2 b2)

def benchDef_37 : Type _ := (A : Type 0) → (B : Type 0) → (f : A → B) → (g : B → A) → ((a : A) → Identity (g (f a)) a) → ((b : B) → Identity (f (g b)) b) → Type 0

def benchDef_38 : Type _ := Sigma (fun (P : Type 0 → Type 0) => Sigma (fun (_ : (A : Type 0) → P A) => Type 0))

def benchDef_39 : Type _ := (A : Type 1) → (B : A → Type 0) → (C : A → Type 0) → ((a : A) → B a → C a) → ((a : A) → C a → B a) → Sigma (fun (a : A) => Type 0)

-- def benchDef_40 : Type _ := (A : Type 0) → (B : Type 0) → (p : Identity A B) → (a : A) → (b : B) → Identity a b → Type 0

def benchDef_41 : Type _ := (A : Type 0) → Sigma (fun (f : A → A) => Sigma (fun (g : A → A) => (a : A) → Identity (f (g a)) a))

def benchDef_42 : Type _ := (A : Type 0) → (B : A → Type 0) → (C : A → Type 0) → Sigma (fun (f : (a : A) → B a → C a) => Sigma (fun (g : (a : A) → C a → B a) => Type 0))

def benchDef_43 : Type _ := (A : Type 0) → (x : A) → (y : A) → (z : A) → (p : Identity x y) → (q : Identity y z) → (r : Identity x z) → Identity r r → Type 0

def benchDef_44 : Type _ := (A : Type 0) → (B : Type 0) → (C : Type 0) → (D : Type 0) → (A → B) → (B → C) → (C → D) → A → D

def benchDef_45 : Type _ := Sigma (fun (A : Type 0) => Sigma (fun (B : A → Type 0) => Sigma (fun (_ : (a : A) → B a) => A)))

-- def benchDef_46 : Type _ := (A : Type 0) → (B : A → Type 0) → (s : Sigma B) → (t : Sigma B) → Identity s.fst t.fst → Identity s.snd t.snd → Identity s t

def benchDef_47 : Type _ := (P : Type 0 → Type 0 → Type 0) → ((A : Type 0) → (B : Type 0) → P A B → P B A) → Type 0

def benchDef_48 : Type _ := (A : Type 0) → (B : Type 0) → (f : A → B) → (g : B → A) → (h : A → A) → ((a : A) → Identity (h a) (g (f a))) → ((a : A) → Identity (h (h a)) a) → Type 0

def benchDef_49 : Type _ := (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) → (D : (a : A) → (b : B a) → C a b → Type 0) → Sigma (fun (a : A) => Sigma (fun (b : B a) => Sigma (fun (c : C a b) => D a b c)))

def benchDef_50 : Type _ := Sigma (fun (F : Type 0 → Type 0) => Sigma (fun (G : Type 0 → Type 0) => (A : Type 0) → Identity (F (G A)) (G (F A))))

def benchDef_51 : Type _ := (A : Type 0) → (P : A → Type 1) → (Q : (a : A) → P a → Type 0) → (R : (a : A) → (p : P a) → Q a p → Type 0) → ((a : A) → (p : P a) → (q : Q a p) → R a p q) → Sigma (fun (a : A) => Sigma (fun (p : P a) => Sigma (fun (q : Q a p) => R a p q)))

def benchDef_52 : Type _ := (A : Type 0) → (B : Type 0) → (f : A → B) → (g : A → B) → (h : B → B) → ((a : A) → Identity (f a) (g a)) → ((b : B) → Identity (h b) b) → (a : A) → Identity (h (f a)) (g a)

def benchDef_53 : Type _ := (A : Type 0) → (B : Type 0) → Sigma (fun (f : A → B) => Sigma (fun (g : B → A) => Sigma (fun (_ : (a : A) → Identity (g (f a)) a) => (b : B) → Identity (f (g b)) b)))

-- def benchDef_54 : Type _ := (A : Type 0) → (B : A → Type 0) → (C : A → Type 0) → (f : (a : A) → B a → C a) → (p : Sigma B) → (q : Sigma B) → Identity p q → Identity (f p.fst p.snd) (f q.fst q.snd)

-- def benchDef_55 : Type _ := (A : Type 0) → (B : Type 0) → (C : Type 0) → (p : Identity A B) → (q : Identity B C) → (r : Identity A C) → Identity r r → (a : A) → (c : C) → Identity a c → Type 0

def benchDef_56 : Type _ := Sigma (fun (A : Type 0) => Sigma (fun (B : A → Type 0) => Sigma (fun (C : (a : A) → B a → Type 0) => Sigma (fun (_ : (a : A) → (b : B a) → C a b) => Type 0))))

-- def benchDef_57 : Type _ := (A : Type 0) → (B : A → Type 0) → (f : (a : A) → B a) → (g : (a : A) → B a) → (p : (a : A) → Identity (f a) (g a)) → (a : A) → (b : A) → Identity a b → Identity (p a) (p b) → Type 0

def benchDef_58 : Type _ := (P : (A : Type 0) → A → Type 0) → ((A : Type 0) → (a : A) → P A a) → Sigma (fun (A : Type 0) => Sigma (fun (a : A) => P A a))

def benchDef_59 : Type _ := (A : Type 0) → (B : Type 0) → (C : Type 0) → (D : Type 0) → (f : A → B → C) → (g : C → D) → (h : A → B → D) → ((a : A) → (b : B) → Identity (g (f a b)) (h a b)) → Sigma (fun (a : A) => Sigma (fun (b : B) => Identity (g (f a b)) (h a b)))

end sample3

namespace sample4

def benchDef_10 : (A : Type 0) → (B : Type 0) → (f : A → B) → (a : A) → Identity (f a) (f a) :=
  fun A B f a => Identity.refl (f a)

def benchDef_11 : (A : Type 0) → (P : A → Type 0) → Sigma P → A :=
  fun A P s => s.fst

def benchDef_12 : (A : Type 0) → (a : A) → Sigma (fun (b : A) => Identity a b) :=
  fun A a => Sigma.mk a (Identity.refl a)

def benchDef_13 : (A : Type 0) → (B : Type 0) → A → B → Sigma (fun (_ : A) => B) :=
  fun A B a b => Sigma.mk a b

def benchDef_14 : (A : Type 0) → (B : Type 0) → (C : Type 0) → (A → B) → (B → C) → A → C :=
  fun A B C f g a => g (f a)

def benchDef_15 : (A : Type 0) → (a : A) → (b : A) → (c : A) → Identity a b → Identity b c → Identity a c :=
  fun A a b c p q => match p, q with | Identity.refl _, Identity.refl _ => Identity.refl a

def benchDef_16 : (A : Type 0) → (B : A → Type 0) → (a : A) → B a → Sigma B :=
  fun A B a b => Sigma.mk a b

def benchDef_17 : (A : Type 0) → Identity ((fun (x : A) => x) = (fun (x : A) => x)) ((fun (x : A) => x) = (fun (x : A) => x)) :=
  fun A => Identity.refl ((fun (x : A) => x) = (fun (x : A) => x))

def benchDef_18 : Sigma (fun (A : Type 1) => Sigma (fun (a : A) => Identity a a)) :=
  Sigma.mk (Type 0 → Type 0) (Sigma.mk (fun x => x) (Identity.refl (fun x => x)))

def benchDef_19 : (A : Type 0) → (B : Type 0) → Sigma (fun (_ : A → B) => B → A) → A → A :=
  fun A B s a => s.snd (s.fst a)

def benchDef_20 : (A : Type 1) → (B : Type 1) → (f : A → B) → (g : B → A) →
  (a : A) → Identity (g (f a)) (g (f a)) :=
  fun A B f g a => Identity.refl (g (f a))

def benchDef_21 : (A : Type 0) → (P : A → Type 0) → (Q : A → Type 0) →
  ((a : A) → P a → Q a) → Sigma P → Sigma Q :=
  fun A P Q f s => Sigma.mk s.fst (f s.fst s.snd)

def benchDef_22 : (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) →
  Sigma (fun (a : A) => Sigma (fun (b : B a) => C a b)) → Sigma B :=
  fun A B C s => Sigma.mk s.fst s.snd.fst

-- def benchDef_23 : (A : Type 0) → (a : A) → (b : A) → Identity a b → Identity b a →
--   Sigma (fun (_ : Identity a a) => Identity b b) :=
--   fun A a b p q => match p, q with | Identity.refl _, Identity.refl _ => Sigma.mk (Identity.refl a) (Identity.refl b)

def benchDef_24 : (A : Type 0) → (B : Type 0) → (C : Type 0) → (D : Type 0) →
  (A → B) → (B → C) → (C → D) → A → D :=
  fun A B C D f g h a => h (g (f a))

def benchDef_25 : (A : Type 0) → (B : A → Type 0) →
  Sigma B → Sigma (fun (a : A) => Sigma (fun (b : B a) => Identity (Sigma.mk a b) (Sigma.mk a b))) :=
  fun A B s => Sigma.mk s.fst (Sigma.mk s.snd (Identity.refl (Sigma.mk s.fst s.snd)))

def benchDef_26 : (A : Type 1) → (B : Type 1) → (C : Type 1) →
  Sigma (fun (f : A → B) => B → C) → A → C :=
  fun A B C s a => s.snd (s.fst a)

-- def benchDef_27 : (A : Type 0) → (a : A) → (b : A) → (c : A) → (d : A) →
--   Identity a b → Identity b c → Identity c d → Identity a d :=
--   fun A a b c d p q r =>
--     match p, q, r with | Identity.refl _, Identity.refl _, Identity.refl _ => Identity.refl a

-- def benchDef_28 : (A : Type 0) → (B : Type 0) → (f : A → B) → (g : A → B) →
--   ((a : A) → Identity (f a) (g a)) → (a : A) → Identity (g a) (g a) :=
--   fun A B f g h a => match h a with | Identity.refl _ => Identity.refl (g a)

def benchDef_29 : Sigma (fun (A : Type 1) => Sigma (fun (B : Type 1) => (A → B) → A → B)) :=
  Sigma.mk (Type 0) (Sigma.mk (Type 0) (fun f a => f a))

def benchDef_30 : (A : Type 0) → (B : A → Type 0) → (C : A → Type 0) →
  ((a : A) → B a → C a) → ((a : A) → B a) → (a : A) → C a :=
  fun A B C f g a => f a (g a)

-- def benchDef_31 : (A : Type 0) → (P : A → Type 0) →
--   Sigma (fun (a : A) => P a → P a) → Sigma P → Sigma P :=
--   fun A P s t => if t.fst = s.fst then Sigma.mk t.fst (s.snd t.snd) else t

def benchDef_32 : (A : Type 1) → (B : A → Type 1) → (C : A → Type 1) →
  ((a : A) → B a) → ((a : A) → C a) → (a : A) → Sigma (fun (_ : B a) => C a) :=
  fun A B C f g a => Sigma.mk (f a) (g a)

def benchDef_33 : (A : Type 0) → (B : Type 0) → (f : A → B) →
  Sigma (fun (a : A) => Sigma (fun (b : B) => Identity (f a) b)) → B :=
  fun A B f s => s.snd.fst

def benchDef_34 : (A : Type 0) → (a : A) → (b : A) → (p : Identity a b) → (q : Identity a b) →
  Sigma (fun (_ : Identity a b) => Identity a a) :=
  fun A a b p q => Sigma.mk p (match p with | Identity.refl _ => Identity.refl a)

def benchDef_35 : (A : Type 0) → (B : Type 0) → (C : Type 0) → (D : Type 0) → (E : Type 0) →
  (A → B) → (B → C) → (C → D) → (D → E) → A → E :=
  fun A B C D E f g h i a => i (h (g (f a)))

def benchDef_36 : (A : Type 1) → (B : A → Type 1) → (C : (a : A) → B a → Type 1) →
  Sigma (fun (a : A) => Sigma (fun (b : B a) => C a b)) → Sigma B :=
  fun A B C s => Sigma.mk s.fst s.snd.fst

-- def benchDef_37 : (A : Type 0) → (B : A → Type 0) → (C : A → Type 0) →
--   Sigma B → Sigma C → Sigma (fun (a : A) => Sigma (fun (_ : B a) => C a)) :=
--   fun A B C sb sc => Sigma.mk sb.fst (Sigma.mk sb.snd sc.snd)

def benchDef_38 : (A : Type 0) → (f : A → A) → (a : A) →
  Sigma (fun (b : A) => Identity (f (f a)) (f b)) :=
  fun A f a => Sigma.mk (f a) (Identity.refl (f (f a)))

def benchDef_39 : (A : Type 0) → (B : Type 0) → (C : Type 0) →
  ((A → B) → C) → Sigma (fun (_ : A) => B) → C :=
  fun A B C f s => f (fun _ => s.snd)

def benchDef_40 : (A : Type 1) → (B : A → Type 1) → (C : A → Type 1) → (D : A → Type 1) →
  ((a : A) → B a → C a) → ((a : A) → C a → D a) → (a : A) → B a → D a :=
  fun A B C D f g a b => g a (f a b)

-- def benchDef_41 : (A : Type 0) → (a : A) → (b : A) → (c : A) →
--   Identity a b → Identity a c → Sigma (fun (p : Identity b c) => Identity a a) :=
--   fun A a b c p q => match p, q with
--     | Identity.refl _, Identity.refl _ => Sigma.mk (Identity.refl b) (Identity.refl a)

-- def benchDef_42 : (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) →
--   ((a : A) → (b : B a) → C a b) →
--   Sigma (fun (a : A) => Sigma (B a)) → Sigma (fun (s : Sigma B) => C s.fst s.snd) :=
--   fun A B C f s => Sigma.mk (Sigma.mk s.fst s.snd.fst) (f s.fst s.snd.fst)

def benchDef_43 : (A : Type 0) → (B : Type 0) → (f : A → B) → (g : B → A) →
  (a : A) → (b : B) → Identity (f (g b)) (f (g b)) :=
  fun A B f g a b => Identity.refl (f (g b))

def benchDef_44 : (A : Type 0) → (P : A → Type 0) → (Q : A → Type 0) → (R : A → Type 0) →
  ((a : A) → P a → Q a) → ((a : A) → Q a → R a) → (a : A) → P a → R a :=
  fun A P Q R f g a p => g a (f a p)

def benchDef_45 : (A : Type 1) → (B : Type 1) → (C : Type 1) → (D : Type 1) →
  Sigma (fun (f : A → B) => Sigma (fun (g : B → C) => C → D)) → A → D :=
  fun A B C D s a => s.snd.snd (s.snd.fst (s.fst a))

def benchDef_46 : (A : Type 0) → (B : A → Type 0) →
  ((a : A) → B a) → (a : A) → Sigma (fun (b : B a) => Identity b b) :=
  fun A B f a => Sigma.mk (f a) (Identity.refl (f a))

def benchDef_47 : (A : Type 0) → (a : A) → (b : A) → (c : A) → (d : A) → (e : A) →
  Identity a b → Identity b c → Identity c d → Identity d e → Identity a e :=
  fun A a b c d e p q r s =>
    match p, q, r, s with
    | Identity.refl _, Identity.refl _, Identity.refl _, Identity.refl _ => Identity.refl a

-- def benchDef_48 : (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) →
--   (D : (a : A) → (b : B a) → C a b → Type 0) →
--   Sigma (fun (a : A) => Sigma (fun (b : B a) => Sigma (fun (c : C a b) => D a b c))) →
--   Sigma (fun (a : A) => Sigma (B a)) :=
--   fun A B C D s => Sigma.mk s.fst (Sigma.mk s.snd.fst s.snd.fst)

def benchDef_49 : (A : Type 1) → (B : A → Type 1) → (C : A → Type 1) →
  Sigma (fun (f : (a : A) → B a → C a) => Sigma (fun (a : A) => B a)) →
  Sigma (fun (a : A) => C a) :=
  fun A B C s => Sigma.mk s.snd.fst (s.fst s.snd.fst s.snd.snd)

def benchDef_50 : (A : Type 0) → (B : Type 0) → (f : A → B) → (g : B → A) →
  ((a : A) → Identity (g (f a)) a) → ((b : B) → Identity (f (g b)) b) →
  (a : A) → (b : B) → Sigma (fun (_ : Identity (g (f a)) a) => Identity (f (g b)) b) :=
  fun A B f g h k a b => Sigma.mk (h a) (k b)

def benchDef_51 : (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) →
  ((a : A) → Sigma (fun (b : B a) => C a b)) →
  Sigma (fun (f : (a : A) → B a) => (a : A) → C a (f a)) :=
  fun A B C f => Sigma.mk (fun a => (f a).fst) (fun a => (f a).snd)

def benchDef_52 : (A : Type 1) → (B : Type 1) → (C : Type 1) → (D : Type 1) → (E : Type 1) →
  (f : A → B) → (g : B → C) → (h : C → D) → (i : D → E) → (j : E → A) →
  (a : A) → Identity (j (i (h (g (f a))))) (j (i (h (g (f a))))) :=
  fun A B C D E f g h i j a => Identity.refl (j (i (h (g (f a)))))

-- def benchDef_53 : (A : Type 0) → (B : A → Type 0) → (C : A → Type 0) →
--   Sigma (fun (a : A) => (B a → C a) → C a) → ((a : A) → B a) → Sigma C :=
--   fun A B C s f => Sigma.mk s.fst (s.snd (f s.fst))

def benchDef_54 : (A : Type 0) → (P : A → Type 0) → (Q : (a : A) → P a → Type 0) →
  Sigma (fun (a : A) => Sigma (fun (p : P a) => Q a p)) →
  Sigma (fun (s : Sigma P) => Q s.fst s.snd) :=
  fun A P Q s => Sigma.mk (Sigma.mk s.fst s.snd.fst) s.snd.snd

def benchDef_55 : (A : Type 0) → (B : Type 0) → (C : Type 0) →
  (f : A → B → C) → (a1 : A) → (a2 : A) → (b : B) →
  Identity a1 a2 → Identity (f a1 b) (f a2 b) :=
  fun A B C f a1 a2 b p => match p with | Identity.refl _ => Identity.refl (f a1 b)

def benchDef_56 : (A : Type 0) → (B : A → Type 0) → (C : (a : A) → B a → Type 0) →
  (D : (a : A) → B a → Type 0) →
  ((a : A) → (b : B a) → C a b → D a b) →
  Sigma (fun (a : A) => Sigma (fun (b : B a) => C a b)) →
  Sigma (fun (a : A) => Sigma (fun (b : B a) => D a b)) :=
  fun A B C D f s => Sigma.mk s.fst (Sigma.mk s.snd.fst (f s.fst s.snd.fst s.snd.snd))

def benchDef_57 : (A : Type 1) → (B : A → Type 1) → (C : A → Type 1) → (D : A → Type 1) →
  ((a : A) → B a → C a → D a) →
  Sigma (fun (a : A) => Sigma (fun (_ : B a) => C a)) → Sigma (fun (a : A) => D a) :=
  fun A B C D f s => Sigma.mk s.fst (f s.fst s.snd.fst s.snd.snd)

def benchDef_58 : (A : Type 0) → (f : A → A) → (g : A → A) →
  ((a : A) → Identity (f a) (g a)) →
  (a : A) → Sigma (fun (b : A) => Sigma (fun (_ : Identity (f a) b) => Identity b (g a))) :=
  fun A f g h a => Sigma.mk (g a) (Sigma.mk (h a) (Identity.refl (g a)))

def benchDef_59 : (A : Type 0) → (B : Type 0) → (C : Type 0) → (D : Type 0) →
  (E : Type 0) → (F : Type 0) →
  (A → B) → (B → C) → (C → D) → (D → E) → (E → F) → A → F :=
  fun A B C D E F f g h i j a => j (i (h (g (f a))))

end sample4

namespace sample5

def benchDef_2 : Type -> Type := fun A => A
def benchDef_3 : Identity (Type 1) (Type 1) := Identity.refl (Type 1)
def benchDef_4 : (A : Type) → Identity A A := fun A => Identity.refl A
def benchDef_5 : (A : Type) → (a : A) → Identity a a := fun _ a => Identity.refl a
def benchDef_6 : Type 1 := Sigma (fun (_ : Type) => Type)
def benchDef_7 : Sigma (fun (A : Type 1) => A → A) := Sigma.mk Type (fun A => A)
def benchDef_8 : (A : Type) → (B : Type) → Identity A B → Identity A B := fun A _ p => p
def benchDef_9 : (p : Sigma (fun (A : Type) => A)) → Identity p.fst p.fst := fun p => Identity.refl p.fst

end sample5

namespace sample6

def benchDef_10 : (A B C : Type) -> (A -> B) -> (B -> C) -> A -> C := fun _ _ _ f g x => g (f x)
def benchDef_11 : (A B : Type) -> A -> B -> A := fun _ _ a _ => a
def benchDef_12 : Type 1 := Sigma (fun (A : Type) => A -> A)
def benchDef_13 : Sigma (fun (A : Type) => A) -> Type := fun p => p.fst
def benchDef_14 : (A : Type) -> (a : A) -> Identity (Identity.refl a) (Identity.refl a) := fun _ a => Identity.refl (Identity.refl a)
def benchDef_15 : (A : Type) -> (B : Type) -> (A -> B) -> A -> B := fun _ _ f a => f a
def benchDef_16 : Type 2 := Sigma (fun (_ : Type 1) => Type 1)
-- def benchDef_17 : Sigma (fun (F : Type 1 -> Type 1) => F Type) := Sigma.mk (fun A => A) Type
def benchDef_18 : (A : Type) -> Identity (fun (x : A) => x) (fun y => y) := fun A => Identity.refl (fun x => x)
def benchDef_19 : (A : Type) -> (B : A -> Type) -> ((x : A) -> B x) -> (y : A) -> B y := fun _ _ f y => f y
def benchDef_20 : (A : Type) -> (p : Identity A A) -> Identity p p := fun _ p => Identity.refl p
def benchDef_21 : Type 1 := (A : Type) -> Sigma (fun (B : Type) => A -> B)
def benchDef_22 : (A : Type) -> Sigma (fun (B : Type) => A -> B) := fun A => Sigma.mk A (fun a => a)
-- def benchDef_23 : Sigma (fun (A : Type) => Sigma (fun (_ : Type) => A)) -> Type := fun p => p.snd.snd
def benchDef_24 : (A : Type) -> (B : Type) -> (f : A -> B) -> Sigma (fun (_ : Type) => Sigma (fun (_ : Type) => A -> B)) := fun A B f => Sigma.mk A (Sigma.mk B f)
def benchDef_25 : (A : Type) -> (a : A) -> (p : Identity a a) -> Sigma (fun (x : A) => Identity x x) := fun _ a p => Sigma.mk a p
def benchDef_26 : (A : Type) -> (B : A -> Type) -> Sigma (fun (a : A) => B a) -> A := fun _ _ p => p.fst
def benchDef_27 : (A : Type) -> (B : A -> Type) -> (p : Sigma (fun (a : A) => B a)) -> B p.fst := fun _ _ p => p.snd
-- def benchDef_28 : (A : Type) -> (a : A) -> Identity (Sigma.mk A a) (Sigma.mk A a) := fun A a => Identity.refl (Sigma.mk A a)
def benchDef_29 : (p : Sigma (fun (A : Type) => A)) -> Identity p p := fun p => Identity.refl p
def benchDef_30 : (F : Type -> Type) -> (A : Type) -> F A -> F A := fun _ _ fa => fa
def benchDef_31 : (A : Type) -> A -> Sigma (fun (a : A) => Identity a a) := fun A a => Sigma.mk a (Identity.refl a)
-- def benchDef_32 : (A B : Type) -> Identity A B -> Identity (Type -> A) (Type -> B) := fun A B p => Identity.refl (fun (_ : Type) => A)
-- def benchDef_33 : (A : Type) -> (a b : A) -> Identity a b -> Identity b a := fun _ _ _ p => p

def benchDef_34 : (A B C : Type) -> (A -> B -> C) -> B -> A -> C := fun _ _ _ f b a => f a b

def benchDef_35 : (A : Type) -> (f : A -> A) -> Sigma (fun (g : A -> A) => Identity f g) := fun A f => Sigma.mk f (Identity.refl f)

def benchDef_36 : (A : Type) -> A -> (A -> A) := fun A _ => (fun x => x)

def benchDef_37 : Identity (Sigma (fun (A : Type) => A)) (Sigma (fun (B : Type) => B)) := Identity.refl (Sigma (fun (A : Type) => A))

-- def benchDef_38 : Type 0 -> Type 1 := fun A => A -> A

def benchDef_39 : (A : Type) -> (p : Identity A A) -> Sigma (fun (T : Type) => Identity T T) := fun A p => Sigma.mk A p

def benchDef_40 : (A B : Type) -> (f : A -> B) -> Identity f f := fun _ _ f => Identity.refl f

-- def benchDef_41 : (A : Type) -> (B : Type) -> Type 1 := fun A B => (A -> B) -> A -> B

def benchDef_42 : (A : Type) -> (a : A) -> Sigma (fun (_ : Type) => A) := fun A a => Sigma.mk A a

def benchDef_43 : ((A : Type 2) -> A -> A) -> Type 1 := fun f => f (Type 1) Type

def benchDef_44 : Type 1 -> Type 1 := fun T => T

-- def benchDef_45 : (A : Type) -> (a : A) -> Identity (Sigma.fst (Sigma.mk A a)) A := Identity.refl A

def benchDef_46 : (A : Type) -> (a : A) -> Identity ((fun x => x) a) a := fun _ a => Identity.refl a

def benchDef_47 : (A : Type) -> (B : A -> Type) -> (a : A) -> (b : B a) -> Sigma (fun x => B x) := fun A B a b => Sigma.mk a b

def benchDef_48 : (A : Type) -> (B : A -> Type) -> (f : (a : A) -> B a) -> (a : A) -> Identity (f a) (f a) := fun _ _ f a => Identity.refl (f a)

def benchDef_49 : (A : Type) -> (a b : A) -> (p : Identity a b) -> Sigma (fun (x : A) => Identity x b) := fun _ a _ p => Sigma.mk a p

def benchDef_50 : Identity ((A : Type) -> A -> A) ((B : Type) -> B -> B) := Identity.refl ((A : Type) -> A -> A)

-- def benchDef_51 : (A : Type) -> (f : A -> A) -> (a : A) -> Identity (f a) (f a) := fun _ _ a => Identity.refl a

def benchDef_52 : (A : Type) -> (B : Type) -> Sigma (fun (_ : A) => B) -> A := fun _ _ p => p.fst

def benchDef_53 : (p : Sigma (fun (A : Type) => A -> A)) -> p.fst -> p.fst := fun p => p.snd

def benchDef_54 : (A : Type) -> ((A -> A) -> (A -> A)) -> (A -> A) := fun A f => f (fun x => x)

def benchDef_55 : (A : Type) -> (a : A) -> Sigma (fun (f : A -> A) => Identity (f a) a) := fun A a => Sigma.mk (fun x => x) (Identity.refl a)

-- def benchDef_56 : (A : Type) -> (B : Type) -> (C : Type) -> (f : A -> B) -> (g : B -> C) -> Identity (fun x => g (f x)) (fun x => g (f x)) := fun _ _ _ _ _ => Identity.refl (fun x => x)

def benchDef_57 : (A : Type) -> (B : A -> Type) -> (p : Sigma (fun a => B a)) -> Sigma (fun a => B a) := fun _ _ p => Sigma.mk p.fst p.snd

-- def benchDef_58 : (A : Type) -> (f g : A -> A) -> Identity f g -> Identity g f := fun _ _ _ p => p

def benchDef_59 : (p : Sigma (fun (A : Type) => Sigma (fun (B : Type) => A -> B))) -> p.fst -> p.snd.fst := fun p x => p.snd.snd x

end sample6
