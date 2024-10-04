#import "prooftree.typ": prooftree, axiom, rule
#import "prelude.typ": *

#show: template

#let box_size = 8em

We present #hott0 as an explicit substitution calculus.

== Raw syntax
#v(1em) // TODO why is the spacing so tight by default

$"(de Bruijn index)" i     &∈ ℕ \
"(type)"            A,B   ::=& U ∣ "El" t ∣ ∏_A B ∣ ∑_A B ∣ "Id"(u_0,u_1) ∣ A[σ] \
"(term)"            t,u   ::=& bold(v)_i ∣ Π_t u ∣ Σ_t u ∣ "I "_t (u_0, u_1) \
                          &     ∣ λ_A t ∣ t#sp u ∣ ⟨ t , u ⟩_B ∣ "fst" t ∣ "snd" t  \
                          &     ∣ "refl"_t ∣ "J"_A t ∣ t[σ] \
"(context)"         Θ,Δ,Γ ::=& · ∣ Γ.A \
"(substitution)"    σ,ρ   ::=& id_Γ ∣ σ ∘ ρ ∣ ↑_A ∣ σ.t$

== Inference rules

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($⊢ Γ "ctx"$)),
  $ prooftree(#rule($⊢ · "ctx"$, n: 0))

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #rule($⊢ Γ.A "ctx"$))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($σ : Δ ⟶ Γ$)),
  $ prooftree(
      #axiom($⊢ Γ "ctx"$),
      #rule($id_Γ : Γ ⟶ Γ$))

    prooftree(
      #axiom($ρ : Θ ⟶ Δ$),
      #axiom($σ : Δ ⟶ Γ$),
      #rule($σ∘ρ : Θ ⟶ Γ$, n: 2)) \ \

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #rule($↑_A : Γ.A ⟶ Γ$))

    prooftree(
      #axiom($σ : Δ ⟶ Γ$),
      #axiom($Δ ⊢ t : A[σ]$),
      #rule($σ.t : Δ ⟶ Γ.A$, n: 2))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($σ ≡ ρ : Δ ⟶ Γ$)),
  $ prooftree(
      #axiom($σ : Δ ⟶ Γ$),
      #axiom($Δ ⊢ t : A[σ]$),
      #rule($↑_A∘σ.t ≡ σ : Δ ⟶ Γ$, n: 2))

    \ \

    prooftree(
      #axiom($ρ : Θ ⟶ Δ$),
      #axiom($σ : Δ ⟶ Γ$),
      #axiom($Θ ⊢ t : A[σ∘ρ]$),
      #rule($(σ∘ρ).t ≡ ... : Θ ⟶ Γ$, n: 3))

    "(+ axioms of a category.)"
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ A "type"$)),
  $ prooftree(#rule($Γ ⊢ U "type"$, n: 0))

    prooftree(
      #axiom($Γ ⊢ t : U$),
      #rule($Γ ⊢ "El" t "type"$))

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #axiom($Γ.A ⊢ B "type"$),
      #rule($Γ ⊢ ∏_A B "type"$, n: 2))

   \ \

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #axiom($Γ.A ⊢ B "type"$),
      #rule($Γ ⊢ ∑_A B "type"$, n: 2))

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #axiom($Γ ⊢ u_0 : A$),
      #axiom($Γ ⊢ u_1 : A$),
      #rule($ Γ ⊢ "Id"(u_0,u_1) "type"$, n: 3))

   \ \

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #axiom($σ : Δ ⟶ Γ$),
      #rule($Δ ⊢ A[σ] "type"$, n: 2))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ A ≡ B "type"$)),
  $
    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ."El" t ⊢ u : U$),
      #rule($Γ ⊢ "El" (Π_t u) ≡ ∏_("El" t)"El" u "type"$, n: 2))

    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ."El" t ⊢ u : U$),
      #rule($Γ ⊢ "El" (Σ_t u) ≡ ∑_("El" t)"El" u "type"$, n: 2))

   \ \

    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ ⊢ u_0 : "El" t$),
      #axiom($Γ ⊢ u_1 : "El" t$),
      #rule($Γ ⊢ "El" ("I "_t (u_0, u_1)) ≡ "Id"(u_0, u_1)$, n: 3))

    "(+ substitution naturalities.)"
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ t : A$)),
  $
    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ."El" t ⊢ u : U$),
      #rule($Γ ⊢ Π_t u : U$, n: 2))

    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ."El" t ⊢ u : U$),
      #rule($Γ ⊢ Σ_t u : U$, n: 2))

    \ \

   prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ ⊢ u_0 : "El" t$),
      #axiom($Γ ⊢ u_1 : "El" t$),
      #rule($Γ ⊢ "I "_t (u_0, u_1) : U$, n: 3))

     \ \

    prooftree(
      #axiom($Γ.A ⊢ t : B$),
      #rule($Γ ⊢ λ_A t : ∏_A B$))

    prooftree(
      #axiom($Γ ⊢ t : ∏_A B$),
      #axiom($Γ ⊢ u : A$),
      #rule($Γ ⊢ t#sp u : B[id_Γ.u]$, n: 2))

    \ \

    prooftree(
      #axiom($Γ ⊢ t : A$),
      #axiom($Γ ⊢ u : B[id_Γ.t]$),
      #rule($Γ ⊢ ⟨ t , u ⟩_B : ∑_A B$, n: 2))

    prooftree(
      #axiom($Γ ⊢ t : ∑_A B$),
      #rule($Γ ⊢ "fst" t : A$))

    prooftree(
      #axiom($Γ ⊢ t : ∑_A B$),
      #rule($Γ ⊢ "snd" t : B[id_Γ."fst" t]$))

    \ \

    prooftree(
      #axiom($Γ ⊢ t : A$),
      #rule($Γ ⊢ "refl"_t : "Id"(t, t)$)
    )

    prooftree(
      #axiom($Γ.A.A[↑_A]."Id"(bold(v)_1, bold(v)_0) ⊢ B "type"$),
      #axiom($Γ.A ⊢ t : B[id_(Γ.A) . v_0 . "refl"_v_0]$),
      #rule($Γ.A.A[↑_A]."Id"(bold(v)_1, bold(v)_0) ⊢ J_B (t) : B$, n: 2)
    )

    \ \

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #rule($Γ.A ⊢ bold(v)_0 : A[↑_A]$))

    prooftree(
      #axiom($Γ ⊢ t : A$),
      #axiom($σ : Δ ⟶ Γ$),
      #rule($Δ ⊢ t[σ] : A[σ]$, n: 2))
    \ \
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ t ≡ u : A$)),
  $ "(TODO: standard)"
  $
))


== Nondepenent functions and binary products


  $
    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #axiom($Γ ⊢ B "type"$),
      #rule($Γ ⊢ A × B ≜ ∑_A B[↑_A]$, n: 2))

    #h(1cm)

    prooftree(
      #axiom($Γ ⊢ A "type"$),
      #axiom($Γ ⊢ B "type"$),
      #rule($Γ ⊢ A → B ≜ ∏_A B[↑_A]$, n: 2))
  $

  $
    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ ⊢ u : U$),
      #rule($Γ ⊢ t × u ≜ Σ_t u[↑_("El" t)]$, n: 2))

    #h(1cm)

    prooftree(
      #axiom($Γ ⊢ t : U$),
      #axiom($Γ ⊢ u : U$),
      #rule($Γ ⊢ t → u ≜ Π_t u[↑_("El" t)]$, n: 2))
  $

== Univalence

In the following we will use $[↑^?]$ to denote a series of weakening substitutions,
which will be clear from context.

Univalence will be a term of the (merely propositional) type
$ Γ.U.U[↑] ⊢ "IsBigEquiv"[id_( Γ.U.U[↑] ) . "IdToEquiv"] "type" $
Here $"IsBigEquiv"$ and its components $"BigLinv"$ and $"BigRinv"$ (defined later)
are shorthand for longer type expressions,
whereas "IdToEquiv" is a term expression.
In order to write the type expressions as shorthands internal to the type theory
it is necessary and sufficient to have a second,
larger universe containing $"U"$ as a term.

Supposing that $Γ ⊢ A "type"$ and $Γ ⊢ B "type"$ we define the shorthands

$ Γ.A → B ⊢
  "BigLinv"_(A,B) ≜ ∑_((B → A)[↑^?]) ∏_(A[↑^?])
  "Id"( bold(v_1)(bold(v_2) #sp bold(v_0)) , bold(v_0) ) $

$ Γ.A → B ⊢
  "BigRinv"_(A,B) ≜ ∑_((B → A)[↑^?]) ∏_(B[↑^?])
  "Id"( bold(v_2)(bold(v_1) #sp bold(v_0)) , bold(v_0) ) $

$ Γ.A → B ⊢ "IsBigEquiv"_(A,B) ≜ "BigLinv"_(A,B) × "BigRinv"_(A,B) $

We can verify that

$
  Γ.A → B ⊢ "BigLinv"_(A,B) "type"
  #h(1cm)
  Γ.A → B ⊢ "BigRinv"_(A,B) "type"
  #h(1cm)
  Γ.A → B ⊢ "IsBigEquiv"_(A,B) "type"
$

There are also versions of these bounded by the universe $"U"$.
// Supposing that we have two codes for small types
// $Γ ⊢ u_A : U$ and $Γ ⊢ u_B : U$

#let easy(x) = text(fill: blue, $#x$)

// $ Γ."El"(u_A → u_B) ⊢ "Linv" ≜ Σ_((u_B → u_A)[↑^?]) Π_(u_A [↑^?]) "I "_(u_A [↑^?])
//   ( bold(v_1)(bold(v_2) #sp bold(v_0)) , bold(v_0) ) : U[↑^?] $

$ Γ.U.U[↑]."El"(bold(v_0) → bold(v_1)) ⊢
  "Linv" ≜ Σ_(bold(v_1) → bold(v_2)) Π_(bold(v_3))
  "I "_(bold(v_4))( bold(v_1)(bold(v_2) #sp bold(v_0)) , bold(v_0) ) : U[↑^?] $
$ easy(Γ.a:U.b:U.f:"El"(a → b) ⊢
  "Linv" ≜ Σ_(g:"El" (b → a)) Π_(x: "El" a)
  "I "_a ( g(f #sp x) , x ) : U ) $

$ Γ.U.U[↑]."El"(bold(v_0) → bold(v_1)) ⊢
  "Rinv" ≜ Σ_(bold(v_1) → bold(v_2)) Π_(bold(v_3))
  "I "_(bold(v_4))( bold(v_1)(bold(v_2) #sp bold(v_0)) , bold(v_0) ) : U[↑^?] $
$ easy(Γ.a:U.b:U.f:"El"(a → b) ⊢
  "Rinv" ≜ Σ_(g:"El" (b → a)) Π_(x: "El" b) "I "_b ( f(g #sp x) , x ) : U) $

// $ Γ."El"(u_A → u_B) ⊢ "Rinv" ≜ Σ_((u_B → u_A)[↑^?]) Π_(u_B[↑^?])
//   "I "_(u_B) ( bold(v_2)(bold(v_1) #sp bold(v_0)) , bold(v_0) ) $

$ Γ.U.U[↑]."El"(bold(v_0) → bold(v_1)) ⊢ "IsEquiv" ≜ "Linv" × "Rinv" : U[↑^?] $

$ Γ.U.U[↑] ⊢ "Equiv" ≜ Σ_(bold(v_1) → bold(v_0)) "IsEquiv" : U[↑^?] $

When we define
$Γ.U.U[↑] ⊢ "IdToEquiv" : "Id"(bold(v_1), bold(v_0)) → "Equiv"$,
we see the necessesity of defining both big and small equivalences;
given $u_0 , u_1 : U$ we do not have $"Id"(u_0, u_1) : U$.

The underlying function in our equivalence transports along the given identity
$ Γ.U.U[↑]."Id"(bold(v_1) , bold(v_0)) ⊢ "IdToFun" ≜
  J_("El"(bold(v_2) → bold(v_1))) (λ_("El"bold(v_0)) v_0) : "El"(bold(v_2) → bold(v_1)) $

$ easy(Γ.a:U.b:U."Id"(a, b) ⊢ "IdToFun" ≜ J_("El"(a → b)) id_("El" a) : "El"(a → b)) $
// $ Γ.U.U[↑] ⊢ "IdToFun" ≜
//   λ_("Id"(bold(v_1) , bold(v_0)))
//   ( J_("El"(bold(v_2) → bold(v_1))) (λ_("El"bold(v_0)) v_0) ) :
//   "Id"(bold(v_1) , bold(v_0)) → "El"(bold(v_2) → bold(v_1)) $

// $ easy(Γ.a:U.b:U ⊢ "IdToFun" ≜
//   λ_("Id"(a, b)) ( J_("El"(a → b)) id_("El" a) ) : "El"(a → b)) $

Identity is symmetrical, which we use to construct the inverse in the equivalence.
$ Γ.A.A[↑]."Id"(bold(v_1) , bold(v_0)) ⊢
  "sym"_A ≜  J_("Id"(bold(v_1), bold(v_2))) "refl"_(bold(v_0)) : "Id"(bold(v_1), bold(v_2)) $

$ easy(Γ.x:A.y:A."Id"(x, y) ⊢ "sym"_A ≜ J_("Id"(y,x)) "refl"_x : "Id"(y,x)) $

The inverse of the equivalence
$ Γ.U.U[↑]."Id"(bold(v_1) , bold(v_0)) ⊢ "IdToInv" ≜
  "IdToFun"[id_Γ.bold(v_1).bold(v_2)."sym"_U] : "El"(bold(v_1) → bold(v_2)) $

$ easy(Γ.a:U.b:U."Id"(a, b) ⊢ "IdToInv" ≜ "IdToFun"[id_Γ.b.a."sym"_U] : "El"(b → a)) $

That it is a left inverse and a right inverse can be proven with path induction,
where the diagonal case is an equality that holds definitionally,
by the computation rule for $J$.
$ Γ.U.U[↑]."Id"(bold(v_1) , bold(v_0)) ⊢ "LinvIdToFun" ≜ ⟨ "IdToInv",
  J_("El"(Π_(bold(v_2)) "I "_(bold(v_3))( "IdToInv"[↑]("IdToFun"[↑] #sp bold(v_0)) , bold(v_0) )))
  (λ_("El" bold(v_0)) "refl"_(bold(v_0)))
  ⟩ $
$ : "Linv"[↑_("Id"(bold(v_1), bold(v_0))) . "IdToFun"[↑]]  $

$ Γ.U.U[↑]."Id"(bold(v_1) , bold(v_0)) ⊢ "RinvIdToFun" ≜ ⟨ "IdToInv",
  J_("El"(Π_(bold(v_1)) "I "_(bold(v_2))( "IdToInv"[↑]("IdToFun"[↑] #sp bold(v_0)) , bold(v_0) )))
  (λ_("El" bold(v_0)) "refl"_(bold(v_0)))
  ⟩ $
$ : "Rinv"[↑_("Id"(bold(v_1), bold(v_0))) . "IdToFun"[↑]]  $

Now we have all the components for defining $"IdToEquiv"$

$ Γ.U.U[↑]."Id"(bold(v_1) , bold(v_0)) ⊢ "IsEquivIdToFun" ≜ ⟨ "IdToFun",
  ⟨
  "LinvIdToFun",
  "RinvIdToFun"
  ⟩
  ⟩ $
$ : "IsEquiv"[↑_("Id"(bold(v_1), bold(v_0))) . "IdToFun"[↑]]  $


$ Γ.U.U[↑] ⊢ "IdToEquiv" ≜ λ_("Id"(bold(v_1), bold(v_0))) ⟨ "IdToFun" , "IsEquivIdToFun" ⟩ : "Id"(bold(v_1), bold(v_0)) → "Equiv" $

// $ easy(Γ.U.U[↑] ⊢ "IdToEquiv" ≜ λ_("Id"(bold(v_1), bold(v_0))) ⟨ "IdToFun" , "IsEquivIdToFun" ⟩ : "Id"(bold(v_1), bold(v_0)) → "Equiv") $

Finally, the univalence axiom states

$
  prooftree(
  #rule($Γ.U.U[↑] ⊢ "ua" : "IsBigEquiv"[id_( Γ.U.U[↑] ) . "IdToEquiv"]$, n: 0)
)

$

== Uniqueness of Identity Principle

In the groupoid model of HoTT,
we could take the universe $"U"$ to be all small discrete groupoids,
i.e. small sets.
In lean, these would satisfy the uniqueness of identity principle (UIP).

$
  prooftree(
  #axiom($Γ ⊢ u_A : U$),
  #axiom($Γ ⊢ t_0 : "El" u_A$),
  #axiom($Γ ⊢ t_1 : "El" u_A$),
  #axiom($Γ ⊢ p : "Id"(t_0,t_1)$),
  #axiom($Γ ⊢ q : "Id"(t_0,t_1)$),
  #rule($Γ ⊢ p ≡ q : "Id"(t_0,t_1)$,n:5)
)
$
