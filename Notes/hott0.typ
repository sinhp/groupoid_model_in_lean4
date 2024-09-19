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
