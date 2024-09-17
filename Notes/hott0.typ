#import "prooftree.typ": prooftree, axiom, rule
#import "prelude.typ": *

#show: template

#let box_size = 8em

We present #hott0 as an explicit substitution calculus.

== Raw syntax
#v(1em) // TODO why is the spacing so tight by default

$"(de Bruijn index)" i     &∈ ℕ \
"(type)"            A,B   &::= U ∣ "el" t ∣ ∏_A B ∣ A[σ] \
"(term)"            t,u   &::= bold(v)_i ∣ λ_A t ∣ t#sp u ∣ Π_t u ∣ t[σ] \
"(context)"         Θ,Δ,Γ &::= · ∣ Γ.A \
"(substitution)"    σ,ρ   &::= id_Γ ∣ σ ∘ ρ ∣ ↑_A ∣ σ.t$

== Inference rules

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($⊢ Γ "ctx"$)),
  $ prooftree(#rule($⊢ · "ctx"$, n: 0))

    prooftree(
      axiom(Γ ⊢ A "type"),
      rule(⊢ Γ.A "ctx"))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($σ : Δ ⟶ Γ$)),
  $ prooftree(
      axiom(⊢ Γ "ctx"),
      rule(id_Γ : Γ ⟶ Γ))

    prooftree(
      axiom(ρ : Θ ⟶ Δ),
      axiom(σ : Δ ⟶ Γ),
      #rule($σ∘ρ : Θ ⟶ Γ$, n: 2)) \ \

    prooftree(
      axiom(Γ ⊢ A "type"),
      rule(↑_A : Γ.A ⟶ Γ))

    prooftree(
      axiom(σ : Δ ⟶ Γ),
      axiom(Δ ⊢ t : A[σ]),
      #rule($σ.t : Δ ⟶ Γ.A$, n: 2))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($σ ≡ ρ : Δ ⟶ Γ$)),
  $ prooftree(
      axiom(σ : Δ ⟶ Γ),
      axiom(Δ ⊢ t : A[σ]),
      #rule($↑_A∘σ.t ≡ σ : Δ ⟶ Γ$, n: 2))

    \ \

    prooftree(
      axiom(ρ : Θ ⟶ Δ),
      axiom(σ : Δ ⟶ Γ),
      axiom(Θ ⊢ t : A[σ∘ρ]),
      #rule($(σ∘ρ).t ≡ ... : Θ ⟶ Γ$, n: 3))

    "(+ axioms of a category.)"
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ A "type"$)),
  $ prooftree(#rule($Γ ⊢ U "type"$, n: 0))

    prooftree(
      axiom(Γ ⊢ t : U),
      rule(Γ ⊢ "el" t "type"))

    prooftree(
      axiom(Γ ⊢ A "type"),
      axiom(Γ.A ⊢ B "type"),
      #rule($Γ ⊢ ∏_A B "type"$, n: 2))

   \ \

   prooftree(
      axiom(Γ ⊢ A "type"),
      axiom(σ : Δ ⟶ Γ),
      #rule($Δ ⊢ A[σ] "type"$, n: 2))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ A ≡ B "type"$)),
  $
    prooftree(
      axiom(Γ ⊢ t : U),
      rule(Γ ⊢ "el" (Π_t u) ≡ ∏_("el" t)"el" u "type"))

    "(+ substitution naturalities.)"
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ t : A$)),
  $ prooftree(
      axiom(Γ ⊢ A "type"),
      rule(Γ.A ⊢ bold(v)_0 : A[↑_A]))

    prooftree(
      axiom(Γ.A ⊢ t : B),
      rule(Γ ⊢ λ_A t : ∏_A B))

    prooftree(
      axiom(Γ ⊢ t : ∏_A B),
      axiom(Γ ⊢ u : A),
      #rule($Γ ⊢ t#sp u : B[id_Γ.u]$, n: 2))

    \ \

    prooftree(
      axiom(Γ ⊢ t : U),
      axiom(Γ."el" t ⊢ u : U),
      #rule($Γ ⊢ Π_t u : U$, n: 2))

    prooftree(
      axiom(Γ ⊢ t : A),
      axiom(σ : Δ ⟶ Γ),
      #rule($Δ ⊢ t[σ] : A[σ]$, n: 2))
  $
))

#figure(grid(
  columns: (box_size, 1fr),
  align(left, gbox($Γ ⊢ t ≡ u : A$)),
  $ "(TODO: standard)"
  $
))
