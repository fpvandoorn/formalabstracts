import ..basic ring_theory.ideals .algebra2

universes u v w
variables {α : Type*} {β : Type*} [comm_ring α] [comm_ring β]

open set

namespace ideal

lemma is_maximal_of_field {I : ideal α}
  (h1 : has_inv I.quotient)
  (h2 : zero_ne_one_class I.quotient)
  (h3 : ∀{a : I.quotient}, a ≠ 0 → a * a⁻¹ = 1)
  (h4 : ∀{a : I.quotient}, a ≠ 0 → a⁻¹ * a = 1) : is_maximal I :=
omitted

protected def ker (f : α → β) [is_ring_hom f] : ideal α :=
linear_map.ker (alg_hom.of_ring_hom f).to_linear_map

instance (f : α → β) [is_ring_hom f] : is_ring_hom (range_factorization f) :=
begin
  constructor; intros; apply subtype.eq; simp [range_factorization],
  rw [is_ring_hom.map_one f], refl,
  rw [is_ring_hom.map_mul f], refl,
  rw [is_ring_hom.map_add f], refl
end

def quotient_ker_map (f : α → β) [is_ring_hom f] : (ideal.ker f).quotient → range f :=
λ x, x.lift _ (range_factorization f) sorry



end ideal