/-
Group Theory in Lean

Produced while reading through:

A. Zipperer "A formalization of elementary group theory
in the proof assistant Lean"

Notation used here:

- `f : α → β` is a function

- `s : set α` and `s₁ s₂ : set α` are subsets of `α`

- `preimage f t : set α` : the preimage f⁻¹(t)
-/
-- lets hold everything in our namespace to deconflict with defaults
namespace mygroup

-- definition of a set in lean. set X is the term X → Prop and has type Type
-- definition set' := λ (A : Type), A → Prop
-- equivalent syntax
definition set' (A : Type) := A → Prop

-- add membership notation (A → Prop)(a) membership hypothesis prop
notation x ∈ S := S x


-- this is one way to define set intersection and union. Using squiggly braces, we do not
-- need to pass the argument the type of sets.
-- definition intersection {A : Type} (S : set A) (T: set A) : set A := λ x, x ∈ S ∧ x ∈ T
-- definition union {A : Type} (S : set A) (T: set A) : set A := λ x, x ∈ S ∨ x ∈ T

-- this is a better way to write the above definitions. Using sections, we can simulatneously
-- represent the type in the background and achieve the previous definitions.
section
  variable {A : Type}

  -- this is using the λ-abstract
  -- definition intersection (S : set A) (T : set A) : set A :=
  --  λ (x : A), x ∈ S ∧ x ∈ T

  -- definition union (S : set A) (T : set A) : set A :=
  --  λ (x : A), x ∈ S ∨ x ∈ T

  -- this is using set builder notation
  definition intersection (S : set A) (T : set A) : set A :=
    {a : A | a ∈ S ∧ a ∈ T}

  definition union (S : set A) (T : set A) : set A :=
    {a : A | a ∈ S ∨ a ∈ T}

  definition subset (S : set A) (T : set A) : Prop :=
    ∀ (a : A), a ∈ S → a ∈ T

  infix ` ∩ `:50 := intersection
  infix ` ∪ `:50 := union
  -- infix ` ⊆ `:50 := subset

  -- show identity bewteen (x ∈ (S₁ ∩ S₂)) and ((x ∈ S₁) ∧ (x ∈ S₂)) by reducing them to a common
  -- term 
  example {X : Type} (S₁ : set X) (S₂ : set X) (x : X) : (x ∈ (S₁ ∩ S₂)) = ((x ∈ S₁) ∧ (x ∈ S₂)) := 
  begin
    refl,
  end

  -- prove that is A ⊆ B, and B ⊆ C, then A ⊆ C
  example {X : Type} (A : set X) (B : set X) (C : set X) (HAB : A ⊆ B) 
    (HBC : B ⊆ C) : A ⊆ C :=
  begin
    intros x Hx,
    apply HBC,
    apply HAB,
    apply Hx,
  end
end


section
  variables {A B : Type}

  definition image (f : A → B) (S : set A) : set B :=
    {y : B | ∃ x : A, x ∈ S ∧ f x = y}

  definition preimage (f : A → B) (T : set B) : set A :=
    {x : A | f x ∈ T}

  definition injective (f : A → B) : Prop :=
    ∀ x y, f x = f y → x = y

  definition inj_on (f : A → B) (S : set A) : Prop  :=
    ∀ x y, x ∈ S → y ∈ S → f x = f y → x = y

  definition surjective (f : A → B) : Prop :=
    ∀ x, ∃ y, f x = y

  definition surj_on (f : A → B) (S : set A) (T : set B) : Prop :=
    ∀ (y : B), (y ∈ T → ∃ (x : A), (x ∈ S ∧ f x = y))
end

definition unary_operation (A : Type) := A → A 
definition binary_operation (A : Type) := A → A → A
-- definition is_commutative (A : Type) (op : A → A → A) := 
--  ∀ x y, op x y = op y x
section
  variable {A : Type}

  definition is_distributive (f : A → A) (op : A → A → A) : Prop :=
    ∀ x y, f (op x y) = op (f x) (f y)
end

-- object has multiplication
class has_mul (A : Type) := (mul : A → A → A)
-- object has one
class has_one (A : Type) := (one : A)
-- object has an inverse
class has_inv (A : Type) := (inv : A → A)

class semigroup (A : Type) extends has_mul A :=
  (assoc : ∀ x y z, mul x (mul y z) = mul (mul x y) z)

class monoid (A : Type) extends semigroup A, has_one A :=
  (mul_one : ∀ x, mul x one = x)
  (one_mul : ∀ x, mul one x = x)

class group (A : Type) extends monoid A, has_inv A :=
  (mul_left_inv : ∀ x, mul (inv x) x = one)

infix * := has_mul.mul
postfix ⁻¹ := has_inv.inv
notation 1 := has_one.one

section
  variables {X : Type} [G : group X] (a : X) (b : X)

  #check a
  #check a⁻¹
  #check a * b
  #check (a * b⁻¹) * b = a
end

section
  variables {G : Type} [group G] (a b : G)
  example : (a * b⁻¹) * b = a :=
  calc (a * b⁻¹) * b = a * (b⁻¹ * b) : by rw semigroup.assoc
        ... = a * has_one.one : by rw group.mul_left_inv
        ... = a : by rw monoid.mul_one
end

section 
  variable {A : Type}

  class is_mul_closed [has_mul A] (S : set A) : Prop :=
    (mul_mem : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S)

  class is_inv_closed [has_inv A] (S : set A) : Prop :=
    (inv_mem : ∀ x, x ∈ S → x⁻¹ ∈ S)

  class is_one_closed [has_one A] (S : set A) : Prop :=
    (one_mem : has_one.one ∈ S)

  class is_subgroup [group A] (S : set A) extends is_mul_closed S, 
    is_inv_closed S, is_one_closed S

end

section 
  variables {X : Type}[has_mul X]

  definition lcoset (x : X) (S : set X):= image (has_mul.mul x) S
  definition rcoset (S : set X) (x : X) := image ((λ x y, has_mul.mul y x) x) S

  infix ` * `:55 := lcoset
  infix ` * `:55 := rcoset

  variables {A : Type} [has_mul A]

  definition normalizes (a : A) (S : set A) : Prop := a * S = S * a
  
  definition is_normal (S : set A) : Prop :=
    ∀ (a : A), normalizes a S

  definition normalizer (S : set A) : set A :=
    {a : A | normalizes a S}
end
end mygroup
