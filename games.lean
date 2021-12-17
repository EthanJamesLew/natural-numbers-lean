--- Implement my own mynat from the built-in natural numbers
open nat

-- add zero is used in the game
theorem add_zero (m : nat) : m + 0 = m := rfl
theorem one_eq_succ_zero : 1 = succ 0 := rfl
lemma mul_zero (m : ℕ) : m * 0 = 0 := rfl

-- tutorial world
lemma example1 (x y z : ℕ) : x * y + z = x * y + z :=
begin
refl,
end

lemma example2 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin
rw h,
end

lemma example3 (a b : ℕ) (h : succ a = b) : succ(succ(a)) = succ(b) :=
begin
rw h,
end

-- addition world
lemma add_succ_zero (a : ℕ) : a + succ(0) = succ(a) :=
begin
rw add_succ,
rw add_zero,
end

lemma zero_add (n : ℕ) : 0 + n = n :=
begin
induction n with h hd,
rw add_zero,
rw add_succ,
rw hd,
end

lemma add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) :=
begin
induction c with h hd,
repeat {rw add_zero},
repeat {rw add_succ},
rw hd,
end

lemma succ_add' (a b : ℕ) : succ a + b = succ (a + b) :=
begin
induction b with h hd,
repeat {rw add_zero},
rw add_succ,
rw hd,
rw add_succ,
end

lemma add_comm (a b : ℕ) : a + b = b + a :=
begin
induction b with h hd,
rw add_zero,
rw zero_add,
rw add_succ,
rw hd,
rw succ_add',
end

theorem succ_eq_add_one' (n : ℕ) : succ n = n + 1 :=
begin
rw one_eq_succ_zero,
end

lemma add_right_comm (a b c : ℕ) : a + b + c = a + c + b :=
begin
induction a with h hd,
repeat {rw zero_add},
rw add_comm,
repeat {rw succ_add},
rw hd,
repeat {rw succ_add},
end

-- function world
example (P Q : Type) (p : P) (h : P → Q) : Q :=
begin
exact h(p),
end

example : ℕ → ℕ :=
begin
intro n,
exact n,
end

example (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
have q := h(p),
have t : T := j(q),
have u : U := l(t),
exact u,
end

example (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
have q := h(p),
have t : T := j(q),
have u : U := l(t),
exact u,
end

example (P Q : Type) : P → (Q → P) :=
begin
intros p q,
exact p,
end

example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
intros p q r,
exact p(r)(q(r)),
end

example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=
begin
intros p q r,
exact q(p(r)),
end

example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) :=
begin
intros p q r,
exact q(p(r)),
end

example (A B C D E F G H I J K L : Type)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L :=
begin
intro f,
apply f15,
apply f11,
apply f9,
apply f8,
apply f5,
apply f2,
apply f1,
exact f,
end

-- multiplication world
lemma zero_mul (m : ℕ) : 0 * m = 0 :=
begin
induction m with h hd,
rw mul_zero,
rw mul_succ,
rw add_zero,
rw hd,
end

lemma mul_one (m : ℕ) : m * 1 = m :=
begin
rw one_eq_succ_zero,
rw mul_succ,
rw mul_zero,
rw zero_add,
end

lemma one_mul (m : ℕ) : 1 * m = m :=
begin
induction m with h hd,
rw mul_zero,
rw mul_succ,
rw hd,
end

lemma mul_add (t a b : ℕ) : t * (a + b) = t * a + t * b :=
begin
induction b with h hd,
induction a with j jd,
induction t with k kd,
rw mul_zero,
rw add_zero,
rw mul_zero,
rw add_zero,
rw mul_zero,
rw add_zero,
rw add_succ,
rw mul_succ,
rw hd,
rw mul_succ,
rw add_assoc,
end

lemma mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) :=
begin
induction c with h hd,
rw mul_zero,
rw mul_zero,
rw mul_zero,
rw mul_succ,
rw mul_succ,
rw hd,
rw mul_add,
end

lemma succ_mul' (a b : ℕ) : succ a * b = a * b + b :=
begin
induction b with h hd,
simp,
refl,
rw mul_succ,
rw hd,
rw mul_succ,
rw succ_eq_add_one',
rw succ_eq_add_one',
simp,
end

lemma add_mul (a b t : ℕ) : (a + b) * t = a * t + b * t :=
begin
induction t with h hd,
rw mul_zero,
rw mul_zero,
refl,
rw mul_succ,
rw hd,
rw succ_eq_add_one,
rw mul_add,
rw mul_add,
rw mul_one,
rw mul_one,
simp,
end

lemma mul_comm (a b : ℕ) : a * b = b * a :=
begin
induction a with h hd,
rw mul_zero,
rw zero_mul,
rw succ_mul',
rw hd,
rw mul_succ,
end

lemma mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) :=
begin
induction c with h hd,
rw mul_zero,
rw mul_zero,
rw mul_zero,
rw mul_succ,
rw mul_add,
rw hd,
rw succ_eq_add_one,
rw mul_add,
rw mul_add,
rw mul_one,
rw mul_comm,
refl,
end
