/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Conjecture 20.12
by G. M. Bergman

Let us say that a group G has the unique n-fold product property (u.-n-p.) if
for every n-tuple of finite nonempty subsets A_1, . . . , A_n ⊆ G there exists g ∈ G which
can be written in one and only one way as g = a1 · · · an with ai ∈ Ai. It is easy to
see that u.-n-p. implies u.-m-p. for n ⩾ m (since some of the Ai can be {1}).
Are the conditions u.-n-p. (n ⩾ 2) all equivalent to u.-2-p., the usual unique
product condition?

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
!-/

@[expose] public section

namespace Kourovka.«20.12»


/--
A group $G$ has the unique $n$-fold product property (u.-n-p.) if for every
$n$-tuple of finite nonempty subsets $A_1, ..., A_n ⊆ G$ there exists $g ∈ G$ which can be
written in precisely one way as $g = a_1 ... a_n$ with $a_i ∈ A_i$.
-/
def UniqueNFoldProd (G : Type*) [Group G] (n : ℕ) :  Prop :=
  ∀ (A : Fin n → Finset G), ((∀ i, (A i).Nonempty) → ∃ g : G,
    ∃! (a : (i : Fin n) → G), (∀ i, a i ∈ A i) ∧ g = Fin.prod a)

/--
It is easy to see, that u.-n-p. implies u.-m-p. for $n ≥ m$ (since some of the $A_i$
can be $\{1\}$).

Note: We started formalizing the proof, but didn't finish it, as after some hours (and ~30 lines)
we thought this is too much for project 1 and didn't continue.
The proof sketch goes as follows:
Let $n ≥ m$ and $G$ be u.-n-p. Now take $A_1, ... A_m ⊆ G$ to show u.-m-p.
Define $A_{m+1}, ..., A_n := \{1\}$ and apply u.-n-p. to get $g ∈ G$ with
$g = a_1, ..., a_n$ with $a_i ∈ A_i$. Since $A_i = \{1\}$ for $i > m$ this implies
$g = a_1, ..., a_m$, i.e. G is u.-m-p.
-/

@[category API, AMS 20]
lemma UniqueNFoldProd.mono (G : Type* ) [Group G] {n m : ℕ} (mn : m ≤ n) (h : UniqueNFoldProd G n):
    UniqueNFoldProd G m := by
  induction n, mn using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    refine ih fun A hA ↦ ?_
    obtain ⟨g, b, ⟨hb, hg⟩, huniq⟩ := h (Fin.cons {1} A) (Fin.cases (by simp) (by simpa))
    have hb0 : b 0 = 1 := by simpa using hb 0
    refine ⟨g, fun i ↦ b i.succ, ⟨fun i ↦ by simpa using hb i.succ, ?_⟩, ?_⟩
    · rw [hg, Fin.prod_succ, hb0, one_mul]
    · rintro a ⟨ha, rfl⟩
      have := huniq (Fin.cons 1 a) ⟨Fin.cases (by simp) (by simpa), by rw [Fin.prod_succ]; simp⟩
      ext i
      simpa using congrFun this i.succ

/--
Are the conditions u.-n-p. ($n ≥ 2$) all equivalent to u.-2-p., the usual unique
product condition?

Note: one implication follows from the lemma above, the other one is an open conjecture.
-/

@[category research open, question, AMS 20]
theorem kourovka_20_12 :
    ∀ (G : Type) [Group G], ∀ n ≥ 2, (UniqueNFoldProd G n ↔ UniqueNFoldProd G 2) := by
  sorry

end Kourovka.«20.12»
