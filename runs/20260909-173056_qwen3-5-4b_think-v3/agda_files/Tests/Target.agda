module Tests.Target where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Tests.Util
open import Tests.Helpers
open import Tests.Context

addComm : (n m : Nat) → n + m ≡ m + n
-- Base case: 0 + m reduces to m, and m + 0 equals m by plusZeroRight. By commutativity of zero or just definition we have equality with RHS? Wait, goal is $m = m+0$. Uses Lemma `plusZeroRight` to show $m+0=m$, so $m=m$.
addComm zero m = sym (plusZeroRight m)
-- Inductive case: assume n + m = m + n. Then suc n + m reduces to suc (n + m), which by the hypothesis is suc (m + n). We need this equal to m + suc n? Wait, goal $suc\ n+m \equiv m+suc\ n$. By Lemma `addSucL` ($x+0$?) No.
-- Induction on first arg of LHS ($n$ in my case). Goal $(suc\ n)+m = suc(n+m)$.
addComm (suc n) m = trans (congSuc (addComm n m)) (sym (addSucL m n))
