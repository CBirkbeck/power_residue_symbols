import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Group.Commute.Units

open scoped NumberField BigOperators
open scoped Classical

section Preliminaries

variable {R S : Type*} [instR : CommRing R] [instS : CommRing S]

-- definitions relative to primitive roots

def fullRoots (n : ℕ+) (R : Type*) [CommRing R] : Prop :=
  ∃ (a : R), IsPrimitiveRoot a n

def nice (n : ℕ+) (f : R →+*S) : Prop :=
  ∀ (a : R), IsPrimitiveRoot a n → IsPrimitiveRoot (f a) n

lemma toFull {n : ℕ+} (f : R →+* S) (hR : fullRoots n R) (hf : nice n f) :
  fullRoots n S := by
  rcases hR with ⟨ u, hu⟩
  use (f u)
  exact hf u hu

lemma isNice {n : ℕ+} (f : R →+* S) [IsDomain R] [IsDomain S] (hn : (n : S) ≠ 0) : nice n f := by
  haveI neZero : NeZero (n : S) := by
    rw [neZero_iff]
    exact hn
  intro u hu
  have rootR := IsPrimitiveRoot.isRoot_cyclotomic n.pos hu
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have rootS := @Polynomial.IsRoot.map R S _ _ f u _ rootR
  simp only [Polynomial.IsRoot.definition, Polynomial.map_cyclotomic] at *
  exact rootS


-- unit, nonunit, coercion

noncomputable def unit_from_primitive {n : ℕ+} {u : R} (hu : IsPrimitiveRoot u n) : Rˣ :=
  IsUnit.unit (IsPrimitiveRoot.isUnit hu n.2)

/-
lemma prim_is_prim {n : ℕ+} {u : Rˣ} (hu : IsPrimitiveRoot u n) :
  IsPrimitiveRoot (u : R) n := by sorry
-/

def nth_root_from_primitive {n : ℕ+} {u : R} (hu : IsPrimitiveRoot u n) :
  rootsOfUnity n R := IsPrimitiveRoot.toRootsOfUnity hu

-- cardinality

-- rootsOfUnity.fintype
-- card.rootsOfUnity
-- IsPrimitiveRoot.eq_orderOf
-- IsPrimitiveRoot.injOn_pow_mul

noncomputable instance finn  (R : Type*)  (n : ℕ+)  [CommRing R]  [IsDomain R] :
Fintype ↥(rootsOfUnity n R) := rootsOfUnity.fintype R n

#check finn

lemma cardFull (n : ℕ+) {R : Type*} [CommRing R] [IsDomain R] (hn : fullRoots n R) :
  Fintype.card ↥(rootsOfUnity n R) = n.val := by sorry

-- map from roots of unity

def nth_root_map (n : ℕ+) (f : R →+* S) :
  rootsOfUnity n R →* rootsOfUnity n S :=
  restrictRootsOfUnity (RingHom.toMonoidHom f) n

-- properties of this map

lemma nth_root_map_surj (n : ℕ+) (f : R →+* S) [IsDomain S]
  (hf : nice n f) (hR : fullRoots n R) :
  Function.Surjective (nth_root_map n f) := by
    rcases hR with ⟨ u, hu⟩
    have prim : IsPrimitiveRoot (f u) n := by
      exact hf u hu
    have prim' : IsPrimitiveRoot (unit_from_primitive prim) n := by
      rw [←IsPrimitiveRoot.coe_units_iff]
      sorry
    intro a
    have : (a:Sˣ) ∈ Subgroup.zpowers (unit_from_primitive prim) := by
      have powS := @IsPrimitiveRoot.zpowers_eq S instS _ n (unit_from_primitive prim) prim'
      have a_root : (a:Sˣ) ∈ rootsOfUnity n S := by
        sorry
      rw [powS]
      sorry
    rw [Subgroup.mem_zpowers_iff] at this
    rcases this with ⟨i, hi⟩
    use (nth_root_from_primitive hu)^i
    sorry

lemma nth_root_map_bij (n : ℕ+) (f : R →+* S) [IsDomain R] [IsDomain S]
    (hR : fullRoots n R) (hf : nice n f) :
    Function.Bijective (nth_root_map n f) := by
    have hS := toFull f hR hf
    have surj := nth_root_map_surj n f hf hR
    -- use cardinality
    sorry

noncomputable def bij_nth_roots_gen (n : ℕ+) (f : R →+* S) [IsDomain R][IsDomain S]
  (hR : fullRoots n R) (hf : nice n f) :
  (rootsOfUnity n R) ≃ (rootsOfUnity n S) :=
    Equiv.ofBijective (nth_root_map n f) (nth_root_map_bij n f hR hf)


-- def coe_nth (n : ℕ+) (a : rootsOfUniIty n R) : Rˣ := sorry

/-
lemma nth_power (n : ℕ+) (a : rootsOfUnity n R) : (coe_nth n a)^n.val = 1 := by
  sorry

lemma nth_root_image (n : ℕ+) (f : R →+* S) (a : R) (ha : a^n.val = 1) :
  (f a) ^ n.val = 1 := by sorry
-/

  /-
  rootsOfUnity.mkOfPowEq (f (coe_nth n a))
  (nth_root_image n f (coe_nth n a) (nth_power n a))



lemma root_is_unit
{R : Type*} [CommRing R] (a : R) (k : ℕ+) (ha : a^(k : ℕ) = 1) : IsUnit a := by
  rw [← isUnit_pow_iff (n := k)]
  simp only [ha, isUnit_one,ne_eq, PNat.ne_zero, not_false_eq_true]

lemma pow1 {R : Type*} [CommRing R] [IsDomain R] (k : ℕ+) (a : Rˣ) (u : Rˣ)
  (hu : IsPrimitiveRoot u k) (ha : a^k.val = 1) :
   ∃ (i : ℤ), u^i = a := by
  have : a ∈ Subgroup.zpowers u := by
    have pow_u := IsPrimitiveRoot.zpowers_eq hu
    have a_root : a ∈ rootsOfUnity k R := by
      rw [← mem_rootsOfUnity] at ha
      exact ha
    rw [pow_u]
    assumption
  rw [Subgroup.mem_zpowers_iff] at this
  rcases this with ⟨ i, hi⟩
  use i

lemma pow2 {R : Type*} [CommRing R] [IsDomain R] (k : ℕ+)  (a : R) (u : Rˣ)
  (hu : IsPrimitiveRoot u k) (ha : a^k.val = 1) :
  ∃ (i : ℤ), ↑(u^i)  = a := by
  have a_unit := root_is_unit a k  ha
  have ha' : (IsUnit.unit a_unit)^k.val = 1 := by aesop
  rcases pow1 k (IsUnit.unit a_unit) u hu ha' with ⟨i, hi⟩
  use i
  rw_mod_cast [hi]
  simp only [IsUnit.unit_spec]

  -/



end Preliminaries
