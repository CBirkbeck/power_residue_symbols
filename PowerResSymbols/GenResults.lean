import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Group.Commute.Units

open scoped Classical

section Preliminaries

variable {R S : Type*} [CommRing R] [CommRing S]

-- definitions relative to primitive roots

def fullRoots (n : ℕ+) (R : Type*) [CommRing R] : Prop :=
  ∃ (a : R), IsPrimitiveRoot a n

def nice (n : ℕ+) (f : R →+*S) : Prop :=
  ∀ (a : R), IsPrimitiveRoot a n → IsPrimitiveRoot (f a) n

-- various coercions

noncomputable def unit_from_primitive {n : ℕ+} {u : R} (hu : IsPrimitiveRoot u n) : Rˣ :=
  IsUnit.unit (IsPrimitiveRoot.isUnit hu n.2)

lemma prim_is_prim {n : ℕ+} {u : R} (hu : IsPrimitiveRoot u n) :
  IsPrimitiveRoot (unit_from_primitive hu) n :=
  IsPrimitiveRoot.isUnit_unit n.pos hu

def nth_root_from_primitive {n : ℕ+} {u : R} (hu : IsPrimitiveRoot u n) :
  rootsOfUnity n R := IsPrimitiveRoot.toRootsOfUnity hu

lemma is_nth_root {n : ℕ+} {u : R} (hu : IsPrimitiveRoot u n) :
  unit_from_primitive hu ∈ rootsOfUnity n R := by
  simp [unit_from_primitive]
  rw [← Units.eq_iff]
  simp
  exact hu.pow_eq_one



-- morphisms and primitive roots

lemma toFull {n : ℕ+} {f : R →+* S} (hR : fullRoots n R) (hf : nice n f) :
  fullRoots n S := by
  rcases hR with ⟨ u, hu⟩
  use (f u)
  exact hf u hu

lemma isNice {n : ℕ+} (f : R →+* S) [IsDomain R] [IsDomain S] (hn : (n : S) ≠ 0) : nice n f := by
  haveI instNeZero : NeZero (n : S) := by
    rw [neZero_iff]
    exact hn
  intro u hu
  have rootR := IsPrimitiveRoot.isRoot_cyclotomic n.pos hu
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have rootS := @Polynomial.IsRoot.map R S _ _ f u _ rootR
  simp only [Polynomial.IsRoot.definition, Polynomial.map_cyclotomic] at *
  exact rootS


-- cardinality

noncomputable instance (R : Type*)  (n : ℕ+)  [CommRing R]  [IsDomain R] :
Fintype ↥(rootsOfUnity n R) := rootsOfUnity.fintype R n



lemma cardFull (n : ℕ+) {R : Type*} [CommRing R] [IsDomain R] (hn : fullRoots n R) :
  Fintype.card ↥(rootsOfUnity n R) = n.val := by
    rcases hn with ⟨ u, hu⟩
    exact IsPrimitiveRoot.card_rootsOfUnity hu

-- map from roots of unity

def nth_root_map (n : ℕ+) (f : R →+* S) :
  rootsOfUnity n R →* rootsOfUnity n S :=
  restrictRootsOfUnity (RingHom.toMonoidHom f) n

-- properties of this map


lemma image_nth_root_map {n : ℕ+} {f : R →+* S} [IsDomain S]
  (hR : fullRoots n R) (hf : nice n f) :
  ∀ (a : Sˣ), a ∈ rootsOfUnity n S → ∃ (b : Rˣ), (Units.map f) b = a ∧ b ∈ rootsOfUnity n R := by
    intro a ha
    rcases hR with ⟨ u, hu⟩
    have prim : IsPrimitiveRoot (f u) n := by
      exact hf u hu
    have eq0 : Units.val ((Units.map f) (unit_from_primitive hu)) = ((unit_from_primitive prim):S) := by
      simp [unit_from_primitive]
    have eq1 : (Units.map f) (unit_from_primitive hu) = (unit_from_primitive prim) := by
      rw [← Units.eq_iff]
      exact eq0
    have prim' : IsPrimitiveRoot (unit_from_primitive prim) n := by
      exact prim_is_prim prim
    have pow_fu := IsPrimitiveRoot.zpowers_eq prim'
    rw [← pow_fu,← eq1] at ha
    have := @MonoidHom.map_zpowers Rˣ _ Sˣ _ (Units.map f) (unit_from_primitive hu)
    rw [← this] at ha
    simp at ha
    rcases ha with ⟨i, hi⟩
    simp at hi
    rw [← map_zpow]  at hi
    use (unit_from_primitive hu)^i,hi, Subgroup.zpow_mem (rootsOfUnity n R) (is_nth_root hu) i

lemma nth_root_map_surj {n : ℕ+} {f : R →+* S} [IsDomain S]
  (hR : fullRoots n R) (hf : nice n f):
  Function.Surjective (nth_root_map n f) := by
    intro a
    have ha := a.mem
    rcases (image_nth_root_map hR hf a ha) with ⟨ b,hba,hb⟩
    use ⟨ b,hb⟩
    simp only [nth_root_map]
    apply rootsOfUnity.coe_injective
    simp
    rw [← Units.eq_iff] at hba
    rw [← hba]
    rw [Units.coe_map]
    simp


lemma nth_root_map_bij {n : ℕ+} {f : R →+* S} [IsDomain R] [IsDomain S]
    (hR : fullRoots n R) (hf : nice n f) :
    Function.Bijective (nth_root_map n f) := by
    have surj := nth_root_map_surj hR hf
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    . exact surj
    have cardR := cardFull n hR
    have cardS := cardFull n (toFull hR hf)
    rw [cardR,cardS]

/- bijection between the sets of n-roots of unity -/
noncomputable def bij_nth_roots_gen {n : ℕ+} {f : R →+* S} [IsDomain R][IsDomain S]
  (hR : fullRoots n R) (hf : nice n f) :
  (rootsOfUnity n R) ≃* (rootsOfUnity n S) :=
    MulEquiv.ofBijective (nth_root_map n f) (nth_root_map_bij hR hf)


end Preliminaries

section FiniteRing

/- show that in a finite ring, if there are all n-th roots of unity then n
divides the cardinality of units ; and we can construct n-th roots of unity
by raising to the power card(units)/n -/

variable {R : Type*} [CommRing R] [Fintype R]
lemma div_n {n : ℕ+} (hR: fullRoots n R) : n.val ∣ Fintype.card Rˣ := by
  obtain ⟨ u, hu⟩ := hR
  have divide := orderOf_dvd_card (G := Rˣ)
        (x := unit_from_primitive hu)
  convert divide
  have := IsPrimitiveRoot.eq_orderOf hu
  simp [unit_from_primitive] at *
  rw [this,← orderOf_units,IsUnit.unit_spec]

lemma pow_n {n : ℕ+} (hdiv: n.val ∣ Fintype.card Rˣ) (x : Rˣ) : (x^((Fintype.card Rˣ)/n.val))^n.val = 1 := by
  obtain ⟨k,hk⟩ := hdiv
  rw [hk]
  simp
  have : (x^k)^n.val = x^(n.val*k) := by group
  rw [this,← hk]
  exact pow_card_eq_one

lemma root_n {n : ℕ+} (hdiv : n.val ∣ Fintype.card Rˣ) : ∀ (x:Rˣ), x^((Fintype.card Rˣ)/n.val) ∈ rootsOfUnity n R := by
  intro x
  rw [mem_rootsOfUnity]
  exact pow_n hdiv x

def pow_map (k : ℕ) : Rˣ →* Rˣ :=
  MonoidHom.mk' (fun x => x^k) (by intro x y ; simp ; exact mul_pow x y k )

/- map from the units to the n-th roots of unity -/
noncomputable def toRoots {n : ℕ+} (hn : fullRoots n R) : Rˣ →* rootsOfUnity n R :=
  MonoidHom.codRestrict (pow_map ((Fintype.card Rˣ)/n.val)) (rootsOfUnity n R) (root_n (div_n hn))

end FiniteRing

section ResidueMultMap

/-
The goal here is to put it all together to a statement that will apply to rings of integers of
number fields containing n-th roots of unity, with n prime to the residue characteristic.

So we make a statement for a domain R, n, a maximal ideal p, the property that
R has all n-th root of unity and the map R -> R/p is "nice", and we state that
we have a multiplicative map from R \ p to the n-th roots of unity.

We write also the property that the image is 1 iff the element is an n-th root modulo p

Ideal.primeCompl p is the monoid R \ p (when p is assumed to be prime)

the map is a composition of 3 maps:
- multiplicative map from R \ p to (R/p)ˣ (this is residueMultMap below)
- map from (R/p)ˣ to the n-th roots of the quotient (this is toRootsQuot below, an application of toRoots above)
- inverse of the bijection between n-th roots of R and n-th roots of R/p (this is bij_nth_roots_gen above)

We write also the property that the image is 1 iff the element is an n-th root modulo p,
which we deduce from is_nth_pow above

Remark: we can also do it as a multiplicative map R -> 0 union n-th roots of unity,
this is also a monoid map
-/

variable {R : Type*} [CommRing R] [IsDomain R]
variable {p : Ideal R} (hp : Ideal.IsMaximal p) [instFinite: Fintype (R ⧸ p)]
variable {n : ℕ+} (hR : fullRoots n R) (hn : nice n (Ideal.Quotient.mk p))

lemma imageUnit :
  ∀ (x : p.primeCompl), IsUnit ((Ideal.Quotient.mk p).toMonoidHom x) := by
  intro x
  have : Ideal.Quotient.mk p x ≠ 0 := by
    by_contra h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    exact (Set.not_mem_of_mem_compl x.mem) h
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hp
  rcases (IsField.mul_inv_cancel hp this) with ⟨ b, hb⟩
  rw [isUnit_iff_exists]
  use b, hb
  rw [mul_comm] at hb
  exact hb

noncomputable def residueMultMap :
(Ideal.primeCompl p) →* (R ⧸ p)ˣ
:=
{ toFun := fun x => (IsUnit.unit (imageUnit hp x))
  map_one' := by
    ext
    simp
  map_mul' := by
    intros
    ext
    simp
}

noncomputable def toRootsQuot :
(R ⧸ p)ˣ →* (rootsOfUnity n (R ⧸ p)) :=
toRoots (toFull hR hn)

noncomputable def residueSymbolMap :
(Ideal.primeCompl p) →* (rootsOfUnity n R) :=
(((bij_nth_roots_gen hR hn).symm.toMonoidHom).comp (@toRootsQuot _ _ _ _ _ hR hn)).comp
(@residueMultMap _ _ _ hp)

end ResidueMultMap

section NumberField

/- here we state everything for a number field -/

end NumberField

/-
lemma card_units : Fintype.card (Rˣ) = Fintype.card R - 1 := by
  rw [← Fintype.card_units]
-/
