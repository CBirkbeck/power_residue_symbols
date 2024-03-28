import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Group.Commute.Units

open scoped NumberField BigOperators

variable {F : Type*} [Field F] [NumberField F] (ζ : (𝓞 F)ˣ) (n : ℕ+) (h : IsPrimitiveRoot ζ n)
variable (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥)  (r : Ideal (𝓞 F))

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueFieldAtPrime (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥) :=
  LocalRing.ResidueField (Localization.AtPrime p)

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueRingAtIdeal := 𝓞 F ⧸ r

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueFieldAtPrime2 (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥) := 𝓞 F ⧸ p

noncomputable section


-- noncomputable instance : Field (ResidueFieldAtPrime p hp) := by
  -- apply LocalRing.ResidueField.field

-- noncomputable instance : CommRing (ResidueFieldAtPrime2 p) := by
--   apply Ideal.Quotient.commRing

noncomputable instance : Field (ResidueRingAtIdeal p) := by
  have h : Ideal.IsMaximal p := by
    apply Ideal.IsPrime.isMaximal hp hp2
  apply Ideal.Quotient.field

noncomputable instance : CommRing (ResidueRingAtIdeal r) := by
  apply Ideal.Quotient.commRing

noncomputable instance : Field (ResidueFieldAtPrime2 p hp hp2) := by
  have h : Ideal.IsMaximal p := by
    apply Ideal.IsPrime.isMaximal hp hp2
  apply Ideal.Quotient.field

abbrev residue_map : 𝓞 F →+* (ResidueFieldAtPrime p hp hp2) :=
  (LocalRing.residue (Localization.AtPrime p)).comp (algebraMap (𝓞 F) (Localization.AtPrime p))

abbrev residue_map_at_ideal (n : Ideal (𝓞 F)) : 𝓞 F →+* (ResidueRingAtIdeal n) := Ideal.Quotient.mk n

abbrev residue_map2 : 𝓞 F →+* (ResidueFieldAtPrime2 p hp hp2) := Ideal.Quotient.mk p

instance [hp2 : Fact (p ≠ ⊥)]   : Fintype (ResidueRingAtIdeal p) :=
  Ideal.fintypeQuotientOfFreeOfNeBot p hp2.out

instance as : Fintype (ResidueFieldAtPrime2 p hp hp2) := Ideal.fintypeQuotientOfFreeOfNeBot p hp2


lemma l0  [Fact (p ≠ ⊥)] : Fintype.card (ResidueRingAtIdeal p) = Ideal.absNorm p := by
  rw [@Ideal.absNorm_apply]
  symm
  convert Submodule.cardQuot_apply _


lemma l1 : Fintype.card (ResidueFieldAtPrime2 p hp hp2) = Ideal.absNorm p := by
  rw [@Ideal.absNorm_apply]
  symm
  convert Submodule.cardQuot_apply _

open scoped Classical

-- compute the cardinality of the units of the residue field
lemma l3 : Fintype.card ((ResidueFieldAtPrime2 p hp hp2)ˣ ) = ((Ideal.absNorm p) - 1) := by
  rw [← l1]
  rw [← Fintype.card_units]

lemma n_not_zero (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) : (residue_map2 p hp hp2) n ≠ 0 := by
  have := FiniteField.cast_card_eq_zero (ResidueFieldAtPrime2 p hp hp2)
  rw [l1] at this
  rcases hpn with ⟨ a,b,H⟩
  have nquot : (a : (ResidueFieldAtPrime2 p hp hp2)) * (n : (ResidueFieldAtPrime2 p hp hp2)) = 1 := by
    have eq1 : ((a*n+b*(Ideal.absNorm p)):(ResidueFieldAtPrime2 p hp hp2)) = (1 : (ResidueFieldAtPrime2 p hp hp2)) := by
      rw_mod_cast [H]
      simp only [Nat.cast_one]
    rw [← eq1,this]
    ring
  intro hnzero
  have : (n : (ResidueFieldAtPrime2 p hp hp2)) = 0 := hnzero
  rw [this] at nquot
  ring_nf at nquot
  exact zero_ne_one nquot


/-
abbrev cyclo (m : ℕ) : Polynomial ℤ := (Polynomial.X ^m) - (Polynomial.C 1)

abbrev cyclom1  (m : ℕ): Polynomial ℤ :=
  Finset.sum (Finset.range m) fun (i : ℕ) => Polynomial.X ^ i

lemma P1 : Polynomial.eval (1 : ℤ) (cyclom1 n) = (n : ℤ) := by
  rw [cyclom1]
  rw [@Polynomial.eval_geom_sum]
  simp


lemma P_cyclo (m : ℕ) : (cyclom1 m) * (cyclo 1) = (cyclo m) := by
  rw [cyclo,cyclom1,cyclo]
  rw [@Polynomial.C_1]
  simp [@pow_one]
  rw [geom_sum_mul (α := Polynomial ℤ) (x:=Polynomial.X) (n:=m)]

lemma Pzeta (i : ℕ):
  ¬ (n ∣ i) → Polynomial.eval₂ (Int.castRingHom (𝓞 F)) (ζ^i) (cyclom1 n) = 0:= by
  intro hi
  have is_zero : Polynomial.eval₂ (Int.castRingHom (𝓞 F)) (ζ^i) (cyclo n) = 0 := by
    rw [cyclo]
    simp only [map_one, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one]
    have : (ζ^i)^n = (ζ^n)^i := by ring
    rw [this, ((IsPrimitiveRoot.iff_def ζ n).mp h).1]
    ring_nf
  have hii : ζ^i ≠ 1 := by
    have := IsPrimitiveRoot.pow_eq_one_iff_dvd h i
    contrapose! this
    left
    exact ⟨this,hi⟩
  have non_zero : Polynomial.eval₂ (Int.castRingHom (𝓞 F)) (ζ^i) (cyclo 1) ≠ 0 := by
    rw [cyclo]
    simp only [pow_one, map_one, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one,
      ne_eq]
    exact sub_ne_zero_of_ne hii

  rw [← P_cyclo] at is_zero
  simp only [Polynomial.eval₂_mul] at is_zero
  rw [mul_eq_zero] at is_zero
  cases' is_zero with h1 h2
  . exact h1
  . by_contra h
    simp only [ne_eq, Polynomial.eval₂_sub, pow_one, Polynomial.eval₂_X, map_one,
      Polynomial.eval₂_one] at *
    exact non_zero h2


-/



/-
-- show that if ζ^i has image 1 in the residue field then n divides i (this uses that n is prime to p)
lemma injectivity (hpn : IsCoprime (n : ℤ) (Ideal.absNorm p)) :
  ∀ (i : ℕ), ζ^i-1 ∈ p ↔ n ∣ i := by
  intro i
  constructor
  . intro hinp
    by_contra hi
    have eval0 := Pzeta ζ n i hi
    have evalmodp : Polynomial.eval₂ ((residue_map2 p hp hp2).comp (Int.castRingHom (𝓞 F))) ((residue_map2 p hp hp2) (ζ^i)) (cyclom1 n) = 0 := by
      have : Polynomial.eval₂ ((residue_map2 p hp hp2).comp (Int.castRingHom (𝓞 F))) ((residue_map2 p hp hp2) (ζ^i)) (cyclom1 n) =
         Finset.sum (Finset.range n) fun (i : ℕ) => (residue_map2 p hp hp2) ζ^i := by
         unfold cyclom1
         simp
         sorry
      sorry

    have equalzetai : (residue_map2 p hp hp2) (ζ^i) = 1 := by sorry
    rw [equalzetai] at evalmodp
    sorry
  intro hi
  rcases hi with ⟨ k,rfl⟩
  have : ζ^(n*k) = (ζ^n)^k := by ring
  rw [this,((IsPrimitiveRoot.iff_def ζ n).mp h).1]
  ring_nf
  exact Ideal.zero_mem p

#check injectivity
-/


lemma primitivemodp' (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) :
  IsPrimitiveRoot ((residue_map2 p hp hp2) ζ) n := by
  haveI  : NeZero (n : ResidueFieldAtPrime2 p hp hp2) := by
    have := n_not_zero  n p hp hp2 hpn
    rw [neZero_iff]
    exact this
  rw [← IsPrimitiveRoot.coe_units_iff] at h
  rw [← Polynomial.isRoot_cyclotomic_iff] at *
  have h1 := Polynomial.IsRoot.map (x := ζ) (f := residue_map2 p hp hp2) h
  simp at *
  exact h1


/-
lemma primitivemodp (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) :
  IsPrimitiveRoot ((residue_map2 p hp hp2) ζ) n := by
    rw [IsPrimitiveRoot.iff_def]
    constructor
    . calc (residue_map2 p hp hp2) ζ ^ (n : ℕ)= (residue_map2 p hp hp2) (ζ^ (n : ℕ)) := by exact rfl
                _ = (residue_map2 p hp hp2) 1 := by rw [((IsPrimitiveRoot.iff_def ζ n).mp h).1]
                _ = 1 := by exact rfl
    intro i hi
    rw [← injectivity ζ n h p hp hp2 hpn i]
    have : (residue_map2 p hp hp2) ζ^i = (residue_map2 p hp hp2 (ζ^i)) := rfl
    rw [this] at hi
    rw [← Ideal.Quotient.eq,hi]
    exact rfl
-/

lemma isunit : IsUnit ((residue_map2 p hp hp2) ζ) := by
  rw [← IsPrimitiveRoot.coe_units_iff] at h
  exact IsUnit.map (residue_map2 p hp hp2) (IsPrimitiveRoot.isUnit h n.2)


-- deduce the divisibility result
lemma norm_div_lemmas (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) :
    (n : ℕ)  ∣ ((Ideal.absNorm p) - 1) := by
  rw [← l3 p hp hp2]
  have divide := orderOf_dvd_card (G := (ResidueFieldAtPrime2 p hp hp2)ˣ)
        (x := IsUnit.unit (isunit ζ n h p hp hp2)  )
  convert divide
  have ht : IsPrimitiveRoot (IsUnit.unit (isunit ζ n h p hp hp2)) n := by
    have := (primitivemodp' ζ n h p hp hp2 hpn)
    rw [ ← IsPrimitiveRoot.coe_units_iff]
    simp [this]
  have := IsPrimitiveRoot.eq_orderOf ht
  simp at *
  rw [this]

/-
this should help for the lemma
should we assume ζ to be a unit at the beginning? it would make things easier
-/

lemma root_is_unit
{R : Type*} [CommRing R] (a : R) (k : ℕ+) (ha : a^(k : ℕ) = 1) : IsUnit a := by
  rw [← isUnit_pow_iff (n := k)]
  simp [ha]
  simp

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
  simp


--def powerResidueSymbol (a : 𝓞 F) (r : Ideal (𝓞 F)): ResidueRingAtIdeal r  :=


lemma exists_pth_root (a : 𝓞 F) (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥)
   (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) :
  ∃! (η : rootsOfUnity n (𝓞 F)ˣ) , (a ^ (((Ideal.absNorm p) - 1) / n)) -  η.1.1  ∈ p := by

  have h0 : (residue_map2 p hp hp2) (a ^ (((Ideal.absNorm p) - 1) / n))^ (n : ℕ) = 1 := by sorry
  have := IsPrimitiveRoot.eq_pow_of_pow_eq_one (primitivemodp' ζ n h p hp hp2 hpn) h0 n.2
  obtain ⟨i, hi1, hi2⟩ := this
  have hy : (ζ^i)^(n : ℕ) = 1 := by sorry
  let z := rootsOfUnity.mkOfPowEq (ζ^i) hy
  use z
  simp
  constructor
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  convert hi2.symm
  intro b hb hb2
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hb2
  rw [← hi2] at hb2
  simp [z]

  sorry




def powerResidueSymbol (a : 𝓞 F) (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥)
  (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) : rootsOfUnity n (𝓞 F)ˣ :=
   Classical.choose  (exists_pth_root ζ n h a p hp hp2 hpn)
