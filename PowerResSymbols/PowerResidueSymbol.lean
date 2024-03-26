import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm

open scoped NumberField BigOperators

variable {F : Type*} [Field F] [NumberField F] (ζ : 𝓞 F) (n : ℕ) (h : IsPrimitiveRoot ζ n)
variable (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥)

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueFieldAtPrime (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥) :=
  LocalRing.ResidueField (Localization.AtPrime p)

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueFieldAtPrime2 (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥) := 𝓞 F ⧸ p

noncomputable section


-- noncomputable instance : Field (ResidueFieldAtPrime p hp) := by
  -- apply LocalRing.ResidueField.field

-- noncomputable instance : CommRing (ResidueFieldAtPrime2 p) := by
--   apply Ideal.Quotient.commRing


noncomputable instance : Field (ResidueFieldAtPrime2 p hp hp2) := by
  have h : Ideal.IsMaximal p := by
    apply Ideal.IsPrime.isMaximal hp hp2
  apply Ideal.Quotient.field




abbrev residue_map : 𝓞 F →+* (ResidueFieldAtPrime p hp hp2) :=
  (LocalRing.residue (Localization.AtPrime p)).comp (algebraMap (𝓞 F) (Localization.AtPrime p))


abbrev residue_map2 : 𝓞 F →+* (ResidueFieldAtPrime2 p hp hp2) := Ideal.Quotient.mk p

instance as : Fintype (ResidueFieldAtPrime2 p hp hp2) := Ideal.fintypeQuotientOfFreeOfNeBot p hp2

lemma l1 : Fintype.card (ResidueFieldAtPrime2 p hp hp2) = Ideal.absNorm p := by
  rw [@Ideal.absNorm_apply]
  symm
  convert Submodule.cardQuot_apply _

instance : IsCyclic (ResidueFieldAtPrime2 p hp hp2)ˣ := by
  infer_instance
open scoped Classical

-- compute the cardinality of the units of the residue field
lemma l3 : Fintype.card ((ResidueFieldAtPrime2 p hp hp2)ˣ ) = ((Ideal.absNorm p) - 1) := by
  rw [← l1]
  rw [← Fintype.card_units]

lemma n_not_zero (hpn : IsCoprime n (Ideal.absNorm p)) : (residue_map2 p hp hp2) n ≠ 0 := by
  sorry

def cyclo : Polynomial (𝓞 F) := (Polynomial.X ^n) - (Polynomial.C 1)

def P : Polynomial (𝓞 F) := sorry

lemma P1 : Polynomial.eval 1 P = (n : 𝓞 F) := by sorry

lemma P_cyclo : P * (cyclo 1) = (cyclo n) := by sorry

lemma Pzeta (i : ℕ): ¬ (n ∣ i) → Polynomial.eval (ζ^i) P = 0 := by sorry
-- show that if ζ^i has image 1 in the residue field then n divides i (this uses that n is prime to p)
lemma injectivity (hpn : IsCoprime n (Ideal.absNorm p)) :
  ∀ (i : ℕ), ζ^i-1 ∈ p ↔ n ∣ i := by
  sorry


lemma primitivemodp (hpn : IsCoprime n (Ideal.absNorm p)) :
  IsPrimitiveRoot ((residue_map2 p hp hp2) ζ) n := by
    rw [IsPrimitiveRoot.iff_def]
    constructor
    . calc (residue_map2 p hp hp2) ζ ^ n = (residue_map2 p hp hp2) (ζ^n) := by exact rfl
                _ = (residue_map2 p hp hp2) 1 := by rw [((IsPrimitiveRoot.iff_def ζ n).mp h).1]
                _ = 1 := by exact rfl
    intro i hi
    rw [← injectivity ζ n p hpn i]
    have : (residue_map2 p hp hp2) ζ^i = (residue_map2 p hp hp2 (ζ^i)) := rfl
    rw [this] at hi
    rw [← Ideal.Quotient.eq,hi]
    exact rfl

-- deduce the divisibility result
lemma norm_div_lemmas (hpn : IsCoprime n (Ideal.absNorm p)) : n  ∣ ((Ideal.absNorm p) - 1) := by
    rw [← l3 p hp hp2]
    have divide : orderOf ((residue_map2 p hp hp2) ζ) ∣ Fintype.card ((ResidueFieldAtPrime2 p hp hp2)ˣ)  := by
      -- exact orderOf_dvd_card
      sorry
    have := IsPrimitiveRoot.eq_orderOf (primitivemodp ζ n h p hp hp2 hpn)
    rw [← this] at divide
    exact divide


lemma exits_pth_root (a : 𝓞 F) (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p)
    (hpn : p ⊔ Ideal.span ({(n * a : (𝓞 F))} : Set (𝓞 F)) = ⊤) :
  ∃! (i : ℕ), (a ^ (((Ideal.absNorm p) - 1) / n)) -  ζ^i ∈ p := by sorry
