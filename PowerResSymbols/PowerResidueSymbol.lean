import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm

open scoped NumberField BigOperators

variable {F : Type*} [Field F] [NumberField F] (ζ : 𝓞 F) (n : ℕ) (h : IsPrimitiveRoot ζ n)
variable (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) [hp2: Fact (p ≠ ⊥)]

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueFieldAtPrime (hp : Ideal.IsPrime p) :=
  LocalRing.ResidueField (Localization.AtPrime p)

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
abbrev ResidueFieldAtPrime2 := 𝓞 F ⧸ p

noncomputable section


-- noncomputable instance : Field (ResidueFieldAtPrime p hp) := by
  -- apply LocalRing.ResidueField.field

-- noncomputable instance : CommRing (ResidueFieldAtPrime2 p) := by
--   apply Ideal.Quotient.commRing


noncomputable instance : Field (ResidueFieldAtPrime2 p) := by
  have h : Ideal.IsMaximal p := by
    apply Ideal.IsPrime.isMaximal hp hp2.out
  apply Ideal.Quotient.field

def residue_map2 : 𝓞 F →+* (ResidueFieldAtPrime2 p) := by
  have := Ideal.Quotient.mk p
  unfold ResidueFieldAtPrime2
  convert this

abbrev residue_map : 𝓞 F →+* (ResidueFieldAtPrime p hp) :=
  (LocalRing.residue (Localization.AtPrime p)).comp (algebraMap (𝓞 F) (Localization.AtPrime p))


instance as : Fintype (ResidueFieldAtPrime2 p) := Ideal.fintypeQuotientOfFreeOfNeBot p hp2.out

#check as
-- instance : Fintype ( (ResidueFieldAtPrime2 p)ˣ ) := by
--   infer_instance

lemma l1 : Fintype.card (ResidueFieldAtPrime2 p) = Ideal.absNorm p := by
  rw [@Ideal.absNorm_apply]
  symm
  convert Submodule.cardQuot_apply _

instance : IsCyclic (ResidueFieldAtPrime2 p)ˣ := by
  infer_instance
open scoped Classical

lemma l3 : Fintype.card ( (ResidueFieldAtPrime2 p)ˣ ) = ((Ideal.absNorm p) - 1) := by
  rw [← l1]
  rw [← Fintype.card_units]


lemma norm_div_lemmas
      (hpn : p ⊔ Ideal.span ({(n : (𝓞 F))} : Set (𝓞 F)) = ⊤) : n  ∣ ((Ideal.absNorm p) - 1) := by
    sorry

lemma exits_pth_root (a : 𝓞 F) (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p)
    (hpn : p ⊔ Ideal.span ({(n * a : (𝓞 F))} : Set (𝓞 F)) = ⊤) :
  ∃! (i : ℕ), (a ^ (((Ideal.absNorm p) - 1) / n)) -  ζ^i ∈ p := by sorry
