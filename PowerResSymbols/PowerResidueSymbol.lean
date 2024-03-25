import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm

open scoped NumberField BigOperators

variable {F : Type*} [Field F] [NumberField F] (ζ : 𝓞 F) (n : ℕ) (h : IsPrimitiveRoot ζ n)

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
def ResidueFieldAtPrime (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) :=
  LocalRing.ResidueField (Localization.AtPrime p)

/--The residue field of a number field (specifically the ring of intergers) at a prime-/
def ResidueFieldAtPrime2 (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) :=  𝓞 F ⧸ p

variable (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p)

noncomputable section

noncomputable instance : Field (ResidueFieldAtPrime p hp) := by
  apply LocalRing.ResidueField.field

noncomputable instance (hp2 : p ≠ ⊥) : Field (ResidueFieldAtPrime2 p hp) := by
  have h : Ideal.IsMaximal p := by
    apply Ideal.IsPrime.isMaximal hp hp2
  apply Ideal.Quotient.field

def residue_map : 𝓞 F →+* (ResidueFieldAtPrime p hp) :=
  (LocalRing.residue (Localization.AtPrime p)).comp (algebraMap (𝓞 F) (Localization.AtPrime p))

instance inst1 (hp2: p ≠ ⊥) : Fintype (ResidueFieldAtPrime2 p hp) := by
  letI := Ideal.fintypeQuotientOfFreeOfNeBot p hp2
  convert this

lemma norm_div_lemmas (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p)
      (hpn : p ⊔ Ideal.span ({(n : (𝓞 F))} : Set (𝓞 F)) = ⊤) : n  ∣ ((Ideal.absNorm p) - 1) := by
    sorry

lemma exits_pth_root (a : 𝓞 F) (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p)
    (hpn : p ⊔ Ideal.span ({(n * a : (𝓞 F))} : Set (𝓞 F)) = ⊤) :
  ∃! (i : ℕ), (a ^ (((Ideal.absNorm p) - 1) / n)) -  ζ^i ∈ p := by sorry
