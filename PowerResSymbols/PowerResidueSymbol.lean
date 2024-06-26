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

--local notation "𝓞Fp" => (ResidueFieldAtPrime p hp hp2)
noncomputable section


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

abbrev residue_map : 𝓞 F →+* ResidueFieldAtPrime p hp hp2 :=
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


lemma primitivemodp' (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) :
  IsPrimitiveRoot ((residue_map2 p hp hp2) ζ) n := by
  haveI  : NeZero (n : ResidueFieldAtPrime2 p hp hp2) := by
    have := n_not_zero  n p hp hp2 hpn
    rw [neZero_iff]
    exact this
  rw [← IsPrimitiveRoot.coe_units_iff] at h
  rw [← Polynomial.isRoot_cyclotomic_iff] at *
  have h1 := Polynomial.IsRoot.map (x := ζ) (f := residue_map2 p hp hp2) h
  simp only [Polynomial.IsRoot.definition, Polynomial.map_cyclotomic] at *
  exact h1


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
    simp only [IsUnit.unit_spec, this]
  have := IsPrimitiveRoot.eq_orderOf ht
  simp only at *
  rw [this]


--def powerResidueSymbol (a : 𝓞 F) (r : Ideal (𝓞 F)): ResidueRingAtIdeal r  :=

def bij_nth_roots (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) (hp2 :p ≠ ⊥)
   (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) :
   rootsOfUnity n (𝓞 F) ≃ rootsOfUnity n (ResidueFieldAtPrime2 p hp hp2) := sorry

#check bij_nth_roots

set_option profiler true in
set_option trace.profiler true in
lemma exists_pth_root (a : 𝓞 F) -- (p : Ideal (𝓞 F)) (hp : Ideal.IsPrime p) (hp2 : p ≠ ⊥)
    (hpn : IsCoprime (n : ℕ) (Ideal.absNorm p)) (hpa : a ∉ p) :
  ∃! η : rootsOfUnity n (𝓞 F)ˣ, a ^ ((Ideal.absNorm p - 1) / n) -  η.1.1  ∈ p := by

  have h0 : residue_map2 p hp hp2 (a ^ ((Ideal.absNorm p - 1) / n))^ (n : ℕ) = 1 := by
    rw [RingHom.map_pow, ← pow_mul, Nat.div_mul_cancel (norm_div_lemmas ζ n h p hp hp2 hpn)]
    have : IsUnit (M := ResidueFieldAtPrime2 p hp hp2) <| residue_map2 p hp hp2 a := by
      rw [isUnit_iff_ne_zero]
      simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, hpa, not_false_eq_true]
    lift (residue_map2 p hp hp2 a) to (ResidueFieldAtPrime2 p hp hp2)ˣ using this with y
    rw [← l1 _ hp hp2]
    norm_cast
    rw [@Units.val_eq_one]
    rw [(FiniteField.forall_pow_eq_one_iff _ _).mpr dvd_rfl]
  have := IsPrimitiveRoot.eq_pow_of_pow_eq_one (primitivemodp' ζ n h p hp hp2 hpn) h0 n.2
  obtain ⟨i, hi1, hi2⟩ := this
  have hy : (ζ^i)^(n : ℕ) = 1 := by
    have : (ζ^i)^(n : ℕ) = (ζ^(n : ℕ))^i := by group
    simp only [this, ((IsPrimitiveRoot.iff_def ζ n).mp h).1, one_pow]
  let z := rootsOfUnity.mkOfPowEq (ζ^i) hy
  use z
  simp only [Subtype.forall, mem_rootsOfUnity]
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
