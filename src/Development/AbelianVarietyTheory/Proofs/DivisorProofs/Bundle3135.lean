module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.BotConstPf

theorem gBig_imp {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | (apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem ..)

theorem lamC_div_norm {p : ℕ} [Fact p.Prime] {u₁ u₂ : ℂ} (h₁ : u₁ ∈ Qbar) (h₂ : u₂ ∈ Qbar)
    (n₁ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₁‖ = 1) (n₂ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₂‖ = 1) :
    u₁ / u₂ ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (u₁ / u₂)‖ = 1 := by
  have h3 : u₁ / u₂ ∈ Qbar := div_mem h₁ h₂
  refine ⟨h3, fun lam => ?_⟩
  have e : (⟨u₁ / u₂, h3⟩ : Qbar) = ⟨u₁, h₁⟩ / ⟨u₂, h₂⟩ := rfl
  have a := n₁ lam
  have b := n₂ lam
  rw [lamC, dite_eq_left h₁] at a
  rw [lamC, dite_eq_left h₂] at b
  rw [lamC, dite_eq_left h3, e, map_div₀, norm_div, a, b, div_one]

end GlobalTheory.SqTop.BotConstPf

namespace GlobalTheory.SqTop

open BotConstPf

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByPrimeAtEtalePlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.GeoCard

theorem card_ker_elt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {w0 : Ideal (𝓞 D.F)} (hw : IsEtPlace b w0) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F) (hc : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) :
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} =
      (Algebra.norm ℤ c).natAbs ^ (D.m * D.n) := by
  obtain ⟨ℓ, hℓ1, hℓ⟩ := Nat.exists_infinite_primes (p + ringChar k + 1)
  have hℓp : ℓ ≠ p := by omega
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k (ringChar k)]
    intro hd
    rcases (Nat.dvd_prime hℓ).1 hd with h1 | h1
    · exact CharP.ringChar_ne_one (R := k) h1
    · omega
  exact GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow S o.A o.ab D.F (o.act.toF D) k x (D.m * D.n) ℓ hℓ hℓk (GlobalTheory.T.exists_level_structure_on_torsion p D R b N S s o k x ℓ hℓ hℓp) c hc
    (GlobalTheory.T.harrisTaylor_tangent_injective_away_from_etalePlace p D R b N w0 hw S s o k x c hc hcw)

theorem card_ker_place : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ w0,
      g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} = Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
  intro p _ D R _ b N w0 hw S s o k _ _ x
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  have act0 : o.act.act 0 = 1 := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  letI : Module (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) :=
    { smul := fun c g => Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c))
      one_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
        rw [map_one, o.act.one, Category.comp_id]; rfl
      mul_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
        rw [map_mul, o.act.mul, Category.assoc]
      smul_zero := fun c => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) = Additive.ofMul 1
        rw [MonObj.one_comp]
      smul_add := fun c g g' => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((g.toMul * g'.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) *
            (g'.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
        rw [MonObj.mul_comp]
      add_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) *
            (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)))
        rw [map_add (f := _), o.act.add, MonObj.comp_mul]
      zero_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
        rw [map_zero, act0, MonObj.comp_one] }
  have hsm : ∀ (c : 𝓞 D.F) (g : Additive (Over.mk x ⟶ o.A)),
      c • g = Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) := fun _ _ => rfl
  have hmax : w0.IsMaximal := hw.1
  have hne : w0 ≠ ⊥ := by
    intro h0
    have hp : ((p : ℕ) : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h0, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

  have hdiv : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive (Over.mk x ⟶ o.A) => c • g) := by
    intro c hc g
    set n := Ideal.absNorm (Ideal.span {c}) with hn
    have hn0 : 0 < n := by
      rw [hn, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc
    have hmem : ((n : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g', hg'⟩ := GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme S o.A o.ab k x n hn0 g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, hc', Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl

  have hT : ∀ I : Ideal (𝓞 D.F), Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      (I : Set (𝓞 D.F))) = Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ I,
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} := by
    intro I
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBySet_iff]
    constructor
    · intro h c hc
      have := h ⟨c, hc⟩
      rw [hsm] at this
      exact this
    · intro h c
      rw [hsm]
      exact congrArg Additive.ofMul (h c.1 c.2)

  have hw0nz : w0 ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨w0, hw0nz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : w0 ^ H ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (w0 ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨w0 ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 D.F))) = ⟨w0, hw0nz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : w0 ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w := by
    intro w hwm _ hww hcw
    apply hww
    have h1 : w0 ^ H ≤ w := by rw [hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hcw
    exact (hmax.eq_of_le hwm.ne_top (hwm.isPrime.le_of_pow_le h1)).symm
  have hcount := card_ker_elt hw o k x c hc0 hcw
  have hnorm : (Algebra.norm ℤ c).natAbs = Nat.card (𝓞 D.F ⧸ w0) ^ H := by
    rw [← Ideal.absNorm_span_singleton, ← hspan, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

  have hTH : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) = Nat.card (𝓞 D.F ⧸ w0) ^ (H * (D.m * D.n)) := by
    rw [hspan, Submodule.torsionBySet_span_singleton_eq, pow_mul, ← hnorm, ← hcount]
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBy_iff, hsm]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

  have hq : 1 < Nat.card (𝓞 D.F ⧸ w0) := by
    have hfin : Finite (𝓞 D.F ⧸ w0) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field w0
    exact Finite.one_lt_card

  have hTHfin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F)) ≤
      Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field w0
  haveI : Module.Finite (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) =
      Nat.card (𝓞 D.F ⧸ w0) ^ h' := Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField D.F _ w0 h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * (D.m * D.n) = H * h' := Nat.pow_right_injective hq hall
  have he' : h' = D.m * D.n := (Nat.eq_of_mul_eq_mul_left hH0 he).symm
  rw [← hT, hT1, he']

end GlobalTheory.UPel.HT.EtLev.GeoCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem injective_of_flat_of_isDomain {A R : Type} [CommRing A] [IsDomain A] [CommRing R] [Nontrivial R] (ψ : A →+* R)
    (h : ψ.Flat) : Function.Injective ψ := by
  letI := ψ.toAlgebra
  haveI : Module.Flat A R := h
  refine (injective_iff_map_eq_zero ψ).2 fun a ha => ?_
  by_contra h0
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : a • (1 : R) = a • (0 : R) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, _root_.mul_one]; exact ha
  exact one_ne_zero (hr h1)

theorem exists_canon_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hn
  obtain ⟨D', L, θ₀, N, ε, e, s, hp, hq, hθ₀, hb, hδ, hs, hu, hdiv⟩ := _root_.GlobalTheory.VData.exists_divFrom Xo c φ V hV hk C hn
  have hC₀ : (MvPolynomial.eval₂Hom θ₀ s).comp MvPolynomial.C = θ₀ := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ _
  have hsm : ∀ i, s (.inl i) ∈ maximalIdeal V := fun i => by
    obtain ⟨u, hu⟩ := (hs i).symm
    rw [← hu]; exact Ideal.mul_mem_right _ _ (C.s_mem i)
  have hs0 : ∀ i, s (.inl i) ≠ 0 := fun i h => C.s_ne_zero i ((hs i).eq_zero_iff.1 h)
  obtain ⟨k, _, e', ψ, θ, hcompl, hθ, hθψ, hψ, hbd⟩ := _root_.GlobalTheory.TChart.exists_chartRing_factor L.W ⟨L.b.comp (algebraMap ℚ c.F)⟩ C.m N V hV.1.2.2.2
    (MvPolynomial.eval₂Hom θ₀ s) (by rw [hC₀]; exact hθ₀) (fun i => by rw [MvPolynomial.eval₂Hom_X']; exact hsm i)
  have hθX : ∀ j, θ (ψ (MvPolynomial.X j)) = s j := fun j => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = θ₀ := by rw [← RingHom.comp_assoc, hθψ, hC₀]
  have hinj : Function.Injective (ψ.comp MvPolynomial.C) :=
    (injective_of_flat_of_isDomain ψ hcompl.2.2.1).comp (MvPolynomial.C_injective _ _)
  let b₁ : c.F →+* ChartRing k C.m e' := (ψ.comp MvPolynomial.C).comp L.b
  have hR : GlobalTheory.Mum.Base (ChartRing k C.m e') :=
    ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k C.m e', (b₁.charZero_iff b₁.injective).1 inferInstance⟩
  have htor : ∀ j, IsUnit (ψ (MvPolynomial.X (.inr j))) := fun j => hθ.map_nonunit _ (by rw [hθX]; exact hu j)
  have hmem : ∀ i, ψ (MvPolynomial.X (.inl i)) ∈ maximalIdeal (ChartRing k C.m e') := fun i hi =>
    hsm i (by rw [← hθX]; exact hi.map θ)
  have hne : ∀ i, θ (ψ (MvPolynomial.X (.inl i))) ≠ 0 := fun i => by rw [hθX]; exact hs0 i
  have hval : ∀ i y, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y = C.δ i (e.symm y) (e.symm y) := fun i y => by
    rw [hδ i]
    show _ = (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm y)) (e (e.symm y))
    rw [e.apply_symm_apply]
  have hnn : ∀ i y, 0 ≤ (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun i y => by
    rw [hval]; exact C.cone.nonneg i _
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun y hy => by
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (y := e.symm y) (by simpa using hy)
    refine Finset.sum_pos' (fun j _ => hnn j y) ⟨i, Finset.mem_univ _, ?_⟩
    rw [hval]
    exact pos_of_mul_pos_left (by rw [mul_comm]; exact hi) (Int.natCast_nonneg l.M')
  obtain ⟨t₁, P₁, e₁, hdiv₁, hmono⟩ := _root_.GlobalTheory.UCanon.FamFrom.main L (ChartRing k C.m e') hR (ψ.comp MvPolynomial.C) hinj C.m N
    (fun j => ψ (MvPolynomial.X j)) (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) (fun j => (ε j).2)
    (fun i => ⟨hmem i, fun h => hne i (by rw [h, map_zero])⟩) htor hnn hpos e.injective.nontrivial
  obtain ⟨y₁, yo, κ, h₁, h₂, h₃, h₄, h₅⟩ := _root_.GlobalTheory.clsOpen Xo c φ D' L (ChartRing k C.m e') V hR hV C.toFam t₁ P₁
    (ψ.comp MvPolynomial.C) θ hθ (by rw [← RingHom.comp_assoc, hθC, hb]) C.m N (fun j => ψ (MvPolynomial.X j))
    (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) e₁ e (fun j => (ε j).2) hne htor hdiv₁
    (by rw [hθC, funext hθX]; exact hdiv)
  have hrk : Module.finrank (𝓞 E) P₁.D.toPre.X = Module.finrank (𝓞 E) C.P.D.toPre.X := (e₁.trans e.symm).finrank_eq
  have hcone : IsCone H.bar φ fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
    have h := C.cone.pull_equiv (e₁.trans e.symm)
    have he : (fun i => pull (e₁.trans e.symm).toLinearMap (C.δ i)) =
        fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
      funext i
      rw [hδ i]
      refine LinearMap.ext₂ fun a b => ?_
      show (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm (e₁ a))) (e (e.symm (e₁ b))) = _
      rw [e.apply_symm_apply, e.apply_symm_apply]
      rfl
    rwa [he] at h
  let C₁ : MonoFam Xo c φ (ChartRing k C.m e') :=
    ⟨⟨b₁, t₁, P₁, y₁, h₁, h₂⟩, C.m, fun i => ψ (MvPolynomial.X (.inl i)), hmem,
      fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X), hcone, hrk.le.trans C.rank, hmono⟩
  exact ⟨k, _, C.m, e', C₁, θ, ⟨⟨D', by rw [← hp, ← hrk], by rw [← hq, ← hrk], L, N, ε, e₁, fun _ => rfl, ψ, hcompl, hψ,
    rfl, fun _ => rfl, htor, hdiv₁⟩⟩, ⟨rfl, hbd⟩, hθ, yo, κ, h₃, h₄, h₅⟩

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.TChart

theorem torsRat_of_isGrpPullback_siegPre {S : Scheme.{0}} {h n : ℕ} {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ)
    {s : S ⟶ Sp o} (c : SiegPre h n ζ s) {R : Type} [CommRing R] [IsDomain R] (b : o →+* R) (B : Over (Sp R)) [GrpObj B]
    (f : Sp R ⟶ S) (hf : f ≫ s = spMap b) (β : B.left ⟶ c.A.left) (hβ : IsGrpPullback B c.A f β) : TorsRat B n := by
  intro K _ _ κ x hx
  let b₀ : o →+* K := (κ.comp (algebraMap R (FractionRing R))).comp b
  have hb₀ : ((spMap κ ≫ jK R) ≫ f) ≫ s = spMap b₀ := by
    rw [Category.assoc, hf]
    simp only [b₀, spMap, jK, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨-, h2, -⟩ := c.geom K ((spMap κ ≫ jK R) ≫ f) b₀ (hζ.map b₀).unit hb₀ rfl
  obtain ⟨a, ha⟩ := h2 (pushHom hβ (Over.mk (spMap κ ≫ jK R)) x) (by rw [← map_pow, hx, map_one])
  have ha' : ((spMap κ ≫ jK R) ≫ f) ≫ (c.lev a).left = x.left ≫ β := congrArg (fun q => q.left) ha
  have hl : (c.lev a).left ≫ c.A.hom = 𝟙 S := Over.w (c.lev a)
  have w : (jK R ≫ f ≫ (c.lev a).left) ≫ c.A.hom = jK R ≫ f := by
    simp only [Category.assoc]
    erw [hl, Category.comp_id]
  refine ⟨Over.homMk (hβ.1.lift (jK R ≫ f ≫ (c.lev a).left) (jK R) w) (hβ.1.lift_snd _ _ _), ?_⟩
  apply hβ.1.hom_ext
  · rw [← ha']
    show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ β
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_fst]
    simp only [Category.assoc]
  · show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ B.hom
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_snd]
    exact Over.w x

theorem Taut.torsRat_B {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ) {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) :
    TorsRat C.Q.B n := by
  obtain ⟨β, -, -, hβ, -⟩ := C.data
  refine torsRat_of_isGrpPullback_siegPre hζ C.F.univ C.b C.Q.B _ ?_ _ (IsGrpPullback.comp hβ C.cart)
  have := C.u_base
  rw [LowChart.toO] at this
  rw [Category.assoc, Category.assoc, this]
  simp only [Taut.b, Taut.iw, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem Taut.exists_family : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ C : Taut (zetaAway n) g n φ, ∃ (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P ∧ GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ TorsRat G₁ n := by
  intro g n φ hn _ C
  have hn0 : n ≠ 0 := by omega
  have hn1 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  obtain ⟨hreg, hchar, hinj, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  have hCN : IsCN C.R :=
    ⟨C.compl.1, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R).2, C.compl.2.1, hchar⟩
  have hsym : ∀ k a b, ((n : ℤ) • C.δ k) a b = ((n : ℤ) • C.δ k) b a := fun k a b => by
    simp only [LinearMap.smul_apply, (hcone.mem k).1 a b]
  have hnn : ∀ k a, 0 ≤ ((n : ℤ) • C.δ k) a a := fun k a => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hn1.le (hcone.nonneg k a)
  have hpos : ∀ a, a ≠ 0 → ∃ k, 0 < ((n : ℤ) • C.δ k) a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn1 hk⟩
  have hne : ∀ k, (n : ℤ) • C.δ k ≠ 0 := fun k hk => by
    apply C.ε.ne_zero (.inl k)
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    have h1 : (n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e (C.e.symm a)) (C.e (C.e.symm b)) = 0 :=
      congrArg (fun B : LinearMap.BilinForm ℤ C.Q.X => B (C.e.symm a) (C.e.symm b)) hk
    rw [C.e.apply_symm_apply, C.e.apply_symm_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left hn1.ne'
  have hQ : C.Q.IsPos (maximalIdeal C.R) := hmono.isPos (fun k => C.bd k) hnn hpos
  obtain ⟨G, _, _, P, hM, hC⟩ := _root_.GlobalTheory.Mum.exists_canonOn_of_isMonomialTau C.R hCN C.Q hQ C.m C.t _ hmono ht hsym hnn hpos
  have hζ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  refine ⟨G, inferInstance, inferInstance, P, hM, hC,
    GlobalTheory.Mum.abLocus_iff_of_monomialTau C.R hCN C.Q hQ G P hM C.m C.t _ (fun k => ⟨C.bd k, ht k⟩) hsym hnn hpos hne hmono, ?_⟩
  exact _root_.GlobalTheory.Mum.torsRat_of_canon C.T C.R _ _ _ n hCN (by omega) (by simpa using (isUnit_natCast hn0).map C.b) (C.b (zetaAway n))
    (hζ.map_of_injective hinj) C.Q C.e C.data (C.torsRat_B (hζ.isUnit hn0)) G P hC.canon

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageConstantTriangle
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

theorem gBig_of₃ {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqTower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
end

