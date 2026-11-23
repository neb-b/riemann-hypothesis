module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.CycBase

abbrev CF (k : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zeta k}

def zF (k : ℕ) : CF k := ⟨zeta k, IntermediateField.subset_adjoin _ _ rfl⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_isPrimitiveRoot' {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k) k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta; exact Complex.isPrimitiveRoot_exp k hk

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
lemma _root_.GlobalTheory.ZM.CycBase.zF_prim {k : ℕ} (hk : k ≠ 0) :
    IsPrimitiveRoot (_root_.GlobalTheory.ZM.CycBase.zF k) k :=
  IsPrimitiveRoot.of_map_of_injective (f := (_root_.GlobalTheory.ZM.CycBase.CF k).val)
    (zeta_isPrimitiveRoot' hk) (_root_.GlobalTheory.ZM.CycBase.CF k).val.injective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
lemma _root_.GlobalTheory.ZM.CycBase.cyc {k : ℕ} [NeZero k] :
    IsCyclotomicExtension {k} ℚ (_root_.GlobalTheory.ZM.CycBase.CF k) := by
  have hζ := zeta_isPrimitiveRoot' (NeZero.ne k)
  haveI := hζ.adjoin_isCyclotomicExtension ℚ
  have h2 : (_root_.GlobalTheory.ZM.CycBase.CF k).toSubalgebra = Algebra.adjoin ℚ {_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral (NeZero.pos k)).tower_top.isAlgebraic)
  exact IsCyclotomicExtension.equiv _ _ _ (Subalgebra.equivOfEq _ _ h2).symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
lemma _root_.GlobalTheory.ZM.CycBase.mem_ZP (p n e : ℕ) (hn : n.Prime) (a : 𝓞 (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e))) :
    ((a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : NeZero (n ^ e) := ⟨pow_ne_zero _ hn.ne_zero⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim (NeZero.ne (n ^ e))
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  obtain ⟨x, hx⟩ := hcl.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe a)
  have hax : (a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) = x := hx.symm
  rw [hax]
  obtain ⟨y, hmem⟩ := x
  change ((y : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)
  clear hx hax
  induction hmem using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
    exact Subring.subset_closure (Or.inl rfl)
  | algebraMap r =>
    simpa using intCast_mem (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) r
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | mul y z _ _ hy hz => simpa using mul_mem hy hz

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma inv_natCast_mem_ZP_of_coprime {p M m : ℕ} (hm : m.Coprime p) :
    ((m : ℂ)⁻¹) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma snd_eq_zero_of_natCast_mul_eq_one {K : Type} [Field K] {m : ℕ} {v : DualNumber K}
    (h : (m : DualNumber K) * v = 1) : v.snd = 0 ∧ (m : K) ≠ 0 := by
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp at h1 h2
  have hm : (m : K) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨by simpa [hm] using h2, hm⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_mem_ZP (p M : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta M ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inl rfl)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma ringHom_ZP_pow_dualNumber_snd_eq_zero {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0) (f : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) →+* DualNumber K)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) : (f x).snd = 0 := by
  have hnK : (n : K) ≠ 0 := by
    have hmul : ((n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) * ⟨(n : ℂ)⁻¹, inv_natCast_mem_ZP_of_coprime hn⟩ = 1 := by
      apply Subtype.ext; simp [hn0]
    have := congrArg f hmul
    rw [map_mul, map_natCast, map_one] at this
    exact (snd_eq_zero_of_natCast_mul_eq_one this).2
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨m, hm, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      set z := f ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ with hz
      have hN : n ^ e ≠ 0 := pow_ne_zero _ hn0
      have hpow : z ^ (n ^ e) = 1 := by
        rw [hz, ← map_pow]
        have : (⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) ^ (n ^ e) = 1 :=
          Subtype.ext (by simpa using (zeta_isPrimitiveRoot' hN).pow_eq_one)
        rw [this, map_one]
      have h1 := congrArg TrivSqZeroExt.fst hpow
      have h2 := congrArg TrivSqZeroExt.snd hpow
      simp only [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h1
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one] at h2
      have hz0 : z.fst ≠ 0 := by
        intro h0; rw [h0, zero_pow hN] at h1; exact zero_ne_one h1
      simp only [nsmul_eq_mul, smul_eq_mul] at h2
      have hNK : ((n ^ e : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hnK
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hNK
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 hz0
        · exact h
    · by_cases hm0 : m = 0
      · subst hm0
        have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨0, hm, rfl⟩)⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]; rfl
      · have hmul : ((m : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) *
            ⟨(m : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)⟩ = 1 := by
          apply Subtype.ext; simp [hm0]
        have := congrArg f hmul
        rw [map_mul, map_natCast, map_one] at this
        exact (snd_eq_zero_of_natCast_mul_eq_one this).1
  | zero => rw [show (⟨0, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 from rfl, map_zero]; rfl
  | one => rw [show (⟨1, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 1 from rfl, map_one]; rfl
  | add y z hy hz ihy ihz =>
    rw [show (⟨y + z, add_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl, map_add (f := _),
      TrivSqZeroExt.snd_add, ihy, ihz, add_zero]
  | neg y hy ihy =>
    rw [show (⟨-y, neg_mem hy⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = -⟨y, hy⟩ from rfl, map_neg,
      TrivSqZeroExt.snd_neg, ihy, neg_zero]
  | mul y z hy hz ihy ihz =>
    rw [show (⟨y * z, mul_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl, map_mul,
      TrivSqZeroExt.snd_mul, ihy, ihz, smul_zero, smul_zero, add_zero]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma spec_dualNumber_hom_ZP_eq_constPt {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0)
    (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e))) : y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
  conv_lhs => rw [← Spec.map_preimage y]
  conv_rhs => rw [← Spec.map_preimage y]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, ringHom_ZP_pow_dualNumber_snd_eq_zero hn hn0]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.CycBase.exists_base : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e →
    k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : _root_.GlobalTheory.ZM.TBase o k) (em : o →+* ℂ)
      (j : o →+* _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k), _root_.GlobalTheory.ZM.ArBase em ∧ j (b.ζ : o) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP p k ∧
      (∀ x, ((j x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k) : ℂ) = em x) ∧
      ∀ (K : Type) [Field K] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k)), y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  intro n e p k hn hp hnp _ hk
  subst hk
  have hN : n ^ e ≠ 0 := pow_ne_zero _ hn.ne_zero
  haveI : NeZero (n ^ e) := ⟨hN⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  haveI : NumberField (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) :=
    IsCyclotomicExtension.numberField {n ^ e} ℚ _
  have hcop : n.Coprime p := (Nat.coprime_primes hn hp).mpr hnp
  set F := _root_.GlobalTheory.ZM.CycBase.CF (n ^ e) with hF
  obtain ⟨em, har, hcomp⟩ :=
    _root_.GlobalTheory.ZM.exists_arBase_away (F := F) F.val.toRingHom hn.ne_zero
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim hN
  have hζi := hζ.toInteger_isPrimitiveRoot
  have hpos : 0 < n ^ e := Nat.pos_of_ne_zero hN
  let u : (𝓞 F)ˣ := (hζi.isUnit hN).unit
  let ζo : (Localization.Away (n : 𝓞 F))ˣ := Units.map (algebraMap (𝓞 F) _).toMonoidHom u
  have hkunit : IsUnit ((n ^ e : ℕ) : Localization.Away (n : 𝓞 F)) := by
    have := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F))
      (n : 𝓞 F)).pow e
    simpa using this
  have hprim : ∀ (K : Type) [Field K] (β : Localization.Away (n : 𝓞 F) →+* K),
      IsPrimitiveRoot (β ζo) (n ^ e) := by
    intro K _ β
    have hroot := (hζi.isRoot_cyclotomic hpos).map (f := β.comp (algebraMap (𝓞 F) _))
    rw [Polynomial.map_cyclotomic] at hroot
    haveI : NeZero ((n ^ e : ℕ) : K) := ⟨by simpa using (hkunit.map β).ne_zero⟩
    exact Polynomial.isRoot_cyclotomic_iff.mp hroot
  let b : _root_.GlobalTheory.ZM.TBase (Localization.Away (n : 𝓞 F)) (n ^ e) := ⟨ζo, hkunit, hprim⟩
  have hcompx : ∀ a : 𝓞 F, em (algebraMap _ _ a) = ((a : F) : ℂ) := fun a =>
    RingHom.congr_fun hcomp a
  have hmemZ : ∀ x, em x ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : 𝓞 F)) x
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hspec := congrArg em (IsLocalization.mk'_spec (Localization.Away (n : 𝓞 F)) a s)
    rw [map_mul, hcompx, hcompx, ← hm] at hspec
    have hnm : (((((n : 𝓞 F) ^ m : 𝓞 F)) : F) : ℂ) = (n : ℂ) ^ m := by simp
    rw [hnm] at hspec
    have hn0 : (n : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne_zero)
    rw [eq_div_of_mul_eq hn0 hspec, div_eq_mul_inv, ← inv_pow]
    exact mul_mem (_root_.GlobalTheory.ZM.CycBase.mem_ZP p n e hn a)
      (pow_mem (inv_natCast_mem_ZP_of_coprime hcop) m)
  refine ⟨Localization.Away (n : 𝓞 F), inferInstance, b, em, em.codRestrict _ hmemZ, har, ?_,
    fun x => rfl, ?_⟩
  · apply Subtype.ext
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP
    change em (algebraMap (𝓞 F) _ hζ.toInteger) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e)
    rw [hcompx]
    exact congrArg Subtype.val hζ.coe_toInteger
  · intro K _ y
    exact spec_dualNumber_hom_ZP_eq_constPt hcop hn.ne_zero y

end GlobalTheory.ZM.CycBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_det_ne_zero_of_common_ker {K J : Type} [Field K] {g : ℕ} (φ : J → (Fin g → K) →ₗ[K] K)
    (h : ∀ w, (∀ i, φ i w = 0) → w = 0) :
    ∃ c : Fin g → J, (Matrix.of fun a b => φ (c b) (Pi.single a 1)).det ≠ 0 := by
  classical
  let ψ : J → Module.Dual K (Fin g → K) := φ
  have hspan : Submodule.span K (Set.range ψ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hco : (Submodule.span K (Set.range ψ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      exact (Submodule.mem_bot K).2 (h w fun i => hw _ (Submodule.subset_span ⟨i, rfl⟩))
    have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span K (Set.range ψ))
    rw [hco, finrank_bot, add_zero] at hdim
    rw [hdim, Subspace.dual_finrank_eq]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range ψ)
  let B : Module.Basis b K (Module.Dual K (Fin g → K)) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let D : Module.Basis (Fin g) K (Module.Dual K (Fin g → K)) := (Pi.basisFun K (Fin g)).dualBasis
  let e : b ≃ Fin g := B.indexEquiv D
  have hex : ∀ k : Fin g, ∃ j, ψ j = ((e.symm k : b) : Module.Dual K (Fin g → K)) := fun k => hbsub (e.symm k).2
  choose c hc using hex
  refine ⟨c, ?_⟩
  have hM : (Matrix.of fun a k => φ (c k) (Pi.single a 1)) = D.toMatrix (B.reindex e) := by
    ext a k
    rw [Matrix.of_apply]
    change ψ (c k) (Pi.single a 1) = _
    rw [hc k]
    simp only [Module.Basis.toMatrix_apply, D, Module.Basis.dualBasis_repr,
      Module.Basis.reindex_apply, B, Module.Basis.mk_apply, Pi.basisFun_apply]
  rw [hM]
  intro h0
  have hone := congrArg Matrix.det (D.toMatrix_mul_toMatrix_flip (B.reindex e))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hone
  exact zero_ne_one hone

theorem top_le_preimage_finset_inf {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {κ : Type} (s : Finset κ) (W : κ → X.Opens)
    (h : ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ W i) : ⊤ ≤ x ⁻¹ᵁ (s.inf W) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ p _
    simp
  | @insert a s ha ih =>
    intro h p hp
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a s) hp, ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hp⟩

theorem fderiv_fn_resG {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    {X : Scheme.{0}} (m : A₀.left ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  have key : ∀ (y : Sp ℂ ⟶ X), ⊤ ≤ y ⁻¹ᵁ W' → valAt' y W' (resG X h f) = valAt' y W f := by
    intro y hy
    have hy2 : ⊤ ≤ y ⁻¹ᵁ W := hy.trans (fun q hq => h hq)
    unfold valAt'
    rw [dite_eq_left hy, dite_eq_left hy2]
    unfold valAt
    congr 1
    rw [← Scheme.Hom.map_appLE y hy (homOfLE h).op]
    rfl
  have hopen : IsOpen (dom u m W') := by
    exact (u.hol (m ⁻¹ᵁ W') 0).1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hopen.mem_nhds hz] with z' hz'
  exact key _ hz'

theorem exists_fibre_coords : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb z
  let J : Type := {Wf : (W : X.Opens) × Γ(X, W) // z ∈ dom u m Wf.1}
  let φ : J → (Fin P₀.g → ℂ) →ₗ[ℂ] ℂ := fun j => (fderiv ℂ (fn u m j.1.1 j.1.2) z).toLinearMap
  have hker : ∀ w, (∀ j, φ j w = 0) → w = 0 := by
    intro w hw
    have hδ : PtDer ((u.ex z).left ≫ m) (fun _ _ => (0 : ℂ)) :=
      ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
    obtain ⟨w₀, _, huniq⟩ := _root_.GlobalTheory.KS.VertFamily.existsUnique_vector P₀ u Hm χ hG R x₀ X p m hsm hpb z (fun _ _ => 0) hδ (fun _ => rfl)
    have e1 : w = w₀ := huniq w (fun W f hzW => (hw ⟨⟨W, f⟩, hzW⟩).symm)
    have e2 : (0 : Fin P₀.g → ℂ) = w₀ := huniq 0 (fun W f _ => (ContinuousLinearMap.map_zero _).symm)
    exact e1.trans e2.symm
  obtain ⟨c, hc⟩ := exists_det_ne_zero_of_common_ker φ hker
  have hzW : z ∈ dom u m (Finset.univ.inf fun b => (c b).1.1) :=
    top_le_preimage_finset_inf ((u.ex z).left ≫ m) Finset.univ (fun b => (c b).1.1) (fun b _ => (c b).2)
  refine ⟨Finset.univ.inf fun b => (c b).1.1,
    fun b => resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2, hzW, ?_⟩
  have hE : (Matrix.of fun a b => fderiv ℂ (fn u m (Finset.univ.inf fun b => (c b).1.1)
      (resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2)) z (Pi.single a 1)) =
      Matrix.of fun a b => φ (c b) (Pi.single a 1) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [fderiv_fn_resG u m (Finset.inf_le (Finset.mem_univ b)) (c b).1.2 hzW]
    rfl
  rw [hE]
  exact hc

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGrpObjOfLocalGroupLawsOnCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_grpObj_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by
  intro S I U A G _ ψ m n e hU hpb hgrp hone

  have hl : ∀ i (T' : Over (U i).toScheme) (a : Over.mk (T'.hom ≫ (U i).ι) ⟶ A),
      ∃ x : T' ⟶ G i, a.left = x.left ≫ ψ i :=
    fun i _ a => GlobalTheory.CoverGlue.exists_lift (hpb i) a
  have hm : ∀ i (T' : Over (U i).toScheme) (a b : Over.mk (T'.hom ≫ (U i).ι) ⟶ A) (x y : T' ⟶ G i),
      a.left = x.left ≫ ψ i → b.left = y.left ≫ ψ i → (lift a b ≫ m).left = (x * y).left ≫ ψ i :=
    fun i T' a b x y ha hb => (hgrp i T' x y a b ha hb).1
  have hn : ∀ i (T' : Over (U i).toScheme) (a b : Over.mk (T'.hom ≫ (U i).ι) ⟶ A) (x y : T' ⟶ G i),
      a.left = x.left ≫ ψ i → b.left = y.left ≫ ψ i → (lift a b ≫ n).left = (x⁻¹).left ≫ ψ i :=
    fun i T' a b x y ha hb => (hgrp i T' x y a b ha hb).2
  obtain ⟨e', he'⟩ : ∃ e' : 𝟙_ (Over S) ⟶ A, e' = e := ⟨e, rfl⟩
  subst he'

  have h1 : ∀ i (T' : Over (U i).toScheme) (p : Over.mk (T'.hom ≫ (U i).ι) ⟶ 𝟙_ (Over S)),
      (p ≫ e').left = (1 : T' ⟶ G i).left ≫ ψ i := by
    intro i T' p
    have hp : p.left = T'.hom ≫ (U i).ι := by
      have h := Over.w p
      first | simpa using h | simpa [Over.tensorUnit_hom] using h | exact (Category.comp_id _).symm.trans h
    have hT : (toUnit T').left = T'.hom := by
      have h := Over.w (toUnit T')
      first | simpa using h | simpa [Over.tensorUnit_hom] using h | exact (Category.comp_id _).symm.trans h
    have h1' : (1 : T' ⟶ G i) = toUnit T' ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i) := by
      rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc]
      first | exact congrArg (· ≫ _) (toUnit_unique _ _) | (congr 1; exact toUnit_unique _ _)
    rw [h1']
    first
      | (rw [Over.comp_left, Over.comp_left, Category.assoc, hone i, hp, hT, Category.assoc])
      | (simp only [Over.comp_left, Category.assoc, hone i, hp, hT])
  have ax1 : e' ▷ A ≫ m = (λ_ A).hom := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨p, c, rfl⟩ : ∃ p c, r = lift p c := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerRight_assoc, leftUnitor_hom, lift_snd]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ 1 z (h1 i T' p) hz, _root_.one_mul, hz]
  have ax2 : A ◁ e' ≫ m = (ρ_ A).hom := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨c, p, rfl⟩ : ∃ c p, r = lift c p := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerLeft_assoc, rightUnitor_hom, lift_fst]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z 1 hz (h1 i T' p), _root_.mul_one, hz]
  have ax3 : m ▷ A ≫ m = (α_ A A A).hom ≫ A ◁ m ≫ m := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨q, c, rfl⟩ : ∃ q c, r = lift q c := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, q = lift a b := ⟨_, _, (lift_comp_fst_snd q).symm⟩
    obtain ⟨x, hx⟩ := hl i T' a
    obtain ⟨y, hy⟩ := hl i T' b
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ (x * y) z (hm i T' a b x y hx hy) hz,
      hm i T' _ _ x (y * z) hx (hm i T' b c y z hy hz), _root_.mul_assoc]
  have ax4 : lift (lift (𝟙 A) (𝟙 A) ≫ n) (𝟙 A) ≫ m = toUnit A ≫ e' := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨z, hz⟩ := hl i T' r
    simp only [comp_lift_assoc, Category.comp_id]
    rw [← Category.assoc r (toUnit A) e']
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z⁻¹ z (hn i T' r r z z hz hz) hz, _root_.inv_mul_cancel, h1 i T' (r ≫ toUnit A)]
  have ax5 : lift (𝟙 A) (lift (𝟙 A) (𝟙 A) ≫ n) ≫ m = toUnit A ≫ e' := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨z, hz⟩ := hl i T' r
    simp only [comp_lift_assoc, comp_lift, Category.comp_id]
    rw [← Category.assoc r (toUnit A) e']
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z z⁻¹ hz (hn i T' r r z z hz hz), _root_.mul_inv_cancel, h1 i T' (r ≫ toUnit A)]
  let inst : GrpObj A :=
    { one := e', mul := m, inv := lift (𝟙 A) (𝟙 A) ≫ n,
      one_mul := ax1, mul_one := ax2, mul_assoc := ax3, left_inv := ax4, right_inv := ax5 }
  refine ⟨inst, fun i => ⟨hpb i, fun T x y x₀ y₀ hx hy => ?_⟩⟩
  rw [CategoryTheory.Hom.mul_def]
  exact hm i T x₀ y₀ x y hx hy

end GlobalTheory.CoverGlue
end

