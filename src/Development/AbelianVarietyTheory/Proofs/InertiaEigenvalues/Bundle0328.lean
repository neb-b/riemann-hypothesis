module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualLatticeSetting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem repIso_of_zIdem_eq_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (h : Simple τ) (h' : Simple τ') (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := by
  classical
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hco : ∀ γ, (Module.finrank ℂ τ : ℂ) * τ.character γ
      = (Module.finrank ℂ τ' : ℂ) * τ'.character γ := by
    intro γ
    have h1 := congrArg (fun z => z.coeff γ⁻¹) he
    simp only [zIdem_coeff, inv_inv] at h1
    have h2 := congrArg (fun x => (Fintype.card Γ : ℂ) * x) h1
    simp only [div_mul_eq_mul_div, mul_div_cancel₀ _ hc0, mul_div_assoc'] at h2
    simpa [FDRep.character, mul_div_cancel_left₀ _ hc0] using h2
  have hd : Module.finrank ℂ τ = Module.finrank ℂ τ' := by
    have h1 := hco 1
    rw [FDRep.char_one, FDRep.char_one] at h1
    have h2 : Module.finrank ℂ τ * Module.finrank ℂ τ
        = Module.finrank ℂ τ' * Module.finrank ℂ τ' := by exact_mod_cast h1
    exact Nat.mul_self_inj.1 h2
  have hs0 := FDRep.char_orthonormal τ τ
  rw [if_pos ⟨Iso.refl _⟩] at hs0
  have hpos : (Module.finrank ℂ τ : ℂ) ≠ 0 := by
    intro h0
    have h1 : Module.finrank ℂ τ = 0 := by exact_mod_cast h0
    have : Subsingleton τ := Module.finrank_zero_iff.1 h1
    have hz : ∀ g, τ.character g = 0 := fun g => by
      have : τ.ρ g = 0 := Subsingleton.elim _ _
      simp [FDRep.character, this]
    simp [hz] at hs0
  have hch : ∀ γ, τ'.character γ = τ.character γ := fun γ => by
    have h1 := hco γ
    rw [← hd] at h1
    exact (mul_left_cancel₀ hpos h1).symm
  have hs := FDRep.char_orthonormal τ τ'
  simp only [hch] at hs
  rw [hs0] at hs
  have hne : Nonempty (τ ≅ τ') := by
    by_contra hn
    rw [if_neg hn] at hs
    exact one_ne_zero hs
  obtain ⟨i⟩ := hne
  refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
  rw [FDRep.Iso.conj_ρ i γ]
  simp [LinearEquiv.conj_apply]

end GlobalTheory.SerOSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Colim

section General

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  [TopologicalSpace Γ] {B : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]

theorem exists_fg_cocycle [CompactSpace Γ] (z : Z1 (repOn ρ κ B)) :
    ∃ B' : Submodule Λ B, B'.FG ∧ ∃ z' : Z1 (repOn ρ κ B'), ∀ g a, ((z'.1 g a : B') : B) = z.1 g a := by
  have hfin : (Set.range fun p : Γ × Fin r => z.1 p.1 p.2).Finite := by
    have hc : Continuous fun p : Γ × Fin r => z.1 p.1 p.2 :=
      continuous_prod_of_discrete_right.2 fun a => (continuous_apply a).comp z.2.1
    exact (isCompact_range hc).finite_of_discrete
  refine ⟨Submodule.span Λ _, Submodule.fg_span hfin, ⟨fun g a => ⟨z.1 g a, Submodule.subset_span ⟨(g, a), rfl⟩⟩,
    continuous_pi fun a => ((continuous_apply a).comp z.2.1).subtype_mk _, fun g h => ?_⟩, fun g a => rfl⟩
  funext a
  apply Subtype.ext
  have e := congrFun (repOn_map ρ κ (Submodule.span Λ (Set.range fun p : Γ × Fin r => z.1 p.1 p.2)).subtype g
    (fun a => ⟨z.1 h a, Submodule.subset_span ⟨(h, a), rfl⟩⟩)) a
  have e2 := congrFun (z.2.2 g h) a
  exact e2.trans (congrArg (z.1 g a + ·) e.symm)

omit [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] in
theorem repOn_eq_of_eq_one {g : Γ} (h1 : ρ g = 1) (h2 : κ g = 1) (m : Fin r → B) : repOn ρ κ B g m = m := by
  have : repOn ρ κ B g = repOn ρ κ B 1 := by simp [repOn, h1, h2]
  rw [this, map_one, Module.End.one_apply]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tgl_eq_one (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) (v : PlE D.host)
    (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (A : ValuationSubring N.Om) (hA : IsPlaceOver A v)
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) A) : Tgl i s σ = 1 := by
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have hp : v ∉ X.pD i := fun hk => hS ⟨Or.inr hk, hl⟩
  have h1 : X.rhoS i s σ = 1 := h.1 v hl hg A hA σ hσ
  have h2 : chiS i s σ = 1 := X.twistCharacterFamily_unramified i _ _ v hl hg hp A hA σ hσ
  simp [Tgl, twGL, h1, h2]

theorem selColim : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → SelColim bkP i s κ Q := by
  intro D N X bkP i s Λ _ _ _ κ Q hSet _ hSat B _ _ _ _ hB y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨B', hfg, z', hz⟩ := exists_fg_cocycle (Tgl i s) κ z
  have hmap : h1Map (Tgl i s) κ B'.subtype (Submodule.Quotient.mk z') = Submodule.Quotient.mk z :=
    congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => hz g a))
  refine ⟨B', hfg, Submodule.Quotient.mk z', ?_, hmap⟩
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hy v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with hl hS
  · refine hSat v hl B' B hB B'.subtype B'.injective_subtype _ ?_
    rw [← hmap] at hv
    exact hv
  · trivial
  · have hS1 : v ∉ Spl i := fun h => hS (Or.inl h)
    have hQ : v ∉ Q := fun h => hS (Or.inr h)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hv)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => ?_⟩)
    have hg : (g.1.1 : GE N) ∈ Ine (F := D.host.E) (N.plOm.1 v) := g.2
    have e : z.1 g.1.1 = repOn (Tgl i s) κ B g.1.1 m - m := hm g
    rw [repOn_eq_of_eq_one _ _ (tgl_eq_one bkP i s hSet.1.1 v hl hS1 _ (N.plOm.2 v) _ hg)
      (hSet.2.2.2.2.2.2.2 v hQ _ (N.plOm.2 v) _ hg), sub_self] at e
    show z'.1 g.1.1 = repOn (Tgl i s) κ B' g.1.1 0 - 0
    rw [LinearMap.map_zero, sub_zero]
    funext a
    apply Subtype.ext
    exact (hz g.1.1 a).trans (congrFun e a)

end GlobalTheory.SelFun.Colim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerIffSelmerMatrixAtPrimes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

namespace GlobalTheory.SelMatrixCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem l_mem_maximalIdeal (i : X.Tw) : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem maxLam_le (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (m : Ideal (abelian₂ X i M ι)) [hm : m.IsMaximal] :
    maxLam X i M ι ≤ m := by
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h0 : (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ m := by
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap (X.O0 i) (abelian₂ X i M ι))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := X.O0 i) m
    exact (IsLocalRing.eq_maximalIdeal this).ge
  refine sup_le h0 ?_
  rw [Ideal.span_le]
  rintro _ ⟨q, rfl⟩
  have hl : ((X.l i : ℕ) : abelian₂ X i M ι) ∈ m := by
    have h := Ideal.mem_map_of_mem (algebraMap (X.O0 i) (abelian₂ X i M ι)) (l_mem_maximalIdeal X i)
    rw [map_natCast] at h
    exact h0 h
  have : Nontrivial (abelian₂ X i M ι ⧸ m) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
  have : CharP (abelian₂ X i M ι ⧸ m) (X.l i) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk m)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hl
  have hg : (Multiplicative.ofAdd (Pi.single q 1) : Del X i M ι) ^ (X.l i ^ M) = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, toAdd_one, Pi.zero_apply]
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine hm.isPrime.mem_of_pow_mem (X.l i ^ M) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  simp only [toLam, MvPolynomial.aeval_X, map_sub, map_one]
  rw [sub_pow_char_pow, ← map_pow, ← map_pow]
  rw [one_pow, sub_eq_zero]
  convert map_one (Ideal.Quotient.mk m) using 2
  convert map_one (MonoidAlgebra.of (X.O0 i) (Del X i M ι)) using 2

theorem exists_const (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    ∃ c : X.O0 i, x - algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι := by
  obtain ⟨F, rfl⟩ := toLam_surjective X i M ι x
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨a, by rw [MvPolynomial.algHom_C, sub_self]; exact zero_mem _⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := add_mem ha hb
    rw [map_add (f := _), map_add (f := _)]
    convert this using 1
    ring
  | mul_X p q _ =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))

theorem mem_maxLam_iff (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    x ∈ maxLam X i M ι ↔ ¬ IsUnit x := by
  refine ⟨fun hx hu => maxLam_ne_top X i M ι (Ideal.eq_top_of_isUnit_mem _ hx hu), fun hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  obtain ⟨c, hc⟩ := exists_const X i M ι x
  have h1 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ m := by
    have := sub_mem hxm (maxLam_le X i M ι m hc)
    rwa [sub_sub_cancel] at this
  have h2 : c ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map _))
  have h3 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι :=
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h2)
  have := add_mem hc h3
  rwa [sub_add_cancel] at this

theorem maxLam_isMaximal (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : (maxLam X i M ι).IsMaximal := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (maxLam_ne_top X i M ι)
  have : maxLam X i M ι = m := le_antisymm hle fun x hx =>
    (mem_maxLam_iff X i M ι x).2 fun hu => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  rwa [this]

variable {X} (bkP : BKPh X)

end GlobalTheory.SelMatrixCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
section
open Formalism.IrreducibleCountingLemmas.TYPES (zIdem)
open Formalism.L2.NT
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem zIdem_eq_charIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

theorem zIdem_centralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ →
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  intro Γ _ _ τ hτ
  have h := orthogonalCentral Γ τ τ hτ hτ
  rw [zIdem_eq_charIdem]
  exact ⟨h.2.2.1, h.2.2.2.1⟩

end GlobalTheory.SerOSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNe
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem nontrivial_of_simpleRep {Γ : Type} [Group Γ] [Fintype Γ] (V : FDRep ℂ Γ) (h : Simple V) :
    Nontrivial V := by
  rw [FDRep.simple_iff_char_is_norm_one] at h
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ g, V.character g = 0 := fun g => by
    rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
  simp only [h0, mul_zero, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card Γ : ℂ) ≠ 0) h.symm

theorem invariant_eq_bot_or_top_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ)
    [Simple τ] (U : Submodule ℂ τ) (hU : ∀ g, ∀ x ∈ U, τ.ρ g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let A : Subrepresentation τ.ρ := ⟨U, fun g v hv => hU g v hv⟩
  let X : FDRep ℂ Γ := FDRep.of A.toRepresentation
  let i : X ⟶ τ := ⟨InducedCategory.homMk (ModuleCat.ofHom U.subtype), fun g => by
    ext1; ext x; rfl⟩
  have hinj : Function.Injective ⇑(ConcreteCategory.hom i) := by
    intro x y h; exact Subtype.ext h
  have : Mono i := ConcreteCategory.mono_of_injective i hinj
  by_cases h0 : i = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := congrArg (fun f : X ⟶ τ => ConcreteCategory.hom f ⟨x, hx⟩) h0
    have h1 : ConcreteCategory.hom i ⟨x, hx⟩ = x := rfl
    have h2 : ConcreteCategory.hom (0 : X ⟶ τ) ⟨x, hx⟩ = 0 := rfl
    simp only [h1, h2] at this
    exact this
  · right
    have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 h0
    apply Submodule.eq_top_of_finrank_eq
    exact (FDRep.isoToLinearEquiv (asIso i)).finrank_eq

theorem zIdem_eq_of_linearEquiv {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) : zIdem τ = zIdem τ' := by
  apply MonoidAlgebra.ext
  ext γ
  rw [zIdem_coeff, zIdem_coeff, φ.finrank_eq]
  have h : τ'.ρ γ⁻¹ = φ.conj (τ.ρ γ⁻¹) := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp [hφ]
  rw [h, LinearMap.trace_conj']

theorem zIdem_eq_centralIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ),
    Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  intro Γ _ _ τ τ' hτ hτ' hne
  haveI := nontrivial_of_simpleRep τ hτ
  haveI := nontrivial_of_simpleRep τ' hτ'
  rw [zIdem_eq_centralIdem, zIdem_eq_centralIdem]
  exact Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_orthogonal Γ τ τ' τ.ρ τ'.ρ
    (invariant_eq_bot_or_top_of_simple τ) (invariant_eq_bot_or_top_of_simple τ')
    (by rintro ⟨φ, hφ⟩; exact hne (zIdem_eq_of_linearEquiv τ τ' φ hφ))

end GlobalTheory.SerOSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanQ
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.InvLine

theorem spanQ : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0) := by
  intro hT l _ P K
  obtain ⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩ := GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT l P K
  obtain ⟨⟨hcc, hcoc⟩, hsp⟩ := GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental l ↥(GK K) χ c hχc hgen hfin
  have hcyc : ∀ g, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχ]; rfl
  refine ⟨fun p => (c p : ℚ_[l]), ⟨hcc, fun g h k => by rw [hcyc]; exact hcoc g h k⟩, fun z hz hzc => ?_⟩
  obtain ⟨x, f, hf, hfd⟩ := hsp z hz (fun g h k => by rw [← hcyc]; exact hzc g h k)
  refine ⟨x, f, hf, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have e := hfd g h
  rw [← hcyc] at e
  simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← e]
  simp [charRep]

theorem exists_inv : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ (Z : Submodule LL (↥(GK K) × ↥(GK K) → LL)) (inv : ↥Z →ₗ[LL] LL), (∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) ∧ ∀ z : ↥Z, inv z = 0 ↔ CobL (P.PD K) z.1 := by
  intro hT l _ P K LL _ _ _ O _ _ hO
  obtain ⟨z0, ⟨hz0c, hz0⟩, hspan⟩ := GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension l P K LL O hO (spanQ hT l P K)
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let Z : Submodule LL (↥(GK K) × ↥(GK K) → LL) :=
    { carrier := {z | Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g h k => by
        have e1 := ha.2 g h k
        have e2 := hb.2 g h k
        simp only [Pi.add_apply]
        linear_combination e1 + e2⟩
      zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun g h k => by
        have e1 := ha.2 g h k
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * e1⟩ }
  have hZ : ∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0 := fun z => Iff.rfl
  let B : Submodule LL ↥Z :=
    { carrier := {z | CobL (P.PD K) z.1}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨f1, hf1, e1⟩ := ha
        obtain ⟨f2, hf2, e2⟩ := hb
        exact ⟨f1 + f2, hf1.add hf2, by rw [map_add (f := _), e1, e2]; rfl⟩
      zero_mem' := ⟨0, continuous_const, by rw [map_zero]; rfl⟩
      smul_mem' := fun c a ha => by
        obtain ⟨f1, hf1, e1⟩ := ha
        exact ⟨c • f1, hf1.const_smul c, by rw [map_smul, e1]; rfl⟩ }
  have hB : ∀ z : ↥Z, z ∈ B ↔ CobL (P.PD K) z.1 := fun z => Iff.rfl
  let z0' : ↥Z := ⟨z0, hz0c, hz0⟩
  have hQ : ∀ z : ↥Z, ∃ x : LL, B.mkQ z = x • B.mkQ z0' := by
    intro z
    obtain ⟨x, hx⟩ := hspan z.1 z.2.1 z.2.2
    refine ⟨x, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨Z, ?_⟩
  by_cases h0 : B.mkQ z0' = 0
  · refine ⟨0, hZ, fun z => ?_⟩
    obtain ⟨x, hx⟩ := hQ z
    rw [h0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    simp only [LinearMap.zero_apply, true_iff]
    exact hx
  · have htop : Submodule.span LL {B.mkQ z0'} = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨z, rfl⟩ := B.mkQ_surjective q
      obtain ⟨x, hx⟩ := hQ z
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    let φ := LinearEquiv.toSpanNonzeroSingleton LL _ _ h0
    let inv : ↥Z →ₗ[LL] LL :=
      (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap).comp B.mkQ
    have hinj : Function.Injective (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap) :=
      φ.symm.injective.comp (LinearEquiv.ofTop _ htop).symm.injective
    refine ⟨inv, hZ, fun z => ?_⟩
    have e1 : inv z = 0 ↔ B.mkQ z = 0 :=
      (injective_iff_map_eq_zero' _).1 hinj (B.mkQ z)
    rw [e1, ← hB, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end GlobalTheory.InvLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleFundamentalMultipleModPowStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  first | exact @GlobalTheory.UnifSpan.span_mod_pow | exact GlobalTheory.UnifSpan.span_mod_pow | (intros; apply GlobalTheory.UnifSpan.span_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleMemCoboundariesOfModUniformizerPowStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  first | exact @GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | exact GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | (intros; apply GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem <;> assumption)
end

