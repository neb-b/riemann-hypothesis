module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0019

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

abbrev Ix (E : Type) [Field E] [NumberField E] (n : ℕ) : Type := Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E)

def dl {E : Type} [Field E] [NumberField E] {n : ℕ} (m : Ix E n) : Fin n → 𝓞 E :=
  Pi.single m.1 (RingOfIntegers.basis E m.2)

def mkN {E : Type} [Field E] [NumberField E] {n : ℕ} (p : ℕ) (x : Fin n → 𝓞 E) : TestPt.NAdd E n p :=
  fun i => Ideal.Quotient.mk _ (x i)

def toRC {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (h : ∀ a ∈ R, algebraMap Ω C a ∈ RC) : R →+* RC :=
  ((algebraMap Ω C).comp (R.val : R →+* Ω)).codRestrict RC fun a => h a a.2

def IsDerAt0 {C R W N : Type} [Field C] [CommRing R] [Algebra R C] [AddCommGroup W] [Module R W] [AddCommGroup N]
    (M : Submodule R (N → C)) (Dv : M →ₗ[R] W) : Prop :=
  ∀ (f g h : M) (a b : R), (h : N → C) = (f : N → C) * (g : N → C) → algebraMap R C a = (f : N → C) 0 →
    algebraMap R C b = (g : N → C) 0 → Dv h = a • Dv g + b • Dv f

end PositivityTheory.Xgn.TestGroupPoint
end
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceProjectionExists
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceProjection

section Loc

variable {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
  {V : Type} [AddCommGroup V] [Module Ω V] [Module R V] [IsScalarTower R Ω V]

def locAt (Ω : Type) [Field Ω] [Algebra R Ω] (𝔮 : Ideal R) [h : 𝔮.IsPrime] : Subalgebra R Ω where
  carrier := {x | ∃ u v : R, v ∉ 𝔮 ∧ x * algebraMap R Ω v = algebraMap R Ω u}
  mul_mem' := by
    rintro a b ⟨u, v, hv, e⟩ ⟨u', v', hv', e'⟩
    refine ⟨u * u', v * v', fun hh => (h.mem_or_mem hh).elim hv hv', ?_⟩
    rw [map_mul, map_mul, ← e, ← e']; ring
  add_mem' := by
    rintro a b ⟨u, v, hv, e⟩ ⟨u', v', hv', e'⟩
    refine ⟨u * v' + u' * v, v * v', fun hh => (h.mem_or_mem hh).elim hv hv', ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_mul, ← e, ← e']; ring
  algebraMap_mem' := fun r => ⟨r, 1, (Ideal.ne_top_iff_one 𝔮).1 h.ne_top, by simp⟩

theorem inv_mem (hinj : Function.Injective (algebraMap R Ω)) (𝔮 : Ideal R) [h : 𝔮.IsPrime] {v : R} (hv : v ∉ 𝔮) :
    algebraMap R Ω v ≠ 0 ∧ (algebraMap R Ω v)⁻¹ ∈ locAt Ω 𝔮 := by
  have h0 : algebraMap R Ω v ≠ 0 := fun e => hv (by
    have : v = 0 := hinj (by rw [e, map_zero])
    rw [this]; exact 𝔮.zero_mem)
  exact ⟨h0, 1, v, hv, by rw [inv_mul_cancel₀ h0, map_one]⟩

theorem isLoc (hinj : Function.Injective (algebraMap R Ω)) (𝔮 : Ideal R) [h : 𝔮.IsPrime] :
    IsLocalization.AtPrime (locAt Ω 𝔮) 𝔮 := by
  refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun z => ?_, fun {x y} e => ?_⟩
  · obtain ⟨h0, h1⟩ := inv_mem hinj 𝔮 y.2
    exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  · obtain ⟨u, v, hv, e⟩ := z.2
    exact ⟨(u, ⟨v, hv⟩), Subtype.ext e⟩
  · have : x = y := hinj (congrArg Subtype.val e)
    exact ⟨1, by rw [this]⟩

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
theorem proj_transfer {R M Rp Mp : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing Rp] [Algebra R Rp]
    [AddCommGroup Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp] (S : Submonoid R) [IsLocalization S Rp]
    (f : M →ₗ[R] Mp) [IsLocalizedModule S f] (h : Module.Projective Rp Mp) :
    Module.Projective (Localization S) (LocalizedModule S M) := by
  letI : Algebra Rp (Localization S) := (IsLocalization.algEquiv S Rp (Localization S)).toRingHom.toAlgebra
  haveI : IsScalarTower R Rp (Localization S) :=
    IsScalarTower.of_algebraMap_eq fun r => ((IsLocalization.algEquiv S Rp (Localization S)).commutes r).symm
  letI : Module (Localization S) Mp := Module.compHom Mp (IsLocalization.algEquiv S Rp (Localization S)).symm.toRingHom
  haveI : IsScalarTower R (Localization S) Mp := IsScalarTower.of_algebraMap_smul fun r x => by
    change (IsLocalization.algEquiv S Rp (Localization S)).symm (algebraMap R _ r) • x = r • x
    rw [AlgEquiv.commutes, algebraMap_smul]
  haveI : Module.Projective (Localization S) Mp :=
    Module.Projective.of_equiv (M := Mp) (R := Rp) (σ := (IsLocalization.algEquiv S Rp (Localization S)).toRingEquiv)
      { __ := AddEquiv.refl Mp
        map_smul' := fun r x => by
          change r • x = (IsLocalization.algEquiv S Rp (Localization S)).symm
            (IsLocalization.algEquiv S Rp (Localization S) r) • x
          rw [AlgEquiv.symm_apply_apply] }
  exact Module.Projective.of_equiv
    ((IsLocalizedModule.iso S f).symm.extendScalarsOfIsLocalization S (Localization S))

theorem proj_of_loc [IsNoetherianRing R] (hinj : Function.Injective (algebraMap R Ω)) (M : Submodule R V) (hM : M.FG)
    (H : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], Module.Projective (locAt Ω 𝔮) (Submodule.span (locAt Ω 𝔮) (M : Set V))) :
    Module.Projective R M := by
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 hM
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  refine Module.projective_of_localization_maximal fun P hP => ?_
  haveI : IsLocalization.AtPrime (locAt Ω P) P := isLoc hinj P
  haveI : IsLocalizedModule P.primeCompl (LinearMap.id : V →ₗ[R] V) :=
    isLocalizedModule_id P.primeCompl V (locAt Ω P)
  refine proj_transfer P.primeCompl (Rp := locAt Ω P) (M.toLocalized' (locAt Ω P) P.primeCompl LinearMap.id) ?_
  have h := H P
  have e : Submodule.span (locAt Ω P) (M : Set V) = M.localized' (locAt Ω P) P.primeCompl LinearMap.id := by
    rw [Submodule.localized'_eq_span]; simp
  rw [e] at h
  exact h

theorem loc_of_proj (hinj : Function.Injective (algebraMap R Ω)) (M : Submodule R V) [Module.Projective R M]
    (P : Ideal R) [P.IsPrime] : Module.Projective (locAt Ω P) (Submodule.span (locAt Ω P) (M : Set V)) := by
  haveI : IsLocalization.AtPrime (locAt Ω P) P := isLoc hinj P
  haveI : IsLocalizedModule P.primeCompl (LinearMap.id : V →ₗ[R] V) :=
    isLocalizedModule_id P.primeCompl V (locAt Ω P)
  have e : Submodule.span (locAt Ω P) (M : Set V) = M.localized' (locAt Ω P) P.primeCompl LinearMap.id := by
    rw [Submodule.localized'_eq_span]; simp
  rw [e]
  exact Module.projective_of_isLocalizedModule P.primeCompl (M.toLocalized' (locAt Ω P) P.primeCompl LinearMap.id)

omit [Module R V] [IsScalarTower R Ω V] in
theorem proj_of_frame (B : Subring Ω) (S : Subalgebra R Ω) (hB : ∀ x, x ∈ B ↔ x ∈ S) (M : Set V) {r : ℕ}
    (b : Fin r → V) (hb : LinearIndependent Ω b) (e : Submodule.span B (Set.range b) = Submodule.span B M) :
    Module.Projective S (Submodule.span S M) := by
  have hBS : B = S.toSubring := Subring.ext hB
  subst hBS
  have e' : Submodule.span S (Set.range b) = Submodule.span S M := e
  rw [← e']
  have hb' : LinearIndependent S b := hb.restrict_scalars' S
  haveI := Module.Free.of_basis (Module.Basis.span hb')
  infer_instance

end Loc

section Chart

open GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  (D : HTChart A K c p R N V)

theorem pow_mem {x : V} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩; exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩; exact D.om.smul_mem _ hx

theorem om'_stable (a : 𝓞 E) {x : V} (hx : x ∈ D.om') : D.ρΩ a x ∈ D.om' := by
  have : D.om' ≤ D.om'.comap ((D.ρΩ a).restrictScalars A) := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, hw, e⟩ := D.h_lin a z
      have e' : D.ρΩ a (D.h z) = D.h (a • z) - ((p : A) ^ R) • w := by
        rw [e, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; abel
      change D.ρΩ a (D.h z) ∈ D.om'
      rw [e']
      exact D.om'.sub_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)) (pow_mem D hw)
    · rintro _ ⟨z, hz, rfl⟩
      change D.ρΩ a (((p : A) ^ R) • z) ∈ D.om'
      rw [LinearMap.map_smul_of_tower]
      exact pow_mem D (D.om_stable a z hz)
  exact this hx

theorem omHT_proj (σ : E →+* K) (hσ : ∀ k, ∃ a : A, algebraMap A K a = σ (dualInt E k))
    [Module.Projective A D.om'] : Module.Projective A (D.omHT σ) := by
  have hle : D.omHT σ ≤ D.om' := by
    rintro _ ⟨x, hx, rfl⟩
    change eigProj D.ρΩ σ x ∈ D.om'
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨a, ha⟩ := hσ k
    rw [← ha, algebraMap_smul]
    exact D.om'.smul_mem a (om'_stable D _ hx)
  refine Module.Projective.of_split (Submodule.inclusion hle)
    (((eigProj D.ρΩ σ).restrictScalars A).restrict (p := D.om') (q := D.omHT σ) fun x hx => ⟨x, hx, rfl⟩) ?_
  ext z
  exact LatBasic.eigProj_of_mem (LatBasic.eigQuot_le_eigSp D.ρΩ σ D.om' z.2)

theorem span_eq_of_notMem (hinj : Function.Injective (algebraMap A K)) (𝔮 : Ideal A) [h : 𝔮.IsPrime]
    (hp : (p : A) ∉ 𝔮) :
    Submodule.span (locAt K 𝔮) (D.om' : Set V) = Submodule.span (locAt K 𝔮) (D.om : Set V) := by
  refine le_antisymm (Submodule.span_mono (om'_le D)) (Submodule.span_le.2 fun x hx => ?_)
  obtain ⟨h0, h1⟩ := inv_mem hinj 𝔮 (v := (p : A) ^ R) fun hh => hp (h.mem_of_pow_mem _ hh)
  have h2 := Submodule.smul_mem (Submodule.span (locAt K 𝔮) (D.om' : Set V)) ⟨_, h1⟩
    (Submodule.subset_span (pow_mem D hx))
  have e : (⟨_, h1⟩ : locAt K 𝔮) • ((p : A) ^ R) • x = x := by
    change (algebraMap A K ((p : A) ^ R))⁻¹ • ((p : A) ^ R) • x = x
    rw [← algebraMap_smul K ((p : A) ^ R) x, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [e] at h2
  exact h2

end Chart

end PositivityTheory.Xgn.SequenceProjection

open PositivityTheory.Xgn.SequenceProjection in
theorem PositivityTheory.Xgn.sequence_projection_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), IsNoetherianRing (CR O y c') → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → Module.Projective (CR O y c') P.Dh.om' ∧ ∀ t : CMType H ⊕ CMType H, ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) → Module.Projective (CR O y c') (P.Dh.omHT σ) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ hfree hp A _ _ _ m _ hm O _ _ _ _ _ _ _ G c' _ P
    hN hpt hloc
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have h1 : Module.Projective (CR O y c') P.Dh.om' := by
    refine proj_of_loc hinj _ (by
      haveI := isNoetherian_of_fg_of_noetherian _ P.Dh.om_lat.fg
      exact isNoetherian_submodule.1 this _ (om'_le P.Dh)) fun 𝔮 h𝔮 => ?_
    by_cases hq : (p : CR O y c') ∈ 𝔮
    · obtain ⟨q, hc, hO, hr⟩ := hpt 𝔮 h𝔮
      have hf : InFibre 𝔐.ξ p q := by
        rintro ⟨h0, -, hi⟩
        obtain ⟨u, v, hv, e⟩ := (hr _).1 hi
        apply hv
        have : v = (p : CR O y c') * u := by
          apply Subtype.ext
          have e1 : (((p : CR O y c') * u : CR O y c') : Ω) = (p : Ω) * (u : Ω) := by simp
          rw [e1, ← e, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
        rw [this]
        exact 𝔮.mul_mem_right _ hq
      obtain ⟨U, hU, b, -, hb⟩ := hfree.1 q hf
      obtain ⟨hli, hsp⟩ := hb q hf hU
      exact proj_of_frame (regAt 𝔐.ξ q) (locAt Ω 𝔮) hr _ b hli (hsp.symm.trans (hloc q hc hO))
    · rw [span_eq_of_notMem P.Dh hinj 𝔮 hq]
      haveI := P.Dh.om_proj
      exact loc_of_proj hinj _ 𝔮
  refine ⟨h1, fun t σ _ => omHT_proj P.Dh σ fun k => ?_⟩
  obtain ⟨hint, x, hx, o, ho⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hp A m hm O σ
  obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x hx k
  obtain ⟨o', ho'⟩ := hint z
  refine ⟨algebraMap O _ (o * o'), ?_⟩
  rw [← IsScalarTower.algebraMap_apply, map_mul, ho', hz, map_mul, ← _root_.mul_assoc, ho, _root_.one_mul]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestCharacterExists
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestCharacter

theorem emb_pow (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Fintype F] [CharP F p] [Field k]
    (f g : F →+* k) : ∃ n : ℕ, ∀ a, g a = f a ^ p ^ n := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra F k := f.toAlgebra
  letI : Algebra (ZMod p) k := (f.comp (algebraMap (ZMod p) F)).toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : F →ₐ[ZMod p] k :=
    { g with
      commutes' := fun r => by
        have : g.comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) k := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun this r }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 (g'.restrictNormal F)
  refine ⟨n, fun a => ?_⟩
  have h1 := g'.restrictNormal_commutes F a
  have h2 := DFunLike.congr_fun hn a
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h2
  rw [← h2, map_pow] at h1
  exact h1.symm

theorem eq_of_root {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (q : ℕ)
    (hq : (q : R) ∈ IsLocalRing.maximalIdeal R) {x y : R} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue R x = IsLocalRing.residue R y) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y q
  rw [hx, hy] at h1
  have h2 : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 :=
    mul_right_cancel₀ (sub_ne_zero.2 hne) (by rw [h1, _root_.one_mul])
  have h3 := congrArg (IsLocalRing.residue R) h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at h3
  simp only [map_mul, map_pow, h] at h3
  rw [geom_sum₂_self] at h3
  have h4 : ((q : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact hq
  rw [h4, zero_mul] at h3
  exact zero_ne_one h3

theorem fund {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) {x y z : R}
    (hx : x ^ p ^ n = x) (hy : y ^ p ^ n = y) (hz : z ^ p ^ n = z)
    (h : z - x - y ∈ IsLocalRing.maximalIdeal R) : z - x - y ∈ Ideal.span {(p : R)} := by
  set d := z - x - y with hd
  have hz' : z = (x + y) + d := by rw [hd]; ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (x + y) d n
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp x y n
  rw [← hz', hz, hs, hx, hy] at hr
  obtain ⟨m, hm⟩ : ∃ m, p ^ n = m + 2 := by
    have := Nat.one_lt_pow hn hp.one_lt
    exact ⟨p ^ n - 2, by omega⟩
  have hu : IsUnit (1 - d ^ (m + 1)) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact Ideal.pow_mem_of_mem (IsLocalRing.maximalIdeal R) h _ (Nat.succ_pos m)
  have h1 : d * (1 - d ^ (m + 1)) ∈ Ideal.span {(p : R)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨x * y * s + (x + y) * d * r, ?_⟩
    rw [hm] at hr
    linear_combination hd - hr
  exact (Ideal.mul_unit_mem_iff_mem _ hu).1 h1

theorem core (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) {F : Type} [Field F] [Fintype F] [CharP F p] {Sg : Type}
    (τ₀ : Sg) (φ' : Sg → Sg) (ρ : Sg → F →+* IsLocalRing.ResidueField R) (χ : Sg → F →*₀ R)
    (hχ : ∀ τ a, IsLocalRing.residue R (χ τ a) = ρ τ a) (hφ : ∀ τ a, ρ (φ' τ) a = ρ τ a ^ p) :
    ∃ (σ' : MulChar F R) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = (σ' ^ p ^ ee τ) a) ∧
      ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : ((Fintype.card F : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hn, Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hp _ n.pos
  have hroot : ∀ τ a, χ τ a ^ Fintype.card F = χ τ a := fun τ a => by
    rw [← map_pow, FiniteField.pow_card]
  choose ee hee using fun τ => emb_pow p (ρ τ₀) (ρ τ)
  let σ' : MulChar F R :=
    { (χ τ₀).toMonoidHom with
      map_nonunit' := fun a ha => by
        have : a = 0 := by simpa using ha
        subst this
        exact map_zero (χ τ₀) }
  have hσ : ∀ a, σ' a = χ τ₀ a := fun _ => rfl
  have key : ∀ τ a, χ τ a = (σ' ^ p ^ ee τ) a := fun τ a => by
    rw [MulChar.pow_apply' _ (pow_ne_zero _ hpp.ne_zero), hσ, ← map_pow]
    refine eq_of_root _ hq (hroot _ _) (hroot _ _) ?_
    rw [hχ, hχ, hee, map_pow]
  refine ⟨σ', ee, fun a b => ?_, key, fun τ => ?_⟩
  · rw [hσ, hσ, hσ]
    refine fund hpp n.ne_zero (hn ▸ hroot _ _) (hn ▸ hroot _ _) (hn ▸ hroot _ _) ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, hχ, hχ, hχ, map_add (f := _)]
    ring
  · ext a
    rw [← key, pow_succ, pow_mul, MulChar.pow_apply' _ hpp.ne_zero, ← key, ← map_pow]
    refine eq_of_root _ hq (hroot _ _) (hroot _ _) ?_
    rw [hχ, hχ, hφ, map_pow]

theorem overC (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [Field C] [Algebra O C]
    (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (hvp : v (p : C) < 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] {Sg : Type}
    (τ₀ : Sg) (φ' : Sg → Sg) (σ : Sg → F →+* IsLocalRing.ResidueField O) (χ : Sg → F →*₀ C)
    (hχ : ∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
      χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1)
    (hφ : ∀ τ a, σ (φ' τ) a = σ τ a ^ p) :
    ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧
      (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  have hunit : ∀ a : RC, v (a : C) = 1 → IsUnit a := fun a ha => by
    have h0 : (a : C) ≠ 0 := by
      intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
    refine IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, (hv _).2 (by rw [map_inv₀, ha, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  haveI : IsLocalRing RC := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases ((hv _).1 a.2).eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · exact Or.inr (hunit _ (v.map_one_sub_of_lt h))
  have hnu : ∀ x : RC, (∀ u ∈ RC, u * (x : C) ≠ 1) → x ∈ IsLocalRing.maximalIdeal RC := fun x hx hu => by
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    exact hx u u.2 (congrArg Subtype.val hu)
  have hp : (p : RC) ∈ IsLocalRing.maximalIdeal RC := hnu _ fun u hu h => by
    have h1 := congrArg v h
    rw [map_mul, map_one] at h1
    have h2 : v u * v ((p : RC) : C) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 hu) zero_le (by simpa using hvp)
    exact h2.ne h1
  have hmem : ∀ τ a, χ τ a ∈ RC := fun τ a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ τ a)
    have := RC.add_mem (hχ τ a o ho).1 (RC.algebraMap_mem o)
    simpa using this
  let χ' : Sg → F →*₀ RC := fun τ =>
    { toFun := fun a => ⟨χ τ a, hmem τ a⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
  have hdiff : ∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
      χ' τ a - algebraMap O RC o ∈ IsLocalRing.maximalIdeal RC := fun τ a o ho =>
    hnu _ (hχ τ a o ho).2
  haveI : IsLocalHom (algebraMap O RC) := ⟨fun o ho => by
    by_contra hno
    have h1 := hdiff τ₀ 0 o (by rw [map_zero, IsLocalRing.residue_eq_zero_iff]; exact hno)
    rw [map_zero, zero_sub, neg_mem_iff] at h1
    exact h1 ho⟩
  let ψ := IsLocalRing.ResidueField.map (algebraMap O RC)
  obtain ⟨σ', ee, h1, h2, h3⟩ := core p hp τ₀ φ' (fun τ => ψ.comp (σ τ)) χ' (fun τ a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ τ a)
    have h := hdiff τ a o ho
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h
    rw [h, RingHom.comp_apply, ← ho]
    rfl) (fun τ a => by rw [RingHom.comp_apply, RingHom.comp_apply, hφ, map_pow])
  exact ⟨σ', ee, h1, fun τ a => congrArg Subtype.val (h2 τ a), h3⟩

theorem inj_loc {A Ω O : Type} [CommRing A] [Field Ω] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime]
    [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro o ho
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
  have h1 := congrArg (algebraMap O Ω) h
  rw [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at h1
  have ha : a = 0 := IsIntegralClosure.algebraMap_injective A ℤ Ω (by rw [map_zero]; exact h1.symm)
  rw [ha, map_zero] at h
  exact (IsLocalization.map_units O s).mul_left_eq_zero.1 h

theorem exists_lift {A Ω T : Type} [CommRing A] [Field Ω] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    [CommRing T] [Algebra.IsIntegral ℤ T] (f : T →+* Ω) : ∃ g : T →+* A, ∀ t, algebraMap A Ω (g t) = f t := by
  letI : Algebra T Ω := f.toAlgebra
  exact ⟨(IsIntegralClosure.lift ℤ A Ω (S := T) : T →ₐ[ℤ] A), fun t => IsIntegralClosure.algebraMap_lift ℤ A Ω t⟩

end PositivityTheory.Xgn.TestCharacter

theorem PositivityTheory.Xgn.test_character_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ _ _ _ b _ φ hφ A _ _ _ m _ _ O _ _ _ _ _ _ _ t₀ Sg _ e φ' F
    _ _ _ pq sc w σ hO _ G c' _ P i _ _ C _ _ _ _ RC hT χ hχ
  obtain ⟨⟨τ₀, -⟩, -, he, hsurj, hσ, -, ⟨-, -, hpO⟩, -⟩ := hO
  obtain ⟨-, ⟨v, hv, hvp⟩, -⟩ := hT
  refine PositivityTheory.Xgn.TestCharacter.overC p RC v hv hvp τ₀ φ' σ χ hχ fun τ a => ?_
  have hinj := PositivityTheory.Xgn.TestCharacter.inj_loc (Ω := Ω) (O := O) m
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.Xgn.TestCharacter.exists_lift (A := A)
    (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))
  let g : 𝓞 c.F →+* O := (algebraMap A O).comp g₀
  have hg : ∀ t, algebraMap O Ω (g t) = 𝔐.cst (t : c.F) := fun t => by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hg₀]; rfl
  obtain ⟨a, rfl⟩ := hsurj a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hint : ∀ s, IsIntegral ℤ (labelEmb c s a) := fun s =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom
  obtain ⟨o₁, h₁, h₁'⟩ := hσ (φ' τ) a
  obtain ⟨o₂, h₂, h₂'⟩ := hσ τ a
  obtain ⟨u₁, hu₁⟩ : ∃ u : 𝓞 c.F, (u : c.F) = labelEmb c (φ (e τ)) a := ⟨⟨_, hint (φ (e τ))⟩, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : 𝓞 c.F, (u : c.F) = labelEmb c (e τ) a := ⟨⟨_, hint (e τ)⟩, rfl⟩
  have hn := hφ ((IsLocalRing.maximalIdeal O).comap g) (Ideal.comap_isPrime _ _)
    (by rw [Ideal.mem_comap, map_natCast]; exact hpO) (e τ) a u₁ u₂ hu₁ hu₂
  have e₁ : g u₁ = o₁ := hinj (by rw [hg, h₁, he, hu₁]; rfl)
  have e₂ : g u₂ = o₂ := hinj (by rw [hg, h₂, hu₂]; rfl)
  rw [Ideal.mem_comap, map_sub, map_pow, e₁, e₂, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero] at hn
  rw [← h₁', ← h₂', hn]
end

