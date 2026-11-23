module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexDvdClassNumber
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UnramHom

section Algebra

variable {O M G Γ : Type} [CommRing O] [AddCommGroup M] [Module O M] [Group G] [CommGroup Γ]

def asHom (f : G → M) (hf : ∀ a b, f (a * b) = f a + f b) : G →* Multiplicative M :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun a b => by rw [hf, ofAdd_add]

theorem length_le {l : ℕ} (hl : l.Prime) (hu : ∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : O)) (L : ℕ∞)
    (hL : Module.length O (Submodule.torsionBy O M (l : O)) ≤ L) (π : G →* Γ) (hπ : Function.Surjective π) (n : ℕ) :
    n ≠ 0 → ∀ N : Subgroup Γ, N.index = n → ∀ C : Submodule O (G → M), (∀ f ∈ C, ∀ a b, f (a * b) = f a + f b) →
      (∀ f ∈ C, ∀ a, π a ∈ N → f a = 0) → Module.length O C ≤ L * (padicValNat l n : ℕ∞) := by
  have := Fact.mk hl
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn N hN C hadd hker
  by_cases h1 : n = 1
  · have hT : N = ⊤ := Subgroup.index_eq_one.1 (hN.trans h1)
    have : C = ⊥ := (Submodule.eq_bot_iff _).2 fun f hf => funext fun a => hker f hf a (hT ▸ trivial)
    subst this
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have := Fact.mk hp
  have : N.FiniteIndex := ⟨hN ▸ hn⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Γ ⧸ N) p (hN ▸ hpn :)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, rfl⟩ := hπ y
  let N' : Subgroup Γ := (Subgroup.zpowers (π a : Γ ⧸ N)).comap (QuotientGroup.mk' N)
  have hi : p * N'.index = n := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), ← hx, ← Nat.card_zpowers,
      Subgroup.card_mul_index, ← hN]
    rfl
  have hi0 : N'.index ≠ 0 := fun h => hn (by rw [← hi, h, mul_zero])
  have hlt : N'.index < n := by
    rw [← hi]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hi0) hp.one_lt
  let ev : C →ₗ[O] M := (LinearMap.proj a).comp C.subtype
  let C' : Submodule O (G → M) := (LinearMap.ker ev).map C.subtype
  have hC' := ih _ hlt hi0 N' rfl C' (by rintro _ ⟨f, -, rfl⟩; exact hadd f f.2) (by
    rintro _ ⟨f, hf, rfl⟩ b ⟨k, hk⟩
    have hf' : asHom f.1 (hadd f f.2) a = 1 := congrArg Multiplicative.ofAdd (LinearMap.mem_ker.1 hf)
    have h2 : π ((a ^ k)⁻¹ * b) ∈ N := by
      rw [map_mul, map_inv, map_zpow]
      exact QuotientGroup.eq.1 hk
    have h3 : asHom f.1 (hadd f f.2) ((a ^ k)⁻¹ * b) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_mul, map_inv, map_zpow, hf', one_zpow, inv_one, one_mul] at h3
    exact congrArg Multiplicative.toAdd h3)
  have hk : Module.length O (LinearMap.ker ev) = Module.length O C' :=
    (Submodule.equivMapOfInjective _ C.injective_subtype _).length_eq
  have hr : LinearMap.range ev ≤ Submodule.torsionBy O M (p : O) := by
    rintro _ ⟨f, rfl⟩
    have h2 : π (a ^ p) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, map_pow, QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
    have h3 : asHom f.1 (hadd f f.2) (a ^ p) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_pow] at h3
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    exact congrArg Multiplicative.toAdd h3
  have hsum : Module.length O C = Module.length O (LinearMap.ker ev) + Module.length O (LinearMap.range ev) :=
    Module.length_eq_add_of_exact (LinearMap.ker ev).subtype ev.rangeRestrict (Submodule.injective_subtype _)
      ev.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have hr' := Module.length_le_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
  rw [hsum, hk, ← hi, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hp.ne_zero hi0, Nat.cast_add, mul_add, add_comm (L * _)]
  refine add_le_add hC' (hr'.trans ?_)
  by_cases hpl : p = l
  · subst hpl
    rwa [Nat.padicValNat_def, Nat.Prime.multiplicity_self, Nat.cast_one, mul_one]
  · have : Submodule.torsionBy O M (p : O) = ⊥ := (Submodule.eq_bot_iff _).2 fun m hm =>
      ((hu p hp hpl).smul_eq_zero).1 ((Submodule.mem_torsionBy_iff _ _).1 hm)
    rw [this]
    simp

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] {a : O} (ha : a ≠ 0) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  have ha' : algebraMap O (FractionRing O) a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha
  let u : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
  have hu : a • u = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun _ => 1, funext fun j => ?_⟩
    simp [Algebra.smul_def, ha']
  let g : (O ⧸ Ideal.span {a}) →ₗ[O] Submodule.torsionBy O (KOG O 1) a :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton O _ ⟨u, hu⟩) (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hu)
  refine Module.length_le_of_surjective g ?_
  rintro ⟨m, hm⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨Submodule.Quotient.mk (c 0), Subtype.ext ?_⟩
  show c 0 • u = _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h0 : algebraMap O (FractionRing O) (c 0) = a • x 0 := congrFun hc 0
  rw [Pi.smul_apply, Algebra.smul_def, h0, Algebra.smul_def]
  field_simp

end Algebra

section Galois

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.HeckeGal GlobalTheory.Mem.UnitIndex Filter

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem eq_one_of_class [_root_.NumberField.IsTotallyComplex E] {art : Neutral.B1.Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {B : Type} [CommGroup B] [TopologicalSpace B] [DiscreteTopology B] (φ : G E Ω →* B) (hφ : Continuous φ)
    (A : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v)
    (hI : ∀ v, ∀ σ ∈ Ine (F := E) (A v), φ σ = 1) (σ : G E Ω)
    (hσ : toAb E Ω σ ∈ (classHom E).ker.map art) : φ σ = 1 := by
  obtain ⟨x, hx, e⟩ := hσ
  let ψ : Neutral.B1.Ideles E →* B := (liftAb φ hφ).comp art
  have hψ : Continuous ψ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (ψ.ker : Set (Neutral.B1.Ideles E)) := (isOpen_discrete {1}).preimage hψ
  have hfin : Finite ψ.range := by
    refine ((isCompact_range hφ).finite_of_discrete.subset ?_).to_subtype
    rintro _ ⟨y, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art y)
    exact ⟨τ, by rw [MonoidHom.comp_apply, ← hτ, liftAb_toAb]⟩
  have hu : ∀ v x, Formalism.L2.Host.IsUnitAt v x → ψ (Neutral.B1.localIdele E v x) = 1 := fun v y hy => by
    obtain ⟨τ, hτ, e⟩ := (ha.ine v (A v) (hA v) _).1 ⟨y, hy, rfl⟩
    rw [MonoidHom.comp_apply, ← e, liftAb_toAb, hI v τ hτ]
  have hle : unitIdl E ⊔ (Neutral.B1.diagUnits E).range ≤ ψ.ker := by
    refine sup_le (fun b hb => ?_) ?_
    · have e1 : ψ (finPartI E b) = ψ b := congrArg Subtype.val (GlobalTheory.RingCls.map_finPartI ψ.rangeRestrict b)
      rw [MonoidHom.mem_ker, ← e1]
      refine (ψ.ker.isClosed_of_isOpen ho).mem_of_tendsto
        (GlobalTheory.Mem.LocTriv.tendsto_part (finPartI_mem_unitIdl.2 hb) fun _ => rfl) (Eventually.of_forall fun S => ?_)
      refine Subgroup.prod_mem _ fun v _ => ?_
      exact hu v _ (hb v)
    · rintro _ ⟨k, rfl⟩
      have hk : Neutral.B1.diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have := MonoidHom.mem_ker.1 (hle (ker_classHom_le E hx))
  rwa [MonoidHom.comp_apply, e, liftAb_toAb] at this


omit [IsAlgClosure E Ω] in
theorem index_dvd_classNumber {art : Neutral.B1.Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ((classHom E).ker.map art).index ∣ classNumber E := by
  refine (Subgroup.index_map_dvd _ ha.quot.surjective).trans ?_
  rw [Subgroup.index_ker, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card _

end Galois

theorem wkg_one (D : D7) (i : D.nd.Loc) (g : GE D.nd) (m : KOG (D.nd.O i) 1) :
    WKG (chiRatO D.nd i 1) g m = m := by
  have h : chiRatO D.nd i 1 g = chiRatO D.nd i 1 1 := by
    rw [map_one]
    simp [chiRatO, twistM]
  have h2 : WKG (chiRatO D.nd i 1) g = WKG (chiRatO D.nd i 1) 1 := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    exact congrArg (fun X : Matrix (Fin 1) (Fin 1) (D.nd.O i) => (Submodule.Quotient.mk
      (Matrix.toLinAlgEquiv' (X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) x) : KOG (D.nd.O i) 1)) h
  rw [h2, map_one]
  rfl

theorem length_le_classNumber : GlobalTheory.Published.GlobalArtinReciprocity →
    ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)),
      C ≤ Z1 (WKG (chiRatO D.nd i 1)) → (∀ v, resIne i C v = ⊥) →
      Module.length (D.nd.O i) ↥C ≤
        lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) := by
  intro H D i C hC hres
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := H D.host.E D.nd.Om
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hadd : ∀ f ∈ C, ∀ a b, f (a * b) = f a + f b := fun f hf a b => by
    rw [(hC hf).2, wkg_one]
  have hl0 : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
    rw [map_natCast, map_zero, ← map_natCast (D.nd.embK i), map_eq_zero] at h1
    exact hl.ne_zero (Nat.cast_eq_zero.1 h1)
  have hu : ∀ p : ℕ, p.Prime → p ≠ D.nd.l i → IsUnit (p : D.nd.O i) := fun p hp hpl => by
    have h1 : IsUnit (p : ℤ_[D.nd.l i]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hl hp).2 hpl.symm))
    simpa using h1.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  have hd := index_dvd_classNumber ha
  have hh : classNumber D.host.E ≠ 0 := classNumber_ne_zero _
  refine (length_le hl hu _ (length_torsionBy_le hl0) (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
    GlobalTheory.HeckeGal.toAb_surjective _ (ne_zero_of_dvd_ne_zero hh hd) _ rfl C hadd fun f hf σ hσ => ?_).trans ?_
  · refine congrArg Multiplicative.toAdd (eq_one_of_class ha (asHom f (hadd f hf)) (hC hf).1 D.nd.plOm.1 D.nd.plOm.2
      (fun v τ hτ => ?_) σ hσ)
    have h1 : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) 1) Subtype.val f ∈ resIne i C v := ⟨f, hf, rfl⟩
    rw [hres v, Submodule.mem_bot] at h1
    exact congrArg Multiplicative.ofAdd (congrFun h1 ⟨τ, hτ⟩)
  · refine mul_le_mul_right (Nat.cast_le.2 ?_) _
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hh).1 ((_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hd)

end GlobalTheory.UnramHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaVanishingNoInvariantsFirstHalfPlaces
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.StageFirst

open IsLocalRing GlobalTheory.ScalarFrob GlobalTheory.PrimeToInertia GlobalTheory.AntiRamConj
open scoped Pointwise

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem isLocalHom_of_kills {A : Type} [CommRing A] [Nontrivial A] [Algebra (X.O0 i) A] (h : Kills i A) :
    IsLocalHom (algebraMap (X.O0 i) A) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ maximalIdeal (X.O0 i) := hn
  have : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have hl : ((X.l i : ℕ) : X.O0 i) ^ nu X i ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : (X.l i).Prime).ne_zero)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ϖ ∣ x := by
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have h2 : ((X.l i : ℕ) : X.O0 i) ^ nu X i ∣ x ^ n := by
    rw [hu, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd h1 n
  have h3 := h (x ^ n * x) (Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 h2) hm)
  rw [← pow_succ, map_pow] at h3
  exact (hx.pow _).ne_zero h3

theorem frob_scalar (bkP : BKPh X) (h : GalHyp bkP i s) {z : GE N} {L : Subgroup (GE N)} (hz : IsTameInertiaElementAtTwistPrime X i z)
    (hL : Small i s L z) {P : PlE D.host}
    (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := _root_.GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 hp.2 hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 hp0.2 hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem firstHalf : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  intro hT D N X bkP i s h hl2 M R n d A₀ L z P hM hz hL hP A _ _ _ _ κ ρ hK hκ hρ Y _ _ _ _ b
  have := isLocalHom_of_kills i hK
  have hA : ∀ v, Over (P (.inl b)) v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1 := fun v hv =>
    ⟨(hP.1.1 _ v hv).2.2.2.1, natCast_eq_one i (show 1 ≤ M by omega) (hP.1.1 _ v hv).2.2.2.2.2⟩
  have fix0 : ∀ v, Over (P (.inl b)) v → ∀ σ : GE N, IsFrob (N.plOm.1 v) (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv σ hσ m hm
    obtain ⟨c, c0, c1, hc⟩ := frob_scalar i s bkP h hz hL.1 hA (hP.2.1 b).2 hv hσ
    obtain ⟨c', c1', hc'⟩ : ∃ c' : ResidueField (X.O0 i), c' ≠ 1 ∧
        ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (residue _) = c' • 1 := by
      rcases hρ with rfl | hρ
      · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
      · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i (hA v hv).1 (hA v hv).2 hσ) c0 hc]⟩
    exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκ σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  have fix : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ : GE N, IsFrob B (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv B hB σ hσ m hm
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hB (N.plOm.2 v)
    have h3 := isFrob_smul hσ g
    rw [hg] at h3
    have h4 := fix0 v hv _ h3 (repOn ρ κ Y g m) (by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hm])
    have h5 := congrArg (repOn ρ κ Y g⁻¹) h4
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
  have van : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v →
      (∀ τ ∈ Ine (F := D.host.E) B, κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) B, f.1 τ = 0 := by
    intro v hv B hB hκB f
    obtain ⟨γ, -, hγ⟩ := GlobalTheory.TameRead.exists_gen_read hT.1 D.host.E N.Om (X.l i) B v hB
      (fun h => (hA v hv).1 (X.twistExcludedPlaces_contains_residueChar i h))
    have h1 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (l_mem i))
      rw [map_mul, map_pow, map_natCast] at this
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, pow_succ, this, zero_smul]
    have h2 : normV v ≡ 1 [MOD X.l i ^ (nu X i + 1)] := by
      have hq := (hP.1.1 _ v hv).2.2.2.2.2
      have hd : X.l i ^ (nu X i + 1) ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (pow_dvd_pow _ hM) 2
      have h6 : normV v ≡ 1 [MOD 2 * X.l i ^ M] := by
        rw [← hq]
        exact (Nat.mod_modEq _ _).symm
      exact h6.of_dvd hd
    have h3 : ∀ σ ∈ Ine (F := D.host.E) B, ∀ m, repOn ρ κ Y σ m = m := by
      intro σ hσ m
      have hσL := (hP.2.1 b).1 v hv B hB hσ
      rcases hρ with rfl | hρ
      · rw [(_root_.GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl2 M L z hM hL A κ _ hK (isDual_dualRep i s) Y σ hσL).1, hκB σ hσ, Units.val_one,
          one_smul]
      · rw [(_root_.GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl2 M L z hM hL A κ _ hK hρ Y σ hσL).2.1, hκB σ hσ, Units.val_one, one_smul]
    obtain ⟨h4, h5⟩ := hγ A _ (repOn ρ κ Y) (nu X i + 1) h1 h2 h3 f
    obtain ⟨φ, hφ⟩ := exists_isFrob (F := D.host.E) hB
    exact h4 (fix v hv B hB φ hφ _ (h5 φ hφ))
  refine ⟨fun v hv m hm => ?_, fun hanti hκI f τ hτ => ⟨van _ (over_refl _) _ (N.plOm.2 _) hκI f τ hτ, ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    exact fix0 v hv σ hσ m (hm σ hσ.1)
  · obtain ⟨v, hv⟩ := exists_isConjPl (P (.inl b))
    refine van v (Or.inr hv) _ (isPlaceOver_moveVal_cc X hv (N.plOm.2 _)) (fun σ hσ => ?_) f _ (cConj_mem_ine X hτ)
    have h1 := cConj_mem_ine X hσ
    have e : moveVal X.cc (moveVal X.cc (N.plOm.1 (P (.inl b)))) = N.plOm.1 (P (.inl b)) := by
      ext y
      rw [mem_moveVal, mem_moveVal, cc_symm, cc_symm, cc_cc]
    rw [e] at h1
    have h2 := hκI _ h1
    rwa [antiHom_cConj X hanti, inv_eq_one] at h2

end GlobalTheory.StageFirst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isδMap_of_dense_δLocus : ∀ (l : ℕ) [Fact l.Prime] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (D : Delta l Q) (DC : Delta l C) (J : Ideal Q) (JC : Ideal C) (h : Q →+* C), (l : Q) ∈ J → J.map h ≤ JC → IsHausdorff JC C → (∀ (x : Q) (n : ℕ), ∃ a ∈ δLocus D DC h, x - a ∈ J ^ n) → IsδMap D DC h := by
  intro l _ Q _ C _ D DC J JC h hl hJ hH hd x
  have hlC : (l : C) ∈ JC := by
    have := hJ (Ideal.mem_map_of_mem h hl)
    simpa using this
  have hpow : ∀ m : ℕ, (J ^ m).map h ≤ JC ^ m := fun m => by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hJ m
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha, hxa⟩ := hd x (n + 1)
  have ha' := (mem_δLocus).1 ha
  set y := x - a with hy
  have hxy : x = a + y := by rw [hy]; ring
  have h1 : D.δ (a + y) - D.δ a ∈ J ^ n := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l Q D J hl n a y hxa
  have h1' : h (D.δ x) - h (D.δ a) ∈ JC ^ n := by
    rw [hxy, ← map_sub]; exact hpow n (Ideal.mem_map_of_mem h h1)
  have hyC : h y ∈ JC ^ (n + 1) := hpow (n + 1) (Ideal.mem_map_of_mem h hxa)
  have h2 : DC.δ (h a + h y) - DC.δ (h a) ∈ JC ^ n := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C DC JC hlC n (h a) (h y) hyC
  have h2' : DC.δ (h x) - DC.δ (h a) ∈ JC ^ n := by rw [hxy, map_add (f := _)]; exact h2
  have key : h (D.δ x) - DC.δ (h x) ∈ JC ^ n := by
    have := (JC ^ n).sub_mem h1' h2'
    rw [ha'] at this
    convert this using 1; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A), B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  first | exact @GlobalTheory.BSP.isUnit_δ_of_I_eq_span | exact GlobalTheory.BSP.isUnit_δ_of_I_eq_span | (intros; apply GlobalTheory.BSP.isUnit_δ_of_I_eq_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsGoodOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.Jumps

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem map_round_cast (S : Multiset ℂ) (h : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    (S.map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id S]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  simp

end GlobalTheory.TripleGal.Jumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_dual_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  first | exact @GlobalTheory.tate_double_annihilator | exact GlobalTheory.tate_double_annihilator | (intros; apply GlobalTheory.tate_double_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModulesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDuality_perfect_pair_finite_modules : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  first | exact @GlobalTheory.LocalPair.local_pair | exact GlobalTheory.LocalPair.local_pair | (intros; apply GlobalTheory.LocalPair.local_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariantStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_equivariant_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  first | exact @GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | exact GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | (intros; apply GlobalTheory.NewPrime.PairEquiv.pairing_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocyclePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle_pow : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (ζ : Ω), 0 < n → IsPrimitiveRoot ζ (l ^ n) → ∃ inv : InvFam F Ω l n, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l n), (∀ g h : G F Ω, ∀ u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ u' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * u, h * u') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l n (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  first | exact @GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle_pow | exact GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle_pow | (intros; apply GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle_pow <;> assumption)
end

