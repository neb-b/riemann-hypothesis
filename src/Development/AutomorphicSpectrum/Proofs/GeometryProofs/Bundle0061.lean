module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegrality
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTStalk

section Lattices

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem mem_htW_iff (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨Submodule.zero_mem _, fun d _ => by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun d hd => ?_⟩
      rw [smul_add]
      exact Submodule.add_mem _ (hx.2 d hd) (hy.2 d hd)
    | smul c x _ hx =>
      refine ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem (c : Ω) hx.1, fun d hd => ?_⟩
      have h : σ d • c • x = c • σ d • x := smul_comm _ _ _
      rw [h]
      exact Submodule.smul_mem _ c (hx.2 d hd)
  · exact fun h => Submodule.subset_span h

theorem mem_htW_iff_forms (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔
      e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, ∀ d ∈ 𝔡, σ d * w e ∈ regAt ξ q := by
  rw [mem_htW_iff]
  refine and_congr_right fun he => ⟨fun h w hw d hd => ?_, fun h d hd => ?_⟩
  · have := ((M.mem_htDual_iff L n ρ σ q _).1 (h d hd)).2 w hw
    simpa [map_smul, smul_eq_mul] using this
  · refine (M.mem_htDual_iff L n ρ σ q _).2 ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem _ he, fun w hw => ?_⟩
    simpa [map_smul, smul_eq_mul] using h w hw d hd

end Lattices

theorem forall_different_iff {o Ω E : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field E] [NumberField E]
    (A : Subalgebra o Ω) (B : Subring Ω) (hA : ∀ a : A, (a : Ω) ∈ B) (σ : E →+* Ω) (ds : A)
    (hds : GeneratesDiff σ ds) (t : Ω) :
    (∀ x ∈ differentIdeal ℤ (𝓞 E), σ (x : E) * t ∈ B) ↔ (ds : Ω) * t ∈ B := by
  constructor
  · intro h
    have h1 : algebraMap A Ω ds ∈ Submodule.span A {algebraMap A Ω ds} :=
      Submodule.subset_span rfl
    rw [hds] at h1
    have h2 : ∀ z ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}, z * t ∈ B := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact h x hx
      | zero => simpa using B.zero_mem
      | add u v _ _ hu hv =>
        rw [add_mul]
        exact B.add_mem hu hv
      | smul a u _ hu =>
        have : (a • u) * t = (a : Ω) * (u * t) := by
          rw [Algebra.smul_def, mul_assoc]
          rfl
        rw [this]
        exact B.mul_mem (hA a) hu
    exact h2 _ h1
  · intro h x hx
    have h1 : σ (x : E) ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [← hds, Submodule.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    have : σ (x : E) * t = (a : Ω) * ((ds : Ω) * t) := by
      rw [← ha, Algebra.smul_def, mul_assoc]
      rfl
    rw [this]
    exact B.mul_mem (hA a) h

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem inv_natCast_mem {p : ℕ} (hp : p.Prime) {q : Cpt 𝔐.ξ} (hq : InFibre 𝔐.ξ p q) (b : ℕ) (hb : ¬ p ∣ b) :
    ((b : Ω))⁻¹ ∈ regAt 𝔐.ξ q := by
  have hZ : OverZp 𝔐 p q := by
    intro r hr hrq
    by_contra hne
    have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
        (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one => simpa using (regAt 𝔐.ξ q).one_mem
  | prime r hr =>
    have hne : r ≠ p := by
      rintro rfl
      exact hb dvd_rfl
    have hu : unitAt 𝔐.ξ q (r : Ω) := by
      by_contra hnot
      exact hne (hZ r hr hnot)
    exact hu.2.2
  | mul a b ha hb' =>
    have h1 : ¬ p ∣ a := fun h => hb (h.mul_right b)
    have h2 : ¬ p ∣ b := fun h => hb (h.mul_left a)
    rw [Nat.cast_mul, mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (ha h1) (hb' h2)

theorem chart_mem_regAt {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {s : ∀ k, J k} {q : Cpt 𝔐.ξ} (hs : InChart 𝔐.ξ (mseg y) s q) (hq : InFibre 𝔐.ξ p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  obtain ⟨a, ha⟩ := a
  change a ∈ regAt 𝔐.ξ q
  change a ∈ Algebra.adjoin o _ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hs.2 j
  | algebraMap r =>
    obtain ⟨u, b, hb, h⟩ := (ho _).1 ⟨r, rfl⟩
    rw [h, div_eq_mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (intCast_mem _ u) (inv_natCast_mem 𝔐 hp hq b hb)
  | add u v _ _ hu hv => exact (regAt 𝔐.ξ q).add_mem hu hv
  | mul u v _ _ hu hv => exact (regAt 𝔐.ξ q).mul_mem hu hv

end Model

theorem mem_V_inl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (ds : chartRing o (mseg y) s.1), GeneratesDiff σ ds → ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inl τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hD hpS τ σ hσ s ds hds q hs hq e
  have hp : p.Prime := Fact.out
  have hZ : OverZp 𝔐 p q := by
    intro r hr hrq
    by_contra hne
    have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
        (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  have hV : 𝔐.V (Sum.inl τ) q = 𝔐.HT p (Sum.inl τ) q :=
    Lat.patch_of_unique S _ _ hpS hq fun p' hp' h =>
      hZ p' (𝔐.S_prime p' hp') h
  have hE : e ∈ GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb (Sum.inl τ)) ↔ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ := by
    rw [LatBasic.mem_eigSp]
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hσ]
  have hA := chart_mem_regAt 𝔐 hp ho hs hq
  have hO : omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li)) :=
    hD.om'_loc s q hs hq
  rw [hV]
  change e ∈ 𝔐.M.htW _ _ _ _ _ q ↔ _
  rw [mem_htW_iff_forms, hE]
  refine and_congr_right fun _ => ?_
  have hT : ∀ w : Module.Dual Ω 𝔐.Li,
      (∀ d ∈ differentIdeal ℤ (𝓞 E), 𝔐.emb (Sum.inl τ) d * w e ∈ regAt 𝔐.ξ q) ↔
        (ds : Ω) * w e ∈ regAt 𝔐.ξ q := fun w => by
    rw [← forall_different_iff _ _ hA σ ds hds]
    simp only [hσ]
  constructor
  · intro h w hw
    have hw' : w ∈ omP 𝔐 p q := by
      rw [hO]
      exact Submodule.subset_span hw
    exact (hT w).1 (h w hw')
  · intro h w hw
    rw [show 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = omP 𝔐 p q from rfl, hO] at hw
    refine (hT w).2 ?_
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simpa using (regAt 𝔐.ξ q).zero_mem
    | add u v _ _ hu hv =>
      have : (ds : Ω) * (u + v) e = (ds : Ω) * u e + (ds : Ω) * v e := by
        rw [LinearMap.add_apply, mul_add]
      rw [this]
      exact (regAt 𝔐.ξ q).add_mem hu hv
    | smul a u _ hu =>
      have : (ds : Ω) * (a • u) e = (a : Ω) * ((ds : Ω) * u e) := by
        change (ds : Ω) * ((a : Ω) • u) e = _
        rw [LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact (regAt 𝔐.ξ q).mul_mem a.2 hu

end GlobalTheory.CompanionTheory.Ar.Flat.HTStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem htDual_htW_relabel : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  intro E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h
  have hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
    eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ
  have h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q := by
    unfold LieModel.htDual
    rw [hE, h]
  refine ⟨h1, ?_⟩
  unfold LieModel.htW
  rw [hE, h1]
  congr 1
  ext e
  constructor
  · rintro ⟨he, H⟩
    refine ⟨he, fun d hd => ?_⟩
    have hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E) :=
      (_root_.GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff E s (s.symm d)).1 (by simpa using hd)
    simpa using H _ hd'
  · rintro ⟨he, H⟩
    exact ⟨he, fun d hd => H _ ((_root_.GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff E s d).2 hd)⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li]
      [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n g : ℕ) (O : Type) [CommRing O]
      (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (q : Cpt ξ), M.lat.IsVBOn {q} g ⊤ → M.htOm L n q = M.omLat q →
      M.htDual L n ρ σ q = M.eigLat ρ σ q ∧ ∀ 𝔡 : Ideal O, (∀ a, σ a ∈ regAt ξ q) →
        (∃ d ∈ 𝔡, unitAt ξ q (σ d)) → M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  intro X Ω _ ξ G _ Li _ _ M L n g O _ ρ σ q hVB hOm
  have hbi := (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat {q} g hVB).2 q rfl
  have hD : M.htDual L n ρ σ q = M.eigLat ρ σ q := by
    refine le_antisymm (fun e he => ?_) (M.eigLat_le_htDual L n ρ σ q)
    obtain ⟨he1, he2⟩ := (M.mem_htDual_iff L n ρ σ q e).1 he
    refine ⟨(hbi e).2 fun w hw => he2 w ?_, he1⟩
    rw [hOm]
    exact hw
  refine ⟨hD, fun 𝔡 hσ ⟨d, hd, hu, _, hinv⟩ => le_antisymm ?_ fun e he => ?_⟩
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 : σ d • e ∈ M.eigLat ρ σ q := hD ▸ he.2 d hd
    have h2 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) ∈ M.eigLat ρ σ q := Submodule.smul_mem _ _ h1
    have h3 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) = e := by
      change (σ d)⁻¹ • (σ d • e) = e
      rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
    rwa [h3] at h2
  · refine Submodule.subset_span ⟨he.2, fun a ha => ?_⟩
    rw [hD]
    exact Submodule.smul_mem (M.eigLat ρ σ q) (⟨σ a, hσ a⟩ : regAt ξ q) he

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtEnd

theorem pullPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.comp_mul, ih]

theorem homPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {Z : Over X} (a : G ⟶ G) [IsMonHom a] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ a = (x ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.mul_comp, ih]

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  haveI : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom a)) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

theorem powDescend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a)
  haveI : Epi ψ := Over.epi_of_epi_left ψ (hk := epiSp a)
  have hψ : ψ ≫ g₀ = g := Over.OverMorphism.ext (by simp [ψ, e])
  apply (cancel_epi ψ).mp
  rw [pullPow, hψ, hg, CategoryTheory.MonObj.comp_one]

theorem secVal_app {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z ⟶ Z')
    (W : Z'.Opens) (f : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) :
    secVal x (φ ⁻¹ᵁ W) h ((φ.app W).hom f) = secVal (x ≫ φ) W h' f := by
  simp only [secVal, Scheme.Hom.comp_appLE]
  rfl

end GlobalTheory.CompanionTheory.Ar.HtEnd


open GlobalTheory.CompanionTheory.Ar.HtEnd in
theorem GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  intro X _ Ω _ _ ξ _ _ G _ _ L n _ hFT ep hW E _ _ M a _ A hA y y' hy hy' hyy' q w hH
  obtain ⟨hw, W, f, hη, P1, P2⟩ := hH
  have hExt : ∀ {e' : E} {v}, M.Extends q e' v → M.Extends q (A e') (v ≫ a) := by
    intro e' v hv
    refine ⟨?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, CategoryTheory.MonObj.one_comp]
    · rw [hA e', Over.comp_left, hv.2]
      erw [Category.assoc]
  have hlat : ∀ e' ∈ M.lat q, A e' ∈ M.lat q := by
    intro e' he'
    have hle : M.lat q ≤ (M.lat q).comap (A.restrictScalars (regAt ξ q)) := by
      refine Submodule.span_le.mpr ?_
      rintro e'' ⟨v, hv⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      exact Submodule.subset_span ⟨v ≫ a, hExt hv⟩
    exact hle he'
  have hw' : ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q := hw
  refine ⟨?_, a.left ⁻¹ᵁ W, (a.left.app W).hom f, ?_, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, (w ∘ₗ A) e' ∈ regAt ξ q
    intro e' he'
    exact hw' (A e') (hlat e' he')
  · have h1 : (η[G] ≫ a).left = (η[G]).left := by rw [IsMonHom.one_hom]
    show a.left ((η[G]).left q.1) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact hη
  · intro k _ _ i xk g c h hx hg hWe
    have h2 : ⊤ ≤ (g.left ≫ a.left) ⁻¹ᵁ W := h
    rw [secVal_app g.left a.left W f h h2]
    obtain ⟨g₀, hg₀⟩ := hFT k i g hg
    have hg₀n : g₀ ^ n = 1 := powDescend i hg₀ hg
    have hga : (g ≫ a) ^ n = 1 := by rw [← homPow, hg, CategoryTheory.MonObj.one_comp]
    have hg₀a : (g₀ ≫ a) ^ n = 1 := by rw [← homPow, hg₀n, CategoryTheory.MonObj.one_comp]
    have hc : (c : k) = i (ep y' g₀) := (hW.weil y' g₀ hy' hg₀n k i xk g c hx hg₀).mp hWe
    rw [hyy' g₀ hg₀n] at hc
    let xk0 : Over.mk (spMap i ≫ ξ) ⟶ G := Over.homMk (spMap i ≫ y.left)
    have hg' : (g ≫ a).left = spMap i ≫ (g₀ ≫ a).left := by
      rw [Over.comp_left, Over.comp_left, hg₀, Category.assoc]
    have hWa := (hW.weil y (g₀ ≫ a) hy hg₀a k i xk0 (g ≫ a) c rfl hg').mpr hc
    exact P1 k i xk0 (g ≫ a) c h2 rfl hga hWa
  · intro e' v hv h
    have h2 : ⊤ ≤ (v.left ≫ a.left) ⁻¹ᵁ W := h
    obtain ⟨r, hr, hE⟩ := P2 (A e') (v ≫ a) (hExt hv) h2
    refine ⟨r, hr, ?_⟩
    rw [LinearMap.comp_apply, secVal_app v.left a.left W f h h2]
    exact hE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombBase

theorem comp_list_prod {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (g : A ⟶ B) (l : List (B ⟶ G)) :
    g ≫ l.prod = (l.map (g ≫ ·)).prod := by
  induction l with
  | nil => simp [comp_one]
  | cons a l ih => simp only [List.prod_cons, List.map_cons, comp_mul, ih]

theorem isComb_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G)) (w' : epsAt x' ⟶ G), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → w'.left = spMap (dualMap f) ≫ w.left → IsComb cf v w → IsComb (fun i => f (cf i)) v' w' := by
  rintro S G _ _ F _ x F' _ f x' hx n v cf w v' w' hv hw ⟨u, hu, e⟩
  refine ⟨fun i => LieTangent.epsBase f hx ≫ u i, fun i => ?_, ?_⟩
  · change spMap (dualMap f) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, LieTangent.spec_dual_eps, Category.assoc, hv i]
  · rw [(LieTangent.left_eq_iff f hx w' w).1 hw, e, comp_list_prod, List.map_ofFn]
    rfl

end GlobalTheory.CompanionTheory.Ar.CombBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrix
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_ofFn_lieModel_pt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => M.pt (f j)).prod = M.pt (∑ j, f j)
  | 0, f => by simp [M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_lieModel_pt M, Fin.sum_univ_succ, M.add]

theorem isComb_unit_row : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F]
    (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) →
    ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  intro S G _ _ F _ x n v hv i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  choose e he using fun j => M.onto (v j) (hv j)
  refine ⟨fun j => M.pt ((1 : Matrix (Fin n) (Fin n) F) i j • e j), fun j => ?_, ?_⟩
  · rw [M.smul, he]
  · rw [prod_ofFn_lieModel_pt M, ← he i]
    congr 1
    simp [Matrix.one_apply, ite_smul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

