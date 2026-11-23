module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBound
section
namespace GlobalTheory.CompanionTheory.Ar.LocalStep

theorem exists_away_basis (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] [Algebra ℚ S] [Algebra.Smooth S T] [Algebra.Smooth ℚ S]
    (e r : ℕ) (hr : Module.finrank L (KaehlerDifferential K L) = r) (z : Fin e → S)
    (hli : LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)))
    (hsp : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (P : Ideal T) [P.IsPrime] :
    ∃ g : T, g ∉ P ∧ ∀ (T' : Type) [CommRing T'] [IsDomain T'] [Algebra T T'] [IsLocalization.Away g T']
      [Algebra ℚ T'] [Algebra T' L] [IsScalarTower T T' L],
      Algebra.Smooth ℚ T' ∧ ∃ z' : Fin (e + r) → T',
        (∀ i, z' (Fin.castAdd r i) = algebraMap T T' (algebraMap S T (z i))) ∧
        LinearIndependent T' (fun i => KaehlerDifferential.D ℚ T' (z' i)) ∧
        Submodule.span T' (Set.range fun i => KaehlerDifferential.D ℚ T' (z' i)) = ⊤ := by
  haveI : Algebra.IsSmoothAt S P := inferInstance
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth S P
  refine ⟨g, hg, ?_⟩
  intro T' _ _ _ _ _ _ _
  letI : Algebra S T' := ((algebraMap T T').comp (algebraMap S T)).toAlgebra
  haveI : IsScalarTower S T T' := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℚ S T' := .of_algebraMap_eq fun x =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ T') ((algebraMap S T').comp (algebraMap ℚ S))) x
  haveI : IsScalarTower S T' L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply S T L, IsScalarTower.algebraMap_apply S T T',
      ← IsScalarTower.algebraMap_apply T T' L]
  let f : Localization.Away g ≃ₐ[T] T' := IsLocalization.algEquiv (Submonoid.powers g) _ _
  haveI : Algebra.IsStandardSmooth S T' := Algebra.IsStandardSmooth.of_algEquiv (f.restrictScalars S)
  haveI : Algebra.Smooth S T' := inferInstance
  have hsm : Algebra.Smooth ℚ T' := Algebra.Smooth.comp ℚ S T'
  refine ⟨hsm, ?_⟩
  obtain ⟨m, w, hli', hsp'⟩ : ∃ (m : ℕ) (w : Fin m → T'),
      LinearIndependent T' (fun i => KaehlerDifferential.D S T' (w i)) ∧
      Submodule.span T' (Set.range fun i => KaehlerDifferential.D S T' (w i)) = ⊤ := by
    obtain ⟨-, I, b, hb⟩ := (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
      (R := S) (S := T')).1 inferInstance
    haveI : Finite I := Module.Finite.finite_basis b
    cases nonempty_fintype I
    let b' := b.reindex (Fintype.equivFin I)
    have hb' : ∀ i, ∃ x, KaehlerDifferential.D S T' x = b' i := fun i => by
      obtain ⟨x, hx⟩ := hb ⟨(Fintype.equivFin I).symm i, rfl⟩
      exact ⟨x, by simpa [b'] using hx⟩
    choose w hw using hb'
    refine ⟨_, w, ?_, ?_⟩
    · simpa only [hw] using b'.linearIndependent
    · simpa only [hw] using b'.span_eq
  haveI : IsDomain T := (IsFractionRing.injective T L).isDomain (algebraMap T L)
  haveI : IsFractionRing T' L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) T' L
  have hm : Module.finrank L (KaehlerDifferential K L) = m := GlobalTheory.T.kaehler_finrank_fraction_field S T' K L m w hli' hsp'
  obtain rfl : r = m := hr.symm.trans hm
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower ℚ S T' e r z w hli hsp hli' hsp'
  exact ⟨_, fun i => by rw [Fin.append_left]; rfl, h1, h2⟩

theorem local_step : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' _ r₀ r₁ v hv e r bd hr h hh S T hS hT ψ hψ hsm hfS hfT hsS z n hn hli hsp hq
    P hP h₁ hh₁ hh₁P
  letI : Algebra S T := ψ.toAlgebra
  haveI : Algebra.Smooth S T := hsm
  haveI : IsScalarTower S T Ω := .of_algebraMap_eq fun s => (hψ s).symm
  haveI : IsScalarTower S Ω₀ Ω := .of_algebraMap_eq fun s => rfl
  have hr₁T : ∀ p, r₁ p ∈ T := fun p => by
    rw [hT]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle₁ : Algebra.adjoin ℚ (Set.range r₁) ≤ T := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁T p)
  letI : Algebra (Algebra.adjoin ℚ (Set.range r₁)) T := (Subalgebra.inclusion hle₁).toRingHom.toAlgebra
  have hne₁ : h₁ ≠ 0 := fun h0 => hh₁P (h0 ▸ P.zero_mem)
  haveI : IsLocalization.Away h₁ T :=
    GlobalTheory.T.adjoin_inverse_is_localization_away Ω _ T (Set.range r₁) rfl h₁ hne₁ (by rw [hT, hh₁]) hle₁
  have hdisj : Disjoint ((Submonoid.powers h₁ : Submonoid (Algebra.adjoin ℚ (Set.range r₁))) :
      Set (Algebra.adjoin ℚ (Set.range r₁))) (↑P : Set (Algebra.adjoin ℚ (Set.range r₁))) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI hPT : (P.map (algebraMap _ T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers h₁) T P hP hdisj
  have hcomap : (P.map (algebraMap _ T)).comap (algebraMap _ T) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers h₁) T hP hdisj
  obtain ⟨g, hgP, Hg⟩ := exists_away_basis S T Ω₀ Ω e r hr z hli hsp (P.map (algebraMap _ T))
  obtain ⟨k, g₀, hk⟩ := IsLocalization.Away.surj h₁ g
  have hg₀ : g₀ ∉ P := by
    intro hmem
    have h1 := Ideal.mem_map_of_mem (algebraMap _ T) hmem
    rw [← hk] at h1
    rcases hPT.mem_or_mem h1 with h2 | h2
    · exact hgP h2
    · have h3 := hPT.mem_of_pow_mem _ h2
      have h4 : h₁ ∈ (P.map (algebraMap _ T)).comap (algebraMap _ T) := h3
      rw [hcomap] at h4
      exact hh₁P h4
  refine ⟨g₀ * h₁, hP.mul_notMem hg₀ hh₁P, ?_⟩
  intro S' hS'
  have hk' : (g : Ω) * (h₁ : Ω) ^ k = (g₀ : Ω) := congrArg T.val hk
  have hg0 : g ≠ 0 := fun h0 => hgP (h0 ▸ Ideal.zero_mem _)
  have hgΩ : (g : Ω) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
  have hHΩ : (h₁ : Ω) ≠ 0 := fun h0 => hne₁ (Subtype.ext h0)
  have hg₀Ω : (g₀ : Ω) ≠ 0 := by rw [← hk']; exact mul_ne_zero hgΩ (pow_ne_zero _ hHΩ)
  have ht : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω) = (g₀ : Ω) * h₁ := rfl
  have hr₁S' : ∀ p, r₁ p ∈ S' := fun p => by
    rw [hS']; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle' : Algebra.adjoin ℚ (Set.range r₁) ≤ S' := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁S' p)
  have htS' : ((g₀ : Ω) * h₁)⁻¹ ∈ S' := by
    rw [hS', ht]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have hTS' : T ≤ S' := by
    rw [hT]
    refine Algebra.adjoin_le (Set.insert_subset ?_ (by rintro _ ⟨p, rfl⟩; exact hr₁S' p))
    have : (algebraMap Ω₀ Ω h)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (g₀ : Ω) := by
      rw [← hh₁]; field_simp
    rw [SetLike.mem_coe, this]
    exact S'.mul_mem htS' (hle' g₀.2)
  have hEq : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ (T : Set Ω)) := by
    refine le_antisymm ?_ (Algebra.adjoin_le (Set.insert_subset ?_ hTS'))
    · rw [hS']
      refine Algebra.adjoin_le (Set.insert_subset ?_ ?_)
      · have hinv : (h₁ : Ω)⁻¹ ∈ T := by
          rw [hT, hh₁]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
        have : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω)⁻¹ = (g : Ω)⁻¹ * ((h₁ : Ω)⁻¹) ^ (k + 1) := by
          rw [ht, ← hk', inv_pow, ← mul_inv, mul_assoc, ← pow_succ]
        rw [SetLike.mem_coe, this]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _))
          (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hinv)) _)
      · rintro _ ⟨p, rfl⟩
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hr₁T p))
    · have : (g : Ω)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (h₁ : Ω) ^ (k + 1) := by
        rw [← hk', mul_assoc, ← pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hHΩ), mul_one]
      rw [SetLike.mem_coe, this]
      exact S'.mul_mem htS' (S'.pow_mem (hle' h₁.2) _)
  letI : Algebra T S' := (Subalgebra.inclusion hTS').toRingHom.toAlgebra
  haveI : IsLocalization.Away g S' := GlobalTheory.T.adjoin_inverse_is_localization_away Ω T S' (T : Set Ω) (Algebra.adjoin_eq T).symm g hg0 hEq hTS'
  haveI : IsScalarTower T S' Ω := .of_algebraMap_eq fun _ => rfl
  obtain ⟨hsm', z', hz', hli', hsp'⟩ := Hg S'
  refine ⟨hsm', z', n, by omega, hli', hsp', ?_⟩
  intro q hq'
  let θ : S →+* S' := (algebraMap T S').comp ψ
  have hθ : ∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s := fun s => hψ s
  have hr₀S : ∀ p, r₀ p ∈ S := fun p => by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  rw [_root_.GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff Ω₀ Ω σ σ' r₀ r₁ v hv bd S S' θ hθ hr₀S hr₁S' q, hq (q.comap θ) (hq'.comap θ)]
  constructor
  · rintro ⟨i, hi, hmem⟩
    refine ⟨Fin.castAdd r i, by simpa using hi, ?_⟩
    rw [hz']; exact hmem
  · rintro ⟨j, hj, hmem⟩
    have hje : (j : ℕ) < e := by omega
    refine ⟨⟨j, hje⟩, hj, ?_⟩
    have : j = Fin.castAdd r ⟨j, hje⟩ := Fin.ext rfl
    rw [this, hz'] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.Ar.LocalStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieModel_exists_unique_act : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E)
    (O : Type) [CommRing O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G →
    (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) →
    ∃! ρ : O →+* Module.End R E, M.IsActOf act ρ := by
  intro S G _ R _ x E _ _ M O _ act hmon h1 hmul hadd
  have hex : ∀ a, ∃ A : E →ₗ[R] E, (∀ e, M.pt (A e) = M.pt e ≫ act a) ∧
      ∀ B : E →ₗ[R] E, (∀ e, M.pt (B e) = M.pt e ≫ act a) → B = A := by
    intro a
    have := hmon a
    exact lieModel_exists_unique_diff S G G R x E E M M (act a)
  choose A hA hAu using hex
  have hone : LinearMap.id = A 1 := hAu 1 LinearMap.id fun e => by
    rw [h1, Category.comp_id]
    rfl
  have hmul' : ∀ a b, A (a * b) = A a * A b := fun a b => (hAu (a * b) (A a * A b) fun e => by
    rw [Module.End.mul_apply, hA a, hA b, Category.assoc, ← hmul b a, mul_comm]).symm
  have hadd' : ∀ a b, A (a + b) = A a + A b := fun a b => (hAu (a + b) (A a + A b) fun e => by
    rw [LinearMap.add_apply, M.add, hA a, hA b, ← MonObj.comp_mul, hadd]).symm
  refine ⟨RingHom.mk' { toFun := A, map_one' := hone.symm, map_mul' := hmul' } hadd',
    fun a e => hA a e, fun ρ hρ => ?_⟩
  ext a : 1
  exact hAu a (ρ a) (hρ a)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPrimes

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : X.Opens) (hg : genPt ξ ∈ V) : Γ(X, V) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ V (genPt ξ) hg).hom

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq (V : X.Opens) (hg : genPt ξ ∈ V) (p : Cpt ξ) (hp : p.1 ∈ V) (f : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = secVal ξ V hg f := by
  change _ = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f)
  rw [← X.presheaf.germ_stalkSpecializes hp p.2]
  rfl

theorem isUnit_iff_unitAt (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p))
    (s : X.presheaf.stalk p.1) : IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro h
    have h1 : IsUnit (genMap ξ p s) := h.map (genMap ξ p)
    refine ⟨h1.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := h
    refine ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ), ?_⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    simp
  · rintro ⟨h0, -, ⟨w, hw⟩⟩
    refine IsUnit.of_mul_eq_one w (hinj ?_)
    rw [map_mul, hw, map_one]
    exact mul_inv_cancel₀ h0

theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  change hU.fromSpec y ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨y, rfl⟩

theorem exists_secVal_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genPt ξ ∈ U)
    (hs : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → a ∈ regAt ξ ⟨q, h⟩) :
    ∃ f : Γ(X, U), secVal ξ U hg f = a := by
  let ρ := secVal ξ U hg
  let I : Ideal Γ(X, U) :=
    { carrier := {r | ∃ f, ρ f = ρ r * a}
      add_mem' := by
        rintro r s ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f + g, by rw [map_add (f := _), map_add (f := _), hf, hg, add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r s ⟨f, hf⟩
        exact ⟨r * f, by rw [smul_eq_mul, map_mul, map_mul, hf, _root_.mul_assoc]⟩ }
  by_cases hI : I = ⊤
  · obtain ⟨f, hf⟩ : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
    exact ⟨f, by rw [hf, map_one, _root_.one_mul]⟩
  · exfalso
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    let q : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
    have hq : hU.fromSpec q ∈ U := fromSpec_mem hU q
    have hsp := hs _ hq
    obtain ⟨σ, hσ⟩ := ha _ hsp hq
    have hloc := hU.isLocalization_stalk' q hq
    obtain ⟨⟨r, s⟩, e⟩ := @IsLocalization.surj _ _ _ _ _
      (X.presheaf.algebra_section_stalk ⟨hU.fromSpec q, hq⟩) hloc σ
    have e' : σ * X.presheaf.germ U _ hq s.1 = X.presheaf.germ U _ hq r := e
    have e2 := congrArg (genMap ξ ⟨_, hsp⟩) e'
    rw [map_mul, hσ, genMap_germ_eq U hg ⟨_, hsp⟩ hq s.1, genMap_germ_eq U hg ⟨_, hsp⟩ hq r] at e2
    exact s.2 (hIm ⟨r, by rw [← e2, mul_comm]⟩)

theorem notMem_iff_isUnit_germ {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (hq : hU.fromSpec y ∈ U) (f : Γ(X, U)) :
    f ∉ y.asIdeal ↔ IsUnit (X.presheaf.germ U (hU.fromSpec y) hq f) := by
  rw [← X.mem_basicOpen f _ hq, ← PrimeSpectrum.mem_basicOpen]
  have h := hU.fromSpec_preimage_basicOpen f
  change _ ↔ y ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)
  rw [h]
  rfl

theorem inChart_genPt (hξ : IsCptGen ξ) {κ : Type} (x : κ → Ω) (c : κ) (hc : x c ≠ 0) :
    InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := by
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨s, hs⟩ := hξ.bij.2 (x j / x c)
  refine ⟨s, ?_⟩
  rw [← hs]
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end GlobalTheory.CompanionTheory.Ar.ChartPrimes

namespace GlobalTheory.CompanionTheory.Ar


open ChartPrimes in
theorem chart_point_of_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type)
    [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ), x c ≠ 0 →
    ∀ I : Ideal (Algebra.adjoin o (Set.range fun j => x j / x c)), I.IsPrime →
    ∃! p : Cpt ξ, InChart ξ x c p ∧ ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ I ↔ unitAt ξ p (s : Ω) := by
  intro X Ω _ ξ o _ _ κ x T c hc I hI
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hs : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h, -⟩ := (hmem q).1 hq
    exact h
  have hin : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → InChart ξ x c ⟨q, h⟩ := fun q h hq => by
    obtain ⟨_, h'⟩ := (hmem q).1 hq
    exact h'
  let ρ := secVal ξ U hg
  have hρA : ∀ f, ρ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun f =>
    (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq U hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩
  have hsurj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∃ f, ρ f = a := fun a ha =>
    exists_secVal_eq hU hg hs a fun q h hq => (T.ring c hc a).1 ha _ (hin q h hq)
  let ρ' : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) := ρ.codRestrict _ hρA
  have hρ' : ∀ f, ((ρ' f : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = ρ f := fun _ => rfl

  have key : ∀ (y : PrimeSpectrum Γ(X, U)) (h : genPt ξ ⤳ hU.fromSpec y) (f : Γ(X, U)),
      f ∉ y.asIdeal ↔ unitAt ξ ⟨hU.fromSpec y, h⟩ (ρ f) := fun y h f => by
    have hq := fromSpec_mem hU y
    rw [notMem_iff_isUnit_germ hU y hq f, ← genMap_germ_eq U hg ⟨_, h⟩ hq f]
    exact isUnit_iff_unitAt ⟨_, h⟩ (T.gen.inj _) _
  let y : PrimeSpectrum Γ(X, U) := ⟨I.comap ρ', inferInstance⟩
  have hy := fromSpec_mem hU y
  refine ⟨⟨hU.fromSpec y, hs _ hy⟩, ⟨hin _ _ hy, fun s => ?_⟩, ?_⟩
  · obtain ⟨f, hf⟩ := hsurj s s.2
    have hfs : ρ' f = s := Subtype.ext hf
    have := key y (hs _ hy) f
    rw [hf] at this
    rw [← this, ← hfs]
    rfl
  · rintro ⟨p, hp⟩ ⟨hpc, hpI⟩
    have hpU : p ∈ U := (hmem p).2 ⟨hp, hpc⟩
    obtain ⟨y', rfl⟩ : ∃ y', hU.fromSpec y' = p := ⟨_, hU.fromSpec_primeIdealOf ⟨p, hpU⟩⟩
    have hyy : y' = y := PrimeSpectrum.ext (Ideal.ext fun f => not_iff_not.1 ((key y' hp f).trans (hpI (ρ' f)).symm))
    exact Subtype.ext (congrArg (fun t => hU.fromSpec t) hyy)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordLoc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hξ : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hξ).hom f) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have h2 := congrArg (fun g => g.hom f) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom
    ((X.presheaf.germ U q.1 hq).hom f)) = _
  rw [h2]

end GlobalTheory.CompanionTheory.Ar.CoordLoc

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_iff_exists_chart_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  intro X Ω _ ξ o _ _ κ x hT c p hp a
  have hc : x c ≠ 0 := hp.1
  constructor
  · intro ha
    obtain ⟨U, hU, hUmem⟩ := hT.affine c hc
    have hpU : p.1 ∈ U := (hUmem p.1).2 ⟨p.2, hp⟩
    have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
    let φ : Γ(X, U) → Ω := fun f =>
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hgU).hom f)
    have hφA : ∀ f, φ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
      intro f
      rw [hT.ring c hc]
      intro q hq
      have hqU : q.1 ∈ U := (hUmem q.1).2 ⟨q.2, hq⟩
      exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom f, CoordLoc.genMap_germ ξ U hgU q hqU f⟩
    have hφp : ∀ f, φ f = genMap ξ p ((X.presheaf.germ U p.1 hpU).hom f) := fun f =>
      (CoordLoc.genMap_germ ξ U hgU p hpU f).symm
    have ha' : a ∈ (genMap ξ p).range := ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha'
    let xU : U := ⟨p.1, hpU⟩
    have := hU.isLocalization_stalk xU
    have hgerm : ∀ f, algebraMap Γ(X, U) (X.presheaf.stalk xU.1) f = (X.presheaf.germ U p.1 hpU).hom f :=
      fun f => rfl
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf xU).asIdeal.primeCompl
      (S := X.presheaf.stalk xU.1) g
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk xU.1) t s
    simp only at hts
    rw [hts, hgerm, hgerm] at hspec
    have hunit := IsLocalization.map_units (X.presheaf.stalk xU.1) s
    rw [hgerm] at hunit
    obtain ⟨u, hu⟩ := hunit
    refine ⟨φ s, hφA s, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hφp, ← hu]
      exact (u.isUnit.map (genMap ξ p)).ne_zero
    · exact ⟨(X.presheaf.germ U p.1 hpU).hom s, (hφp s).symm⟩
    · refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩
      rw [hφp, ← hu]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    · have hmul : φ s * genMap ξ p g = φ t := by
        rw [hφp, hφp, ← map_mul, mul_comm, hspec]
      rw [hmul]
      exact hφA t
  · rintro ⟨s, _, ⟨hs0, _, hsinv⟩, hsa⟩
    have hsa' : s * a ∈ regAt ξ p := (hT.ring c hc (s * a)).mp hsa p hp
    have heq : a = s⁻¹ * (s * a) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hs0, _root_.one_mul]
    rw [heq]
    exact Subring.mul_mem _ hsinv hsa'

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtTranslate
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_app_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}}
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (s : Γ(Y, U)) :
    valAt x (φ ⁻¹ᵁ U) h (φ.app U s) = valAt (x ≫ φ) U h' s := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_congr_point {B : Type} [CommRing B] {X : Scheme.{0}}
    {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x U h s = valAt y U h' s := by
  subst e
  rfl

theorem QFGroup.regularAt_translate :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T)
      (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t →
      ∀ (f : T → FractionRing R) (g : Γ.G.left),
        Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  intro R _ _ T _ _ Γ σ t ht f g ⟨U, hgU, s, hs⟩
  have key : ∀ h : T, Γ.pt h ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G) = Γ.pt (t * h) := by
    intro h
    rw [MonObj.comp_mul, map_mul, ← ht, Category.comp_id, ← Category.assoc, comp_toUnit]
  refine ⟨((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left ⁻¹ᵁ U, hgU, ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left.app U s, ?_⟩
  intro h hh
  have e : (Γ.pt h).left ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left = (Γ.pt (t * h)).left := by
    rw [← key h]; rfl
  have h' : ⊤ ≤ ((Γ.pt h).left ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left) ⁻¹ᵁ U := hh
  have h'' : ⊤ ≤ (Γ.pt (t * h)).left ⁻¹ᵁ U := e ▸ h'
  rw [valAt_app_pullback _ _ U hh h', valAt_congr_point e U h' h'' s]
  exact hs (t * h) h''

end GlobalTheory.CompanionTheory.Ar.BT
end

