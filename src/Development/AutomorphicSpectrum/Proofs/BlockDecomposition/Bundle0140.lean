module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0132
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransport
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem map_mem_closedNormal {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B) (X : Set A) (Y : Set B)
    (h : ∀ a ∈ X, Φ a ∈ Y) {a : A} (ha : a ∈ (Subgroup.normalClosure X).topologicalClosure) :
    Φ a ∈ (Subgroup.normalClosure Y).topologicalClosure := by
  let f : A →* B := (Φ : A ≃* B).toMonoidHom
  let K : Subgroup B := (Subgroup.normalClosure Y).topologicalClosure
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  haveI : (K.comap f).Normal := Subgroup.Normal.comap ‹_› f
  have hK : IsClosed (K : Set B) := Subgroup.isClosed_topologicalClosure _
  have hc : IsClosed ((K.comap f : Subgroup A) : Set A) := hK.preimage Φ.continuous
  have hle : Subgroup.normalClosure X ≤ K.comap f := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (h x hx))
  exact Subgroup.topologicalClosure_minimal _ hle hc ha

def quotientIso {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B)
    (H : Subgroup A) (K : Subgroup B) [H.Normal] [K.Normal] (h : ∀ a, a ∈ H ↔ Φ a ∈ K) :
    A ⧸ H ≃ₜ* B ⧸ K where
  toMulEquiv := QuotientGroup.congr H K (Φ : A ≃* B) (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro hb
      exact ⟨Φ.symm b, (h _).2 (by simpa using hb), Φ.apply_symm_apply b⟩)
  continuous_toFun := by
    exact (QuotientGroup.isQuotientMap_mk H).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.continuous)
  continuous_invFun := by
    exact (QuotientGroup.isQuotientMap_mk K).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.symm.continuous)

theorem exists_gsIso : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E _ Φ _ eV hP hI T T' hT
  have hfwd : ∀ σ, σ ∈ NS Ω T → Φ σ ∈ NS Ω' T' := by
    intro σ hσ
    refine map_mem_closedNormal Φ _ _ ?_ hσ
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    let A' : ValuationSubring Ω' := A.comap (E.symm : Ω' →+* Ω)
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := by
      intro x
      show E.symm (E x) ∈ A ↔ x ∈ A
      simp
    exact ⟨eV v, fun h => hv ((hT v).2 h), A', (hP A A' hAA v).1 hA, (hI A A' hAA τ).1 hτ⟩
  have hbwd : ∀ σ', σ' ∈ NS Ω' T' → Φ.symm σ' ∈ NS Ω T := by
    intro σ' hσ'
    refine map_mem_closedNormal Φ.symm _ _ ?_ hσ'
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v', hv', A', hA', hτ⟩ := hτ
    let A : ValuationSubring Ω := A'.comap (E : Ω →+* Ω')
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => Iff.rfl
    refine ⟨eV.symm v', fun h => hv' ?_, A, ?_, ?_⟩
    · simpa using (hT _).1 h
    · refine (hP A A' hAA _).2 ?_
      simpa using hA'
    · refine (hI A A' hAA _).2 ?_
      simpa using hτ
  have hiff : ∀ σ, σ ∈ NS Ω T ↔ Φ σ ∈ NS Ω' T' := fun σ =>
    ⟨hfwd σ, fun h => by simpa using hbwd _ h⟩
  exact ⟨quotientIso Φ (NS Ω T) (NS Ω' T') hiff, fun σ => rfl⟩

end GlobalTheory.CompanionTheory.PTIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseLimitCohomologyComparison
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LimLift

open CrystallineSemistableComparison.CechClassBoundaries

variable {R : Type} [CommRing R]

theorem cls_congr {K : Cx.{1} R} {j : ℕ} {a b : K.X j} (h : a = b) (ha : K.d j a = 0) (hb : K.d j b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h
  rfl

theorem pow_tf {K : Cx.{1} R} {c : R} (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (n j : ℕ) (x : K.X j)
    (h : c ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_smul] at h
    exact ih (ht _ _ h)

theorem ker_red {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (j : ℕ) (z : K.H j) (hz : r.mapH j z = 0) :
    ∃ y, z = c ^ n • y := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), (CrystallineSemistableComparison.P.cls_surj L j).2.1] at hz
  have hv : ∃ v : K.X j, v ∈ K.B j ∧ K.d j v = 0 ∧ r.f j (a - v) = 0 := by
    cases j with
    | zero =>
      refine ⟨0, (mem_boundaries_zero_iff _).2 rfl, map_zero _, ?_⟩
      rw [sub_zero]
      exact (mem_boundaries_zero_iff _).1 hz
    | succ j =>
      obtain ⟨b, hb⟩ := (mem_Bs _).1 hz
      obtain ⟨v, rfl⟩ := hs j b
      refine ⟨K.d j v, (mem_Bs _).2 ⟨v, rfl⟩, K.dd j v, ?_⟩
      rw [map_sub, ← r.comm, hb, sub_self]
  obtain ⟨v, hvB, hvd, h0⟩ := hv
  obtain ⟨y, hy⟩ := (hk j _).1 h0
  have hdy : K.d j y = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hy, map_sub, ha, hvd, sub_zero]
  refine ⟨K.cls y hdy, ?_⟩
  have hcy : K.d j (c ^ n • y) = 0 := by rw [map_smul, hdy, smul_zero]
  rw [← cls_smul _ _ hdy hcy, (CrystallineSemistableComparison.P.cls_surj K j).2.2.1 _ _ ha hcy, ← hy]
  simpa using hvB

theorem kill_H {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (j : ℕ) (h : L.H j) : c ^ n • h = 0 := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 h
  obtain ⟨a, rfl⟩ := hs j w
  have h0 : c ^ n • r.f j a = 0 := by
    rw [← map_smul]
    exact (hk j _).2 ⟨a, rfl⟩
  have hd : L.d j (c ^ n • r.f j a) = 0 := by rw [h0, map_zero]
  rw [← cls_smul _ _ hw hd, (CrystallineSemistableComparison.P.cls_surj L j).2.1, h0]
  exact zero_mem _

theorem lift_level {K L : Cx.{1} R} (c : R) (n k j : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0)
    (hA : ∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) (x : L.H j) :
    ∃ y : K.H j, r.mapH j y = c ^ k • x := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 x
  obtain ⟨a, rfl⟩ := hs j w
  have h1 : r.f (j + 1) (K.d j a) = 0 := by rw [← r.comm]; exact hw
  obtain ⟨b, hb⟩ := (hk (j + 1) _).1 h1
  have hdb : K.d (j + 1) b = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hb, K.dd]
  have hcb : K.d (j + 1) (c ^ n • b) = 0 := by rw [map_smul, hdb, smul_zero]
  have h2 : c ^ n • K.cls b hdb = 0 := by
    rw [← cls_smul _ _ hdb hcb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]
    exact (mem_Bs _).2 ⟨a, hb⟩
  have h3 := hA _ n h2
  have hkb : K.d (j + 1) (c ^ k • b) = 0 := by rw [map_smul, hdb, smul_zero]
  rw [← cls_smul _ _ hdb hkb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1] at h3
  obtain ⟨e, he⟩ := (mem_Bs _).1 h3
  have hy : K.d j (c ^ k • a - c ^ n • e) = 0 := by
    rw [map_sub, map_smul, map_smul, he, hb, smul_smul, smul_smul, mul_comm, sub_self]
  have hr : r.f j (c ^ k • a - c ^ n • e) = c ^ k • r.f j a := by
    rw [map_sub, (hk j _).2 ⟨e, rfl⟩, sub_zero, map_smul]
  have hd : L.d j (c ^ k • r.f j a) = 0 := by rw [map_smul, hw, smul_zero]
  refine ⟨K.cls _ hy, ?_⟩
  rw [mapH_cls' r _ hy (cyc r _ hy), ← cls_smul _ _ hw hd]
  exact cls_congr hr _ _

theorem mapH_tr {K L M : Cx.{1} R} (r : Cx.Hom K L (RingHom.id R)) (r' : Cx.Hom K M (RingHom.id R))
    (t : Cx.Hom L M (RingHom.id R)) (j : ℕ) (h : ∀ x, t.f j (r.f j x) = r'.f j x) (z : K.H j) :
    t.mapH j (r.mapH j z) = r'.mapH j z := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), mapH_cls' t _ _ (cyc t _ (cyc r a ha)), mapH_cls' r' a ha (cyc r' a ha)]
  exact cls_congr (h a) _ _

theorem lim_lift : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  intro R _ K Kn c red tr hc hs hk ht j k hA hB hC
  refine ⟨fun x hx => ?_, fun z hz => hB z fun n => ker_red c n (red n) (hs n) (hk n) ht j z (hz n)⟩
  choose y hy using fun n => lift_level c n k j (red n) (hs n) (hk n) ht hA (x n)
  have hdiff : ∀ n, ∃ u, y (n + 1) - y n = c ^ n • u := by
    intro n
    refine ker_red c n (red n) (hs n) (hk n) ht j _ ?_
    rw [map_sub, ← mapH_tr (red (n + 1)) (red n) (tr n) j (hc n j), hy, hy, map_smul, hx, sub_self]
  obtain ⟨z, hz⟩ := hC y hdiff
  refine ⟨z, fun n => ?_⟩
  obtain ⟨u, hu⟩ := hz n
  have e : z = c ^ k • y n + c ^ n • u := by rw [← hu]; abel
  rw [e, map_add (f := _), map_smul, map_smul, hy, kill_H c n (red n) (hs n) (hk n), add_zero, smul_smul, ← pow_add, two_mul]

end GlobalTheory.CompanionTheory.LimLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeCocyclesLiftToNerve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.LowDict

theorem exists_quot_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (K : Submodule R M) (Z : Submodule R N) (hK : ∀ x, x ∈ K ↔ e x ∈ Z)
    (BK : Submodule R K) (BZ' : Submodule R Z)
    (hB : ∀ (x : K) (f : Z), e x.1 = f.1 → (x ∈ BK ↔ f ∈ BZ')) :
    ∃ u : (Z ⧸ BZ') ≃ₗ[R] (K ⧸ BK),
      (∀ (f : Z) (x : K), e x.1 = f.1 → u (BZ'.mkQ f) = BK.mkQ x) ∧ ∀ f : Z, ∃ x : K, e x.1 = f.1 := by
  have hmap : K.map (e : M →ₗ[R] N) = Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨e.symm y, (hK _).2 (by simpa using hy), by simp⟩
  let v : K ≃ₗ[R] Z := e.ofSubmodules K Z hmap
  have hv : ∀ x : K, (v x).1 = e x.1 := fun _ ↦ rfl
  have hq : BZ'.map (v.symm : Z →ₗ[R] K) = BK := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine (hB _ f ?_).2 hf
      rw [← hv]
      simp
    · intro hx
      exact ⟨v x, (hB x (v x) (hv x).symm).1 hx, by simp⟩
  refine ⟨Submodule.Quotient.equiv BZ' BK v.symm hq, fun f x h ↦ ?_, fun f ↦ ⟨v.symm f, ?_⟩⟩
  · have hx : v.symm f = x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext h.symm
    rw [← hx]
    rfl
  · rw [← hv]
    simp

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

theorem Z2_eq_ker : Z2 F = LinearMap.ker (d2 F) := by
  ext z
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · refine LinearMap.mem_ker.2 ?_
    funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.1 h) T) T') T'') T''') φ) ψ) χ
    rw [d2_apply] at this
    simp only [Pi.zero_apply] at this
    linear_combination -this

theorem dict_low : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∃ (u₁ : H1 F ≃ₗ[R] HH F 1) (u₂ : H2 F ≃ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁.toLinearMap ∧ IsDegreeTwoComparison F u₂.toLinearMap ∧
      (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) ∧
      (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) := by
  intro hD R _ C _ F
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, -, h₀, h₁, h₂⟩ := hD R C F
  have k₁ : ∀ x, x ∈ Zc F 1 ↔ e₁ x ∈ Z1 F := fun x ↦ by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₁, LinearEquiv.map_eq_zero_iff]
  have k₂ : ∀ x, x ∈ Zc F 2 ↔ e₂ x ∈ Z2 F := fun x ↦ by
    rw [Z2_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₂, LinearEquiv.map_eq_zero_iff]
  have b₁ : ∀ (x : Zc F 1) (f : Z1 F), e₁ x.1 = f.1 →
      (x ∈ BZ F 1 ↔ f ∈ LinearMap.range ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₀ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₀, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₀.symm g, e₁.injective ?_⟩
      rw [h₀, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  have b₂ : ∀ (x : Zc F 2) (f : Z2 F), e₂ x.1 = f.1 →
      (x ∈ BZ F 2 ↔ f ∈ LinearMap.range ((d1 F).codRestrict (Z2 F) (differential_one_mem_scaled_lattice F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₁ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₁, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₁.symm g, e₂.injective ?_⟩
      rw [h₁, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  obtain ⟨u₁, c₁, s₁⟩ := exists_quot_equiv e₁ (Zc F 1) (Z1 F) k₁ (BZ F 1) _ b₁
  obtain ⟨u₂, c₂, s₂⟩ := exists_quot_equiv e₂ (Zc F 2) (Z2 F) k₂ (BZ F 2) _ b₂
  refine ⟨u₁, u₂, fun f x hx ↦ c₁ f x ?_, fun f x hx ↦ c₂ f x ?_, fun f ↦ ?_, fun f ↦ ?_⟩
  · funext T T' φ
    exact (v₁ x.1 T T' φ).trans (hx T T' φ)
  · funext T T' T'' φ ψ
    exact (v₂ x.1 T T' T'' φ ψ).trans (hx T T' T'' φ ψ)
  · obtain ⟨x, hx⟩ := s₁ f
    exact ⟨x, fun T T' φ ↦ (v₁ x.1 T T' φ).symm.trans (congrFun (congrFun (congrFun hx T) T') φ)⟩
  · obtain ⟨x, hx⟩ := s₂ f
    exact ⟨x, fun T T' T'' φ ψ ↦ (v₂ x.1 T T' T'' φ ψ).symm.trans
      (congrFun (congrFun (congrFun (congrFun (congrFun hx T) T') T'') φ) ψ)⟩

end GlobalTheory.CompanionTheory.HopfC.LowDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem mk₁_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' : C} (φ : T ⟶ T') :
    (ComposableArrows.mk₁ φ ⋙ G : ComposableArrows D 1) = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)

theorem mk₂_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' T'' : C}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (ComposableArrows.mk₂ φ ψ ⋙ G : ComposableArrows D 2) = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext₂ rfl rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)
    (by show G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _; simp)

theorem dictionary_pull : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  intro R _ C C' _ _ F F' m u₁ u₁' u₂ u₂' h1 h1' h2 h2' e1 e2
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    obtain ⟨x, hx⟩ := e1 f
    rw [h1 f x hx, pullH_mk, CoefMap.pullCohomologyOne_class]
    refine h1' _ _ fun T T' φ ↦ ?_
    have e : x.1 (ComposableArrows.mk₁ φ ⋙ m.G) = x.1 (ComposableArrows.mk₁ (m.G.map φ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₁_comp_functor m.G φ))
    exact (congrArg (m.α T') (e.trans (hx _ _ _)))
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    obtain ⟨x, hx⟩ := e2 f
    rw [h2 f x hx, pullH_mk, CoefMap.pullCohomologyTwo_class]
    refine h2' _ _ fun T T' T'' φ ψ ↦ ?_
    have e : x.1 (ComposableArrows.mk₂ φ ψ ⋙ m.G) = x.1 (ComposableArrows.mk₂ (m.G.map φ) (m.G.map ψ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₂_comp_functor m.G φ ψ))
    exact (congrArg (m.α T'') (e.trans (hx _ _ _ _ _)))

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasis
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}

def topEquiv : (⊤ : AddSubmonoid (Gam n d)) ≃ Gam n d := Equiv.Set.univ _

def lrBasis : Module.Basis (Gam n d) K (Lr K n d) :=
  (Module.Basis.ofRepr (AddMonoidAlgebra.coeffLinearEquiv K)).reindex topEquiv

theorem lrBasis_apply (g : Gam n d) : lrBasis (K := K) g = monL K g := by
  rw [lrBasis, Module.Basis.reindex_apply, Module.Basis.coe_ofRepr]
  rfl

def setEquiv (a : ℕ) : {D : Finset (E n d) // D.card = a} ≃ Set.powersetCard (Fin (n + d)) a where
  toFun D := ⟨D.1.map finSumFinEquiv.toEmbedding, by simpa using D.2⟩
  invFun s := ⟨s.1.map finSumFinEquiv.symm.toEmbedding, by simp⟩
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv s := by
    apply Subtype.ext
    ext x
    simp

theorem wedge_basis (bΩ : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K]) (h : ∀ e, bΩ e = dl e) (a : ℕ) :
    ∃ c : Module.Basis {D : Finset (E n d) // D.card = a} (Lr K n d) (Om K (Lr K n d) a),
      ∀ D, c D = wedge (K := K) (enumD D) := by
  refine ⟨((bΩ.reindex finSumFinEquiv).exteriorPower a).reindex (setEquiv a).symm, fun D => ?_⟩
  rw [Module.Basis.reindex_apply, exteriorPower.basis_apply]
  simp only [Equiv.symm_symm]
  unfold exteriorPower.ιMulti_family wedge
  congr 1
  funext i
  simp [Module.Basis.reindex_apply, h, enumD, setEquiv, Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem monW_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  intro K _ n d a
  obtain ⟨bΩ, h⟩ := GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis.exists_basis_dl (K := K) (n := n) (d := d)
  obtain ⟨c, hc⟩ := wedge_basis bΩ h a
  refine ⟨lrBasis.smulTower c, fun p => ?_⟩
  rw [Module.Basis.smulTower_apply, lrBasis_apply, hc]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRes

theorem resZero : CrystallineSemistableComparison.E.ResZero := by
  intro R _ F U
  obtain ⟨h0, h1, -, h3⟩ := GlobalTheory.EtC.resSec R F U
  exact ⟨h1, h0, h3⟩

end GlobalTheory.CompanionTheory.EtRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem apply_eq_pow_cycMod_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω) {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have key := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) Ω σ) ζ hζ
  simpa [cycMod, cycZ] using key

theorem cycMod_intrinsic : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ l _ r σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have h1 := apply_eq_pow_cycMod_val (F := F) (Ω := Ω) l r σ hζ.pow_eq_one
  have h2 := apply_eq_pow_cycMod_val (F := F') (Ω := Ω') l r (Φ σ) (ζ := E ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  rw [hΦ, h1, map_pow] at h2
  have hv := hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  apply Units.ext
  exact ZMod.val_injective _ hv.symm

end GlobalTheory.CompanionTheory.PTIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnitStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_coordinate_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), ∀ k : Fin d, IsUnit (tV i y hy V hV k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | exact GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | (intros; apply GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit <;> assumption)
end

