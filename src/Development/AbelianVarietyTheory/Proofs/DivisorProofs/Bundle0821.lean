module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.AdelicGLn
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusMapOfCharHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace TorusOfCharMap

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem ext_chV {Z : Over S} {a b : Z ⟶ splitTorus S X} (h : ∀ χ, chV a χ = chV b χ) : a = b :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => h χ.toAdd)

theorem chV_torusMap (ρ : X' →+ X) (χ : X') :
    chV (SplitTorusPow.torusMap S ρ) χ = charUnit S X (ρ χ) := by
  ext1
  rw [chV_val]
  exact SplitTorusPow.torusMap_char ρ χ

theorem chV_comp_torusMap (ρ : X' →+ X) {Z : Over S} (s : Z ⟶ splitTorus S X) (χ : X') :
    chV (s ≫ SplitTorusPow.torusMap S ρ) χ = chV s (ρ χ) := by
  unfold chV
  rw [SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_comp {X'' : Type} [AddCommGroup X''] (ρ : X' →+ X) (σ : X'' →+ X') :
    SplitTorusPow.torusMap S ρ ≫ SplitTorusPow.torusMap S σ = SplitTorusPow.torusMap S (ρ.comp σ) := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S ρ ≫ _), ← Category.assoc, chV_comp_torusMap,
    chV_comp_torusMap, ← Category.id_comp (SplitTorusPow.torusMap S (ρ.comp σ)), chV_comp_torusMap]
  rfl

theorem torusMap_id : SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S _), chV_comp_torusMap]
  rfl

end TorusOfCharMap

theorem splitTorus_map_of_charHom : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (X' : Type) [AddCommGroup X'] (ρ : X' →+ X), (∃ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ))) ∧ ∀ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ)) → IsMonHom τ ∧ (Function.Bijective ρ → IsIso τ) ∧ ∀ (Z : Over S) (s : Z ⟶ splitTorus S X) (χ : X'), chV (s ≫ τ) χ = chV s (ρ χ) := by
  intro S X _ X' _ ρ
  have key : ∀ τ : splitTorus S X ⟶ splitTorus S X', (∀ χ, chV τ χ = charUnit S X (ρ χ)) →
      τ = SplitTorusPow.torusMap S ρ := fun τ h =>
    TorusOfCharMap.ext_chV fun χ => (h χ).trans (TorusOfCharMap.chV_torusMap ρ χ).symm
  refine ⟨⟨_, TorusOfCharMap.chV_torusMap ρ⟩, fun τ h => ?_⟩
  obtain rfl := key τ h
  refine ⟨SplitTorusPow.isMonHom_torusMap ρ, fun hb => ?_, fun Z s χ => TorusOfCharMap.chV_comp_torusMap ρ s χ⟩
  let e : X' ≃+ X := AddEquiv.ofBijective ρ hb
  refine ⟨⟨SplitTorusPow.torusMap S e.symm.toAddMonoidHom, ?_, ?_⟩⟩
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X)
    ext x
    exact e.apply_symm_apply x
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X')
    ext x
    exact e.symm_apply_apply x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevel
section
open NumberField

namespace GlobalTheory.NeatLevel

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma val_pow_apply (W : Submodule R M) (S : Module.End R W) (T : Module.End R M)
    (hST : ∀ y : W, ((S y : W) : M) = T y) (k : ℕ) (y : W) :
    (((S ^ k) y : W) : M) = (T ^ k) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hST]

end GlobalTheory.NeatLevel

theorem GlobalTheory.sub_mem_smul_top_of_neat_level : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by

  intro E _ _ La Λ Q _ _ _ _ _ _ J n N m g₁ g₂ I₁ I₂ ev ψ θ F gM hfin htf hn hnJ hev hevs hψ hψs hFθ hθ hN hFN hg₁ hg₂ hg hI₁ hI₂ hgI₁ hgI₂ hJI₁ hJI₂ hu₁ hu₂
  have hevJ : ∀ c : 𝓞 E, c ∈ J → ∀ a, c • ev a = 0 := by
    intro c hc a
    rw [← map_smul, hev]
    exact Submodule.smul_mem_smul hc trivial
  have hevψ : ∀ a, ∃ μ, ψ μ = ev a := by
    intro a; apply hψs
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact hevJ _ hnJ a
  set G := F ^ (N - 1) with hGdef
  have hGF : G * F = 1 := by
    rw [hGdef, ← pow_succ, Nat.sub_add_cancel hN, hFN]
  have hFG : F * G = 1 := by
    rw [hGdef, ← pow_succ', Nat.sub_add_cancel hN, hFN]
  have hFGl : ∀ l, F (G l) = l := fun l => by
    rw [← Module.End.mul_apply, hFG, Module.End.one_apply]
  have hGFl : ∀ l, G (F l) = l := fun l => by
    rw [← Module.End.mul_apply, hGF, Module.End.one_apply]
  have hkey : ∀ (l : Λ) (a : La), ψ l = ev a → ψ (G l) = ev (gM a) := by
    intro l a hla
    obtain ⟨μ, hμ⟩ := hevψ (gM a)
    have h1 : ψ (F (μ - G l)) = 0 := by
      rw [map_sub, map_sub, hFθ, hμ, hθ, hFGl, hla, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 h1
    have h2 : μ - G l = n • G b' := by
      rw [← map_nsmul, ← hb', hGFl]
    have h3 : ψ (μ - G l) = 0 := (hψ _).2 ⟨G b', h2⟩
    rw [map_sub, sub_eq_zero] at h3
    rw [← h3, hμ]
  let W : Submodule (𝓞 E) Λ := (LinearMap.range ev).comap ψ
  have hGW : ∀ l ∈ W, G l ∈ W := by
    rintro l ⟨a, ha⟩; exact ⟨gM a, (hkey l a ha.symm).symm⟩
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {(n : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hnJ)
  have hJ'W : ∀ c' : 𝓞 E, c' ∈ J' → ∀ l, c' • l ∈ W := by
    intro c' hc' l
    obtain ⟨a, ha⟩ := hevs (ψ (c' • l)) (by
      intro c hc
      have hcc : c * c' ∈ Ideal.span {(n : 𝓞 E)} := by rw [hJ']; exact Ideal.mul_mem_mul hc hc'
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hcc
      rw [← map_smul, smul_smul, ← hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
      exact (hψ _).2 ⟨_, rfl⟩)
    exact ⟨a, ha⟩
  have hnW : ∀ I : Ideal (𝓞 E), J ≤ I → ∀ l : Λ, n • l ∈ I • W := by
    intro I hJI l
    have h1 : (n : 𝓞 E) • l ∈ (J * J') • (⊤ : Submodule (𝓞 E) Λ) :=
      Submodule.smul_mem_smul (by rw [← hJ']; exact Ideal.mem_span_singleton_self _) trivial
    rw [Submodule.mul_smul, Nat.cast_smul_eq_nsmul] at h1
    exact Submodule.smul_mono hJI (Submodule.smul_le.2 fun c' hc' l _ => hJ'W c' hc' l) h1
  have hpow : ∀ k (l : Λ) (a : La), ψ l = ev a → ψ (((G - 1 : Module.End (𝓞 E) Λ) ^ k) l) = ev (((gM - 1 : Module.End (𝓞 E) La) ^ k) a) := by
    intro k
    induction k with
    | zero => intro l a h; simpa using h
    | succ k ih =>
      intro l a h
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      apply ih
      simp [map_sub, hkey l a h, h]
  have hunipW : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ l ∈ W, ((G - 1) ^ m) l ∈ I • W := by
    rintro I hJI hu l ⟨a, ha⟩
    have hx := hpow m l a ha.symm
    have hmem : ev (((gM - 1) ^ m) a) ∈ (I • W).map ψ := by
      have h1 : ev (((gM - 1) ^ m) a) ∈ (I • (⊤ : Submodule (𝓞 E) La)).map ev := ⟨_, hu a, rfl⟩
      rw [Submodule.map_smul'', Submodule.map_top] at h1
      rw [Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_ h1
      rintro _ ⟨b, rfl⟩
      obtain ⟨μ, hμ⟩ := hevψ b
      exact ⟨μ, ⟨b, hμ.symm⟩, hμ⟩
    obtain ⟨z, hz, hzx⟩ := hmem
    have hd : ψ (((G - 1) ^ m) l - z) = 0 := by rw [map_sub, hzx, hx, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 hd
    have : ((G - 1) ^ m) l = z + n • b' := by rw [← hb']; abel
    rw [this]; exact Submodule.add_mem _ hz (hnW I hJI b')
  haveI := hfin; haveI := htf
  let Gr : Module.End (𝓞 E) W := G.restrict hGW
  have hGr : ∀ y : W, ((Gr y : W) : Λ) = G y := fun y => rfl
  have hGr1 : ∀ y : W, (((Gr - 1) y : W) : Λ) = (G - 1) y := fun y => rfl
  have hGN : G ^ N = 1 := by
    rw [hGdef, ← pow_mul, mul_comm, pow_mul, hFN, one_pow]
  have hGrN : Gr ^ N = 1 := by
    apply LinearMap.ext; intro y; apply Subtype.ext
    rw [GlobalTheory.NeatLevel.val_pow_apply W Gr G hGr, hGN]; rfl
  have hsub : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ y : W, ((Gr - 1) ^ m) y ∈ I • (⊤ : Submodule (𝓞 E) W) := by
    intro I hJI hu y
    have h1 : ((((Gr - 1) ^ m) y : W) : Λ) ∈ (I • (⊤ : Submodule (𝓞 E) W)).map W.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top, GlobalTheory.NeatLevel.val_pow_apply W (Gr - 1) (G - 1) hGr1]
      exact hunipW I hJI hu y y.2
    obtain ⟨z, hz, hzy⟩ := h1
    have hzz : z = ((Gr - 1) ^ m) y := Subtype.ext hzy
    rwa [← hzz]
  have hGr1' : Gr = 1 := GlobalTheory.eq_one_of_finite_order_unipotent_mod_two_primes E W Gr N m g₁ g₂ I₁ I₂
    hN hGrN hg₁ hg₂ hg hI₁ hI₂ hgI₁ hgI₂ (hsub I₁ hJI₁ hu₁) (hsub I₂ hJI₂ hu₂)
  intro a
  obtain ⟨l, hl⟩ := hevψ a
  have hlW : l ∈ W := ⟨a, hl.symm⟩
  have hGl : G l = l := by
    have := congrArg (fun T : Module.End (𝓞 E) W => ((T ⟨l, hlW⟩ : W) : Λ)) hGr1'
    exact (hGr ⟨l, hlW⟩).symm.trans (by simpa using this)
  have h := hkey l a hl
  rw [hGl, hl] at h
  rw [← hev, map_sub, ← h, sub_self]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.SumWCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def cj (E : Type) [Field E] [StarRing E] : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := RingOfIntegers.ext (star_star (x : E))

theorem cj_algMap (hc : CMData F E) (x : 𝓞 F) : cj E (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
  RingOfIntegers.ext ((hc.fixed _).2 ⟨x, rfl⟩)

theorem exists_norm (hc : CMData F E) (y : 𝓞 E) : ∃ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) x = y * cj E y := by
  obtain ⟨a, ha⟩ := (hc.fixed ((y * cj E y : 𝓞 E) : E)).1 (by
    rw [← cj_coe, map_mul, cj_cj, mul_comm])
  have hi : IsIntegral ℤ a := by
    have h1 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact (y * cj E y).isIntegral_coe
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨a, hi⟩, RingOfIntegers.ext ha⟩

end Places

variable {D : D7}

theorem goodAt_comp {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ} {ι κ J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ))
    (e : ι → κ) (he : Function.Surjective e) (s : κ → LevelCuspCharacters.SSParam p K r) :
    LevelCuspCharacters.GoodAt χ (fun v => s (e v)) ↔ LevelCuspCharacters.GoodAt χ s := by
  simp only [LevelCuspCharacters.GoodAt, he.forall, he.exists]

theorem coeff_centralIdem {G : Type} [Group G] [Finite G] (τ : G → ℂ) (x : G) :
    (LevelCuspCharacters.centralIdem τ).coeff x = τ 1 / (Nat.card G : ℂ) * τ x⁻¹ := by
  classical
  unfold LevelCuspCharacters.centralIdem
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

section Match

variable {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (pl : LevelCuspCharacters.Sq D.host ≃ ↥(GoodIdempotentBadPlaces.typePl pb))
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1))



end Match

end GlobalTheory.SumWCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory

namespace GlobalTheory.WhitBump

abbrev Idx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Vp (E : Type) [Field E] (n : ℕ) : Type := Idx n → Cinf E

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def nu (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else if i = j then 1 else 0

def sdM {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, x i j

theorem superDiag_eq_sdM {R : Type} [CommRing R] (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag g = sdM (g : Matrix (Fin n) (Fin n) R) := rfl

theorem nu_lower (t : Vp E n) {i j : Fin n} (h : j < i) : nu t i j = 0 := by
  simp [nu, not_lt_of_gt h, ne_of_gt h]

theorem nu_diag (t : Vp E n) (i : Fin n) : nu t i i = 1 := by
  simp [nu]

theorem det_nu (t : Vp E n) : (nu t).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [nu_diag]
  · intro i j h; exact nu_lower t h

def nuGL (t : Vp E n) : GL (Fin n) (Cinf E) :=
  Matrix.nonsingInvUnit (nu t) (by rw [det_nu]; exact isUnit_one)

@[simp] theorem nuGL_val (t : Vp E n) : (nuGL t : Matrix (Fin n) (Fin n) (Cinf E)) = nu t := rfl

theorem nuGL_mem (t : Vp E n) : nuGL t ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun _ _ h => nu_lower t h, nu_diag t⟩

variable [_root_.NumberField.IsTotallyComplex E]

def psiInf (z : Cinf E) : ℂ := (GroundTheory.Global.adelicChar E (sInf E z) : ℂ)

def psiFin (a : Af E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E a) : ℂ)

def bumpInf (f : Lie E n → ℝ) (x : Lie E n) : ℂ :=
  ∫ t : Vp E n, (f (toL (nu t * Matrix.of x)) : ℂ) * psiInf (-sdM (nu t))


open Classical in
def bumpFin (g : GL (Fin n) (Af E)) : ℂ :=
  if h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n then
    psiFin (GlobalTheory.Whittaker.superDiag h.choose) else 0

end GlobalTheory.WhitBump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrScaleNeZeroAt
section
noncomputable section

open NumberField Polynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.FamSep

section General

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

theorem trScale_ne_zero_at {P : Pl0} (hq : A.q P ≠ 0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem typesSep_of_local (hq : ∀ P : (A.fam.R A.fam.μ0).Pl, A.q ((A.fam.R A.fam.μ0).pl P) ≠ 0)
    (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (trScale_ne_zero_at A (hq P)) (A.const_of h0 Sg hSg _) (A.const_of h0 Sg' hSg' _) h)⟩

theorem typesSep_of_ok {s : ℕ} (hOk : A.fam.Ok s) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep :=
  typesSep_of_local A (fun P => ((hOk.what₂ A.fam.μ0).q_pos P).ne') h0

end General

section Real

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Real

end GlobalTheory.FamSep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_transport : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 0 < N → UnifAt F σ ρ N D' t P y e → IsMarkedIsom N D' D'' t t' w → (∀ x, P' (w x) = h (P x)) → IsPeriod D'' ρ P' → UnifAt F σ ρ N D'' t' P' y (fun z => e (h.symm z)) := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e w h hN hU hW hPP' hP'
  obtain ⟨hy, hP, hexp, hker, hact, hweil, heta⟩ := hU
  obtain ⟨hiso, hmark⟩ := hW
  have hQs : ∀ x, h.symm (P' x) = P (w.symm x) := by
    intro x
    rw [h.symm_apply_eq, ← hPP', w.apply_symm_apply]

  have hcomm : ∀ a z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    have hL : ((h.toLinearMap ∘ₗ Matrix.mulVecLin (ρ a)).restrictScalars ℝ) =
        ((Matrix.mulVecLin (ρ a) ∘ₗ h.toLinearMap).restrictScalars ℝ) := by
      apply LinearMap.ext_on hP.2.2.2.1
      rintro _ ⟨x, rfl⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
        Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
      rw [← hP.1, ← hPP', ← hPP', map_smul, hP'.1]
    exact congrArg (fun f => f z) hL
  have hcomm' : ∀ a z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    rw [h.symm_apply_eq, hcomm, h.apply_symm_apply]
  set hc := h.symm.toContinuousLinearEquiv with hhc
  have hcc : ∀ z, hc z = h.symm z := fun z => rfl
  have hder : ∀ u v, IsDerivAt0 (fun z => (e (h.symm z)).left) u v ↔ IsDerivAt0 (fun z => (e z).left) (h.symm u) v := by
    intro u v
    unfold IsDerivAt0
    simp only [map_zero]
    refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
    have key := hc.comp_right_fderiv (f := fun z => valAt' (e z).left U f) (x := 0)
    have e1 : ((fun z => valAt' (e z).left U f) ∘ hc) = (fun z => valAt' (e (h.symm z)).left U f) := rfl
    rw [e1, map_zero] at key
    rw [key]
    rfl
  refine ⟨hy, hP', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro z z'
    simp only [map_add (f := _)]
    exact hexp.1 _ _
  · exact hexp.2.1.comp h.symm.surjective
  · intro U f
    obtain ⟨ho, hd⟩ := hexp.2.2.1 U f
    have hs : {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e (h.symm b)).left ⁻¹ᵁ U} =
        hc ⁻¹' {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e b).left ⁻¹ᵁ U} := by
      ext b; simp [hcc]
    rw [hs]
    exact ⟨ho.preimage hc.continuous, hd.comp hc.differentiableOn (Set.mapsTo_preimage _ _)⟩
  · intro u
    obtain ⟨v, hv, huniq⟩ := hexp.2.2.2.1 (h.symm u)
    exact ⟨v, (hder u v.left).2 hv, fun v' hv' => huniq v' ((hder u v'.left).1 hv')⟩
  · intro v hv
    dsimp only at hv
    rw [map_zero] at hv
    obtain ⟨u, hu, huniq⟩ := hexp.2.2.2.2 v hv
    refine ⟨h u, (hder (h u) v.left).2 (by rwa [h.symm_apply_apply]), fun u' hu' => ?_⟩
    rw [← huniq (h.symm u') ((hder u' v.left).1 hu'), h.apply_symm_apply]
  · intro z
    rw [hker]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨w x, by rw [hPP', hx, h.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, (hQs x).symm⟩
  · intro a z
    dsimp only
    rw [hcomm', hact]
  · intro k a b c hk hc'
    have h1 := hweil k (w.symm a) (w.symm b) c hk (by
      rw [hc', ← hiso (w.symm a) (w.symm b), w.apply_symm_apply, w.apply_symm_apply])
    simpa only [map_smul, hQs] using h1
  · intro a
    obtain ⟨x, hx⟩ := hmark a
    rw [heta a]
    have h1 : t' a = w (t a - N • w.symm x) := by
      rw [map_sub, map_nsmul, w.apply_symm_apply, hx, add_sub_cancel_right]
    have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h2 : h.symm ((N : ℂ)⁻¹ • P' (t' a)) = (N : ℂ)⁻¹ • P (t a) + P (-(w.symm x)) := by
      rw [h1, hPP', map_smul, h.symm_apply_apply, map_sub, map_nsmul, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hN', one_smul, map_neg, sub_eq_add_neg]
    dsimp only
    rw [h2, hexp.1, (hker _).2 ⟨_, rfl⟩, _root_.mul_one]

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishingForms_iff_proportional_pullbacks : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔ ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  first | (exact @GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (exact GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (intros; apply GlobalTheory.HomFixUniv.formsOK_iff_exists_proport  <;> assumption)
end

