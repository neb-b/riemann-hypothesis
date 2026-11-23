module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualIntegralLattice
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DualLatticeFamily
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualLatticeFamily

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.dotDual
  simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

noncomputable def dotB (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) (fun a a' b => add_dotProduct a a' b)
    (fun c a b => smul_dotProduct c a b) (fun a b b' => dotProduct_add a b b')
    (fun c a b => dotProduct_smul c a b)

theorem dotB_apply {Ω : Type} [Field Ω] {r : ℕ} (a b : Fin r → Ω) : dotB Ω r a b = a ⬝ᵥ b := rfl

theorem dotB_bij (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotB Ω r).flip := by
  classical
  refine ⟨fun a b h => funext fun i => ?_, fun ψ => ⟨fun i => ψ (Pi.single i 1), ?_⟩⟩
  · have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotB_apply] using this
  · refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin r → Ω) = x • (Pi.single i 1 : Fin r → Ω) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [LinearMap.flip_apply, dotB_apply, single_dotProduct, hx, map_smul, smul_eq_mul]

theorem overlap {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {T : Type} (x : T → Ω) {r : ℕ}
    (i j : T) (hi : x i ≠ 0) (hj : x j ≠ 0) (Li Lj : AddSubgroup (Fin r → Ω))
    (hov : ∀ e ∈ Lj, ∃ m : ℕ, (x j / x i) ^ m • e ∈ Li) (hL : LocFree (chartRing O x j) r Lj)
    (w : Fin r → Ω) (hw : w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x i) Li) :
    ∃ m : ℕ, (x i / x j) ^ m • w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x j) Lj := by
  rw [mem_dotDual] at hw
  have hdiv : x i / x j ∈ chartRing O x j := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Ar.Num.Reflexive.exists_uniform_denominator (chartRing O x j) r Lj hL
    (x i / x j) hdiv ((dotB Ω r).flip w) fun e he => by
      obtain ⟨m, hm⟩ := hov e he
      have h1 := hw _ hm
      rw [smul_dotProduct, smul_eq_mul] at h1
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, (x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w)) ∈ chartRing O x j :=
        ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing x i j hi h1
      have hone : (x i / x j) ^ m * (x j / x i) ^ m = 1 := by
        rw [← mul_pow, div_mul_div_comm, _root_.mul_comm (x i), div_self (mul_ne_zero hj hi), one_pow]
      have h2 := mul_mem (pow_mem hdiv m) hm'
      have h3 : (x i / x j) ^ m * ((x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w))) =
          (x i / x j) ^ m' * (e ⬝ᵥ w) := by
        calc _ = (x i / x j) ^ m' * (e ⬝ᵥ w) * ((x i / x j) ^ m * (x j / x i) ^ m) := by ring
          _ = _ := by rw [hone, _root_.mul_one]
      rw [h3] at h2
      exact ⟨m', h2⟩
  refine ⟨m, (mem_dotDual _ _ _).2 fun l hl => ?_⟩
  rw [dotProduct_smul, smul_eq_mul]
  exact hm l hl

end PositivityTheory.Xgn.DualLatticeFamily

open PositivityTheory.Xgn.DualLatticeFamily in
theorem PositivityTheory.Xgn.dual_lattice_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) := by
  intro O _ Ω _ _ K _ J _ y r Γ hΓ hL
  refine ⟨⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩, fun c hc => ?_⟩
  · refine (mem_dotDual _ _ _).2 fun l hl => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha ((mem_dotDual _ _ _).1 hw l hl)
  · exact overlap (mseg y) s t hs ht (Γ s) (Γ t) (hΓ.2 t s ht hs) (hL t ht) w hw
  · exact (GlobalTheory.CompanionTheory.Ar.Num.DualLattice.locFree_dual _ (dotB Ω r) (dotB_bij Ω r) r (Γ c) _ (hL c hc)
      fun w => mem_dotDual _ _ w).1
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCmTypeEmbedding
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.Xgn.exists_cm_type_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) →
      ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
    intro σ hσ σ' hσ'
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => (hσ' a).trans (hσ a).symm)
  rcases t with τ | τ
  · let φ : E →+* Ω := 𝔐.cst.comp ((τ : E →+* ℂ).codRestrict c.F (c.conj τ))
    have h1 : ∀ a : 𝓞 E, φ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨φ, h1, fun a => ?_, uniq φ h1⟩
    show φ (IsCMField.complexConj E (a : E)) = φ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq]
  · let φ : E →+* Ω := 𝔐.cst.comp ((τ : E →+* ℂ).codRestrict c.F (c.conj τ))
    have h1 : ∀ a : 𝓞 E, (φ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      show φ (IsCMField.complexConj E (a : E)) = φ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq]
    refine ⟨φ.comp (HT.cmConj E).toRingHom, h1, fun a => ?_, uniq _ h1⟩
    show φ (IsCMField.complexConj E (IsCMField.complexConj E (a : E))) = φ (a : E)
    rw [IsCMField.complexConj_apply_apply]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsFunctionAtPoint
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionAtPoint

theorem germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) (a : X.presheaf.stalk (x z)) :
    ∃ r s : R, s ∉ z.asIdeal ∧ φ s * genMap ξ ⟨x z, hz⟩ a = φ r ∧ (r ∉ z.asIdeal → IsUnit a) := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hu : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hu
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := ConcreteCategory.congr_hom e4 a
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl ((x.stalkMap z).hom a)
  refine ⟨r, s, s.2, ?_, fun hr => ?_⟩
  · rw [← e5, ← hlam, ← hlam, ← map_mul, mul_comm]
    exact congrArg lam hrs
  · have h1 : IsUnit (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z) r) :=
      IsLocalization.map_units _ (⟨r, hr⟩ : z.asIdeal.primeCompl)
    rw [← hrs] at h1
    exact isUnit_of_map_unit (x.stalkMap z).hom a (isUnit_of_mul_isUnit_left h1)

theorem inv_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) {b : Ω} (hb : b ∈ regAt ξ ⟨x z, hz⟩) (w : R)
    (hw : φ w * b = 1) : φ w ∈ regAt ξ ⟨x z, hz⟩ := by
  obtain ⟨a, rfl⟩ := hb
  obtain ⟨r, s, hs, e, hu⟩ := germ_frac ξ φ hφ x hx z hz a
  have e1 : s = w * r := by
    apply hφ
    rw [map_mul, ← e, mul_left_comm, hw, _root_.mul_one]
  have hr : r ∉ z.asIdeal := fun h => hs (e1 ▸ z.asIdeal.mul_mem_left w h)
  obtain ⟨a', ha'⟩ := (hu hr).exists_right_inv
  refine ⟨a', ?_⟩
  have e2 := congrArg (genMap ξ ⟨x z, hz⟩) ha'
  rw [map_mul, map_one] at e2
  rw [← _root_.one_mul (genMap ξ ⟨x z, hz⟩ a'), ← hw, _root_.mul_assoc, e2, _root_.mul_one]

end PositivityTheory.Xgn.FunctionAtPoint

theorem PositivityTheory.Xgn.exists_function_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd p _ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' hc' P z
  have hC : HasConstants ℤ A y := (_root_.GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd A).2.2.2.1
  have hφ : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have hinv := fun {b : Ω} (hb : b ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) (w : CR O y c') =>
    PositivityTheory.Xgn.FunctionAtPoint.inv_reg 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) hb w
  obtain ⟨c'', hc''⟩ : ∃ c'', InChart 𝔐.ξ (mseg y) c'' ⟨P.x z, 𝔐.all _⟩ := 𝔐.tie.cover ⟨P.x z, 𝔐.all _⟩
  have hA : ∀ a : A, algebraMap A Ω a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ := fun a =>
    GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt ℤ y c'' _ hc'' (fun o => by simp) (hC c'' hc''.1 a)
  refine ⟨⟨hc', fun j => ?_⟩, fun o => ?_, ?_⟩
  · have h1 : mseg y c'' / mseg y c' ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hc''.2 c') ⟨mseg y c'' / mseg y c', Algebra.subset_adjoin ⟨c'', rfl⟩⟩ (by
        have h0 := hc''.1
        change mseg y c'' / mseg y c' * (mseg y c' / mseg y c'') = 1
        field_simp)
    have h2 := mul_mem (hc''.2 j) h1
    have h0 := hc''.1
    have e : mseg y j / mseg y c'' * (mseg y c'' / mseg y c') = mseg y j / mseg y c' := by field_simp
    rwa [e] at h2
  · obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj m.primeCompl o
    obtain ⟨u, hu⟩ := (IsLocalization.map_units O s).exists_left_inv
    have h1 : algebraMap O Ω u ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hA s) (algebraMap O (CR O y c') u) (by
        change algebraMap O Ω u * _ = 1
        rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu, map_one])
    have e : o = algebraMap A O a * u := by
      have has' : o * algebraMap A O s = algebraMap A O a := has
      rw [← has', _root_.mul_assoc, mul_comm _ u, hu, _root_.mul_one]
    rw [e, map_mul, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (hA a) h1
  · rintro _ ⟨a, rfl⟩
    obtain ⟨r, s, hs, e, -⟩ :=
      PositivityTheory.Xgn.FunctionAtPoint.germ_frac 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) a
    exact ⟨r, s, hs, e⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.GramDeterminantUnitModP
section
namespace PositivityTheory.Xgn.GramDeterminantUnit
open NumberField GlobalTheory.CompanionTheory.Ar

end PositivityTheory.Xgn.GramDeterminantUnit

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.Xgn.gram_determinant_unit_mod_p : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 :=
  _root_.UpperTheory.Reformulated.B.DualIntegralLattice.main
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAtOneCompOfIsDiffOf
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionDerivativeEndomorphism

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (F : X ⟶ Y)
    (s : Γ(Y, ⊤)) :
    BT.valAt v ⊤ le_top ((F.appLE ⊤ ⊤ le_top).hom s) = BT.valAt (v ≫ F) ⊤ le_top s := by
  unfold BT.valAt
  rw [← Scheme.Hom.appLE_comp_appLE v F ⊤ ⊤ ⊤ le_top le_top]
  rfl

theorem exists_endo {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ)
    (h : Γ.IsTorsionAlong G x N i) (a : G ⟶ G) [IsMonHom a] :
    ∃ b : Γ.G ⟶ Γ.G, b.left ≫ i = i ≫ a.left := by
  let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
  have h1 : (g₀ ≫ a) ^ N = 1 := by
    rw [← MonObj.pow_comp, h0, MonObj.one_comp]
  obtain ⟨b, hb⟩ := (h.kernel Γ.G (g₀ ≫ a)).1 h1
  exact ⟨b, hb⟩

end PositivityTheory.Xgn.FunctionDerivativeEndomorphism

theorem PositivityTheory.Xgn.isDerAtOne_comp_of_isDiffOf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (B : L →ₗ[R] L), M.IsDiffOf a B → ∀ (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → ∀ (f : T → R) (w : Module.Dual R L), Γ.IsDerAtOne i M N f w → Γ.IsDerAtOne i M N (fun t => f (α t)) (w ∘ₗ B) := by
  intro R _ _ T _ Γ S G _ _ x i N h L _ _ M a _ B hB α hα f w hd
  obtain ⟨b, hb⟩ := PositivityTheory.Xgn.FunctionDerivativeEndomorphism.exists_endo Γ G x i N h a
  obtain ⟨s, hs, hv⟩ := hd
  refine ⟨(b.left.appLE ⊤ ⊤ le_top).hom s, ?_, ?_⟩
  · intro t
    rw [PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]
    have ht : Γ.pt t ≫ b = Γ.pt (α t) := h.inj _ _ _ (by
      rw [Over.comp_left, Category.assoc, hb, hα])
    have e := congrArg Over.Hom.left ht
    rw [Over.comp_left] at e
    rw [e]
    exact hs (α t)
  · intro e
    obtain ⟨v, hv1, hv2, -⟩ := hv e
    obtain ⟨v', hv1', hv2', hv3'⟩ := hv (B e)
    refine ⟨v, hv1, hv2, ?_⟩
    rw [PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]
    let Y : Over (Spec (CommRingCat.of R)) := Over.mk (v' ≫ Γ.G.hom)
    have hw : (v ≫ b.left) ≫ Γ.G.hom = Y.hom := by
      simp only [Y, Over.mk_hom, Category.assoc, Over.w]
      rw [hv1, hv1']
    have hvv := h.inj Y (Over.homMk (v ≫ b.left) hw) (Over.homMk v' rfl) (by
      simp only [Over.homMk_left, Category.assoc]
      rw [hb, ← Category.assoc, hv2, hv2', hB e, Over.comp_left, Category.assoc])
    have e2 := congrArg Over.Hom.left hvv
    simp only [Over.homMk_left] at e2
    rw [e2, hv3']
    simp only [LinearMap.comp_apply, map_one]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LatticeChartPoints
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.LatticeChartPoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}

theorem int_le (O : Type) [CommRing O] [Algebra O Ω] (S : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin O S := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap n =>
    have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem unitAt_mul_iff {q : Cpt ξ} {a s : Ω} (ha : unitAt ξ q a) : unitAt ξ q (a * s) ↔ unitAt ξ q s := by
  obtain ⟨h0, h1, h2⟩ := ha
  constructor
  · rintro ⟨k0, k1, k2⟩
    have hs : s ≠ 0 := right_ne_zero_of_mul k0
    refine ⟨hs, ?_, ?_⟩
    · have : s = a⁻¹ * (a * s) := by field_simp
      rw [this]; exact mul_mem h2 k1
    · have : s⁻¹ = a * (a * s)⁻¹ := by field_simp
      rw [this]; exact mul_mem h1 k2
  · rintro ⟨k0, k1, k2⟩
    refine ⟨mul_ne_zero h0 k0, mul_mem h1 k1, ?_⟩
    rw [mul_inv]; exact mul_mem h2 k2

theorem reg (O : Type) [CommRing O] [Algebra O Ω] (x : κ → Ω) (c : κ) (a : Ω)
    (ha : a ∈ Algebra.adjoin O (Set.range fun j => x j / x c)) (q : Cpt ξ) (hq : InChart ξ x c q)
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hq.2 j
  | algebraMap o => exact hO o
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (R : Subalgebra O Ω)
    (h : ∀ a ∈ B, a ∈ R) : ∃ φ : B →+* R, ∀ t : B, ((φ t : R) : Ω) = t :=
  ⟨{ toFun := fun t => ⟨t.1, h _ t.2⟩
     map_one' := Subtype.ext rfl
     map_mul' := fun _ _ => Subtype.ext rfl
     map_zero' := Subtype.ext rfl
     map_add' := fun _ _ => Subtype.ext rfl }, fun _ => rfl⟩

theorem point_of_prime (C : Cpt ξ → Prop)
    (A : Type) [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O]
    [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (B : Subalgebra ℤ Ω) (R : Subalgebra O Ω) (hle : ∀ a ∈ B, a ∈ R)
    (hpt : ∀ I : Ideal B, I.IsPrime → ∃ q, C q ∧ ∀ s : B, s ∉ I ↔ unitAt ξ q (s : Ω))
    (hreg : ∀ a ∈ B, ∀ q, C q → a ∈ regAt ξ q)
    (hconst : ∀ a : A, algebraMap A Ω a ∈ B)
    (hloc : ∀ t ∈ R, ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ B)
    (P : Ideal R) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, C q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧
      ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω) := by
  obtain ⟨φ, hφ⟩ := exists_incl B R hle
  obtain ⟨q, hq, hI⟩ := hpt (P.comap φ) (Ideal.comap_isPrime φ P)
  have hAO : ∀ a : A, algebraMap A Ω a = algebraMap O Ω (algebraMap A O a) := fun a =>
    IsScalarTower.algebraMap_apply A O Ω a
  have hnot : ∀ a : A, a ∉ m → φ ⟨_, hconst a⟩ ∉ P := by
    intro a ha hmem
    have hu : IsUnit (algebraMap A O a) := IsLocalization.map_units O (⟨a, ha⟩ : m.primeCompl)
    have he : φ ⟨_, hconst a⟩ = algebraMap O R (algebraMap A O a) :=
      Subtype.ext ((hφ _).trans (hAO a))
    rw [he] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hu.map _))
  have hunit : ∀ a : A, a ∉ m → unitAt ξ q (algebraMap A Ω a) := fun a ha =>
    (hI ⟨_, hconst a⟩).1 (fun h => hnot a ha (Ideal.mem_comap.1 h))
  refine ⟨q, hq, fun o => ?_, fun s => ?_⟩
  · obtain ⟨a, ha, hb⟩ := hloc _ (R.algebraMap_mem o)
    obtain ⟨h0, -, h2⟩ := hunit a ha
    have : algebraMap O Ω o = (algebraMap A Ω a)⁻¹ * (algebraMap A Ω a * algebraMap O Ω o) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (hreg _ hb q hq)
  · obtain ⟨a, ha, hb⟩ := hloc s s.2
    refine Iff.trans ?_ ((hI ⟨_, hb⟩).trans (unitAt_mul_iff (hunit a ha)))
    have he : φ ⟨_, hb⟩ = φ ⟨_, hconst a⟩ * s := Subtype.ext (by
      rw [hφ, MulMemClass.coe_mul, hφ])
    rw [Ideal.mem_comap, he, hP.mul_mem_iff_mem_or_mem]
    exact ⟨fun h h' => h'.elim (hnot a ha) h, fun h h' => h (Or.inr h')⟩

open GlobalTheory.CompanionTheory.Ar.ChartPrimes in
theorem basic_nbhd (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (q : Cpt ξ) (hq : InChart ξ x c q)
    (U : X.Opens) (hU : q.1 ∈ U) : ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), unitAt ξ q g ∧
      ∀ q' : Cpt ξ, InChart ξ x c q' → unitAt ξ q' g → q'.1 ∈ U := by
  obtain ⟨V, hV, hmem⟩ := T.affine c hc
  have hqV : q.1 ∈ V := (hmem _).2 ⟨q.2, hq⟩
  have hg : genPt ξ ∈ V := q.2.mem_open V.2 hqV
  obtain ⟨f, hfU, hqf⟩ := hV.exists_basicOpen_le ⟨q.1, hU⟩ hqV
  have key : ∀ (p : Cpt ξ), p.1 ∈ V → (p.1 ∈ X.basicOpen f ↔ unitAt ξ p (secVal ξ V hg f)) := fun p hp => by
    rw [X.mem_basicOpen f _ hp, ← genMap_germ_eq V hg p hp f]
    exact isUnit_iff_unitAt p (T.gen.inj _) _
  refine ⟨secVal ξ V hg f, (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq V hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩,
    (key q hqV).1 hqf, fun q' hq' hu => hfU ((key q' ((hmem _).2 ⟨q'.2, hq'⟩)).2 hu)⟩

end PositivityTheory.Xgn.LatticeChartPoints

open PositivityTheory.Xgn.LatticeChartPoints in
theorem PositivityTheory.Xgn.lattice_chart_points : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) := by
  intro X Ω _ ξ K _ _ J _ y T A _ _ hA m _ O _ _ _ _ _ _ _ c hc
  refine ⟨fun a ha q hq hO => reg O (mseg y) c a ha q hq hO, fun P hP => ?_, fun q hq _ a ha => ?_,
    fun q hq _ U hU => ?_⟩
  · exact point_of_prime (InChart ξ (mseg y) c) A m O (Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c)) _
      (fun a ha => int_le O _ ha)
      (fun I hI => (chart_point_of_prime X Ω ξ ℤ _ (mseg y) T c hc I hI).exists)
      (fun a ha => (T.ring c hc a).1 ha) (hA c hc)
      (fun t ht => (mem_chartRing_atPrime_iff K J Ω y A hA m O c hc t).1 ht) P hP
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ _ (mseg y) T c q hq a).1 ha
    exact ⟨s, int_le O _ hs, hu, int_le O _ hsa⟩
  · obtain ⟨g, hg, hu, h⟩ := basic_nbhd (mseg y) T c hc q hq U hU
    exact ⟨g, int_le O _ hg, hu, fun q' hq' _ hu' => h q' hq' hu'⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceDifferentialsExist
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceDifferentials

theorem main (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] (p : ℕ) [hpp : Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ NumberField.discr E) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (hm : (p : A) ∈ m) (O : Type) [CommRing O] [IsLocalRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (σ : E →+* Ω) :
    (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧
      ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : IsIntegral ℤ (σ (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := A)).1 h1
    exact ⟨algebraMap A O b, by rw [← IsScalarTower.algebraMap_apply, hb]⟩
  · set n : ℕ := (NumberField.discr E).natAbs with hn
    have hx : ((n : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
      rw [hn, ← NumberField.absNorm_differentIdeal E (𝓞 E)]
      exact Ideal.absNorm_mem _
    have hpn : ¬ p ∣ n := fun h => hp (Int.natCast_dvd.2 h)
    have hnm : ((n : ℕ) : A) ∉ m := by
      intro h
      have hc : IsCoprime (p : A) (n : A) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hpp.out).2 hpn)
      obtain ⟨u, v, huv⟩ := hc
      exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one m).2
        (huv ▸ m.add_mem (m.mul_mem_left u hm) (m.mul_mem_left v h)))
    have hu : IsUnit (algebraMap A O (n : A)) :=
      IsLocalization.map_units O (⟨(n : A), hnm⟩ : m.primeCompl)
    obtain ⟨o, ho⟩ := hu.exists_left_inv
    refine ⟨(n : 𝓞 E), hx, o, ?_⟩
    have h2 := congrArg (algebraMap O Ω) ho
    simp only [map_mul, map_natCast, map_one] at h2
    have h3 : σ (((n : ℕ) : 𝓞 E) : E) = (n : Ω) := by simp
    rw [h3, h2]

end PositivityTheory.Xgn.SequenceDifferentials

theorem PositivityTheory.Xgn.sequence_differentials_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ hp A _ _ _ m _ hm O _ _ _ _ _ _ _ σ
  exact PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hp A m hm O σ
end

