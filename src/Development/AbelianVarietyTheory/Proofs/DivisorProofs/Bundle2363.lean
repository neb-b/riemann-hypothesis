module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdentifications
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegFibreFinite

open GlobalTheory.CechPic GlobalTheory.SiegelPull GlobalTheory.ZM.SiegPull

theorem finite_torsion {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {n : ℕ} (hn : 1 ≤ n) : Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1} := by
  have := hB.smooth
  have := GlobalTheory.MulFiniteAny.isFinite_mulA K B hB n hn
  have := GlobalTheory.TorsionDivisible.finite_fibre_points (Out.mulA B n) 1
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ Out.mulA B n = 1) fun x => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id])

theorem finite_over_point {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hamp : Out.RelAmple A L) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (z : Sp K ⟶ S) (m : Pic B.left) :
    Set.Finite {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} := by
  rcases Set.eq_empty_or_nonempty {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} with
    h | ⟨φ₁, h₁, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.AmpleFiniteOrder.exists_ge_cast_ne_zero K 3
  have := hB.comm
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K B hB N hNK
  let U : Over (Sp K) := 𝟙_ (Over (Sp K))
  have hfin' : Finite {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1} := by
    refine Finite.of_surjective (fun x : {x : U ⟶ B // x ^ N = 1} =>
      (⟨pushHom h₁ U x.1, by rw [← map_pow, x.2, map_one]⟩ : {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})) ?_
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := push_surjective h₁ U g
    exact ⟨⟨x, push_injective h₁ U (by rw [map_pow, hg, map_one])⟩, rfl⟩
  refine Set.finite_coe_iff.1 ?_
  refine Finite.of_injective (β := {x : U ⟶ B // x ^ N = 1} → {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})
    (fun φ x => ⟨pushHom φ.2.1 U x.1, by rw [← map_pow, x.2, map_one]⟩) ?_
  rintro ⟨φ, h, hc⟩ ⟨φ', h', hc'⟩ e
  have e₀ : ∀ x : U ⟶ B, x ^ N = 1 → x.left ≫ φ = x.left ≫ φ' := fun x hx =>
    congrArg (fun q => q.1.left) (congrFun e ⟨x, hx⟩)
  obtain ⟨σ, hσ, eσ⟩ := GlobalTheory.SiegRigid.exists_aut h h'
  have hu : IsMonHom (σ.hom * (𝟙 B)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, eψ⟩ := hdiv _ hu fun x hx => by
    have : x ≫ σ.hom = x := Over.OverMorphism.ext (h'.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, eσ]; exact e₀ x hx) (by rw [Over.w, Over.w]))
    rw [MonObj.comp_mul, GrpObj.comp_inv, this, Category.comp_id, mul_inv_cancel]
  refine Subtype.ext (GlobalTheory.SiegRigid.eq_of_field hL hamp hB h h' (hc.trans hc'.symm) hN hNK fun Ω _ _ t x hx => ?_)
  have e₁ : x ≫ (σ.hom * (𝟙 B)⁻¹) = 1 := by
    rw [eψ, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp]
  rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, mul_inv_eq_one] at e₁
  change x.left ≫ φ = x.left ≫ φ'
  rw [← eσ, ← Category.assoc, ← Over.comp_left, e₁]

theorem pull_diag {S S' : Scheme.{0}} {A : Over S} {B : Over S'} {φ : B.left ⟶ A.left}
    {φ₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) (m : Pic (A ⊗ A).left) :
    pull φ (pull (lift (𝟙 A) (𝟙 A)).left m) = pull (lift (𝟙 B) (𝟙 B)).left (pull φ₂ m) := by
  have e : (lift (𝟙 B) (𝟙 B)).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq hs (T := Over.mk (φ ≫ A.hom)) (T' := B) (𝟙 B.left) (𝟙 B) (𝟙 B)
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  rw [← pull_comp, ← pull_comp, e]

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

theorem point_eq (F : SFam g n ζ) {R : Type} [CommRing R] [IsLocalRing R] {B : Over (Sp R)} [GrpObj B]
    {x x' : Sp R ⟶ F.X} {φ φ' : B.left ⟶ F.univ.A.left} {φ₂ φ₂' : (G2 B).left ⟶ (G2 F.univ.A).left}
    (hs : x ≫ F.s = x' ≫ F.s) (h : IsGrpPullback B F.univ.A x φ) (h' : IsGrpPullback B F.univ.A x' φ')
    (q : IsSquare φ φ₂) (q' : IsSquare φ' φ₂')
    (hc : pull φ₂ (cls F.univ.P F.univ.isLB) = pull φ₂' (cls F.univ.P F.univ.isLB))
    (hl : ∀ a, SiegelPull.secPull h (F.univ.lev a) = SiegelPull.secPull h' (F.univ.lev a)) : x = x' := by
  obtain ⟨c, hc₀⟩ := (GlobalTheory.siegPre_pullback g n o ζ F.X (Sp R) F.s _ x F.univ rfl).1
  refine F.inj R x x' _ c hs hc₀ ?_
  obtain ⟨χ, χ₂, k, r, w, l⟩ := hc₀
  obtain ⟨e, he, ee⟩ := grpPullback_iso k h
  have k' : IsGrpPullback c.A F.univ.A x' (e.hom.left ≫ φ') :=
    ((isGrpPullback_of_iso e).comp h').congr (Category.id_comp _) rfl
  refine ⟨e.hom.left ≫ φ', (e.hom ⊗ₘ e.hom).left ≫ φ₂', k', isSquare_comp (isSquare_tensor e.hom) q', ?_,
    fun a => ?_⟩
  · have e₂ : χ₂ = (e.hom ⊗ₘ e.hom).left ≫ φ₂ := isSquare_unique r (isSquare_comp (isSquare_tensor e.hom) q) ee.symm
    refine (cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).1 ?_
    rw [(cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 w, cls_pull F.univ.isLB, cls_pull F.univ.isLB, e₂, pull_comp,
      pull_comp, hc]
  · have e₃ : c.lev a ≫ e.hom = SiegelPull.secPull h (F.univ.lev a) := Over.OverMorphism.ext (h.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, ee, SiegelPull.secPull_left]; exact l a) (by rw [Over.w, Over.w]))
    rw [← Category.assoc, ← Over.comp_left, e₃, hl, SiegelPull.secPull_left]

theorem finite_points (F : SFam g n ζ) (hn : 1 ≤ n) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (s : Sp K ⟶ Sp o) (m : Pic (G2 B).left) :
    Set.Finite {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} := by
  have := finite_torsion B hB hn
  have := hB.comm
  refine Set.finite_coe_iff.1 ?_
  have H := fun x : {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} => x.2.2
  choose φ φ₂ h q hc using H
  refine Finite.of_injective (β := (Fin g ⊕ Fin g) → {y : 𝟙_ (Over (Sp K)) ⟶ B // y ^ n = 1})
    (fun x i => ⟨SiegelPull.secPull (h x) (F.univ.lev (Pi.single i 1)), push_injective (h x) _ (by
      rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, F.univ.lev_tors, MonObj.comp_one])⟩) ?_
  intro x x' e
  refine Subtype.ext (point_eq F (x.2.1.trans x'.2.1.symm) (h x) (h x') (q x) (q x') ((hc x).trans (hc x').symm) ?_)
  let p := fun y => (AddMonoidHom.mk' (fun a => Additive.ofMul (SiegelPull.secPull (h y) (F.univ.lev a))) fun a b => by
      rw [← ofMul_mul]
      exact congrArg _ (push_injective (h y) _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', F.univ.lev_add, MonObj.comp_mul])) :
    (Fin g ⊕ Fin g → ℤ) →+ Additive (𝟙_ (Over (Sp K)) ⟶ B))
  have hp : p x = p x' := AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int
    (congrArg (fun z => Additive.ofMul z.1) (congrFun e i))
  exact fun a => congrArg Additive.toMul (DFunLike.congr_fun hp a)

theorem finite_identifications : ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ'), 1 ≤ n' → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (x₀ : Sp K ⟶ F'.X) (φ₀ : B.left ⟶ F'.univ.A.left) (φ₀₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), IsGrpPullback B F'.univ.A x₀ φ₀ → IsSquare φ₀ φ₀₂ → ∀ p₀ : Sp K ⟶ B.left, Set.Finite {P' : Sp K ⟶ F'.univ.A.left | ∃ (x' : Sp K ⟶ F'.X) (φ : B.left ⟶ F'.univ.A.left) (φ₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = x₀ ≫ F'.s ∧ IsGrpPullback B F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ P' = p₀ ≫ φ} := by
  intro o _ ζ g n F hn K _ _ B _ x₀ φ₀ φ₀₂ h₀ _ p₀
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab h₀
  let m := pull φ₀₂ (cls F.univ.P F.univ.isLB)
  have h₁ := finite_points F hn hB (x₀ ≫ F.s) m
  have h₂ := fun x => finite_over_point (pull_isLB F.univ.isLB _) F.princ.1 hB x (pull (lift (𝟙 B) (𝟙 B)).left m)
  refine ((h₁.biUnion fun x _ => h₂ x).image (p₀ ≫ ·)).subset ?_
  rintro _ ⟨x, φ, φ₂, hs, h, q, w, rfl⟩
  have e : pull φ₂ (cls F.univ.P F.univ.isLB) = m := by
    have := (cls_eq_iff (pull_isLB F.univ.isLB _) (pull_isLB F.univ.isLB _)).2 w
    rw [cls_pull F.univ.isLB, cls_pull F.univ.isLB] at this
    exact this.symm
  refine ⟨φ, Set.mem_biUnion (x := x) ⟨hs, φ, φ₂, h, q, e⟩ ⟨h, ?_⟩, rfl⟩
  rw [← e, ← pull_diag q]
  exact congrArg _ (cls_pull F.univ.isLB _ _)

end GlobalTheory.SiegFibreFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAut
section
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.MinSysTypeBal

theorem finite_minimiser_systems_upTo_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) →
    μ ∈ S := by
  intro O _ bar φ Y _ _ _ _ hX n N _ _ eb
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone bar φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ Y)) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ Y) x x
  let T : ι → Finset ((Fin n → ZMod N) → Y) := fun i =>
    if h : P i then Classical.choose (_root_.GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat Y n N eb i.1.val _ (fun j x y => (h.1.mem j).1 x y)
      (fun j y => h.1.nonneg j y) h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hb hpos
  obtain ⟨m, γ, k, cf, hcone, hk, hcf, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hX b hb hpos
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j l hjl => by
    have h := congrArg Subtype.val hjl
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, (k : ℤ) * b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    have := LinearMap.congr_fun₂ hsum y y
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have h3 := hpos _ hex
    have h4 := hbyy (e x)
    simp [hz] at h4
    rcases h4 with h4 | h4
    · omega
    · omega
  have hmem : μ ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (_root_.GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat Y n N eb i.1.val _ (fun j x y => (hPi.1.mem j).1 x y)
      (fun j y => hPi.1.nonneg j y) hPi.2) (pull e.toLinearMap b) k cf hk hcf ?_ μ h1 h2
    ext a c
    have := LinearMap.congr_fun₂ hsum (e a) (e c)
    simpa [i, γ', pull_apply, LinearMap.sum_apply] using this
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysTypeBal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.MinSysType

theorem finite_minimiser_systems_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W →
    ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) →
    (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
      qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  intro g φ hφ W hW N _ hN r hr
  classical
  have hX : IsPolFanOn id φ (Fin r → ℤ) := hφ (Fin r → ℤ) (by simpa using hr)
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone id φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x
  let T : ι → Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) := fun i =>
    if h : P i then Classical.choose (_root_.GlobalTheory.Poinc.MinSys.finite_minimiser_systems φ W hW N hN r i.1.val _ h.1 h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hsym hpos
  have hpsd := GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos r b hsym hpos
  obtain ⟨m, γ, cf, hcone, hcf, hb⟩ := GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm g φ hφ r hr b hsym hpsd
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ' h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j k hjk => by
    have h := congrArg Subtype.val hjk
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    rw [hb]; simp [LinearMap.sum_apply]
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have := hpos _ hex
    rw [hbyy] at this
    simp [hz] at this
  have hmem : μ' ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (_root_.GlobalTheory.Poinc.MinSys.finite_minimiser_systems φ W hW N hN r i.1.val _ hPi.1 hPi.2) (pull e.toLinearMap b) 1 cf
      one_pos hcf ?_ μ' h1 h2
    ext a c
    simp [i, γ', pull_apply, hb, LinearMap.sum_apply]
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfFormOrdNeZero
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormOrdFinite

theorem exists_isFrame_genericPoint {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ)
    (hn : topologicalKrullDim X = n) :
    ∃ (U : X.Opens) (ω : FormsOn p n U), genericPoint X ∈ U ∧ IsFrame ω := by
  obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := ⊤) trivial
  haveI : Nonempty V := ⟨⟨_, hgV⟩⟩
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).toAlgebra
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hV _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  haveI : Algebra.FiniteType k Γ(X, V) := h1
  have hd : ringKrullDim Γ(X, V) = n := by
    have h2 := GlobalTheory.OpenDim.topologicalKrullDim_open k p V ⟨_, hgV⟩
    rw [hn] at h2
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← h2]
    exact (topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec).symm
  obtain ⟨s, hs, hsm⟩ := GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (K := k) (A := Γ(X, V)) hd
  have hloc := hV.isLocalization_basicOpen s
  have h₁ : (algebraMap k (Localization.Away s)).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 hsm
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv h₁
  have e : ((IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv.toRingHom.comp (algebraMap k (Localization.Away s))) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen s) := by
    rw [← resG_comp_algX p (X.basicOpen_le s)]
    ext a
    simp [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.Away s)]
    rfl
  rw [e] at h₂
  obtain ⟨ω, hω⟩ := GlobalTheory.TopForm.exists_isFreeGen h₂
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  exact ⟨X.basicOpen s, ω, gen_mem hx, hV.basicOpen s, hω⟩

theorem finite_setOf_formOrd_ne_zero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ η : RatForms p n, η ≠ 0 → {z : X | ∃ E : DivOver p, E.IsAt z ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η ≠ 0}.Finite := by
  intro k _ _ X _ _ _ p n hp hn η hη
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame_genericPoint p n hn
  have hgen := isFreeGen_formOf hU hω
  have h0 : formOf U hU ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  replace hc : c • formOf U hU ω = η := hc
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hc, h, zero_smul])
  obtain ⟨W, hW, hWu⟩ := (unitAt_genericPoint hc0).exists_nhds
  let B : Closeds X := ⟨((U ⊓ W : X.Opens) : Set X)ᶜ, (U ⊓ W).isOpen.isClosed_compl⟩
  have hB : B ≠ ⊤ := fun h => by
    have hm : genericPoint X ∈ (B : Set X) := by rw [h]; trivial
    exact hm ⟨hU, hW⟩
  refine (GlobalTheory.T.finite_codim_one_points_closed X B hB).subset ?_
  rintro z ⟨E, hE, hne⟩
  refine ⟨hE.coheight_eq_one, fun hz => hne ?_⟩
  obtain ⟨hzU, hzW⟩ := hz
  obtain ⟨a, ha, e⟩ := hWu z hzW
  have hord : E.ord (Units.mk0 c hc0) = 0 :=
    E.ord_eq_zero (u := hE.equiv a) (ha.map hE.equiv) e
  have h1 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [Units.val_mk0, hc, hord, DivOver.formOrd_formOf_eq_zero hzU hE hω] at h1
  change E.formOrd η = 0
  simpa using h1

end GlobalTheory.FormOrdFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem fixed_mem_range : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) →
    y ∈ (fracMap ρ hρ).range := by
  classical
  intro R R' _ _ _ _ ρ hρ hG y hy
  obtain ⟨hfin, hinv⟩ := hG
  letI : Fintype (Gal ρ) := Fintype.ofFinite _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R') y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set P : R' := ∏ σ ∈ (Finset.univ : Finset (Gal ρ)).erase 1, σ.1 b with hP
  set N : R' := ∏ σ : Gal ρ, σ.1 b with hN
  have hNP : N = b * P := by
    rw [hN, hP, ← Finset.mul_prod_erase Finset.univ (fun σ : Gal ρ => σ.1 b) (Finset.mem_univ 1)]
    rfl
  have hσ0 : ∀ σ : Gal ρ, σ.1 b ≠ 0 := fun σ => (map_ne_zero_iff σ.1 σ.1.injective).2 hb0
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hNfix : ∀ τ ∈ Gal ρ, τ N = N := by
    intro τ hτ
    rw [hN, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : Gal ρ)) _ _ (fun σ => rfl)
  obtain ⟨n, hn⟩ := hinv N hNfix
  have inj := IsFractionRing.injective R' (FractionRing R')
  have hPK : algebraMap R' (FractionRing R') P ≠ 0 := (map_ne_zero_iff _ inj).2 hP0
  have hNK : algebraMap R' (FractionRing R') N ≠ 0 := (map_ne_zero_iff _ inj).2 hN0
  have hy' : algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b
      = algebraMap R' (FractionRing R') (a * P) / algebraMap R' (FractionRing R') N := by
    rw [hNP, map_mul, map_mul, mul_div_mul_right _ _ hPK]
  have hcfix : ∀ τ ∈ Gal ρ, τ (a * P) = a * P := by
    intro τ hτ
    apply inj
    have hyN : algebraMap R' (FractionRing R') (a * P)
        = (algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b) * algebraMap R' (FractionRing R') N := by
      rw [hy', div_mul_cancel₀ _ hNK]
    rw [← fracAut_algebraMap, hyN, map_mul, hy ⟨τ, hτ⟩, fracAut_algebraMap, hNfix τ hτ]
  obtain ⟨m, hm⟩ := hinv (a * P) hcfix
  refine ⟨algebraMap R (FractionRing R) m / algebraMap R (FractionRing R) n, ?_⟩
  rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hm, hn, hy']

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDescentSectionsInjectiveEqualizer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_fibreSquare_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y := by
  intro R _ S Y Z π y p q H r h1 h2
  have A : IsPullback (pullback.fst p p ≫ q) (pullback.snd p p) π (p ≫ y) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback p p) H.flip
  have X : IsPullback r (pullback.snd p p) (pullback.snd π π) q := by
    refine IsPullback.of_right (h₁₂ := pullback.fst π π) ?_ h2 (IsPullback.of_hasPullback π π)
    rw [h1, ← H.w]; exact A
  have := IsPullback.paste_vert X H.flip
  rwa [pullback.condition (f := p), pullback.condition (f := π)]

theorem descend_of_equalised_fibreSquare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ _ _ _ S Y Z π y p q hπ hs hS hy H
  have hinj := _root_.GlobalTheory.appTop_injective_of_surjective_toSpec_domain R S π hs hS
  have heq := _root_.GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd R S π hπ hS hinj
  let r : pullback p p ⟶ pullback π π := pullback.map p p π π q q y H.w H.w
  have h1 : r ≫ pullback.fst π π = pullback.fst p p ≫ q := pullback.lift_fst _ _ _
  have h2 : r ≫ pullback.snd π π = pullback.snd p p ≫ q := pullback.lift_snd _ _ _
  have hP := isPullback_fibreSquare_baseChange R S Y Z π y p q H r h1 h2
  exact _root_.GlobalTheory.Mum.app_injective_and_descent_of_affineOpens Y Z p fun V hV => ⟨GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper R S Y Z π y p q hπ hy H hinj V hV,
    _root_.GlobalTheory.Mum.AffDesc.mem_range_app_of_flat R S Y Z π y p q hπ hy H r h1 h2 hP heq V hV⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalarLeft.scalar_eq_one | exact GlobalTheory.InertScalarLeft.scalar_eq_one | (intros; apply GlobalTheory.InertScalarLeft.scalar_eq_one <;> assumption)
end

