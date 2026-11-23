module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfProd
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactProd

theorem exactAt_of_prod {ι : Type} {c : ComplexShape ℕ} {K : HomologicalComplex AddCommGrpCat.{1} c}
    {L : ι → HomologicalComplex AddCommGrpCat.{1} c} (φ : ∀ i, K ⟶ L i)
    (hφ : ∀ n, Function.Bijective (fun (x : K.X n) (i : ι) => (φ i).f n x)) (p : ℕ)
    (hL : ∀ i, (L i).ExactAt p) : K.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  suffices key : ∀ z : K.X p, K.d p (c.next p) z = 0 → ∃ v : K.X (c.prev p), K.d (c.prev p) p v = z from key
  intro z hz
  have hcomm : ∀ i {q r : ℕ} (x : K.X q), (L i).d q r ((φ i).f q x) = (φ i).f r (K.d q r x) := by
    intro i q r x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (φ i).comm]
  have hw : ∀ i, ∃ w : (L i).X (c.prev p), (L i).d (c.prev p) p w = (φ i).f p z := by
    intro i
    have hex := hL i
    rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hex
    refine hex ((φ i).f p z) ?_
    change (L i).d p (c.next p) ((φ i).f p z) = 0
    rw [hcomm, hz, map_zero]
  choose w hw using hw
  obtain ⟨v, hv⟩ := (hφ (c.prev p)).2 w
  refine ⟨v, ?_⟩
  apply (hφ p).1
  funext i
  change (φ i).f p (K.d (c.prev p) p v) = (φ i).f p z
  rw [← hcomm, ← hw i]
  exact congrArg _ (congrFun hv i)

theorem wexact_of_prod (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (ι : Type) (M : ι → T ⥤ AddCommGrpCat.{1})
    (N : T ⥤ AddCommGrpCat.{1}) (π : ∀ i, N ⟶ M i)
    (hπ : ∀ V, Function.Bijective (fun (x : N.obj V) (i : ι) => (π i).app V x))
    (hM : ∀ i, WExact (M i) a) : WExact N a := by
  have nat : ∀ i {P Q : T} (f : P ⟶ Q) (x : N.obj P), (π i).app Q (N.map f x) = (M i).map f ((π i).app P x) := by
    intro i P Q f x
    exact ConcreteCategory.congr_hom ((π i).naturality f) x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (hπ U).1
    funext i
    apply (hM i).1
    have h := congrArg ((π i).app _) hxy
    rw [nat, nat] at h
    exact h
  · intro y hy
    have hx : ∀ i, ∃ x : (M i).obj U, (M i).map (a.app (SimplexCategory.mk 0)) x = (π i).app _ y := by
      intro i
      refine (hM i).2.1 ((π i).app _ y) ?_
      rw [← nat, ← nat, hy]
    choose x hx using hx
    obtain ⟨x', hx'⟩ := (hπ U).2 x
    refine ⟨x', ?_⟩
    apply (hπ _).1
    funext i
    change (π i).app _ (N.map (a.app (SimplexCategory.mk 0)) x') = (π i).app _ y
    rw [nat, ← hx i]
    exact congrArg _ (congrFun hx' i)
  · intro n
    refine exactAt_of_prod (fun i => (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map
      (Functor.whiskerLeft X (π i))) (fun k => ?_) (n + 1) (fun i => (hM i).2.2 n)
    exact hπ (X.obj (SimplexCategory.mk k))

end GlobalTheory.EtC.WExactProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChart
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue.CombEx

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) = x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem top_of_comp {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun x _ => h.ge (show f x ∈ (⊤ : B.Opens) from trivial)

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_spMap_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S S' : Type} [CommRing S]
    [CommRing S'] (g : S →+* S') (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ x) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap g ≫ x) h' = g.comp (chartHom V x hx) := by
  have e : spMap (chartHom V (spMap g ≫ x) h') ≫ hV.fromSpec =
      spMap (g.comp (chartHom V x hx)) ≫ hV.fromSpec := by
    rw [chart_rebuild, spMap_comp', Category.assoc, chart_rebuild]
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

end GlobalTheory.SecGlue.CombEx

namespace GlobalTheory.SecGlue.CombEx

theorem mul_eq_zero_of_sq {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {s t : S} (hs : q s = 0) (ht : q t = 0) : s * t = 0 := by
  have h : s * t ∈ RingHom.ker q ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (RingHom.mem_ker.2 hs) (RingHom.mem_ker.2 ht)
  rw [hsq] at h
  exact (Submodule.mem_bot S).1 h

def combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S) (hq : ∀ i, q.comp (ψ i) = q.comp φ) :
    A →+* S where
  toFun x := φ x + ∑ i, a i * (ψ i x - φ x)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add (f := _), mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_mul' x y := by
    have hd : ∀ i z, q (ψ i z - φ z) = 0 := fun i z => by
      rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
    have hD : ∀ z, q (∑ i, a i * (ψ i z - φ z)) = 0 := fun z => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hd, mul_zero, Finset.sum_const_zero]
    have e1 : ∀ i, ψ i (x * y) - φ (x * y) = φ x * (ψ i y - φ y) + (ψ i x - φ x) * φ y := fun i => by
      have := mul_eq_zero_of_sq q hsq (hd i x) (hd i y)
      rw [map_mul, map_mul]; linear_combination this
    have e2 := mul_eq_zero_of_sq q hsq (hD x) (hD y)
    have s : ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
        φ x * ∑ i, a i * (ψ i y - φ y) + φ y * ∑ i, a i * (ψ i x - φ x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i]; ring
    show φ (x * y) + ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
      (φ x + ∑ i, a i * (ψ i x - φ x)) * (φ y + ∑ i, a i * (ψ i y - φ y))
    linear_combination s + map_mul φ x y - e2

theorem combHom_apply {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (x : A) :
    combHom q hsq φ ψ a hq x = φ x + ∑ i, a i * (ψ i x - φ x) := rfl

theorem comp_combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by
  ext x
  have hd : ∀ i, q (ψ i x - φ x) = 0 := fun i => by
    rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.comp_apply, combHom_apply, map_add (f := _), map_sum, map_mul, hd, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem combHom_comp_eq {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (θ : R →+* A) (hθ : ∀ i, (ψ i).comp θ = φ.comp θ) :
    (combHom q hsq φ ψ a hq).comp θ = φ.comp θ := by
  ext r
  have h : ∀ i, ψ i (θ r) = φ (θ r) := fun i => RingHom.congr_fun (hθ i) r
  simp only [RingHom.comp_apply, combHom_apply, h, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_comb : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  intro Y V hV S T _ _ q hqs hsq ι _ u w a hu hw
  have hwV : ∀ i, w i ⁻¹ᵁ V = ⊤ := fun i => (GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hqs hsq Y (w i) u (hw i) V).trans hu
  have hq : ∀ i, q.comp (chartHom V (w i) (hwV i)) = q.comp (chartHom V u hu) := fun i => by
    rw [← chartHom_spMap_comp hV q (w i) (hwV i) (top_of_comp _ _ V (hwV i)),
      ← chartHom_spMap_comp hV q u hu (top_of_comp _ _ V hu)]
    exact chartHom_congr V (hw i) _ _
  let χ := combHom q hsq (chartHom V u hu) (fun i => chartHom V (w i) (hwV i)) a hq
  have hc := fromSpec_comp_top hV χ
  refine ⟨spMap χ ≫ hV.fromSpec, ⟨hu, hc, hwV, fun x => ?_⟩, ?_, ?_⟩
  · rw [chartHom_fromSpec hV χ hc]; rfl
  · calc spMap q ≫ spMap χ ≫ hV.fromSpec = spMap (q.comp χ) ≫ hV.fromSpec := by
          rw [spMap_comp', Category.assoc]
      _ = spMap (q.comp (chartHom V u hu)) ≫ hV.fromSpec := by rw [comp_combHom]
      _ = spMap q ≫ u := by rw [spMap_comp', Category.assoc, chart_rebuild]
  · intro R' _ p hp
    let θ : CommRingCat.of R' ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ p)
    have key : ∀ (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤), x ≫ p = spMap ((chartHom V x hx).comp θ.hom) := by
      intro x hx
      calc x ≫ p = spMap (chartHom V x hx) ≫ hV.fromSpec ≫ p := by rw [← Category.assoc, chart_rebuild]
        _ = spMap (chartHom V x hx) ≫ Spec.map θ := by rw [Spec.map_preimage]
        _ = spMap ((chartHom V x hx).comp θ.hom) := by
          show _ = Spec.map (CommRingCat.ofHom _)
          rw [show CommRingCat.ofHom ((chartHom V x hx).comp θ.hom) = θ ≫ CommRingCat.ofHom (chartHom V x hx)
            from rfl, Spec.map_comp]
    have hθ : ∀ i, (chartHom V (w i) (hwV i)).comp θ.hom = (chartHom V u hu).comp θ.hom := fun i => by
      have e := (key (w i) (hwV i)).symm.trans ((hp i).trans (key u hu))
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rw [key _ hc, key u hu, chartHom_fromSpec hV χ hc]
    exact congrArg spMap (combHom_comp_eq q hsq _ _ a hq θ.hom hθ)

end GlobalTheory.SecGlue.CombEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_basicOpen_fibres_preirreducible :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B →
    ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) →
    PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) →
    ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧
      (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧
      ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) →
        IsPreirreducible {r : PrimeSpectrum B |
          r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  intro A B _ _ _ hsm q Ω _ _ _ hq hΩ
  obtain ⟨b, hbq, n, _, hST, hSE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q.asIdeal)
  have hΩb := _root_.GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway A B b Ω hΩ
  obtain ⟨a, I, haΩ, hIΩ, hall⟩ := _root_.GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads A (Localization.Away b) n hSE Ω hΩb
  have memq : ∀ x : A, algebraMap A B x ∈ q.asIdeal ↔ algebraMap A Ω x = 0 := by
    intro x
    have := congrArg (x ∈ ·) hq
    simpa [Ideal.mem_comap, RingHom.mem_ker] using this
  refine ⟨b, a, I, hbq, fun h => haΩ ((memq a).1 h), fun c hc => (memq c).2 (hIΩ c hc), ?_⟩
  intro t hat hIt
  let k := AlgebraicClosure t.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap A k) = t.asIdeal := by
    rw [IsScalarTower.algebraMap_eq A t.asIdeal.ResidueField k, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap t.asIdeal.ResidueField k).injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have hmem : ∀ x : A, algebraMap A k x = 0 ↔ x ∈ t.asIdeal := by
    intro x; rw [← RingHom.mem_ker, hker]
  have hk := hall k (fun h => hat ((hmem a).1 h)) (fun c hc => (hmem c).2 (hIt c hc))
  have himg := (PreirreducibleSpace.isPreirreducible_univ (X := PrimeSpectrum (k ⊗[A] Localization.Away b))).image
    (PrimeSpectrum.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away b →ₐ[A] k ⊗[A] Localization.Away b).toRingHom.comp
        (algebraMap B (Localization.Away b))))
    (PrimeSpectrum.continuous_comap _).continuousOn
  convert himg using 1
  rw [Set.image_univ, PrimeSpectrum.comap_comp, Set.range_comp,
    _root_.GlobalTheory.range_comap_includeRight_field, hker]
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hr, hbr⟩
    have : r ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]; exact hbr
    obtain ⟨r', rfl⟩ := this
    refine ⟨r', ?_, rfl⟩
    rw [← hr, IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
    rfl
  · rintro ⟨r', hr', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hr', IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
      rfl
    · have : PrimeSpectrum.comap (algebraMap B (Localization.Away b)) r' ∈
          Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨r', rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpoly
section
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem exists_cyclicVector_of_separable_charpoly {K : Type} [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  have hs' : (Matrix.toLin' γ).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (Matrix.toLin' γ) hs'
  refine ⟨e, fun u => ?_⟩
  obtain ⟨p, hp⟩ := he u
  refine ⟨p, ?_⟩
  rw [← hp]
  have h : aeval (Matrix.toLin' γ) p = Matrix.toLin' (aeval γ p) := by
    have := (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom γ p).symm
    exact this.symm
  rw [h, Matrix.toLin'_apply]

end GlobalTheory.LatOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLiftGenericFibreOfFactorization
section
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.GenFibLift

open GlobalTheory.LocAcyc

theorem genFibMap_comp {T E F O : Type} [CommRing T] [CommRing E] [CommRing F] [CommRing O]
    [Algebra T E] [Algebra T F] [Algebra T O] (φ : E →ₐ[T] F) (ψ : F →ₐ[T] O) :
    genFibMap (ψ.comp φ) = (genFibMap ψ).comp (genFibMap φ) :=
  genFib_ringHom_ext (fun e => by
    simp only [RingHom.comp_apply, genFibMap_algebraMap, AlgHom.comp_apply])

def den {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    Algebra.algebraMapSubmonoid O (nonZeroDivisors T) :=
  ⟨algebraMap T O t, Submonoid.mem_map_of_mem _ t.2⟩

theorem exists_mk' {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (x : GenFib T O) :
    ∃ (a : O) (t : nonZeroDivisors T), x = IsLocalization.mk' (GenFib T O) a (den t) := by
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
  obtain ⟨t, ht, hm⟩ := Submonoid.mem_map.1 m.2
  refine ⟨a, ⟨t, ht⟩, ?_⟩
  rw [show m = den ⟨t, ht⟩ from Subtype.ext hm.symm]

theorem exists_of_mk'_eq_zero {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (a : O)
    (m : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (h : IsLocalization.mk' (GenFib T O) a m = 0) :
    ∃ t : nonZeroDivisors T, algebraMap T O t * a = 0 := by
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff a m).1 h
  obtain ⟨t, ht, hct⟩ := Submonoid.mem_map.1 c.2
  exact ⟨⟨t, ht⟩, by simpa [hct] using hc⟩

theorem genFibMap_mk' {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) (t : nonZeroDivisors T) :
    genFibMap ψ (IsLocalization.mk' (GenFib T E) e (den t)) =
      IsLocalization.mk' (GenFib T O) (ψ e) (den t) := by
  simp only [genFibMap, IsLocalization.map_mk']
  congr 1
  ext
  exact ψ.commutes t

theorem exists_finitePresentation_lift (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O]
    (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GenFib T O) :
    ∃ (Z : Type) (_ : CommRing Z) (_ : Algebra R Z) (_ : Algebra T Z) (_ : IsScalarTower T R Z)
      (_ : Algebra.FinitePresentation R Z) (g : Z →ₐ[R] O) (w : U →+* GenFib T Z),
      (genFibMap (g.restrictScalars T)).comp w = u := by
  haveI : Algebra.FinitePresentation ℤ U := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, f, hf, s, hs⟩ := Algebra.FinitePresentation.out (R := ℤ) (A := U)

  choose a t ht using fun i : Fin n => exists_mk' (T := T) (u (f (MvPolynomial.X i)))
  let e : MvPolynomial (Fin n) R →ₐ[R] O := MvPolynomial.aeval a
  let θ : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun i => IsLocalization.mk' _ (MvPolynomial.X i : MvPolynomial (Fin n) R) (den (t i)))
  have key : (genFibMap (e.restrictScalars T)).comp θ = u.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int
        (((genFibMap (e.restrictScalars T)).comp θ).comp MvPolynomial.C)
        ((u.comp f.toRingHom).comp MvPolynomial.C)) r
    · intro i
      simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', genFibMap_mk']
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ht i]
      simp [e]

  have hrel : ∀ r : s, ∃ (p : MvPolynomial (Fin n) R) (τ τ' : nonZeroDivisors T),
      θ r = IsLocalization.mk' _ p (den τ) ∧ e (algebraMap T _ τ' * p) = 0 := by
    intro r
    obtain ⟨p, τ, hp⟩ := exists_mk' (T := T) (θ r)
    have h0 : genFibMap (e.restrictScalars T) (θ r) = 0 := by
      have hr : (r : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span r.2
      rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.mem_ker.1 hr, map_zero]
    rw [hp, genFibMap_mk'] at h0
    obtain ⟨τ', hτ'⟩ := exists_of_mk'_eq_zero _ _ h0
    refine ⟨p, τ, τ', hp, ?_⟩
    rw [map_mul, ← hτ']
    simp [IsScalarTower.algebraMap_apply T R (MvPolynomial (Fin n) R),
      IsScalarTower.algebraMap_apply T R O]
  choose p τ τ' hθ he using hrel
  let I : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range fun r : s => algebraMap T _ (τ' r : T) * p r)
  have hIe : ∀ x ∈ I, e x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker e := Ideal.span_le.2 (by rintro _ ⟨r, rfl⟩; exact he r)
    exact hle hx
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R) :=
    Algebra.FinitePresentation.mvPolynomial R R (Fin n)
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  let g : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] O := Ideal.Quotient.liftₐ I e hIe
  let q : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) := Ideal.Quotient.mkₐ R I
  let w0 : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R ⧸ I) :=
    (genFibMap (q.restrictScalars T)).comp θ
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker w0 := by
    rw [← hs, Ideal.span_le]
    intro r hr
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [w0, RingHom.comp_apply]
    rw [hθ ⟨r, hr⟩, genFibMap_mk']
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) R ⧸ I) (GenFib T (MvPolynomial (Fin n) R ⧸ I))
        (algebraMap T _ (τ' ⟨r, hr⟩ : T))) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)) _ (den _)
    refine (hu.mul_right_eq_zero).1 ?_
    rw [← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)),
      ← IsLocalization.mk'_mul, one_mul]
    have hz : (q.restrictScalars T) (algebraMap T _ (τ' ⟨r, hr⟩ : T) * p ⟨r, hr⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    rw [map_mul, AlgHom.commutes] at hz
    rw [hz, IsLocalization.mk'_zero]

  refine ⟨MvPolynomial (Fin n) R ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g, RingHom.liftOfSurjective f.toRingHom hf ⟨w0, hker⟩, ?_⟩
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  have hy : f y = f.toRingHom y := rfl
  rw [RingHom.comp_apply, hy, RingHom.liftOfSurjective_comp_apply]
  have hgq : (g.restrictScalars T).comp (q.restrictScalars T) = e.restrictScalars T := by
    exact AlgHom.ext fun x => AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I e hIe) x
  have hcomp : (genFibMap (g.restrictScalars T)).comp w0 = u.comp f.toRingHom := by
    simp only [w0]
    rw [← RingHom.comp_assoc, ← genFibMap_comp, hgq, key]
  exact RingHom.congr_fun hcomp y

theorem exists_etale_genFib_lift : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  intro T R O _ _ _ _ _ _ _ H U _ _ u
  obtain ⟨Z, _, _, _, _, _, g, w, hw⟩ := exists_finitePresentation_lift T R O U u
  obtain ⟨W, _, _, _, u0, v, hv⟩ := H Z g
  letI : Algebra T W := ((algebraMap R W).comp (algebraMap T R)).toAlgebra
  haveI hTRW : IsScalarTower T R W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, hTRW, inferInstance, v,
    (genFibMap (u0.restrictScalars T)).comp w, ?_⟩
  rw [← RingHom.comp_assoc, ← genFibMap_comp]
  have hvu : (v.restrictScalars T).comp (u0.restrictScalars T) = g.restrictScalars T :=
    AlgHom.ext fun z => AlgHom.congr_fun hv z
  rw [hvu, hw]

end GlobalTheory.GenFibLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | exact GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | (intros; apply GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra <;> assumption)
end

