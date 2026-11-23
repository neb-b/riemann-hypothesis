module

public import Mathlib
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSq
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.AdelicQuadSol

theorem exists_sq_eq_of_approx {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (r b : v.adicCompletionIntegers K) (hb : b ^ 2 - r ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hu : IsUnit (2 * b)) : ∃ s : v.adicCompletionIntegers K, s ^ 2 = r := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (X ^ 2 - C r : (v.adicCompletionIntegers K)[X]).Monic := monic_X_pow_sub_C r two_ne_zero
  have hd : eval b (derivative (X ^ 2 - C r : (v.adicCompletionIntegers K)[X])) = 2 * b := by
    simp [one_add_one_eq_two]
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K))
    (X ^ 2 - C r) hm b (by simpa using hb) (by rw [hd]; exact hu.map _)
  refine ⟨s, ?_⟩
  have h0 : s ^ 2 - r = 0 := by simpa using hs
  linear_combination h0

theorem local_integral : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (δ a : K), Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 → Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 → Valued.v (algebraMap K (v.adicCompletion K) a) = 1 → ∃ x y : v.adicCompletion K, x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K ∧ x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a := by
  intro K _ _ v δ a h2 hδ ha
  set O := v.adicCompletionIntegers K
  let d : O := ⟨algebraMap K (v.adicCompletion K) δ, by rw [mem_adicCompletionIntegers, hδ]⟩
  let α : O := ⟨algebraMap K (v.adicCompletion K) a, by rw [mem_adicCompletionIntegers, ha]⟩
  have hdu : IsUnit d := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hδ
  have hαu : IsUnit α := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 ha
  have h2u : IsUnit (2 : O) := by
    apply adicCompletionIntegers.isUnit_iff_valued_eq_one.2
    have e2 : ((2 : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) 2 := by
      rw [map_ofNat]; rfl
    rw [e2]; exact h2
  letI := Fintype.ofFinite (ResidueField O)
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := (h2u.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  have hchar : ringChar (ResidueField O) ≠ 2 := by
    intro h
    apply h2k
    have := ringChar.Nat.cast_ringChar (R := ResidueField O)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  have hdk : residue O d ≠ 0 := (hdu.map (residue O)).ne_zero
  have hαk : residue O α ≠ 0 := (hαu.map (residue O)).ne_zero
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 : (ResidueField O)[X])) (g := C (-residue O d) * X ^ 2 + C (-residue O α))
    (by simp) (by compute_degree!) hodd
  obtain ⟨x0, rfl⟩ := residue_surjective s
  obtain ⟨y0, rfl⟩ := residue_surjective t
  have he : x0 ^ 2 - d * y0 ^ 2 - α ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hst
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
    linear_combination hst
  by_cases hx : residue O x0 = 0
  · have hy : residue O y0 ≠ 0 := by
      intro hy
      apply hαk
      have := (residue_eq_zero_iff _).2 he
      rw [map_sub, map_sub, map_mul, map_pow, map_pow, hx, hy] at this
      linear_combination -this
    obtain ⟨e, he'⟩ := hdu
    set di : O := ((e⁻¹ : Oˣ) : O)
    have hdi : di * d = 1 := by rw [← he']; exact e.inv_mul
    obtain ⟨y, hy2⟩ := exists_sq_eq_of_approx v (di * (x0 ^ 2 - α)) y0
      (by
        have : y0 ^ 2 - di * (x0 ^ 2 - α) = -di * (x0 ^ 2 - d * y0 ^ 2 - α) := by
          linear_combination (-(y0 ^ 2)) * hdi
        rw [this]; exact Ideal.mul_mem_left _ _ he)
      (h2u.mul (by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hy))
    refine ⟨(x0 : v.adicCompletion K), (y : v.adicCompletion K), x0.2, y.2, ?_⟩
    have hO : x0 ^ 2 - d * y ^ 2 = α := by
      rw [hy2]; linear_combination (-(x0 ^ 2 - α)) * hdi
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this
  · obtain ⟨x, hx2⟩ := exists_sq_eq_of_approx v (α + d * y0 ^ 2) x0
      (by
        have : x0 ^ 2 - (α + d * y0 ^ 2) = x0 ^ 2 - d * y0 ^ 2 - α := by ring
        rw [this]; exact he)
      (h2u.mul (by rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hx))
    refine ⟨(x : v.adicCompletion K), (y0 : v.adicCompletion K), x.2, y0.2, ?_⟩
    have hO : x ^ 2 - d * y0 ^ 2 = α := by rw [hx2]; ring
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this

theorem eventually_valued_eq_one {K : Type} [Field K] [NumberField K] {c : K} (hc : c ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) c) = 1 := by
  filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) c).2,
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) c⁻¹).2] with v h1 h2
  have h1' : Valued.v (algebraMap K (v.adicCompletion K) c) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h1
  have h2' : Valued.v (algebraMap K (v.adicCompletion K) c⁻¹) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h2
  rw [map_inv₀, map_inv₀] at h2'
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) c) ≠ 0 := by
    rw [Ne, map_eq_zero, map_eq_zero]; exact hc
  exact le_antisymm h1' ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2')

theorem exists_finiteAdele_sq_sub_mul_sq : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  intro K _ _ δ a hδ ha hloc
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 :=
    (eventually_valued_eq_one h2).and ((eventually_valued_eq_one hδ).and (eventually_valued_eq_one ha))
  classical
  let sol : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K × v.adicCompletion K := fun v =>
    if h : Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 then
      ((local_integral K v δ a h.1 h.2.1 h.2.2).choose, (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose)
    else ((hloc v).choose, (hloc v).choose_spec.choose)
  have hsol : ∀ v, (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 =
      algebraMap K (v.adicCompletion K) a := by
    intro v
    simp only [sol]
    split_ifs with h
    · exact (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.2
    · exact (hloc v).choose_spec.choose_spec
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (sol v).1 ∈ v.adicCompletionIntegers K ∧ (sol v).2 ∈ v.adicCompletionIntegers K := by
    filter_upwards [hev] with v h
    simp only [sol, dif_pos h]
    exact ⟨(local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.1,
      (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.1⟩
  refine ⟨⟨fun v => (sol v).1, hint.mono fun _ h => h.1⟩, ⟨fun v => (sol v).2, hint.mono fun _ h => h.2⟩, ?_⟩
  refine FiniteAdeleRing.ext K fun v => ?_
  change (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 = algebraMap K (v.adicCompletion K) a
  exact hsol v

end GlobalTheory.AdelicQuadSol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsSpecFromPairs
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

theorem exists_glue_pair {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X)
    (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1))
    (hh : ∀ p q : Pair x, ∀ hpq : p ≤ q,
      ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) :
    ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  have sub : ∀ (p q : Pair x) (y : Sp B), y ∈ p.1.1.1 → y ∈ q.1.1.1 →
      ∃ r : Pair x, r ≤ p ∧ r ≤ q ∧ y ∈ r.1.1.1 := by
    intro p q y hp hq
    have hyU : x.base y ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hp, q.2 hq⟩
    obtain ⟨W, hW, hyW, hWs⟩ := exists_isAffineOpen_mem_and_subset hyU
    have hyV : y ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ x ⁻¹ᵁ W := ⟨⟨hp, hq⟩, hyW⟩
    obtain ⟨V, hV, hyV', hVs⟩ := exists_isAffineOpen_mem_and_subset hyV
    refine ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), fun z hz ↦ (hVs hz).2⟩, ?_, ?_, hyV'⟩
    · exact ⟨fun z hz ↦ (hVs hz).1.1, fun z hz ↦ (hWs hz).1⟩
    · exact ⟨fun z hz ↦ (hVs hz).1.2, fun z hz ↦ (hWs hz).2⟩
  have cover : ∀ y : Sp B, ∃ p : Pair x, y ∈ p.1.1.1 := by
    intro y
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (show x.base y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hyV, hVs⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ x ⁻¹ᵁ W from hyW)
    exact ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), fun z hz ↦ hVs hz⟩, hyV⟩
  have key : ∀ (p r : Pair x) (hr : r ≤ p) (y : Sp B) (hy : y ∈ r.1.1.1),
      (Sp B).presheaf.germ p.1.1.1 y (Pair.le_fst hr hy) (h p) =
        (Sp B).presheaf.germ r.1.1.1 y hy (h r) := by
    intro p r hr y hy
    rw [← hh r p hr]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  let U : Pair x → (Sp B).Opens := fun p ↦ p.1.1.1
  have hc : TopCat.Presheaf.IsCompatible (Sp B).presheaf U h := by
    intro i j
    refine TopCat.Presheaf.section_ext (Sp B).sheaf _ _ _ fun y hy ↦ ?_
    obtain ⟨r, hri, hrj, hyr⟩ := sub i j y hy.1 hy.2
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ((key i r hri y hyr).trans
      ((key j r hrj y hyr).symm.trans (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm))
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (Sp B).sheaf U ⊤
    (fun _ ↦ homOfLE le_top) (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (cover y)) h hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom s, fun p ↦ ?_⟩
  rw [← hs p]
  have e1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s) = s :=
    Iso.hom_inv_id_apply _ _
  change ((𝟙 (Sp B) : Sp B ⟶ Sp B).appLE ⊤ p.1.1.1 le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s)) = _
  rw [e1]
  simp [Scheme.Hom.appLE]
  rfl

end GlobalTheory.CechDR.AffLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem lift_linear_of_injective {S : Type*} [Ring S] {N A B C : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C]
    (hN : Module.Baer S N)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C) (hex : ∀ b, v b = 0 → ∃ a, u a = b)
    (f : B →ₗ[S] N) (hf : f ∘ₗ u = 0) : ∃ g : C →ₗ[S] N, g ∘ₗ v = f := by
  have hle : LinearMap.ker v ≤ LinearMap.ker f := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    simpa using LinearMap.congr_fun hf a
  let f₁ : (B ⧸ LinearMap.ker v) →ₗ[S] N := (LinearMap.ker v).liftQ f hle
  let f₂ : LinearMap.range v →ₗ[S] N := f₁ ∘ₗ (v.quotKerEquivRange).symm.toLinearMap
  obtain ⟨g, hg⟩ := hN.extension_property (LinearMap.range v).subtype (LinearMap.range v).injective_subtype f₂
  refine ⟨g, LinearMap.ext fun b => ?_⟩
  have h1 := LinearMap.congr_fun hg ⟨v b, b, rfl⟩
  have h2 : (v.quotKerEquivRange).symm ⟨v b, b, rfl⟩ = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h1
  rw [LinearMap.comp_apply, h1]
  simp only [f₂, f₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem lift_homSh : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  intro R _ J X hinj A B C u v hex f hf
  obtain ⟨e, hnat, -⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  have he0 : ∀ M : ModuleCat.{1} (ULift.{1} R), e X M 0 = 0 := by
    intro M
    have := hnat X M M 0 0
    rw [zero_comp, ModuleCat.hom_zero, LinearMap.comp_zero] at this
    exact this
  have hf' : e X B f ∘ₗ u.hom = 0 := by rw [← hnat, hf, he0]
  obtain ⟨g', hg'⟩ := lift_linear_of_injective (Module.Baer.of_injective hinj) u.hom v.hom hex (e X B f) hf'
  refine ⟨(e X C).symm g', (e X B).injective ?_⟩
  rw [hnat, Equiv.apply_symm_apply, hg']
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRightTranslateMemIdentityComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_mem_and_rightTranslate_mem_of_mem_identityComponent :
    ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  intro k _ G _ hs U y hU hy
  set e : G.left := (η[G]).left (IsLocalRing.closedPoint k) with he
  have hirr : IsIrreducible (connectedComponent e) := by
    have h := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k G.left G.hom (η[G]).left hs (Over.w (η[G]))).2
    have hsub : ∀ a : Spec (CommRingCat.of k), a = IsLocalRing.closedPoint k := fun a =>
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    convert h using 1
    ext x
    have h1 : (G.hom ⁻¹' {G.hom x} : Set G.left) = Set.univ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact (hsub _).trans (hsub _).symm
    simp only [Set.mem_ofPred_eq]
    rw [h1, connectedComponentIn_univ, hsub (G.hom x)]
  let T : G ⟶ G := 𝟙 G * (toUnit G ≫ y)
  have hT : (y ≫ ι[G]) ≫ T = η[G] := by
    have h1 : (y ≫ ι[G]) ≫ T = (y ≫ ι[G]) * y := by
      simp only [T]
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit,
        Category.id_comp]
    rw [h1]
    have h2 : (y ≫ ι[G]) = y⁻¹ := rfl
    rw [h2, inv_mul_cancel, Hom.one_def, toUnit_unit, Category.id_comp]
  have hιe : (ι[G]).left e = e := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    have h2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) this
    exact h2
  have hyi : (ι[G]).left (y.left (IsLocalRing.closedPoint k)) ∈ connectedComponent e := by
    have hc := (ι[G]).left.continuous.image_connectedComponent_subset e
    rw [hιe] at hc
    exact hc ⟨_, hy, rfl⟩
  have hTy : T.left ((ι[G]).left (y.left (IsLocalRing.closedPoint k))) = e := by
    have h2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hT
    exact h2
  obtain ⟨z, -, hz1, hz2⟩ := hirr.isPreirreducible (U : Set G.left) (T.left ⁻¹' (U : Set G.left))
    U.isOpen (U.isOpen.preimage T.left.continuous) ⟨e, mem_connectedComponent, hU⟩
    ⟨_, hyi, by rw [Set.mem_preimage, hTy]; exact hU⟩
  exact ⟨z, hz1, hz2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparate
section
namespace GlobalTheory

theorem exists_ne_zero_forall_complexPoint_separate
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroZeroFormPolynomialIsAlgClosed
section
open IsLocalRing

namespace GlobalTheory
namespace TsenCount

open Polynomial

variable {σ k : Type} [CommRing k]

def CoeffHom (e : ℕ) (p : (MvPolynomial σ k)[X]) : Prop := ∀ j, (p.coeff j).IsHomogeneous e

end TsenCount


end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermTransportModularFamiliesValues
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem exists_perm_transport_families (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S]
    (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ)
    (ω₀ ω₁ : ℂ) (hN : 0 < N) (hact : ActBij act) (hf : ∀ s, IsFam act (m s) (f s))
    (hc : ∀ s i, QConj g N (f s i) (f' s i))
    (h4 : g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4) (h6 : g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6) :
    ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.QFam.exists_perm_of_sum_monomial_eq ι S (fun i s => g (f s i τ₀ / ω₀ ^ m s))
    (fun i s => f' s i τ₁ / ω₁ ^ m s)
    (_root_.GlobalTheory.QFam.transport_power_sums g ι S act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hf hc h4 h6)
  exact ⟨ρ, fun s i => congrFun (hρ i) s⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackMulPOfPTorsionInvariant
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_tensor_map_eq_of_exact {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R M]
    [Module.Flat R N] [Module.Flat R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (h : Function.Exact f g) (F : N ⊗[R] N)
    (h₁ : g.rTensor N F = 0) (h₂ : g.lTensor N F = 0) :
    ∃ c : M ⊗[R] M, TensorProduct.map f f c = F := by
  obtain ⟨F', rfl⟩ := (Module.Flat.lTensor_exact N h F).1 h₂
  have h₃ : g.rTensor M F' = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := P) f hf
    rw [map_zero, ← h₁, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  obtain ⟨c, rfl⟩ := (Module.Flat.rTensor_exact M h F').1 h₃
  exact ⟨c, by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩

theorem PDivGroup.exists_tensorSquare_mulP_eq {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1))
    (h₁ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0)
    (h₂ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0) :
    ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by
  refine exists_tensor_map_eq_of_exact (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) _
    (Test.mulP_injective G n) (fun a => ⟨fun ha => ?_, ?_⟩) F h₁ h₂
  · exact GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n a (sub_eq_zero.1 ha)
  · rintro ⟨e, rfl⟩
    exact sub_eq_zero.2 (G.transl_mulP n e)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitaryOfLocallyBijectiveFromFilteredFunctorStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitary_of_locally_bijective_from_filtered_functor : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → Finitary F := by
  first
  | exact @GlobalTheory.EtC.FinitaryOfLocBij.finitary_of_locally_bijective
  | exact GlobalTheory.EtC.FinitaryOfLocBij.finitary_of_locally_bijective
  | (intros; apply GlobalTheory.EtC.FinitaryOfLocBij.finitary_of_locally_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cover_ring_localization_chart : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧ ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  first | (exact @GlobalTheory.PD.rB_mono_loc) | (exact GlobalTheory.PD.rB_mono_loc) | (intros; apply GlobalTheory.PD.rB_mono_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompactStatement
section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type} (e : ι → OpenPartialHomeomorph M (V n)), (∀ y, ∃ i, y ∈ (e i).source) → (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → ∀ (r : ι → V n → ℝ), (∀ i, ContinuousOn (r i) (e i).target) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) → GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  first | exact @GlobalTheory.glueMeas_univ_ne_top_of_compact | exact GlobalTheory.glueMeas_univ_ne_top_of_compact | (intros; apply GlobalTheory.glueMeas_univ_ne_top_of_compact <;> assumption)
end

