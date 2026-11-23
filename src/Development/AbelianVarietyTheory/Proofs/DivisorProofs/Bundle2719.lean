module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixUniv

variable {mA mB : ℕ}

theorem comb_comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) (z : X₂)
    (q : N.ι) (hq : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ : gs p₂ z ⊤ (h.appTop (c i j)) = gs (r ≫ p) z ⊤ (c i j) := by
    rw [← e]; exact gs_pull p₂ h z ⊤ trivial (c i j)
  rw [e₁, gs_comp r p z ⊤ trivial, gs_comp r φ z _ hq]

theorem Generates.comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hg : Generates a φ p c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂)
    (e : p₂ ≫ h = r ≫ p) : Generates a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) := by
  intro z q hq
  obtain ⟨j, hj⟩ := hg (r z) q hq
  exact ⟨j, by rw [comb_comp a φ p c r h p₂ e z q hq j]; exact hj.map _⟩

theorem Proport.comp {A₀ B₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {H : LB B₀} {a : Fin mA → LB.Sec N}
    {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hp : Proport a b φ p Ψ c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) :
    Proport a b (r ≫ φ) p₂ (r ≫ Ψ) (fun i j => h.appTop (c i j)) := by
  intro z q k hq hk j j'
  rw [comb_comp a φ p c r h p₂ e z q hq, comb_comp a φ p c r h p₂ e z q hq, gs_comp r Ψ z _ hk,
    gs_comp r Ψ z _ hk, ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem matOf_comp {Rg : Type} [CommRing Rg] {X X' : Scheme.{0}} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) : matOf (h ≫ g) = fun i j => h.appTop (matOf g i j) := by
  funext i j; exact coord_comp h g _

theorem relift {S T' T : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over T} [GrpObj G₁] {G' : Over T'} [GrpObj G']
    {t₁ : T ⟶ S} {u : T' ⟶ T} {φ₁ : G₁.left ⟶ G.left} {φ' : G'.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G t₁ φ₁)
    (h' : IsGrpPullback G' G (u ≫ t₁) φ') : ∃ ψ : G'.left ⟶ G₁.left, IsGrpPullback G' G₁ u ψ ∧ ψ ≫ φ₁ = φ' := by
  refine ⟨h₁.1.lift φ' (G'.hom ≫ u) (by rw [h'.1.w, Category.assoc]), ?_, h₁.1.lift_fst _ _ _⟩
  exact h₁.cancel (by rw [h₁.1.lift_fst]; exact h') (h₁.1.lift_snd _ _ _)

theorem exists_universal_matrix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH
  obtain ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ := hH
  obtain ⟨hfl, hpj, huc⟩ := GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed Rg A L hAb hL hamp
  haveI := huc
  have hEmb := GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hBb hM hk hva hbB
  have hcov : (⨆ j, nonzeroLocus (bB j)) = ⊤ := hEmb.1
  have hNA : (LPow A L (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hL _ _
  have hNB : (LPow B M (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hM _ _
  choose αA hαA using fun i => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg A L k eA (bA i) hL heA
  choose βB hβB using fun j => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg B M k eB (bB j) hM heB
  obtain ⟨U, hU⟩ := GlobalTheory.T.isOpen_generatingCombinationMatrixLocus Rg _ (fA A) _ mA mB bA hNA
  obtain ⟨ZF, ιF, hιF, hF⟩ := GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections Rg _ _ (fA A) (fA B) _ _ mA mB bA bB hfl hpj hNA
  obtain ⟨ZN, ιN, hιN, hNm⟩ := GlobalTheory.T.linearNormalisation_closed_subscheme Rg mA mB αA βB
  haveI : IsNoetherian (Sp (MvPolynomial (Fin (mA * mB)) Rg)) := isNoetherian_Spec.2 inferInstance
  obtain ⟨W, j₁, hj₁, hj₁q, hWn, hW⟩ := GlobalTheory.T.exists_immersed_closed_open_intersection _ ZF ZN ιF ιN U hιF hιN
  have cond : ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ (topS Rg ⊗ A).left)
      (p : X' ⟶ T), (∃ w, w ≫ j₁ = g) → IsPullback φ p (fA A) (g ≫ affπ Rg (mA * mB)) →
      Generates bA φ p (matOf g) ∧ FormsOK bA (fA B) bB φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ∧
        Normal (g ≫ affπ Rg (mA * mB)) (matOf g) αA βB := by
    intro T X' g φ p hg hP
    obtain ⟨h1, h2, h3⟩ := (hW T g).2 hg
    exact ⟨(hU T X' g φ p hP).2 h3, (hF T X' g φ p hP).2 h1, (hNm T g).2 h2⟩
  have datum : ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (∃ w, w ≫ j₁ = g) →
      ∃ (AT : Over T) (_ : GrpObj AT) (BT : Over T) (_ : GrpObj BT) (φA : AT.left ⟶ A.left) (φB : BT.left ⟶ B.left)
        (Φ : AT ⟶ BT), IsGrpPullback AT A (g ≫ affπ Rg (mA * mB)) φA ∧
        IsGrpPullback BT B (g ≫ affπ Rg (mA * mB)) φB ∧ IsMonHom Φ ∧ Generates bA (φA ≫ θ A) AT.hom (matOf g) ∧
        Proport bA bB (φA ≫ θ A) AT.hom (Φ.left ≫ φB ≫ θ B) (matOf g) := by
    intro T g hg
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj B) := Functor.grpObjObj
    have pA := isGrpPullback_pullback A (g ≫ affπ Rg (mA * mB))
    have pB := isGrpPullback_pullback B (g ≫ affπ Rg (mA * mB))
    have hP := (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A T _ _ _ (g ≫ affπ Rg (mA * mB))).1 pA.1
    obtain ⟨c1, c2, c3⟩ := cond T _ g _ _ hg hP
    obtain ⟨Ψ, hΨ, hpr⟩ := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ T (fA A) (fA B) _ _ mA mB bA bB _ _ _ (matOf g) hEmb hNB hNA hP.w
      c1).1 c2
    obtain ⟨Φ, hΦ, hΦΨ⟩ := GlobalTheory.T.grpHom_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB T _ _ _ _ _ Ψ (matOf g)
      ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ hαA hβB pA pB hΨ c1 hpr c3
    exact ⟨_, inferInstance, _, inferInstance, _, _, Φ, pA, pB, hΦ, c1, by rw [hΦΨ]; exact hpr⟩
  have θf : ∀ C : Over (Sp Rg), θ C ≫ fA C = C.hom := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.1
  have θi : ∀ C : Over (Sp Rg), IsIso (θ C) := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.2
  obtain ⟨A₁, iA₁, B₁, iB₁, φA₁, φB₁, Φ₁, pA₁, pB₁, hΦ₁, hg₁, hp₁⟩ := datum W j₁ ⟨𝟙 _, Category.id_comp _⟩
  haveI := hWn
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic Rg A B L M eA eB W (j₁ ≫ affπ Rg (mA * mB)) A₁ B₁ φA₁ φB₁ Φ₁ hAb hBb hL hM heA heB
    hamp pA₁ pB₁ hΦ₁
  have compare : ∀ (T : Scheme.{0}) (u : T ⟶ W) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φA' →
      IsGrpPullback B' B ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φB' →
      Generates bA (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) →
      Proport bA bB (φA' ≫ θ A) A'.hom (Φ'.left ≫ φB' ≫ θ B) (matOf (u ≫ j₁)) →
      ∃ (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left), IsGrpPullback A' A₁ u ψA ∧ IsGrpPullback B' B₁ u ψB ∧
        ψA ≫ φA₁ = φA' ∧ ψB ≫ φB₁ = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ₁.left := by
    intro T u A' B' _ _ φA' φB' Φ' hA' hB' hgen hprop
    rw [Category.assoc] at hA' hB'
    obtain ⟨ψA, hψA, eA'⟩ := relift pA₁ hA'
    obtain ⟨ψB, hψB, eB'⟩ := relift pB₁ hB'
    refine ⟨ψA, ψB, hψA, hψB, eA', eB', ?_⟩
    apply pB₁.1.hom_ext
    · rw [Category.assoc, eB', Category.assoc, ← cancel_mono (θ B), Category.assoc, Category.assoc, Category.assoc]
      have hp := hp₁.comp ψA u A'.hom hψA.1.w.symm
      rw [← matOf_comp, ← Category.assoc ψA φA₁, eA'] at hp
      refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ _ T (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) _ _ hEmb hNB hNA hgen
        hprop hp ?_
      simp only [Category.assoc, θf]
      rw [hB'.1.w, pB₁.1.w, reassoc_of% (Over.w Φ'), reassoc_of% (Over.w Φ₁), reassoc_of% hψA.1.w]
    · rw [Category.assoc, hψB.1.w, reassoc_of% (Over.w Φ'), Category.assoc, Over.w Φ₁, hψA.1.w]
  obtain ⟨AH, iAH, BH, iBH, φAH, φBH, ΦH, pAH, pBH, hΦH, hgH, hpH⟩ := datum Z (i ≫ j₁) ⟨i, rfl⟩
  obtain ⟨ψA, ψB, hψA, hψB, eψA, eψB, eΦ⟩ := compare Z i AH BH φAH φBH ΦH pAH pBH hgH hpH
  have hlb : LBIso (L.pull φAH) ((M.pull φBH).pull ΦH.left) := by
    have := (hZ Z i AH BH ψA ψB ΦH hψA hψB eΦ).2 ⟨𝟙 _, Category.id_comp _⟩
    rwa [eψA, eψB] at this
  refine ⟨(i ≫ j₁).image, (i ≫ j₁).imageι, Z, (i ≫ j₁).toImage, AH, iAH, BH, iBH, φAH, φBH, ΦH, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.toImage_imageι_assoc]
    exact ⟨pAH, pBH, hΦH, hlb⟩
  · intro R _ t A' B' _ _ φA' φB' Φ' c hT hMat
    obtain ⟨g, hgt, hgc⟩ := GlobalTheory.T.exists_affineSpace_morphism_of_coordinates Rg (Sp R) (mA * mB) t
      (fun n => c (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2)
    have hgm : matOf g = c := by funext a b; simp [matOf, hgc]
    obtain ⟨hgen, hprop, hnorm⟩ := GlobalTheory.T.testHom_matrix_generates_normalised Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c hL hM
      hcov hαA hβB hT hMat
    rw [← hgm] at hgen hprop
    rw [← hgm, ← hgt] at hnorm
    have hP : IsPullback (φA' ≫ θ A) A'.hom (fA A) (g ≫ affπ Rg (mA * mB)) := by
      rw [hgt]; exact (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A _ _ _ _ t).1 hT.1.1
    have hbase : (Φ'.left ≫ φB' ≫ θ B) ≫ fA B = A'.hom ≫ g ≫ affπ Rg (mA * mB) := by
      rw [hgt, Category.assoc, Category.assoc, θf, hT.2.1.1.w, reassoc_of% (Over.w Φ')]
    have hforms := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ _ (fA A) (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (g ≫ affπ Rg _) (matOf g)
      hEmb hNB hNA hP.w hgen).2 ⟨_, hbase, hprop⟩
    obtain ⟨w₁, hw₁⟩ := (hW _ g).1 ⟨(hF _ _ g _ _ hP).1 hforms, (hNm _ g).1 hnorm, (hU _ _ g _ _ hP).1 hgen⟩
    have hA' : IsGrpPullback A' A ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φA' := by rw [hw₁, hgt]; exact hT.1
    have hB' : IsGrpPullback B' B ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φB' := by rw [hw₁, hgt]; exact hT.2.1
    obtain ⟨ψA', ψB', hψA', hψB', eψA', eψB', eΦ'⟩ := compare _ w₁ A' B' φA' φB' Φ' hA' hB'
      (by rw [hw₁]; exact hgen) (by rw [hw₁]; exact hprop)
    have hlb' := hT.2.2.2
    rw [← eψA', ← eψB'] at hlb'
    obtain ⟨w₂, hw₂⟩ := (hZ _ w₁ A' B' ψA' ψB' Φ' hψA' hψB' eΦ').1 hlb'
    refine ⟨w₂, ?_, ?_⟩
    · rw [Scheme.Hom.toImage_imageι_assoc, ← Category.assoc, ← Category.assoc, hw₂, hw₁, hgt]
    · rw [Scheme.Hom.toImage_imageι, ← Category.assoc, hw₂, hw₁, hgm]
  · intro R _ h A' B' _ _ φA' φB' Φ' hT hD
    obtain ⟨ψA', ψB', qA, qB, eA', eB', eΦ'⟩ := hD
    simp only [Scheme.Hom.toImage_imageι_assoc, Scheme.Hom.toImage_imageι] at hT ⊢
    have e₀ : A'.hom ≫ h = ψA' ≫ AH.hom := qA.1.w.symm
    have keyA : ψA' ≫ φAH ≫ θ A = φA' ≫ θ A := by rw [← eA', Category.assoc]
    have keyB : ψA' ≫ ΦH.left ≫ φBH ≫ θ B = Φ'.left ≫ φB' ≫ θ B := by
      rw [← eB']; simp only [Category.assoc]; rw [reassoc_of% eΦ']
    have hgen := hgH.comp ψA' h A'.hom e₀
    rw [keyA, ← matOf_comp] at hgen
    have hpr := hpH.comp ψA' h A'.hom e₀
    rw [keyA, keyB, ← matOf_comp] at hpr
    have hnorm : Normal ((h ≫ i ≫ j₁) ≫ affπ Rg (mA * mB)) (matOf (h ≫ i ≫ j₁)) αA βB :=
      (hNm _ _).2 ((hW _ _).2 ⟨h ≫ i, Category.assoc _ _ _⟩).2.1
    simp only [Category.assoc] at hT hnorm hgen hpr ⊢
    exact GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB R _ A' B' φA' φB' Φ' _ hL hM heA heB hcov hαA hβB hT
      hgen hpr hnorm

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine

theorem val_sum_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) {ι : Type}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hv.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (hv.add _ _)

theorem val_nsmul_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) (n : ℕ) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v (n • f) := by
  have := val_sum_nonneg hv (Finset.range n) (fun _ => f) (fun _ _ => h)
  simpa [Finset.sum_const, Finset.card_range] using this

theorem pnorm_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {ι : Type} (s : Finset ι) (P : ι → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ)
    (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : X.pnorm la (∑ i ∈ s, P i) y ≤ ∑ i ∈ s, X.pnorm la (P i) y := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _)
  rw [Finset.sum_apply]
  exact norm_sum_le _ _

end GlobalTheory.FlatUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitPull

theorem isMonomial_pull {V R : Type} [CommRing V] [IsDomain V] [CommRing R] [IsDomain R]
    {Dg : DegPre V} {Dg' : DegPre R} {ϖ : V} {β : LinearMap.BilinForm ℤ Dg.X} (hm : IsMonomial Dg ![ϖ] ![β])
    (h : V →+* R) (ε : Dg'.X ≃+ Dg.X)
    (hc : ∀ y r, PsiCoord Dg (ε y) r → ∃ u : Rˣ, PsiCoord Dg' y (u * h r)) :
    IsMonomial Dg' ![h ϖ]
      ![β.compl₁₂ (ε : Dg'.X →+ Dg.X).toIntLinearMap (ε : Dg'.X →+ Dg.X).toIntLinearMap] := by
  intro y
  obtain ⟨u, n, hn, hy⟩ := hm (ε y)
  obtain ⟨u', hu'⟩ := hc y _ hy
  refine ⟨u' * Units.map h.toMonoidHom u, n, Fin.forall_fin_one.2 (hn 0), ?_⟩
  have e : (u' : R) * h ((u : V) * ∏ i, ![ϖ] i ^ n i) =
      ((u' * Units.map h.toMonoidHom u : Rˣ) : R) * ∏ i, ![h ϖ] i ^ n i := by
    simp [Fin.prod_univ_one, map_mul, map_pow]
    ring
  exact e ▸ hu'

theorem exists_pull_unif : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (h : T.V →+* R) (hK : FractionRing T.V →+* FractionRing R), IsLocalHom h → (∀ a, hK (algebraMap T.V _ a) = algebraMap R _ (h a)) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (_ : Unif (maximalIdeal R) D A G) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left) (ε : D.toPre.X ≃+ T.D.toPre.X), IsSemiAbelian G ∧ IsGrpPullback A.A F.univ.A (spMap hK ≫ T.y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧ ∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) (h T.ϖ) ^ (T.β (ε a) (ε b')) := by
  intro g n o _ ζ F T R _ _ _ hB hdvr h hK hl hhK
  have hinj : Function.Injective h := by
    intro a b hab
    have e := congrArg (algebraMap R (FractionRing R)) hab
    rw [← hhK, ← hhK] at e
    exact IsFractionRing.injective T.V (FractionRing T.V) (hK.injective e)
  have hϖ : h T.ϖ ≠ 0 := fun e => T.irr.ne_zero (hinj (e.trans (map_zero h).symm))
  have hRC := TraitUniq.isCN_of_base hB
  obtain ⟨κ, hκ, hκβ⟩ := TraitUniq.genFib T h hK hhK
  have hα := hκ.comp T.cart
  have w₁ := hα.1.w
  let α₂B := pullback.map ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)).hom
    ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ ≫ T.α) (κ ≫ T.α) (spMap hK ≫ T.y) w₁.symm w₁.symm
  have hsqB : IsSquare (κ ≫ T.α) α₂B := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨D', A', U', ε, L, hLl, hL, hΛ, hc⟩ := TraitUniq.pull T hRC h hinj hl hK _ _
    (isGrpPullback_pullback T.G (spMap h)) κ hκ hκβ α₂B hsqB
  haveI := U'.gen_hom
  haveI : IsMonHom U'.gen.symm.hom := inferInstanceAs (IsMonHom U'.gen.inv)
  have hgi := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso U'.gen.symm
  have hα' := (hgi.comp hα).congr (Category.id_comp _) rfl
  let H : G2 A'.A ⟶ G2 ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)) :=
    lift (fst A'.A A'.A ≫ U'.gen.inv) (snd A'.A A'.A ≫ U'.gen.inv)
  have hP := F.univ.isLB
  have hAL := A'.isLB
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hAL _ _
  have hΛB : (abelian₂ _ L).IsLB := LB.isLB_linComb hLl _ _
  have e1 : GlobalTheory.CechPic.pull U'.gen.hom.left (GlobalTheory.CechPic.cls _ hAL) = GlobalTheory.CechPic.cls _ hLl := by
    rw [← GlobalTheory.CechPic.cls_pull hAL _ (pull_isLB hAL _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ hLl).2
      (LBIso.trans (pull_isLB hAL _) (pull_isLB U'.LG.isLB _) hLl U'.ext hL.symm)
  have hgi' : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e2 : GlobalTheory.CechPic.cls _ hAL = GlobalTheory.CechPic.pull U'.gen.inv.left (GlobalTheory.CechPic.cls _ hLl) := by
    rw [← e1, ← GlobalTheory.CechPic.pull_comp, hgi', GlobalTheory.CechPic.pull_id]
  have eB : GlobalTheory.CechPic.cls _ hΛB = GlobalTheory.CechPic.pull α₂B (GlobalTheory.CechPic.cls _ hP) := by
    rw [← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hΛ
  have cA : GlobalTheory.CechPic.cls _ hΛA = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ hAL) (fst A'.A A'.A) (snd A'.A A'.A) :=
    GlobalTheory.CechPic.cls_cube_two hAL _ _ hΛA
  have cB : GlobalTheory.CechPic.cls _ hΛB = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ hLl) (fst _ _) (snd _ _) :=
    GlobalTheory.CechPic.cls_cube_two hLl _ _ hΛB
  have eA : GlobalTheory.CechPic.cls _ hΛA = GlobalTheory.CechPic.pull (H.left ≫ α₂B) (GlobalTheory.CechPic.cls _ hP) := by
    rw [cA, e2, GlobalTheory.CechPic.lam_pull, GlobalTheory.CechPic.pull_comp, ← eB, cB, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
  refine ⟨_, inferInstance, inferInstance, D', A', U', U'.gen.inv.left ≫ κ ≫ T.α, H.left ≫ α₂B, ε,
    IsSemiAbelian.pullback (spMap h) T.G T.semi, hα', ⟨?_, ?_⟩,
    (GlobalTheory.CechPic.cls_eq_iff hΛA (pull_isLB hP _)).1 (eA.trans (GlobalTheory.CechPic.cls_pull hP _ _).symm), ?_⟩
  · rw [Category.assoc, hsqB.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsqB.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · intro a b' x hx
    obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre (a + b')
    obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre a
    obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre b'
    obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main R D'.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
    obtain ⟨r₁, c₁, e₁⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₁
    obtain ⟨r₂, c₂, e₂⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₂
    obtain ⟨r₃, c₃, e₃⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₃
    have hm := isMonomial_pull T.mono h ε hc
    obtain ⟨u, hu⟩ := hm.tau (fun i y z => by fin_cases i; exact T.symm (ε y) (ε z))
      (Fin.forall_fin_one.2 hϖ) c₂ c₃ c₁
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, LinearMap.compl₁₂_apply,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_coe] at hu
    refine ⟨u₀ * u, ?_⟩
    have key : algebraMap R (FractionRing R) (u₀ : R) * algebraMap R (FractionRing R) r₁ *
        (algebraMap R (FractionRing R) r₂)⁻¹ * (algebraMap R (FractionRing R) r₃)⁻¹ =
        algebraMap R (FractionRing R) (u₀ : R) * (algebraMap R (FractionRing R) r₁ /
          (algebraMap R (FractionRing R) r₂ * algebraMap R (FractionRing R) r₃)) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [hu₀, e₁, e₂, e₃, key, hu]
    simp only [Units.val_mul, map_mul]
    ring

end GlobalTheory.Poinc.TraitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyByFiniteSubgroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_abelianVariety_by_finiteSubgroup : ∀ (K : Type) [Field K] (A : AbVar K) (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A.X), IsMonHom i → Mono i → IsFinite H.hom → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 ↔ ∃ y, y ≫ i = x := by
  first | (exact @GlobalTheory.AV.AbVar.exists_quotient_finite) | (exact GlobalTheory.AV.AbVar.exists_quotient_finite) | (intros; apply GlobalTheory.AV.AbVar.exists_quotient_finite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOriginStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧ cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  first | (exact @GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin) | (exact GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin) | (intros; apply GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFinite
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GenCut

theorem exists_finite_drop {T : Type} [TopologicalSpace T] [NoetherianSpace T] (Y : Set T) (d : ℕ)
    (hY : topologicalKrullDim Y ≤ (d + 1 : ℕ)) :
    ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → topologicalKrullDim ↥(Y \ U) ≤ d := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hne : ∀ C : irreducibleComponents Y, ∃ y : Y, y ∈ C.1 := fun C => C.2.1.nonempty
  choose y hy using hne
  have : Finite (irreducibleComponents Y) := hfin.to_subtype
  refine ⟨Set.range fun C => (y C : T), Set.finite_range _, fun U hU hS => ?_⟩
  have hC : IsClosed ((Subtype.val : Y → T) ⁻¹' Uᶜ) := hU.isClosed_compl.preimage continuous_subtype_val
  have h := (_root_.GlobalTheory.DimDrop.dim_drop Y).1 _ (d + 1) hC hY fun Z hZ _ hsub =>
    hsub (hy ⟨Z, hZ⟩) (hS ⟨⟨Z, hZ⟩, rfl⟩)
  let f : ↥(Y \ U) → ↥((Subtype.val : Y → T) ⁻¹' Uᶜ) := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have hf : IsInducing f := by
    refine (IsInducing.subtypeVal.comp IsInducing.subtypeVal).of_comp_iff.1 ?_
    exact IsInducing.subtypeVal
  have h2 := lt_of_le_of_lt hf.topologicalKrullDim_le h
  rw [Nat.cast_add, Nat.cast_one] at h2
  exact ENat.WithBot.lt_add_one_iff.1 h2

theorem exists_sections_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  intro k _ X _ p D hp P hA d
  have := hp.isNoetherian
  induction d with
  | zero =>
    intro Z _ hd
    have hf : Finite ↥(Z ∩ fib X 0) := (_root_.GlobalTheory.DimDrop.dim_drop ↥(Z ∩ fib X 0)).2 inferInstance (by simpa using hd)
    refine ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, ?_⟩
    exact (Set.toFinite (Z ∩ fib X 0)).subset (Set.inter_subset_inter_left _ Set.sdiff_subset)
  | succ d ih =>
    intro Z hZ hd
    obtain ⟨S, hS, hdrop⟩ := exists_finite_drop (Z ∩ fib X 0) d hd
    obtain ⟨e₀, he₀, f, hf, hSf⟩ := _root_.GlobalTheory.HSAmp.exists_sec_nonvanishing_finite k X p D hp P hA S hS
    have hU : IsOpen (NV P e₀ 0 f) := (_root_.GlobalTheory.HSAmp.nv_rules k X p P e₀ 0 f hf).1
    have h := hdrop _ hU hSf
    rw [show (Z ∩ fib X 0) \ NV P e₀ 0 f = (Z \ NV P e₀ 0 f) ∩ fib X 0 from by
      ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto] at h
    obtain ⟨e, g, heg, hfin⟩ := ih _ (hZ.sdiff hU) h
    refine ⟨Fin.cons e₀ e, Fin.cons f g, fun j => ?_, hfin.subset ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨he₀, hf⟩
      · exact heg j
    · rintro x ⟨⟨hxZ, hx⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists] at hx
      refine ⟨⟨⟨hxZ, hx 0⟩, ?_⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists]
      exact fun j => hx j.succ

end GlobalTheory.HSAmp.GenCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprimeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  first | (exact @GlobalTheory.AfPZero.main) | (exact GlobalTheory.AfPZero.main) | (intros; apply GlobalTheory.AfPZero.main <;> assumption)
end

