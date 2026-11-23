module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.EmbeddingValuationsAnti
public import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralLocalGridTensorOfLevelChar
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0006
public import Development.AutomorphicArithmetic.LocalEmbeddings.FlipVal
public import Development.AutomorphicArithmetic.LocalEmbeddings.FlipInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.gs_scal_base {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) {Z : Scheme.{0}}
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  have hc : ∀ {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (x : A),
      scal q (φ x) = scal (q ≫ spMap φ) x := by
    intro A B _ _ Y q φ x
    have e := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [e]
  rw [hc, hc]
  have hg : ∀ {A : Type} [CommRing A] {Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Sp A) (x : A),
      gs f z ⊤ (scal q x) = gs (f ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) :=
    fun f q x => gs_pull f q z ⊤ trivial _
  rw [hg, hg]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem Trait.exp_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (r t : R) (u : W), (∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J) → T.Exp 1 u s₂ F → T.Exp (T.φ t) (T.φ r * u) s₁ F := by
  intro R _ _ _ D C W _ _ _ T k F s₁ s₂ r t u hrel hExp
  have h1 := GlobalTheory.Mum.Trait.exp_mul_left R D C W T k s₂ F 1 u (T.φ r) hExp
  rw [_root_.mul_one] at h1
  obtain ⟨σ, hσ, hs⟩ := h1
  refine ⟨σ, hσ, ?_⟩
  intro Z p p' hp z J hJ
  rw [hs Z p p' hp z J hJ, T.gs_scal_base p p' hp z r, T.gs_scal_base p p' hp z t]
  exact (hrel Z p' z J hJ).symm

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

def FibreKilled (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] (P : LB (G2 G).left) (s : S') : Prop :=
  ∀ (T' : Over S') (x : T' ⟶ G),
    (∃ f : T'.left ⟶ Spec (S'.residueField s), T'.hom = f ≫ S'.fromSpecResidueField s) →
    (∃ c : (P.pull (lift (snd G T' ≫ x) (fst G T')).left).Gen, c.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGerms
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslGerm

open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_comp)

theorem point_formula {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {U : X.affineOpens} {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)}
    (hv : ∀ a, IsTanAtG t (chart U) (v a))
    {δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)}
    (hδv : ∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S]
      (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w →
      valR g₀ O (δ a O f) = (valR w O f).snd)
    {r : Fin n → Γ(X, U.1)} {x : tEpsG (chart U) ⟶ t.G} (hx : IsCombAtG t (chart U) v r x.left)
    {S : Type} [CommRing S] {φ : Γ(X, U.1) →+* S} {P : tEpsG (spMap φ ≫ chart U) ⟶ t.G}
    (hP : P.left = spMap (dualMap φ) ≫ x.left) {O : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1)
    (f : Γ(t.G.left, O)) {C : Type} [CommRing C] (z : Sp C ⟶ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left)
    (hz : ⊤ ≤ z ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O)) :
    ⊤ ≤ (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) ⁻¹ᵁ O ∧
    valR (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) O f =
      valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O f +
      valR (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left) ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) *
        valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O
          (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left := ⟨_, rfl⟩
  have hg₀O : ⊤ ≤ g₀ ⁻¹ᵁ O := by rw [hg₀]; exact hz
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : DualNumber S →+* C, z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left = spMap ψ₀ :=
    ⟨(Spec.preimage (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left)).hom, (Spec.map_preimage _).symm⟩
  let ψ : DualNumber Γ(X, U.1) →+* C := ψ₀.comp (dualMap φ)
  have hd : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) = (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext; intro s; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : g₀ ≫ t.G.hom = spMap (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) ≫ chart U := by
    have e1 : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ t.G.hom =
        (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ (tEpsG (spMap φ ≫ chart U)).hom :=
      (Over.w _).trans (Over.w _).symm
    rw [hg₀, Category.assoc, e1, ← Category.assoc, hψ₀]
    show spMap ψ₀ ≫ spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ chart U = _
    rw [← Category.assoc, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    simp only [ψ, RingHom.comp_assoc, hd]
  let a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U) := Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom
    rw [hbase, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap])
  choose w hw using fun b => (existsUnique_isTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))))
    hbase (hv b)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.FirstOrderValue.valR_mul_comb E H X t U n v hv r x hx C ψ g₀ a w rfl hw O f hg₀O

  let zO : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (spMap φ ≫ chart U) ⊗ t.G := Over.homMk z (by
    show z ≫ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).hom = g₀ ≫ t.G.hom
    rw [hg₀, ← Over.w (snd (tEpsG (spMap φ ≫ chart U)) t.G), Category.assoc])
  have hzs : zO ≫ snd (tEpsG (spMap φ ≫ chart U)) t.G = (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) :=
    Over.OverMorphism.ext hg₀.symm
  have hzf : zO ≫ fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P = a ≫ x := by
    apply Over.OverMorphism.ext
    show z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ P.left = spMap ψ ≫ x.left
    rw [hP, ← Category.assoc, hψ₀, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
  have hτ : zO ≫ lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G] =
      (a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) := by
    rw [← Category.assoc, comp_lift, hzs, hzf]
    rfl
  have hτl : z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
      μ[t.G]).left = ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left :=
    congrArg Over.Hom.left hτ
  rw [hτl, ← hg₀]
  refine ⟨h1, ?_⟩
  rw [h2, hψ₀]
  congr 1
  have hε : ψ DualNumber.eps = ψ₀ DualNumber.eps := by simp [ψ, dualMap]
  have hsp : valR (spMap ψ₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) =
      ψ₀ DualNumber.eps := GlobalTheory.Points.valR_specMap (CommRingCat.ofHom ψ₀) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsp, ← hε, valR_eq _ _ hg₀O, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, ← valR_eq _ _ hg₀O, ← valR_eq _ _ hg₀O, GlobalTheory.LogKSLin.valR_base U hO hbase hg₀O,
    hδv b O hO f C _ g₀ (w b) hbase hg₀O (hw b)]
  rfl

theorem transl_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  intro E _ _ _ H X t U n v hv δ _ _ hδv r x hx S _ φ P hP O hO f y hy
  have key := fun (C : Type) [CommRing C] z hz => point_formula hv hδv hx hP hO f (C := C) z hz

  have hVτ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤
      (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left ⁻¹ᵁ O := by
    intro y' hy'
    obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy'
    have hz : ⊤ ≤ hW.fromSpec ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O) :=
      GlobalTheory.Points.le_preimage_mono _ hWV hW.fromSpec_preimage_self.ge
    obtain ⟨p, rfl⟩ : y' ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have := (key Γ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left, W) hW.fromSpec hz).1 (Set.mem_univ p)
    exact this
  have hVπ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ ⊤ :=
    fun _ _ => trivial

  have hAB : ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVτ).op).hom
      (((lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left.app O).hom f) =
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom f +
      ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVπ).op).hom
        (((fst (tEpsG (spMap φ ≫ chart U)) t.G).left.app ⊤).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps)) *
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
    refine GlobalTheory.CechInv.ext_of_valR _ _ _ fun C _ z hz => ?_
    rw [valR_res _ hVτ hz, ← valR_comp, (key C z hz).2, valR_add _ _ hz, valR_mul _ _ hz, valR_res _ hVπ hz,
      ← valR_comp, ← valR_comp, ← valR_comp]
  have hτy := hVτ hy
  rw [gs_eq _ y O hτy, gs_eq _ y O hy, gs_eq _ y ⊤ trivial, gs_eq _ y O hy,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVτ) y hy, hAB, map_add, map_mul,
    TopCat.Presheaf.germ_res_apply _ (homOfLE hVπ) y hy]

end GlobalTheory.TranslGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipsLossBoundedAtExceptionalPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section SlopeTestRemainingChoices

open ValuativeRel UpperTheory.FlipInt UpperTheory.FlipVal

private theorem psi_int {D : D7} {w : Pl D.host.E} {ψ : AddChar (Kw w) Circle} (hc : HasConductor ψ 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) : IsIntegral ℤ (ψ x : ℂ) := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  set q := Ideal.absNorm w.asIdeal
  have hq0 : q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : ψ ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero n hq0)) ?_
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
  exact isIntegral_one

private theorem emb_inj (D : D7) : Function.Injective
    (Sum.elim (Formalism.L2.Host.embTau D) fun i => ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D i)) := by
  have h1 : Function.Injective (Formalism.L2.Host.embTau D) := GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_injective D
  have h2 : ∀ τ τ', ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D τ) ≠ Formalism.L2.Host.embTau D τ' := fun τ τ' h =>
    GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_ne_bar D τ τ' ((RingHom.ext fun _ => rfl).trans h)
  refine h1.sumElim (fun a b h => h1 (star_injective h)) fun a b h => h2 b a h.symm

private theorem lev_two {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {v : HeightOneSpectrum (𝓞 E)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx h' => h x hx (h'.trans (WithZero.exp_le_exp.2 (by norm_num)))

private theorem nu_int {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    (large₂ : SizeData₂ D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) (t : T) (w : Pl D.host.E)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    ((locGrid G t w).nu i j (unifAt w) : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) ∧
      ((locGrid G t w).nu i j (unifAt w)⁻¹ : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) := by
  classical
  obtain ⟨b1, b2⟩ := UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows D large₂ hS hH
  have h12 := (GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS).2.2.2.2.2.2.2
  have e1 : (((locGrid G t w).nu i j (unifAt w) : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).val w : ℂ) * ((L.xiH t).val w : ℂ) * (((G.ch.chiH (D.R.m - i)).val w : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hμ := L.C.isMu0 ⟨j, hj⟩
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.Chain.StepVac.hasInfQ_tau hμ.inf
  have hg0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨m1, m2⟩ := val_int (L.C.mu0 ⟨j, hj⟩) (Formalism.L2.DIV.primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E))
    (fun v hv => hμ.unr v fun k hk => hv (by
      rw [Formalism.L2.DIV.mem_primesOf, and_iff_right hg0, Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem]
      fin_cases k
      exacts [Or.inl hk, Or.inr hk])) (fun v => lev_two (hμ.tame v)) (Formalism.L2.Host.embTau D) (emb_inj D) n hinf
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h1 := hn τ
      simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
      have h2 : (n τ : ℝ) = 2 * -(((D.hc τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by exact_mod_cast h1
      have h3 := b1 τ ⟨j, hj⟩
      rw [Nat.cast_natAbs, Int.cast_abs, h2, abs_mul, abs_neg, abs_two]
      linarith)) w
  have hi1 : 1 ≤ D.R.m - i := by omega
  have hi2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨c1, c2⟩ := val_int (G.ch.chiH (D.R.m - i)) (G.pl.S0.biUnion (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F))
    (fun v hv => G.ch.unr _ hi1 hi2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, h, by simp [Formalism.L2.Host.aboveF]⟩))
    (fun v => by
      by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
        · exact lev_two (G.ch.lev0 _ hi1 hi2 v h).1
        · exact (G.ch.lev1 _ hi1 hi2 v h).1
      · exact fun x hx _ => G.ch.unr _ hi1 hi2 v h x hx) (Formalism.L2.Host.embTau D) (emb_inj D) _ (G.ch.inf _ hi1 hi2)
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h3 := b2 τ _ hi1 hi2
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul, Int.cast_ofNat, abs_two, hc]
      linarith)) w
  obtain ⟨N, hN, hord⟩ := hL.xi_fin t
  have hx : ((L.xiH t).val w : ℂ) ^ N = 1 := by
    have h1 : ((L.xiH t) ^ N).val w = 1 := by rw [show (L.xiH t) ^ N = 1 from hord]; rfl
    have h2 : ((L.xiH t) ^ N).val w = (L.xiH t).val w ^ N := rfl
    rw [← Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one]
  have x1 : IsIntegral ℤ ((L.xiH t).val w : ℂ) := IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one)
  have x2 : IsIntegral ℤ ((L.xiH t).val w : ℂ)⁻¹ := IsIntegral.of_pow hN (by rw [inv_pow, hx, inv_one]; exact isIntegral_one)
  rw [map_inv, Units.val_inv_eq_inv_val, e1, two_mul]
  refine ⟨Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m1) (Lo_zero x1)) (mem_Lo.2 c2), ?_⟩
  rw [mul_inv, mul_inv, inv_inv]
  exact Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m2) (Lo_zero x2)) (mem_Lo.2 c1)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flips_loss_bounded_at_exceptional_places : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)) := by
  refine ⟨0, fun CF _ => ⟨56, fun ε => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc hF t Φ w hw la hla z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hq : resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hq0 : resCard (Kw w) ≠ 0 := by rw [hq]; exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hgap : ch.sc.cGap = 1 := by rw [show ch.sc = _ from hsc]
  have hfl : ∀ x ∈ flipOrder D.R.m, x.1 < D.R.m ∧ x.2 < D.R.m ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧ ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    exact ⟨hi, hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram⟩

  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  obtain ⟨y, hy⟩ : ∃ y, D.what₂.embLL y = Tflip ch.W ch.S.B t Φ w z :=
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ)
      (fun x hx => ⟨(hfl x hx).2.2.1, (hfl x hx).2.2.2, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi (hfl x hx).1 (hfl x hx).2.1⟩)
      (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
      (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z)

  have key : Tflip ch.W ch.S.B t Φ w z ∈ UpperTheory.FlipInt.Lo (resCard (Kw w)) (0 + (flipOrder D.R.m).length *
      (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D))) := by
    refine UpperTheory.FlipInt.flips_mem h00.unif h00.cond h00.one_le hq0 (psi_int h00.cond _) (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ) 0 (fun x hx => ?_) (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm
      (fun z => UpperTheory.FlipInt.Lo_zero (UpperTheory.isIntegral_localGrid_tensor_of_levelChar hL ch.S.B t Φ w z)) z
    obtain ⟨hi, hj, h1, h2⟩ := hfl x hx
    have h3 := nu_int ch.G hL large₂ hS.size hS.host hgap t w hi hj
    rw [← hq] at h3
    refine ⟨h1, h2, h3.1, h3.2, ?_⟩
    change D.R.r + (x.2 + 1) * D.R.t + (x.1 + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have a1 : (x.2 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have a2 : (x.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have a3 : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    rw [mul_add, mul_add]; omega
  rw [zero_add, (canFlip_flipOrder _).2.1, UpperTheory.FlipInt.mem_Lo, ← hy, ← map_natCast D.what₂.embLL, ← map_pow, ← map_mul] at key
  replace key := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 key
  refine ⟨y, hy, ?_⟩
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  refine Or.inr ?_
  have h1 := UpperTheory.FlipVal.vw_ge la hy0 hq0 _ key
  have h2 : -(((D.R.m ^ 2 * (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D)) : ℕ) : ℝ) *
      (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ)) ≤ (vw la y : ℝ) := by exact_mod_cast h1
  refine le_trans (neg_le_neg ?_) h2
  by_cases hW : w ∈ ch.G.pl.W0
  · have hd : depthAt ch.G w = cosExp ch.G w := by
      rw [depthAt, max_eq_left]
      rw [cosExp, if_pos hW]
      exact ch.G.pl.depth_pos _ _
    obtain ⟨s1, -, s2, -, -, -, -, s3⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
    have s2' : (1 : ℝ) ≤ bigN D := by exact_mod_cast s2
    have s4 : (⌊8 * large₂.sc.b⌋₊ : ℝ) ≤ 8 * large₂.sc.b := Nat.floor_le (by linarith)
    have s5 : (0 : ℝ) ≤ (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ) := by
      exact_mod_cast UpperTheory.FlipVal.vw_nat_nonneg la _
    refine mul_le_mul_of_nonneg_right ?_ s5
    rw [hd]
    push_cast
    have s6 : 3 * (2 * (⌊8 * large₂.sc.b⌋₊ : ℝ)) + 8 * bigN D ≤ 56 * (bigN D * large₂.sc.b) := by nlinarith
    calc _ ≤ (D.R.m : ℝ) ^ 2 * ((cosExp ch.G w : ℝ) * bigN D * (56 * (bigN D * large₂.sc.b))) := by gcongr
      _ = _ := by ring
  · have h0 : vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) = 0 := by
      rw [hq]; exact UpperTheory.FlipVal.vw_absNorm la w (hla.resolve_left hW)
    rw [h0]; simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TermDescend

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ₀ σ₁ σ₂ τ₀ τ₁ τ₂ a b h₀ h₁ h₂ H z J hJ
  obtain ⟨Z, p, w, y, hw, hp, hinj, hy⟩ := GlobalTheory.RayLift.exists_flat_lift R Q O oa Y z
  subst hw
  obtain ⟨J', hJ', hJJ⟩ := exists_good Q.P.L Q.P.isLB w (K := (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left)
    (fun ψ => p ≫ ψ) J (fun ψ ψ' e => by rw [(cancel_epi p).1 e]) (fun ψ => by
      rw [Scheme.Hom.comp_apply]; exact hJ ψ)
  have hfun : (fun ψ => J' (p ≫ ψ)) = J := funext hJJ
  let T : Over (Sp R) := Over.mk (y ≫ Y.H.hom)
  let x : T ⟶ Y.H := Over.homMk y rfl
  let v : (Z.presheaf.stalk w)ˣ := val ((Y.Φ T x).s α) (𝟙 _) w J'
  have e₀ : sval τ₀ y w J' = sval σ₀ (y ≫ Y.q.left) w J' * v.val := h₀ T x w J' hJ'
  have e₁ : sval τ₁ y w J' = sval σ₁ (y ≫ Y.q.left) w J' * v.val := h₁ T x w J' hJ'
  have e₂ : sval τ₂ y w J' = sval σ₂ (y ≫ Y.q.left) w J' * v.val := h₂ T x w J' hJ'
  have E := H Z y w J' hJ'
  have hH : y ≫ Y.H.hom = p ≫ ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) := by
    rw [← Category.assoc, ← hy, Category.assoc, Over.w Y.q]
  rw [e₀, e₁, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul] at E
  have E' := (Units.mul_left_inj _).1 E
  rw [hH, hy, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ',
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial,
    GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial, hfun, ← map_mul, ← map_mul, ← map_add] at E'
  exact hinj E'

end GlobalTheory.TermDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_relation_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  first | (exact @GlobalTheory.UPel.HT.zRel_of_pullback) | (exact GlobalTheory.UPel.HT.zRel_of_pullback) | (intros; apply GlobalTheory.UPel.HT.zRel_of_pullback  <;> assumption)
end

