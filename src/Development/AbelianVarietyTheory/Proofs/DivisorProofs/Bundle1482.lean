module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPotentialGoodReductionOfFiniteImageInertia
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem restrictScalars_mem_inertia_of_mem {K L Ω : Type} [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[L] Ω)
    (h : σ ∈ inertia L V) : σ.restrictScalars K ∈ inertia K V := by
  rw [mem_inertia_iff] at h ⊢
  refine ⟨?_, h.2⟩
  have h1 := h.1
  ext x
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem hasPotentialGoodReduction_of_finite_image_inertia : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite → HasPotentialGoodReduction R K A := by
  intro hN R K Ω _ _ _ _ _ _ _ _ _ hs V hV A _ _ hA l _ hl hfin
  haveI : Algebra.IsSeparable K Ω := hs.separable
  haveI : IsSepClosed Ω := hs.sep_closed
  haveI : IsProper A.hom := hA.proper
  obtain ⟨L, hL, hfix⟩ := _root_.GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one K Ω A inferInstance l _ hfin
  let W : ValuationSubring L := V.comap (algebraMap L Ω)
  have hW : IsAbove R K W.toSubring := by
    unfold IsAbove at hV ⊢
    rw [← hV]
    ext x
    rfl
  haveI : IsDiscreteValuationRing W := _root_.GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove R K L W hW
  have hr : (algebraMap W L).range = W.toSubring := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hW' : IsAbove R K (algebraMap W L).range := hr ▸ hW
  obtain ⟨hp, hm⟩ := _root_.GlobalTheory.AbVarRedRes.residue_perfect_and_char R K L W hW'
  obtain ⟨hab, hc⟩ := _root_.GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm K L A hA
  haveI : IsSepClosure L Ω := ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  have hV' : IsAbove W L V.toSubring := by
    unfold IsAbove
    rw [hr]
    rfl
  refine ⟨L, W, inferInstance, inferInstance, hL, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hW', ?_⟩
  refine (hN.iff_tateUnramified hV' hab l (hm l hl)).2 fun σ hσ => ?_
  rw [_root_.GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff K L Ω A l σ]
  exact hfix _ (restrictScalars_mem_inertia_of_mem V σ hσ) fun a ha => σ.commutes ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTangentOfSingleAffineChart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef.TanLoc

theorem ev_congr {R : Type} [CommRing R] {X : Scheme.{0}} {b b' : Sp R ⟶ X} (e : b = b') {U : X.Opens}
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt b h f = evAt b' h' f := by
  subst e; rfl

theorem coeff_one_mul {E : Type} [CommRing E] (P Q : PowerSeries E) :
    PowerSeries.coeff 1 (P * Q) = PowerSeries.constantCoeff (R := E) P * PowerSeries.coeff 1 Q +
      PowerSeries.constantCoeff (R := E) Q * PowerSeries.coeff 1 P := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ring

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {E : Type} [CommRing E] (b : Sp E ⟶ S) {n : ℕ}
  {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E)

theorem rhs_res {Ua Ub : G.left.Opens} (k : Ub ≤ Ua) {Va Vb : S.Opens} (hVa : Va ≤ V) (hVb : Vb ≤ V)
    (hab : Vb ≤ Va) (hea : Va ≤ unitSec G ⁻¹ᵁ Ua) (heb : Vb ≤ unitSec G ⁻¹ᵁ Ub) (hba : ⊤ ≤ b ⁻¹ᵁ Va)
    (hbb : ⊤ ≤ b ⁻¹ᵁ Vb) (g : Γ(G.left, Ua)) :
    ∑ i, w i * evAt b hbb (dualApp (τ i) hVb (dUnit G heb (G.left.presheaf.map (homOfLE k).op g))) =
      ∑ i, w i * evAt b hba (dualApp (τ i) hVa (dUnit G hea g)) := by
  obtain ⟨-, -, ev_res, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h1 : dUnit G heb (G.left.presheaf.map (homOfLE k).op g) = resM _ hab (dUnit G hea g) := by
    rw [resM_dUnit]; exact dUnit_resG G heb k g
  rw [h1]
  have h2 := dualApp_resM (τ i) hVa hab (dUnit G hea g)
  rw [h2]
  exact ev_res E S b Va Vb hab hba hbb _

theorem rhs_mul (ξ : Sp (PowerSeries E) ⟶ G.left)
    (hz : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = b ≫ unitSec G) {U₂ : G.left.Opens}
    (hU₂ : ⊤ ≤ ξ ⁻¹ᵁ U₂) {V₂ : S.Opens} (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U₂)
    (hb₂ : ⊤ ≤ b ⁻¹ᵁ V₂) (g k : Γ(G.left, U₂)) :
    ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ (g * k))) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ g) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ k)) +
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ k) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) := by
  obtain ⟨ev_map, ev_comp, -, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  have hc : ⊤ ≤ (b ≫ unitSec G) ⁻¹ᵁ U₂ := by
    intro x _
    show (b ≫ unitSec G) x ∈ U₂
    rw [← hz, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  have hc' : ⊤ ≤ (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) ⁻¹ᵁ U₂ := hz ▸ hc
  have hε : ∀ f : Γ(G.left, U₂), evAt b hb₂ ((unitSec G).appLE U₂ V₂ he₂ f) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ f) := by
    intro f
    rw [← ev_comp E S G.left b (unitSec G) V₂ U₂ hb₂ hc he₂ f, ← ev_congr hz hc' hc,
      ev_map (PowerSeries E) E G.left (PowerSeries.constantCoeff (R := E)) ξ U₂ hU₂ hc' f]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dUnit_mul, map_add (f := _), LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_add (f := _),
    map_mul, map_mul, hε, hε]
  ring

end GlobalTheory.Nef.TanLoc

namespace GlobalTheory.Nef


open TanLoc in
theorem hasTan_of_affine_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  intro S G _ E _ c b ξ hξ n V τ w U hUa hU V' hV he hb H U₁ hU₁ V₁ hV₁ he₁ hb₁ f₁
  obtain ⟨-, -, ev_res, ev_loc, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  have hyU := (ev_loc (PowerSeries E) G.left ξ U).1 hU
  have hyU₁ := (ev_loc (PowerSeries E) G.left ξ U₁).1 hU₁
  obtain ⟨t, htle, hyt⟩ := hUa.exists_basicOpen_le ⟨_, hyU₁⟩ hyU
  have hk : G.left.basicOpen t ≤ U := G.left.basicOpen_le t
  have hU₂ : ⊤ ≤ ξ ⁻¹ᵁ G.left.basicOpen t := (ev_loc (PowerSeries E) G.left ξ _).2 hyt
  have hV₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ V := inf_le_left.trans (inf_le_left.trans hV)
  have he₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ unitSec G ⁻¹ᵁ G.left.basicOpen t := inf_le_right
  have hb₂ : ⊤ ≤ b ⁻¹ᵁ (V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t) := by
    intro x hx
    refine ⟨⟨hb hx, hb₁ hx⟩, ?_⟩
    show unitSec G (b x) ∈ G.left.basicOpen t
    rw [← Scheme.Hom.comp_apply, ← hξ.zero, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  set L₂ : Γ(G.left, G.left.basicOpen t) → E := fun g => PowerSeries.coeff 1 (evAt ξ hU₂ g) with hL₂
  set R₂ : Γ(G.left, G.left.basicOpen t) → E :=
    fun g => ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) with hR₂
  set ε : Γ(G.left, G.left.basicOpen t) →+* E := (PowerSeries.constantCoeff (R := E)).comp (evAt ξ hU₂) with hε
  have Lmul : ∀ g k, L₂ (g * k) = ε g * L₂ k + ε k * L₂ g := fun g k => by
    simp only [hL₂, hε, RingHom.comp_apply, map_mul, coeff_one_mul]
  have Rmul : ∀ g k, R₂ (g * k) = ε g * R₂ k + ε k * R₂ g := fun g k =>
    rhs_mul G b τ w ξ hξ.zero hU₂ hV₂ he₂ hb₂ g k
  have hA : ∀ g : Γ(G.left, U), L₂ (G.left.presheaf.map (homOfLE hk).op g) =
      R₂ (G.left.presheaf.map (homOfLE hk).op g) := by
    intro g
    simp only [hL₂, hR₂]
    rw [ev_res (PowerSeries E) G.left ξ U _ hk hU hU₂, H g,
      rhs_res G b τ w hk hV hV₂ (inf_le_left.trans inf_le_left) he he₂ hb hb₂ g]
  have hk₁ : G.left.basicOpen t ≤ U₁ := htle
  have hB : L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) = PowerSeries.coeff 1 (evAt ξ hU₁ f₁) ∧
      R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) =
        ∑ i, w i * evAt b hb₁ (dualApp (τ i) hV₁ (dUnit G he₁ f₁)) := by
    refine ⟨?_, ?_⟩
    · simp only [hL₂]; rw [ev_res (PowerSeries E) G.left ξ U₁ _ hk₁ hU₁ hU₂]
    · exact rhs_res G b τ w hk₁ hV₁ hV₂ (inf_le_left.trans inf_le_right) he₁ he₂ hb₁ hb₂ f₁
  rw [← hB.1, ← hB.2]
  have hl := hUa.isLocalization_basicOpen t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) (G.left.presheaf.map (homOfLE hk₁).op f₁)
  have hunit : IsUnit (algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) (s : Γ(G.left, U))) :=
    IsLocalization.map_units _ s
  have hs' : algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) = (G.left.presheaf.map (homOfLE hk).op).hom := rfl
  rw [hs'] at hs hunit
  have key := congrArg (fun z => L₂ z - R₂ z) hs
  simp only at key
  rw [Lmul, Rmul, hA a, hA s, sub_self] at key
  have hne : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) ≠ 0 := (hunit.map ε).ne_zero
  have : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) *
      (L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) - R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁)) = 0 := by
    rw [← key]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSections
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem flatAt_of_simpleAt : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F),
      (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E),
        aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) →
      ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  intro hQ F _ _ X Λ₀ hX δ f Q hS s hs
  have hF : SimpleAt X.toTuple δ f F s := hS F s (by simpa [MvPolynomial.coe_aeval_eq_eval] using hs)
  obtain ⟨E, iE, nE, iFE, iEE, htow, hsp⟩ := GlobalTheory.HSCore.exists_split F X.toTuple F s hF.good
  have heq : (fun i k => @algebraMap F E _ _ iEE (s i k)) = fun i k => @algebraMap F E _ _ iFE (s i k) := by
    funext i k
    rw [@IsScalarTower.algebraMap_apply F F E _ _ _ _ iEE iFE htow (s i k)]
    rfl
  rw [heq] at hsp
  clear heq htow iEE
  have hval : aeval (fun p : Fin X.D × Fin X.N => algebraMap F E (s p.1 p.2)) Q =
      algebraMap F E (eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q) := by
    exact (MvPolynomial.eval₂_comp_left (algebraMap F E) (RingHom.id F) _ Q).symm
  have hSE : SimpleAt X.toTuple δ f E (fun i k => algebraMap F E (s i k)) :=
    hS E _ (by rw [hval]; exact (map_ne_zero _).2 hs)
  have hgood : (X.baseChange E).IsGood (fun i k => algebraMap F E (s i k)) := Geo.isGood_baseChange_iff.2 hSE.good
  obtain ⟨Co, c, hc, hspec⟩ := _root_.GlobalTheory.HSShort.SplitCoord.exists_coord_spec_eq F X.toGeo E _ hgood δ f hsp hSE
  have hnef₂ := nef_big_second_baseChange F X E hX.nef₂ hX.big₂
  have hnefA := GlobalTheory.HSCore.nef_big_baseChange F X E hX.nef hX.big
  have hms : (X.baseChange E).MulStable :=
    (GlobalTheory.HilbertSamuel.Data.complexify_statement F X (fun _ => X.beta) hX.totallyComplex
      (fun _ => one_pos.trans_le X.one_le_beta) hX.mulStable hX.mulBound).2 E
  have hFM : FilMono := GlobalTheory.HSCore.filMono_of_kerRes (GlobalTheory.HSKerRes.kerRes hQ)
  obtain ⟨hind, hmul, hspan⟩ := _root_.GlobalTheory.HSShort.totExt_props F X Λ₀ E
  obtain ⟨hcomm, -, -⟩ := _root_.GlobalTheory.HSShort.shift_comm_single_mono E (X.toGeo.baseChange E)
  have honto := _root_.GlobalTheory.HSShort.map_totRes_range_incl_zero hQ E (X.baseChange E) _ hgood δ Co hnef₂.1 hnef₂.2
  have hker := totFil_totSym_ker E (X.baseChange E) _ hgood δ Co
  have hmono := _root_.GlobalTheory.HSShort.totSym_mono E (X.baseChange E) _ hgood δ Co hms
  have hdiv := _root_.GlobalTheory.HSShort.totFil_deepest hFM E (X.baseChange E) _ hgood hnefA.1 hnefA.2 hms
  let Φ : (sysOf X Λ₀).Flat E (Tot (X.toGeo.baseChange E)) (fun i k => algebraMap F E (s i k)) δ :=
    { ι := totExt X.toGeo E
      indep := hind
      mul := shift (X.toGeo.baseChange E)
      comm := hcomm
      mul_ι := hmul
      y := Co.y
      y_ne := Co.y_ne
      res := totRes (X := X.baseChange E) Co
      onto := by rw [hspan 0]; exact honto
      U := totFil (X.baseChange E) (fun i k => algebraMap F E (s i k))
      sym := totSym (X := X.baseChange E) Co
      le := fun a ha => (hker a ha).1
      ker := fun a ha => (hker a ha).2
      mono := fun a ha α l m hm => hmono a ha α l m (by rw [hspan 0] at hm; exact hm)
      div := by rw [hspan]; exact hdiv }
  exact ⟨E, Tot (X.toGeo.baseChange E), inferInstance, inferInstance, inferInstance, inferInstance, Φ, c, hc, hspec⟩

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZero
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelVanish

variable {n : ℕ}

theorem delAt_const (c : Alt n) (v : V n) : delAt (fun _ => c) v = 0 := by
  simp [delAt, coefwise]

theorem delAt_add {F G : V n → Alt n} {v : V n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  have key (a : Fin n) : coefwise (fun f => del f v (coordVec a)) (fun x => F x + G x) =
      coefwise (fun f => del f v (coordVec a)) F + coefwise (fun f => del f v (coordVec a)) G := by
    simp only [coefwise, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [map_add (f := _), Finsupp.add_apply]
    rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]
  simp only [delAt, key, mul_add, Finset.sum_add_distrib]

theorem repr_ι (x : Fin n ⊕ Fin n → ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (ExteriorAlgebra.ι ℂ x) S =
      ∑ i, x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (x i) : Fin n ⊕ Fin n → ℂ) = x i • Pi.single i 1 by
    ext j; simp [Pi.single_apply]]
  simp

theorem del_mul_const {f : V n → ℂ} {v : V n} (hf : DifferentiableAt ℝ f v) (k : ℂ) (e : V n) :
    del (fun w => f w * k) v e = del f v e * k := by
  rw [del_mul hf (differentiableAt_const k), del_const]; simp

theorem delAt_ι {u : V n → (Fin n ⊕ Fin n → ℂ)} {v : V n}
    (hu : ∀ i, DifferentiableAt ℝ (fun w => u w i) v) :
    delAt (fun w => ExteriorAlgebra.ι ℂ (u w)) v =
      ∑ a, dz a * ExteriorAlgebra.ι ℂ (fun i => del (fun w => u w i) v (coordVec a)) := by
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  have e : (fun x => (bas n).repr (ExteriorAlgebra.ι ℂ (u x)) S) = fun x =>
      ∑ i, u x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := funext fun x => repr_ι _ _
  rw [FormMul.repr_coefwise, repr_ι, e]
  rw [del_sum (fun i _ => (hu i).mul_const _), ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => del_mul_const (hu i) _ _

theorem sum_symm_dz_mul (s : Fin n → Fin n → ℂ) (hs : ∀ a b, s a b = s b a) :
    ∑ a, ∑ b, s a b • (dz a * dz b) = 0 := by
  set X := ∑ a, ∑ b, s a b • (dz a * dz b) with hX
  have h : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    simp only [hX, ← Finset.sum_neg_distrib, ← smul_neg]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs, dz, dz]
    congr 1
    apply eq_neg_of_add_eq_zero_left
    exact ExteriorAlgebra.ι_add_mul_swap _ _
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel X
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem delAt_pull_fderiv_ι {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) (m : Fin n ⊕ Fin n → ℂ) :
    delAt (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) v = 0 := by
  have hJ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hE (b c : Fin n) : DifferentiableAt ℂ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    by
      have := (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v
        (hJ.clm_apply (differentiableAt_const (coordVec b)))
      simpa [Function.comp_def] using this
  have hEr (b c : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    (hE b c).restrictScalars ℝ
  have hEc (b c : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v := by
    have := Complex.conjCLE.differentiableAt.comp v (hEr b c)
    simpa [Function.comp_def] using this
  have hdel (a b c : Fin n) : del (fun w => fderiv ℂ φ w (coordVec b) c) v (coordVec a) =
      fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c := by
    have := del_clm_comp ((EuclideanSpace.proj c).comp (ContinuousLinearMap.apply ℂ (V n) (coordVec b)))
      (hJ.restrictScalars ℝ) (coordVec a)
    rw [del_eq_fderiv hJ] at this
    exact this
  have hdelc (a b c : Fin n) : del (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v (coordVec a) = 0 := by
    rw [del_conj, dbar_eq_zero (hE b c)]; simp
  have hsymm : IsSymmSndFDerivAt ℂ φ v := hφ.isSymmSndFDerivAt (by simp)
  have hF : (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) = fun w => ExteriorAlgebra.ι ℂ
      (Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
        (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c))) := by
    funext w
    rw [pull, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with b | b <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hu : ∀ i, DifferentiableAt ℝ (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v := by
    rintro (b | b)
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEr b c).mul_const (m (.inl c))
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEc b c).mul_const (m (.inr c))
  set s : Fin n → Fin n → ℂ := fun a b => ∑ c, fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c * m (.inl c)
    with hs
  have hw (a : Fin n) : (fun i => del (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v (coordVec a)) =
      ∑ b, s a b • Pi.single (Sum.inl b) 1 := by
    funext i
    rcases i with b | b
    · simp only [Sum.elim_inl]
      rw [del_sum (fun c _ => (hEr b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEr _ _), hdel, Finset.sum_apply, Pi.single_apply, hs]
    · simp only [Sum.elim_inr]
      rw [del_sum (fun c _ => (hEc b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEc _ _), hdelc, Finset.sum_apply, Pi.single_apply]
  rw [hF, delAt_ι hu]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hw, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact sum_symm_dz_mul s fun a b => by simp only [hs, hsymm (coordVec a) (coordVec b)]

theorem delAt_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n},
    ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n,
      GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  intro n φ v hφ γ
  have hD := fun γ S => GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv hφ γ S
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes]; exact delAt_const _ _
  | ι m => exact delAt_pull_fderiv_ι hφ m
  | mul a b ha hb =>
    obtain ⟨y, hy⟩ := FormMul.delAt_mul (hD a) (hD b)
    simp only [map_mul]
    rw [hy, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb =>
    simp only [map_add (f := _)]
    rw [delAt_add (hD a) (hD b), ha, hb, add_zero]

end GlobalTheory.CxForm.DelVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegEqDel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.ImageDegree

theorem imageDeg_eq_del : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → (CompHt.imageDeg ev T.D : ℤ) = T.del := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hG hB hP
  obtain ⟨-, hdeg, hdim⟩ := _root_.GlobalTheory.ImageDegree.degree_image_eq_topSelf hQ F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F T.N T.D T.imageIdeal T.toLinSys.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hG.alg.variety) hdim
  rw [hP.imageDeg_eq hf]
  exact hdeg

end GlobalTheory.HSCore.ImageDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyDegreeKilledByPrimeToPHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), (∀ c : 𝓞 D.F, c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n))) → ∀ (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (K : Over S) (i : K ⟶ o.A), Mono i → (∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
  first | (exact @GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy) | (exact GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy) | (intros; apply GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy <;> assumption)
end

