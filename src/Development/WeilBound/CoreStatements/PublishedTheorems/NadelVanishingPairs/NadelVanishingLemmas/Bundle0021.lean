module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0020
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0016
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0015
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0009
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescendsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicitiesStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_cartier_with_multiplicities : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ, (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) → ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  first | exact @_root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | exact _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | (intros; apply _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundary
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}}

theorem notMem_basicOpen_of_mem_vanishingIdeal (B : Closeds Y) (U : Y.affineOpens) {a : Γ(Y, U.1)}
    (ha : a ∈ (Scheme.IdealSheafData.vanishingIdeal B).ideal U) {y : Y} (hyU : y ∈ U.1)
    (hyB : y ∈ B) : y ∉ Y.basicOpen a := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := Scheme.IdealSheafData.vanishingIdeal B) hyU).1 (by
      rw [← SetLike.mem_coe]; simpa using hyB)
  exact (Scheme.mem_zeroLocus_iff _ _ _).1 h1 a ha

theorem exists_notMem_basicOpen_of_prod {U : Y.Opens} {ι : Type} (J : Finset ι) (f : ι → Γ(Y, U))
    {y : Y} (hy : y ∈ U) (h : y ∉ Y.basicOpen (∏ i ∈ J, f i)) : ∃ i ∈ J, y ∉ Y.basicOpen (f i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one] at h
    exact (h hy).elim
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul] at h
    by_cases h' : y ∈ Y.basicOpen (f a)
    · obtain ⟨i, hi, hi'⟩ := ih fun h'' => h ⟨h', h''⟩
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩
    · exact ⟨a, Finset.mem_insert_self a J, h'⟩

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}}

theorem ne_top_of_snc [IsIntegral Y] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : B ≠ ⊤ := by
  intro hBt
  obtain ⟨-, U, hU, m, f, J, hrsp, hid⟩ := hB (genericPoint Y)
  have hm : m = 0 := by
    have h := hrsp.2
    have h0 : ringKrullDim Y.functionField = 0 := ringKrullDim_eq_zero_of_field Y.functionField
    rw [show ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = ringKrullDim Y.functionField from rfl,
      h0] at h
    exact_mod_cast h
  subst hm
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  rw [Finset.prod_empty] at hid
  have h1 := notMem_basicOpen_of_mem_vanishingIdeal B U (a := 1)
    (hid ▸ Ideal.mem_span_singleton_self _) hU (by rw [hBt]; trivial)
  exact h1 (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hU)

variable [IsIntegral Y]

theorem exists_chart_germ_eq {D : CartierDiv Y} {σ : (toLB D).Sec}
    (hσ : (presents_toLB D).rat σ = 1) {x : Y} {g : Y.functionFieldˣ} (h : D.IsEqn x g) :
    ∃ (c : (toLB D).ι) (hc : x ∈ (toLB D).U c), algebraMap (Y.presheaf.stalk x) Y.functionField
      ((Y.presheaf.germ _ x hc).hom (σ.f c)) = g := by
  obtain ⟨V, hxV, hV⟩ := h.exists_nhds
  let c : (toLB D).ι := ⟨(V, g), gen_mem hxV, hV⟩
  refine ⟨c, hxV, ?_⟩
  have e := (presents_toLB D).rat_mul σ c (gen_mem hxV)
  rw [hσ, one_mul] at e
  exact (algebraMap_germ (X := Y) (U := V) hxV (σ.f c)).trans e.symm

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem exists_local_data [GlobalTheory.IsNormalScheme Y] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) {s : ℕ} (w : Fin s → Y)
    (hw : Function.Injective w) (hw1 : ∀ i, Order.coheight (w i) = 1) (hwB : ∀ i, w i ∈ B)
    (D : Fin s → CartierDiv Y) (hmult : ∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0)
    (σ : ∀ i, (toLB (D i)).Sec) (hσ : ∀ i, (presents_toLB (D i)).rat (σ i) = 1) (x : Y) :
    ∃ (n : ℕ) (t : Fin n → Y.presheaf.stalk x) (c : ∀ i, (toLB (D i)).ι)
      (hc : ∀ i, x ∈ (toLB (D i)).U (c i)) (e : Fin s → Option (Fin n)),
      FinalTheorems.Rsp (Y.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧
        ∀ i, Associated ((Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t) := by
  classical
  obtain ⟨hreg, U, hxU, m, f, J, hrsp, hid⟩ := hB x
  obtain ⟨w₀, u, hw₀, hu⟩ := GlobalTheory.T.regular_sequence_prime_divisors Y x U.1 hxU m f hreg hrsp
  let t : Fin m → Y.presheaf.stalk x := fun j => Y.presheaf.germ U.1 x hxU (f j)
  let e : Fin s → Option (Fin m) := fun i =>
    if h : ∃ j, j ∈ J ∧ w i = w₀ j then some h.choose else none
  have he : ∀ i a, e i = some a → w i = w₀ a := by
    intro i a h
    simp only [e] at h
    split_ifs at h with h'
    cases h
    exact h'.choose_spec.2
  have key : ∀ i, ∃ g : Y.functionFieldˣ, (D i).IsEqn x g ∧
      algebraMap (Y.presheaf.stalk x) Y.functionField ((e i).elim 1 t) = g := by
    intro i
    by_cases h : ∃ j, j ∈ J ∧ w i = w₀ j
    · obtain ⟨j, hei, hwj⟩ : ∃ j, e i = some j ∧ w i = w₀ j := ⟨h.choose, dif_pos h, h.choose_spec.2⟩
      obtain ⟨hu1, -, -, -, hord, hoth⟩ := hu j
      refine ⟨u j, ?_, ?_⟩
      · refine (GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x (u j) fun z hz => ?_
        by_cases hzw : z = w i
        · rw [hzw, (hmult i).1, hwj, hord]
        · rw [(hmult i).2 z hzw]
          by_cases hz1 : Order.coheight z = 1
          · have hzb := hoth z hz hz1 (hwj ▸ hzw)
            have hzU : z ∈ U.1 := hz.mem_open U.1.isOpen hxU
            rw [hu1]
            exact ((unitAt_fnOf_iff hzU _ _).2 hzb).ord_eq_zero
          · exact Scheme.ord_eq_zero_of_coheight_neq_one hz1 _
      · rw [hei, hu1]
        exact algebraMap_germ hxU (f j)
    · have hei : e i = none := dif_neg h
      refine ⟨1, ?_, by rw [hei]; simp⟩
      refine (GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x 1 fun z hz => ?_
      rw [(hmult i).2 z ?_, Units.val_one, (unitAt_one z).ord_eq_zero]
      rintro rfl
      have hzU : w i ∈ U.1 := hz.mem_open U.1.isOpen hxU
      have h0 : w i ∉ Y.basicOpen (∏ j ∈ J, f j) := notMem_basicOpen_of_mem_vanishingIdeal B U
        (hid ▸ Ideal.mem_span_singleton_self _) hzU (hwB i)
      obtain ⟨j, hj, hjb⟩ := exists_notMem_basicOpen_of_prod J f hzU h0
      refine h ⟨j, hj, ?_⟩
      by_contra hne
      exact hjb ((hu j).2.2.2.2.2 (w i) hz (hw1 i) hne)
  choose g hg hga using key
  choose c hc hcg using fun i => exists_chart_germ_eq (hσ i) (hg i)
  refine ⟨m, t, c, hc, e, hrsp, fun i i' a hi hi' => hw ((he i a hi).trans (he i' a hi').symm),
    fun i => ?_⟩
  have : (Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) = (e i).elim 1 t :=
    IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField ((hcg i).trans (hga i).symm)
  rw [this]

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

theorem relSnc_components : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q →
    ∀ B : Closeds Y, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) →
      ∃ (r : ℕ) (w : Fin r → Y) (D : Fin r → CartierDiv Y) (σ : ∀ i, (toLB (D i)).Sec),
        Function.Injective w ∧ (∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0) ∧
        (∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i) ∧
        RelSnc q n (fun i => toLB (D i)) σ := by
  intro k _ _ Y _ _ q n _ hP B hB
  classical
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth q
  have : IsNoetherian Y := by
    obtain ⟨N, i, hi, e⟩ := hP
    have := isProper_str k N
    have : QuasiCompact q := e ▸ inferInstance
    have := QuasiCompact.compactSpace_of_compactSpace q
    exact {}
  have hfin := GlobalTheory.T.finite_codim_one_points_closed Y B (ne_top_of_snc B hB)
  let S := hfin.toFinset
  let w : Fin S.card → Y := fun i => (S.equivFin.symm i).1
  have hw : Function.Injective w := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hwS : ∀ i, Order.coheight (w i) = 1 ∧ w i ∈ B := fun i =>
    hfin.mem_toFinset.1 (S.equivFin.symm i).2
  have hSw : ∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i := fun v h1 h2 =>
    ⟨S.equivFin ⟨v, hfin.mem_toFinset.2 ⟨h1, h2⟩⟩, by simp [w]⟩
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    AbelianProjective.ufd_stalk q
  choose D hD using fun i => GlobalTheory.T.exists_prime_cartier_divisor Y hufd (w i) (hwS i).1
  have heff : ∀ i, (D i).Eff := fun i => ((GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).1).2 fun z => by
    by_cases hz : z = w i
    · rw [hz, (hD i).1]; norm_num
    · rw [(hD i).2 z hz]
  choose σ hσ using fun i => (presents_toLB (D i)).exists_rat_eq (CartierDiv.mem_sections.2 (heff i))
  refine ⟨S.card, w, D, σ, hw, hD, hSw, ?_⟩
  refine GlobalTheory.T.regular_sequence_stalk_snc k Y q n S.card (fun i => toLB (D i)) σ (fun i => isLB_toLB _) fun x _ => ?_
  exact exists_local_data B hB w hw (fun i => (hwS i).1) (fun i => (hwS i).2) D hD σ hσ x

end GlobalTheory.SncComp
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficientsStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.klt_of_snc_coefficients : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  first | exact @_root_.GlobalTheory.Discrepancy.coeff_criterion_snc | exact _root_.GlobalTheory.Discrepancy.coeff_criterion_snc | (intros; apply _root_.GlobalTheory.Discrepancy.coeff_criterion_snc <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KodairaVanishingModPSquared
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open GlobalTheory.Cartier GlobalTheory.LogDR

theorem GlobalTheory.CharPVanish.charp_of_lift : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro p _ Y X _ g f π d _ hpb hproj hdp s L σ h K M A hM hA r b hr hb heq q hq
  obtain ⟨m, E, 𝒜, hdec, hE⟩ := GlobalTheory.LogAtlas.exists_atlas_decomp p Y X g f π d hpb hproj hdp s L σ h
  obtain ⟨M', hM'⟩ := GlobalTheory.Cartier.toPic_surjective (cls M hM)
  have hcan : GlobalTheory.Cartier.toPic (GlobalTheory.Cartier.canonical f d) = cls K.bundle K.isLB :=
    (GlobalTheory.Cartier.presents_canonical f d).toPic_eq.trans
      ((CechPic.cls_eq_iff _ _).2 (CanonLB.lbIso _ _))
  have hH : GlobalTheory.Cartier.toPic (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i)
      = cls A hA.isLB := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_nsmul, map_sum, hM', hcan, hE]
    rw [heq]
    abel
  have hiso : LBIso (GlobalTheory.Cartier.toLB (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i)) A := by
    rw [← CechPic.cls_eq_iff (GlobalTheory.Cartier.isLB_toLB _) hA.isLB, ← GlobalTheory.Cartier.toPic_apply]
    exact hH
  have hampleH := IsAmpleLB.of_lbIso hA (GlobalTheory.Cartier.isLB_toLB _) hiso
  have key := GlobalTheory.CharPVanish.subsingleton_coh_of_decomp p X f d hproj hdp E 𝒜 hdec M'
    (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i) r b hampleH hr hb (by abel) q hq
  refine GlobalTheory.Div.coh_subsingleton_of_cls_eq X (GlobalTheory.Cartier.toLB M') M (GlobalTheory.Cartier.isLB_toLB _) hM ?_ q key
  rw [← GlobalTheory.Cartier.toPic_apply, hM']
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpread
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.LogPair.relSnc_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  intro R k _ _ φ X X' f f' π _ _ d s L σ hpb hL hrel
  let W : X.Opens := ⨆ C : SncChart f d L σ, C.U
  have hW : π ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨C', hC'⟩ := hrel.chart y
    obtain ⟨C, hC⟩ := GlobalTheory.T.snc_chart_descends R k φ X X' f f' π d s L σ C' y hpb hC'
    show π y ∈ W
    exact (Opens.mem_iSup).2 ⟨C, hC⟩
  obtain ⟨a, ha, h⟩ := _root_.GlobalTheory.tube_of_universallyClosed R k φ X X' f f' π W hpb hW
  refine ⟨a, ha, fun T _ χ hχ Z g ρ hρ => ?_⟩
  have hZ := h T χ hχ Z g ρ hρ
  refine ⟨fun i => LB.isLB_pull (hL i) ρ, fun z => ?_⟩
  have hz : ρ z ∈ W := by
    have : z ∈ ρ ⁻¹ᵁ W := by rw [hZ]; trivial
    exact this
  obtain ⟨C, hC⟩ := (Opens.mem_iSup).1 hz
  obtain ⟨C', hC'⟩ := GlobalTheory.T.snc_chart_base_change R T χ X Z f g ρ d s L σ C hρ
  refine ⟨C', ?_⟩
  rw [hC']
  exact hC
end

