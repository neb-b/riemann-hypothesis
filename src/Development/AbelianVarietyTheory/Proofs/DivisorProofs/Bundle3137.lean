module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDataFrom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderIsoOfSameHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByPrimeAtEtalePlaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_killed_by_prime_at_etale_place : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ w0, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} = Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.GeoCard.card_ker_place) | (exact GlobalTheory.UPel.HT.EtLev.GeoCard.card_ker_place) | (intros; apply GlobalTheory.UPel.HT.EtLev.GeoCard.card_ker_place  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartAtSiegelBlowupPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartHit

theorem setup : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (φ : InvFun ℤ) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → S.IsSeparated ∧ LocallyOfFiniteType (π ≫ z) ∧ IsLocallyNoetherian S ∧ Dense (Set.range j) ∧ j ≫ π ≫ z = F.s := by
  intro g n F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨J, -, -, -, -, hproj, hdense, hji, -, -, -⟩ := hBlow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hMin
  have hP := GlobalTheory.ArithCurve.isProper_of_projOver hproj
  have hlft : LocallyOfFiniteType (π ≫ z) := GlobalTheory.isProjOver_locallyOfFiniteType _ _ _ hproj
  haveI : IsNoetherianRing (cycAway n) := is_noetherian_subring_closure _ (Set.toFinite _)
  refine ⟨⟨by rw [← terminal.comp_from (π ≫ z)]; infer_instance⟩, hlft, LocallyOfFiniteType.isLocallyNoetherian (π ≫ z), hdense, ?_⟩
  rw [← Category.assoc, hji, hiz]

theorem away_hom_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (t : R), t ≠ 0 → ∀ (l : Localization.Away t →+* FractionRing R), l.comp (algebraMap R (Localization.Away t)) = algebraMap R (FractionRing R) → ∀ (S : Scheme.{0}) [S.IsSeparated] (a b : Sp (Localization.Away t) ⟶ S), spMap l ≫ a = spMap l ≫ b → a = b := by
  intro R _ _ t ht l hl S _ a b h
  haveI : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hinj : Function.Injective l := by
    refine (injective_iff_map_eq_zero l).2 fun x hx => ?_
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) x
    have h1 : IsLocalization.mk' (Localization.Away t) r s * algebraMap R _ (s : R) = algebraMap R _ r :=
      IsLocalization.mk'_spec _ r s
    have h2 : algebraMap R (FractionRing R) r = 0 := by
      rw [← hl, RingHom.comp_apply, ← h1, map_mul, hx, zero_mul]
    have h3 : r = 0 := IsFractionRing.injective R (FractionRing R) (by rw [h2, map_zero])
    show IsLocalization.mk' (Localization.Away t) r s = 0
    rw [h3, IsLocalization.mk'_zero]
  have : IsDominant (spMap l) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap l) h

end GlobalTheory.ChartHit

namespace GlobalTheory.ChartHit

theorem lowBase_regular {n : ℕ} (L : LowBase (zetaAway n) n) : IsRegularLocalRing L.W := by
  haveI : IsNoetherianRing L.W := L.noeth
  let y := L.u (closedPoint L.W)
  let φ₀ := (Scheme.stalkClosedPointTo L.u).hom
  haveI : IsRegularLocalRing ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk L.F y
  have het := L.u_et
  letI : Algebra ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := φ₀.toAlgebra
  haveI : Module.Flat ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := het.1
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm

theorem chart : ∀ {g n : ℕ} (φ : InvFun ℤ), 3 ≤ n → ∀ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)), L.h + L.T.r = g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) → (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) → IsCN V' → IsLocalHom κ → (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) → DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e → ∃ (C : Taut (zetaAway n) g n φ) (θ : C.R →+* V') (e' : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), IsLocalHom θ ∧ (∀ k, θ (C.s k) ≠ 0) ∧ θ.comp C.b = κ.comp L.T.b ∧ DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e' := by
  intro g n φ hn L m N ε V' _ _ _ κ sv D' e hgen hcone hdef hV hκ hs1 hs2 hD
  haveI : IsRegularLocalRing L.W := lowBase_regular L
  have hψV : IsLocalHom ((MvPolynomial.eval₂Hom κ sv).comp MvPolynomial.C) := by
    rw [MvPolynomial.eval₂Hom_comp_C]; exact hκ
  obtain ⟨R, _, _, _, ψ, θ, hcompl, hθ, hθψ, hψl⟩ :=
    GlobalTheory.TChart.exists_complAt_factor_of_isAdicComplete L.W (Fin m ⊕ Fin N) V' hV.2.2.1 (MvPolynomial.eval₂Hom κ sv) hψV
  have hθX : ∀ k, θ (ψ (MvPolynomial.X k)) = sv k := fun k => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = κ := by
    rw [← RingHom.comp_assoc, hθψ, MvPolynomial.eval₂Hom_comp_C]
  have hne : ∀ k, ψ (MvPolynomial.X k) ≠ 0 := fun k h => by
    have h' := hθX k
    rw [h, map_zero] at h'
    rcases k with k | k
    · exact (hs1 k).2 h'.symm
    · exact (hs2 k).ne_zero h'.symm
  obtain ⟨Q, eQ, hQ⟩ := GlobalTheory.TChart.FromEx.exists_dataFrom L.T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n hne (fun k a b => (ε k).2.1 a b)
  have hbd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R := fun k =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 (hs1 k).1 (hθX (.inl k) ▸ hu.map θ)
  have htor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k))) := fun k =>
    isUnit_of_map_unit θ _ (by rw [hθX]; exact hs2 k)
  let C : Taut (zetaAway n) g n φ :=
    { toLowBase := L
      genus := hgen
      m := m
      N := N
      ε := ε
      cone := hcone
      defin := hdef
      R := R
      ψ := ψ
      compl := hcompl
      ψ_loc := hψl
      bd := hbd
      tor := htor
      Q := Q
      e := eQ
      data := hQ }
  refine ⟨C, θ, e, hθ, fun k => ?_, ?_, ?_⟩
  · show θ (ψ (MvPolynomial.X k)) ≠ 0
    rw [hθX]
    rcases k with k | k
    · exact (hs1 k).2
    · exact (hs2 k).ne_zero
  · show θ.comp ((ψ.comp MvPolynomial.C).comp L.T.b) = κ.comp L.T.b
    rw [← RingHom.comp_assoc, hθC]
  · show DegFrom L.T (θ.comp (ψ.comp MvPolynomial.C)) (fun k => θ (ψ (MvPolynomial.X k)))
      (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e
    rw [hθC, show (fun k => θ (ψ (MvPolynomial.X k))) = sv from funext hθX]
    exact hD

end GlobalTheory.ChartHit

theorem GlobalTheory.TChart.exists_chart_at : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, ∃ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ ∧ y ≫ j = jK C.R ≫ ξ ∧ ξ (closedPoint C.R) = x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hMin hBlow x
  obtain ⟨hsep, hlft, hln, hdense, hjs⟩ := GlobalTheory.ChartHit.setup F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨T, ξT, b, hx, hTj, hTb⟩ := _root_.GlobalTheory.TChart.exists_trait_at F S (π ≫ z) j hn hdense hjs x
  have hyb : T.y ≫ F.s = jK T.V ≫ spMap b := by
    rw [← hjs, ← Category.assoc, ← hTj, Category.assoc, hTb]
  obtain ⟨L, m, N, ε, V', _, _, _, f, κ, sv, D', e, G', _, _, πG, A', U', hgen, hcone, hdef, hV', hdvr, hfi, hff, hfl,
    hκl, hκb, hs1, hs2, hU, hD⟩ := _root_.GlobalTheory.TChart.exists_degFrom_of_trait g hg φ hφ n hn hodd F T b hyb
  obtain ⟨C, θ, e', hθl, hθs, hθb, hD'⟩ := GlobalTheory.ChartHit.chart φ hn L m N ε V' κ sv D' e hgen hcone hdef hV' hκl hs1 hs2 hD
  obtain ⟨G₁, _, _, P, hMP, hCan, hab, htors⟩ := _root_.GlobalTheory.TChart.Taut.exists_family g n φ hn hodd C
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap f := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi
  let fK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') f hle
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq hle a
  have hprod : θ (∏ k, C.t k) ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun k _ => hθs (.inl k)
  have htne : (∏ k, C.t k) ≠ 0 := fun h => hprod (by rw [h, map_zero])
  have hunit : IsUnit ((algebraMap V' (FractionRing V')).comp θ (∏ k, C.t k)) := by
    refine isUnit_iff_ne_zero.2 ?_
    simpa using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hprod) :
      algebraMap V' (FractionRing V') (θ (∏ k, C.t k)) ≠ 0)
  let κ' : Localization.Away (∏ k, C.t k) →+* FractionRing V' := IsLocalization.Away.lift (∏ k, C.t k) hunit
  have hκ' : κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = (algebraMap V' (FractionRing V')).comp θ :=
    IsLocalization.Away.lift_comp (∏ k, C.t k) hunit
  have hSF := _root_.GlobalTheory.TChart.sameFib_trait_chart F C G₁ P hMP hCan T V' θ f fK hV' hθl hθs hfK D' e' hD' G' πG A' U' hU
  have hx₀ : (spMap fK ≫ T.y) ≫ F.s = spMap ((κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) := by
    rw [Category.assoc, hyb, hκ', RingHom.comp_assoc, hθb, hκb]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [hfK]
  rw [← hκ'] at hSF
  obtain ⟨c, hc, hiso, hpt⟩ := _root_.GlobalTheory.TChart.AbLevel.exists_level hn hodd F C G₁ P hMP hab htors (FractionRing V') κ' (spMap fK ≫ T.y) hx₀ hSF
  obtain ⟨y, α₁, yU, l, hFam, hSPB, hl, hyl⟩ := _root_.GlobalTheory.TChart.Taut.exists_isFam_of_siegPre g n φ hn hodd F C G₁ P hMP hab c hc hiso
  obtain ⟨ξ, hξ⟩ := _root_.GlobalTheory.TChart.Taut.exists_ext_normBl g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hMin hBlow C G₁ y α₁ hFam
  have hsA : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl]
  have hyUs : yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl (Sp (cycAway n)) _ _ ?_
    have h := hFam.2.2.2.2
    rw [hyl, Category.assoc] at h
    rw [h, ← hsA]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.assoc]
  have hκy := hpt yU hSPB hyUs
  have hξU : spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) ≫ ξ = yU ≫ j := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl S _ _ ?_
    rw [← Category.assoc, hsA, ← hξ, hyl, Category.assoc]
  have hgen' : jK V' ≫ (spMap θ ≫ ξ) = jK V' ≫ (spMap f ≫ ξT) := by
    have e1 : jK V' ≫ spMap θ = spMap κ' ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ']
    have e2 : jK V' ≫ spMap f = spMap fK ≫ jK T.V := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; ext a; simp [hfK]
    rw [← Category.assoc, e1, Category.assoc, hξU, ← Category.assoc, hκy, ← Category.assoc, e2, Category.assoc,
      Category.assoc, hTj]
  have hdom : IsDominant (jK V') := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).le.trans bot_le)⟩
  have hext : spMap θ ≫ ξ = spMap f ≫ ξT :=
    ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (jK V') hgen'
  refine ⟨C, G₁, inferInstance, y, α₁, ξ, hFam, hξ, ?_⟩
  have h1 : (spMap θ).base (closedPoint V') = closedPoint C.R := IsLocalRing.comap_closedPoint θ
  have h2 : (spMap f).base (closedPoint V') = closedPoint T.V := IsLocalRing.comap_closedPoint f
  rw [← hx, ← h1, ← h2]
  show (spMap θ ≫ ξ).base (closedPoint V') = (spMap f ≫ ξT).base (closedPoint V')
  rw [hext]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersality
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem spMap_isDominant_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : IsDominant (spMap f) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hf]
    exact bot_le)⟩

theorem spMap_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] {S : Scheme.{0}} [S.IsSeparated]
    (f : A →+* B) (hf : Function.Injective f) {a b : Sp A ⟶ S} (h : spMap f ≫ a = spMap f ≫ b) : a = b := by
  haveI := spMap_isDominant_of_injective f hf
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap f) h

theorem isSeparated_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    X.IsSeparated := by
  obtain ⟨N, ci, hci, hcis⟩ := h
  haveI := hci
  have : IsSeparated f := by
    rw [← hcis, PSpace.str]
    infer_instance
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem exists_taut_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep V _ _ _ hB hac C ξV hnt hCV
  obtain ⟨k, hk, m, e, C₁, θ, ⟨hcan⟩, hpar, hθ, hthr⟩ := _root_.GlobalTheory.UCanon.exists_canon_through Xo c φ V hB hac C hnt
  letI := hk
  have hT : IsTautB C₁ := _root_.GlobalTheory.UCanon.isTautB_of_canon Xo c φ hpq hpf hns C₁ hcan hpar
  obtain ⟨ξ, hξ⟩ := GlobalTheory.UChart.taut_exists_map Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C₁ hT.1
  haveI : S.IsSeparated := isSeparated_of_projOver hU.2.2.2.2.1.2.1
  refine ⟨k, hk, m, e, C₁, ξ, θ, hT, hξ, hθ, ?_⟩
  obtain ⟨yo, κ, hgen, hκ, hκy⟩ := hthr

  obtain ⟨hm, hs⟩ := hpar
  have hne : (∏ i, C₁.s i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [hs i]
    exact bdParam_ne_zero k m e _
  set L := Localization.Away (∏ i, C₁.s i)
  have hle : Submonoid.powers (∏ i, C₁.s i) ≤ nonZeroDivisors (ChartRing k m e) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hne
  haveI : IsDomain L := IsLocalization.isDomain_localization hle
  have hu : IsUnit (algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) (∏ i, C₁.s i)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hne)
  let gR : L →+* FractionRing (ChartRing k m e) := IsLocalization.Away.lift (∏ i, C₁.s i) hu
  have hgR : gR.comp (algebraMap (ChartRing k m e) L) = algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) :=
    IsLocalization.Away.lift_comp (∏ i, C₁.s i) hu
  have hinj : Function.Injective gR := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective L hle).eq_iff, (IsFractionRing.injective (ChartRing k m e) (FractionRing (ChartRing k m e))).eq_iff]
  have hg : spMap gR ≫ spMap (algebraMap (ChartRing k m e) L) = jK (ChartRing k m e) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgR]

  have hopen : spMap (algebraMap (ChartRing k m e) L) ≫ ξ = yo ≫ j := by
    refine spMap_ext_of_injective gR hinj ?_
    rw [← Category.assoc, hg, ← hξ, ← Category.assoc, hgen _ hg]
  refine spMap_ext_of_injective (algebraMap V (FractionRing V)) (IsFractionRing.injective _ _) ?_
  change jK V ≫ _ = jK V ≫ _
  rw [← Category.assoc, ← hκ, Category.assoc, hopen, ← Category.assoc, hκy, hCV]

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTUniv.main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨f, hdir, huniq⟩ := GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count p D R b N hN hNp k t o₀
  obtain ⟨o, m, hm⟩ := _root_.GlobalTheory.HTGlue.exists_glue p D R b N hN hNp k t o₀ _ f hdir
  refine ⟨o, ⟨m⟩, fun o' ho' => ?_⟩
  obtain ⟨m'⟩ := ho'
  have key : ∀ (s' : Sp (DualNumber k) ⟶ Sp R) (o'' : GlobalTheory.UPel.HT.Obj b N s')
      (m'' : GlobalTheory.UPel.HT.ObjMap o₀ o'' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
      (c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k)
      (n : GlobalTheory.UPel.HT.ObjMap o'' o (spMap (TrivSqZeroExt.map c).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m''.cart x (∑ j, c (Pi.single j 1) • f j x) := by
    intro s' o'' m'' c n x hx
    have h := GlobalTheory.T.harrisTaylor_hodgeFiltration_naturality p D R b N hN hNp k t o₀ _ _ o m c s' o'' m'' n x _ (hm x hx)
    rw [GlobalTheory.HTUniv.comp_pi] at h
    exact h
  obtain ⟨c₀, hc₀, hc₀u⟩ := huniq o' m'
  let c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k := ∑ j, c₀ j • LinearMap.proj j
  have hcj : ∀ j, c (Pi.single j 1) = c₀ j := fun j => GlobalTheory.HTUniv.sum_proj_single c₀ j
  obtain ⟨oc, ⟨nc⟩⟩ := _root_.GlobalTheory.UPel.HT.Pull.exists_objMap p D R b N _ _ _ (spMap (TrivSqZeroExt.map c).toRingHom) o
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (TrivSqZeroExt.map c).toRingHom =
      spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom := by
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext x
    simp
  obtain ⟨mc⟩ := (_root_.GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ oc o
    (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (spMap (TrivSqZeroExt.map c).toRingHom)).2
    (by rw [hcomp]; exact ⟨m⟩) ⟨nc⟩
  have hfc := key _ oc mc c nc
  simp only [hcj] at hfc
  obtain ⟨iso⟩ := _root_.GlobalTheory.HTFirstOrderIso.objMap_of_filLift p D R b N hN hNp k t o₀ _ _ o' oc m' mc (fun x => ∑ j, c₀ j • f j x) hc₀ hfc
  refine ⟨c, ?_, ?_⟩
  · have h := (_root_.GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' oc o (𝟙 _)
      (spMap (TrivSqZeroExt.map c).toRingHom)).1 ⟨iso⟩ ⟨nc⟩
    rwa [Category.id_comp] at h
  · rintro c' ⟨n'⟩
    have h1 := key _ o' m' c' n'
    have h2 := hc₀u (fun j => c' (Pi.single j 1)) h1
    refine LinearMap.ext fun v => ?_
    rw [GlobalTheory.HTUniv.coord c' v, GlobalTheory.HTUniv.coord c v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcj]
    exact congrArg _ (congrFun h2 j)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d hh hM hMo hd hcop
  obtain ⟨r, eO, W, d₀, hspan, hW, hd₀, hid⟩ := GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix d hd
  obtain ⟨jl, n, o, κ, hex⟩ := GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy h M d hh hM hMo hd hcop
  exact ⟨GlobalTheory.ZarhinFam.ord d, inferInstance, GlobalTheory.ZarhinFam.bar d, r, eO, W, d₀, GlobalTheory.ZarhinFam.idem d, jl, n, o, κ,
    GlobalTheory.ZarhinFam.bar_add d, hspan, hW, hd₀, hid, GlobalTheory.ZarhinFam.idem_mul_self d, hex,
    fun S t c z₁ z₂ act₁ act₂ => GlobalTheory.T.zarhinTrick_principal_objects_iso_unique h M d hh hM hMo hd hcop jl n o κ S t c z₁ z₂ act₁ act₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.obj_lift_sqZero) | (exact GlobalTheory.UPel.HT.obj_lift_sqZero) | (intros; apply GlobalTheory.UPel.HT.obj_lift_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdeal
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

namespace GlobalTheory

theorem exists_point_vanishing_of_isMaximal {X : Scheme} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (hm : m.IsMaximal) : ∃ x, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ X.basicOpen f := by
  let p : PrimeSpectrum Γ(X, U.1) := ⟨m, hm.isPrime⟩
  refine ⟨U.2.fromSpec p, ?_, ?_⟩
  · have h : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
    rw [U.2.range_fromSpec] at h
    exact h
  · intro f hf hx
    have h : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f := hx
    rw [U.2.fromSpec_preimage_basicOpen] at h
    exact h hf

theorem logKS_inj_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm hKS hΘ
  have hp := exists_point_vanishing_of_isMaximal U m hm
  obtain ⟨x, hxU, hxm⟩ := hp
  by_cases hx : x ∈ LogKS.interior Y
  · exact _root_.GlobalTheory.InteriorKS.mem_smul_top_of_isKS E H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm
      ⟨x, hx, hxU, hxm⟩ hKS hΘ
  · have hb : ∃ x, x ∉ LogKS.interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f := ⟨x, hx, hxU, hxm⟩
    have key := _root_.GlobalTheory.ChartDer.logKS_inj_mod_boundary E H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm
    first
      | exact key hb hKS hΘ
      | exact key hKS hΘ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointSeparationPairOfPrincipalisation
section
theorem GlobalTheory.pointSeparationPair_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.PointSeparationPair := fun hP =>
  _root_.GlobalTheory.pointSeparationPair_of_vanishing hP (GlobalTheory.T.nadel_vanishing_pairs_of_principalisation hP) _root_.GlobalTheory.nefNumerics_outright
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_idempotent_image_open_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  first | (exact @GlobalTheory.UPel.HT.idemImage_locus) | (exact GlobalTheory.UPel.HT.idemImage_locus) | (intros; apply GlobalTheory.UPel.HT.idemImage_locus  <;> assumption)
end

