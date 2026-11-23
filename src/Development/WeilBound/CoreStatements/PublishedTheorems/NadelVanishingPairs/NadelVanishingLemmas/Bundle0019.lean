module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0016
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0002
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0013
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompareStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_birational_compare : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)] (U : Y₀.Opens), (U : Set Y₀).Nonempty → IsIso (t ∣_ U) → ∀ (η : RatForms q n), η ≠ 0 → ∀ (K₀ : CartierDiv Y₀) (K₁ : CartierDiv Y₁), IsDivOfForm K₀ η → IsDivOfForm K₁ (EtaleKlt.ratPull q t n η) → ∀ y : Y₁, t y ∈ U → y ∉ (K₁ - pullCart t K₀).supp := by
  first | exact @_root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart | exact _root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart | (intros; apply _root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveMultipleDominatesStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.effective_multiple_dominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  first | exact @_root_.GlobalTheory.effDominates | exact _root_.GlobalTheory.effDominates | (intros; apply _root_.GlobalTheory.effDominates <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.etale_coordinates_log_chart : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U)) (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U → IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) → (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  first | exact @_root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord | exact _root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord | (intros; apply _root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisorStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_prime_cartier_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ z : X, Order.coheight z = 1 → ∃ D : CartierDiv X, D.mult z = 1 ∧ ∀ v, v ≠ z → D.mult v = 0 := by
  first | exact @_root_.GlobalTheory.primeDivisor_isCartier | exact _root_.GlobalTheory.primeDivisor_isCartier | (intros; apply _root_.GlobalTheory.primeDivisor_isCartier <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundary
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem regAt_of_regularAt_neg_roundDown : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  intro k _ _ X _ _ _ p n hproj _ Δ η m G Y _ _ s _ K B F hΔ hmult hres hF x f hf
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  by_cases hf0 : f = 0
  · subst hf0; exact regAt_zero x
  refine regAt_of_forall_coheight_eq_one fun z hzx hz1 => ?_
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hz1
  obtain ⟨E', hE'E⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over k X Y p s hres.bir E
  obtain ⟨w, rfl, hE'⟩ := GlobalTheory.T.divisor_point_proper_lift k X Y p s hres.bir inferInstance E' E hE'E _ hE
  obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
  have hg' := isEqn_pullCart s hg
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hmult.ne_zero ((_root_.GlobalTheory.EtaleKlt.ratPull_bijective_of_birational k X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  have hd := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m
    hmult.pos hres.div E' w (fnPull s g) hE' hg'
  have hd2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
    simp only [discrep]
    have hform := GlobalTheory.T.form_order_birational_pullback k X Y p s hres.bir E' E hE'E n η hmult.ne_zero
    change E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η at hform
    rw [hform, _root_.GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective k X Y p s hres.bir E' E hE'E g]
  have hd3 := (hmult.eqn _ g hg).discrep_eq_neg hmult.pos (specializes_refl _) hE
  have hm : (0 : ℚ) < m := by exact_mod_cast hmult.pos
  have hnn : 0 ≤ (pullCart s G - m • K).mult w := by
    have e : ((pullCart s G - m • K).mult w : ℚ) / m = Δ (s w) := by
      rw [← hd2, hd] at hd3
      rw [neg_div] at hd3
      exact neg_injective hd3
    have h0 : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) / m := e ▸ hΔ (s w)
    have := (div_nonneg_iff.1 h0)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_le.2 hm)
  have hFn : 0 ≤ F.mult w := by
    rw [hF]; exact Int.ediv_nonneg hnn (by exact_mod_cast hmult.pos.le)
  obtain ⟨h, hh⟩ := F.exists_isEqn w
  have hreg := (hh.neg.regularAt_iff).1 (hf w hzx)
  set u : X.functionFieldˣ := Units.mk0 f hf0 with hu
  have hv : ((fnPull s u * h⁻¹ : Y.functionFieldˣ) : Y.functionField) =
      functionFieldMap s f * ((h⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    simp [hu, fnPull]
  have h1 : 0 ≤ E'.ord (fnPull s u * h⁻¹) :=
    (E'.ord_nonneg_iff _).2 (hv ▸ (hE' _).2 hreg)
  rw [E'.ord_mul, E'.ord_inv, _root_.GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective k X Y p s hres.bir E' E hE'E u, hE'.ord_eq h,
    ← hh.mult_eq] at h1
  have h2 : 0 ≤ E.ord u := by omega
  exact (hE f).1 ((E.ord_nonneg_iff u).1 h2)

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceStalkSnc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.RegParams

theorem exists_closed_specialization : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (x : X), ∃ y : X, IsClosed ({y} : Set X) ∧ ∀ U : X.Opens, y ∈ U → x ∈ U := by
  intro k _ X f _ x
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x).closure isClosed_closure.isLocallyClosed
  exact ⟨y, hyc, fun U hU => (specializes_iff_mem_closure.2 hy).mem_open U.isOpen hU⟩

theorem linearIndependent_fibre_of_stalk : ∀ (k B A K : Type) [CommRing k] [CommRing B] [CommRing A] [Field K] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra A K] [Algebra B K] [IsScalarTower B A K] (ι : Type) (b : ι → B), LinearIndependent K (fun i => (1 : K) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap B A (b i))) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D k B (b i)) := by
  intro k B A K _ _ _ _ _ _ _ _ _ _ _ ι b h
  let g : Ω[B⁄k] →ₗ[B] K ⊗[A] Ω[A⁄k] :=
    ((TensorProduct.mk A K Ω[A⁄k] 1).restrictScalars B).comp (KaehlerDifferential.map k k B A)
  let φ : K ⊗[B] Ω[B⁄k] →ₗ[K] K ⊗[A] Ω[A⁄k] := g.liftBaseChange K
  refine LinearIndependent.of_comp φ ?_
  convert h using 1
  funext i
  simp [φ, g, KaehlerDifferential.map_D]

theorem linearIndependent_fibre_of_associated : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] (n s : ℕ) (t : Fin n → A) (g : Fin s → A) (e : Fin s → Option (Fin n)), (∀ a, t a ∈ IsLocalRing.maximalIdeal A) → (∀ i j a, e i = some a → e j = some a → i = j) → (∀ i, Associated (g i) ((e i).elim 1 t)) → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) → LinearIndependent (IsLocalRing.ResidueField A) (fun i : {i : Fin s // IsLocalRing.residue A (g i) = 0} => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (g i)) := by
  intro k A _ _ _ _ n s t g e htm hinj hass hli
  classical
  have hsome : ∀ i : {i : Fin s // IsLocalRing.residue A (g i) = 0}, (e i.1).isSome := by
    rintro ⟨i, hi⟩
    cases he : e i with
    | none =>
      exfalso
      have h1 := hass i
      rw [he] at h1
      have hu : IsUnit (g i) := h1.symm.isUnit isUnit_one
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hi
    | some a => rfl
  let a : {i : Fin s // IsLocalRing.residue A (g i) = 0} → Fin n := fun i => (e i.1).get (hsome i)
  have hea : ∀ i, e i.1 = some (a i) := fun i => (Option.some_get _).symm
  have ha : Function.Injective a := fun i j h => Subtype.ext (hinj i.1 j.1 (a i) (hea i) (h ▸ hea j))
  have hass' : ∀ i : {i : Fin s // IsLocalRing.residue A (g i) = 0}, Associated (g i.1) (t (a i)) := by
    intro i
    have := hass i.1
    rw [hea i] at this
    exact this
  choose u hu using hass'
  let w : {i : Fin s // IsLocalRing.residue A (g i) = 0} → (IsLocalRing.ResidueField A)ˣ :=
    fun i => Units.map (IsLocalRing.residue A).toMonoidHom (u i)⁻¹
  have key : ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (g i.1) =
      (w i : IsLocalRing.ResidueField A) • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t (a i))) := by
    intro i
    have hg : g i.1 = t (a i) * (((u i)⁻¹ : Aˣ) : A) := by rw [← hu i, Units.mul_inv_cancel_right]
    have ht0 : IsLocalRing.residue A (t (a i)) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 (htm _)
    rw [hg, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (IsLocalRing.ResidueField A) (t (a i)), ← algebraMap_smul (IsLocalRing.ResidueField A) (((u i)⁻¹ : Aˣ) : A)]
    simp only [IsLocalRing.ResidueField.algebraMap_eq, ht0, zero_smul, zero_add, w]
    rfl
  have := (hli.comp a ha).units_smul w
  convert this using 1
  funext i
  exact key i

theorem relSnc_of_regular_params : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → (∀ x : X, IsClosed ({x} : Set X) → ∃ (n : ℕ) (t : Fin n → X.presheaf.stalk x) (c : ∀ i, (L i).ι) (hc : ∀ i, x ∈ (L i).U (c i)) (e : Fin s → Option (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧ ∀ i, Associated ((X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t)) → RelSnc f d L σ := by
  intro k _ _ X f d _ s L σ hL H
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨hL, fun x => ?_⟩
  suffices hcl : ∀ y : X, IsClosed ({y} : Set X) → ∃ C : SncChart f d L σ, y ∈ C.U by
    obtain ⟨y, hy, hxy⟩ := exists_closed_specialization k X f x
    obtain ⟨C, hC⟩ := hcl y hy
    exact ⟨C, hxy _ hC⟩
  intro x hx
  obtain ⟨n, t, c, hc, e, hrsp, hinj, hass⟩ := H x hx
  obtain ⟨U, hUa, hxU, hUc⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ i, U ≤ (L i).U (c i) := by
    have hxW : x ∈ ⋂ i, ((L i).U (c i) : Set X) := Set.mem_iInter.2 fun i => hc i
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW
      (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
    exact ⟨V, hV, hxV, fun i y hy => Set.mem_iInter.1 (hVW hy) i⟩
  letI iBK : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra
  refine GlobalTheory.T.finrank_kaehler_affine_chart k X f d s L σ U c hUc x (IsLocalRing.ResidueField (X.presheaf.stalk x)) hUa hxU ?_ ?_
  · intro a
    rw [X.mem_basicOpen a x hxU]
    change ¬ IsLocalRing.residue _ ((X.presheaf.germ U x hxU).hom a) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  letI iB : Algebra k Γ(X, U) := (cstOn f U).toAlgebra
  refine ⟨GlobalTheory.T.finrank_kaehler_residue_field k X f d U x hxU hUa, ?_⟩
  letI iBA : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI iA : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := GlobalTheory.T.residue_field_formally_smooth k X f U x hxU hx
  have hli := GlobalTheory.T.regular_local_differentials_linearIndependent k (X.presheaf.stalk x) n t hrsp.1 hrsp.2
  have htm : ∀ a, t a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun a => hrsp.1 ▸ Ideal.subset_span ⟨a, rfl⟩
  let g : Fin s → X.presheaf.stalk x := fun i => X.presheaf.germ U x hxU (resG X (hUc i) ((σ i).f (c i)))
  have hg : ∀ i, g i = (X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) := by
    intro i
    simp only [g, resG]
    exact X.presheaf.germ_res_apply (homOfLE (hUc i)) x hxU _
  have hass' : ∀ i, Associated (g i) ((e i).elim 1 t) := fun i => (hg i) ▸ hass i
  have h2 := linearIndependent_fibre_of_associated k (X.presheaf.stalk x) n s t g e htm hinj hass' hli
  exact linearIndependent_fibre_of_stalk k Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
    {i : Fin s // IsLocalRing.residue _ (g i) = 0} (fun i => resG X (hUc i.1) ((σ i.1).f (c i.1))) h2

end GlobalTheory.RegParams
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescends
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.ChartDesc

theorem resG_etale (X : Scheme.{0}) (U W : X.Opens) (h : W ≤ U) (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : (resG X h).Etale := by
  have := HasRingHomProperty.appLE (P := @Etale) (𝟙 X) (inferInstanceAs (Etale (𝟙 X))) ⟨U, hU⟩
    ⟨W, hW⟩ (by simpa using h)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at this
  exact this

theorem chart_desc : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  intro R R' _ _ φ X X' f f' π _ d s L σ C' y H hy
  let c : ∀ i, (L i).ι := fun i => C'.c i ⟨⟩
  have hyc : ∀ i, π y ∈ (L i).U (c i) := fun i => by
    exact (Cartier.pull_U (L i) π (C'.c i)).le (C'.le i hy)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hyc) (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
  have hc : ∀ i, (U : X.Opens) ≤ (L i).U (c i) := fun i _ hz => Set.mem_iInter.1 (hUle hz) i
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((C'.U ⊓ π ⁻¹ᵁ U : X'.Opens) : Set X') from ⟨hy, hxU⟩) (C'.U ⊓ π ⁻¹ᵁ U).isOpen
  have hWC : (W : X'.Opens) ≤ C'.U := fun _ hz => (hWle hz).1
  have hWU : (W : X'.Opens) ≤ π ⁻¹ᵁ U := fun _ hz => (hWle hz).2

  have hA : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (Qcqs.baseRingHom f U) (CommRingCat.ofHom φ) (π.app U)
      (Qcqs.baseRingHom f' (π ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Qcqs.baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [Qcqs.baseRingHom]
  let K := X'.residueField y
  letI : Algebra R R' := φ.toAlgebra
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  letI : Algebra R' Γ(X', π ⁻¹ᵁ U) := (cstOn f' (π ⁻¹ᵁ U)).toAlgebra
  letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  letI : Algebra R Γ(X', π ⁻¹ᵁ U) := ((cstOn f' (π ⁻¹ᵁ U)).comp φ).toAlgebra
  letI : Algebra Γ(X', π ⁻¹ᵁ U) Γ(X', W) := (resG X' hWU).toAlgebra
  letI : Algebra R' Γ(X', W) := (cstOn f' W).toAlgebra
  letI : Algebra Γ(X', W) K := (X'.evaluation W y hyW).hom.toAlgebra
  letI : Algebra Γ(X, U) K :=
    ((X'.evaluation W y hyW).hom.comp ((resG X' hWU).comp (π.app U).hom)).toAlgebra
  haveI : IsScalarTower R R' Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ rfl
  have e2 : ∀ r : R, (π.app U).hom (cstOn f U r) = cstOn f' (π ⁻¹ᵁ U) (φ r) := fun r => by
    have h1 := Qcqs.app_baseRingHom π f U r
    have h2 : Qcqs.baseRingHom (π ≫ f) (π ⁻¹ᵁ U) r = Qcqs.baseRingHom f' (π ⁻¹ᵁ U) (φ r) := by
      rw [H.w, Qcqs.baseRingHom_comp_SpecMap]; rfl
    exact h1.trans h2
  haveI : IsScalarTower R Γ(X, U) Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ (e2 r).symm
  haveI : Algebra.IsPushout R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) := by
    have po'' : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, U))) (CommRingCat.ofHom (algebraMap R R'))
        (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U)))
        (CommRingCat.ofHom (algebraMap R' Γ(X', π ⁻¹ᵁ U))) := po'
    exact (CommRingCat.isPushout_iff_isPushout.mp po'').symm
  haveI : IsScalarTower R' Γ(X', π ⁻¹ᵁ U) Γ(X', W) := .of_algebraMap_eq fun r ↦
    (Qcqs.baseRingHom_res f' hWU r).symm
  haveI : Algebra.FormallyEtale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := by
    haveI : Algebra.Etale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := resG_etale X' _ _ hWU hU' hW
    infer_instance

  let t : Fin d → Γ(X', W) := fun a => resG X' hWC (C'.t a)
  have ht : IsEtCoord f' W t := _root_.GlobalTheory.LogPair.isEtCoord_res R' X' f' C'.U W hWC d C'.t C'.affine hW C'.etale
  have hbasis := GlobalTheory.T.etale_coordinates_differentials R' Γ(X', W) K d t ht
  obtain ⟨ebc, hebc⟩ := _root_.GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) Γ(X', W) K (fun _ => rfl)
  have key : ∀ i, algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
      (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i)))) =
      ((Units.map (resG X' hWC).toMonoidHom (C'.u i) : Γ(X', W)ˣ) : Γ(X', W)) *
        resG X' hWC ((C'.e i).elim 1 C'.t) := by
    intro i
    have e := congrArg (resG X' hWC) (C'.eq i)
    rw [map_mul] at e
    refine Eq.trans ?_ e
    show resG X' hWU ((π.app U).hom (resG X (hc i) ((σ i).f (c i)))) =
      resG X' hWC (resG X' (C'.le i) (resG X' _ ((π.app _).hom ((σ i).f (C'.c i ⟨⟩)))))
    rw [Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG, Cartier.resG_resG]
  have hunit : ∀ v : Γ(X', W)ˣ, algebraMap Γ(X', W) K v ≠ 0 := fun v =>
    (v.isUnit.map (algebraMap Γ(X', W) K)).ne_zero
  have hres : ∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ π y ∈ X.basicOpen a := by
    intro a
    change (X'.evaluation W y hyW).hom (resG X' hWU ((π.app U).hom a)) ≠ 0 ↔ _
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    change y ∈ X'.basicOpen ((X'.presheaf.map (homOfLE hWU).op).hom _) ↔ _
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact ⟨fun h => h.2, fun h => ⟨hyW, h⟩⟩
  have hrank : Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d :=
    ebc.finrank_eq.trans hbasis.1
  have hvan : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ∃ a, C'.e i.1 = some a ∧ algebraMap Γ(X', W) K (t a) = 0 := by
    rintro ⟨i, hi⟩
    have h0 : algebraMap Γ(X', W) K (algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
        (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i))))) = 0 := hi
    rw [key i, map_mul] at h0
    rcases hE : C'.e i with _ | a
    · rw [hE] at h0
      simp only [Option.elim, map_one, mul_one] at h0
      exact absurd h0 (hunit _)
    · refine ⟨a, rfl, ?_⟩
      rw [hE] at h0
      exact (mul_eq_zero.1 h0).resolve_left (hunit _)
  choose g hg hg0 using hvan
  let emb : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} ↪ Fin d :=
    ⟨g, fun i j hij => Subtype.ext (C'.inj i.1 j.1 (g i) (hg i) (by rw [hij]; exact hg j))⟩
  let u : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} → Γ(X', W)ˣ :=
    fun i => Units.map (resG X' hWC).toMonoidHom (C'.u i.1)
  have hli := hbasis.2 _ emb u hg0
  have hfam : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ebc ((1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) =
      (1 : K) ⊗ₜ[Γ(X', W)] KaehlerDifferential.D R' Γ(X', W) ((u i : Γ(X', W)) * t (emb i)) := by
    intro i
    rw [hebc, key i.1, hg i]
    rfl
  have hlin : LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K
      (resG X (hc i) ((σ i).f (c i))) = 0} =>
      (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) := by
    refine LinearIndependent.of_comp ebc.toLinearMap ?_
    convert hli using 1
    funext i
    exact hfam i
  exact GlobalTheory.T.finrank_kaehler_affine_chart R X f d s L σ U c hc (π y) K hU hxU hres ⟨hrank, hlin⟩

end GlobalTheory.ChartDesc
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquationStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.snc_chart_divisor_equation : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ D : CartierDiv Y, D.supp ≤ B → D.IsEqn y (∏ j ∈ J, u j ^ D.mult (w j)) := by
  first | exact @_root_.GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial | exact _root_.GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial | (intros; apply _root_.GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial <;> assumption)
end

