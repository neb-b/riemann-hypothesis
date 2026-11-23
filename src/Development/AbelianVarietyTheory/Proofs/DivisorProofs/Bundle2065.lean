module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGenerators
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem alg_cancel {G : Type*} [CommGroup G] (c a b : G) : a * b⁻¹ = (c * a) * (c * b)⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_chain {G : Type*} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_swap {G : Type*} [CommGroup G] (c a b : G) : c * a = c * (b * a⁻¹)⁻¹ * b := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem ratio_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {V V₁ V₂ : Y.Opens} (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    {a₁ : ∀ k, Γ(Y, V₁ ⊓ L.U k)ˣ} {a₂ : ∀ k, Γ(Y, V₂ ⊓ L.U k)ˣ} (ha₁ : LocGen L V₁ a₁) (ha₂ : LocGen L V₂ a₂) :
    ∃ s : Γ(Y, V)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ V → f t ∈ L.U k →
      gm f t V s = gm f t (V₂ ⊓ L.U k) (a₂ k) * (gm f t (V₁ ⊓ L.U k) (a₁ k))⁻¹ := by
  have l₁ : ∀ k, V ⊓ L.U k ≤ V₁ ⊓ L.U k := fun k => inf_le_inf_right _ h₁
  have l₂ : ∀ k, V ⊓ L.U k ≤ V₂ ⊓ L.U k := fun k => inf_le_inf_right _ h₂
  obtain ⟨s, hs⟩ := glue_unit V (fun k => V ⊓ L.U k) (fun k => inf_le_left)
    (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩)
    (fun k => res (l₂ k) (a₂ k) * (res (l₁ k) (a₁ k))⁻¹)
    (fun k k' y hy => by
      rw [map_mul, map_inv, map_mul, map_inv, gm_res _ y (l₂ k) hy.1, gm_res _ y (l₁ k) hy.1,
        gm_res _ y (l₂ k') hy.2, gm_res _ y (l₁ k') hy.2, ha₁ y k k' (h₁ hy.1.1) hy.1.2 hy.2.2,
        ha₂ y k k' (h₂ hy.1.1) hy.1.2 hy.2.2]
      exact (alg_cancel _ _ _).symm)
  refine ⟨s, fun T f t k ht hk => ?_⟩
  have hm : f t ∈ V ⊓ L.U k := ⟨ht, hk⟩
  rw [← gm_res f t (inf_le_left : V ⊓ L.U k ≤ V) hm s, hs k, map_mul, map_inv, gm_res f t (l₂ k) hm,
    gm_res f t (l₁ k) hm]

theorem eq_of_gm {X X' : Scheme.{0}} (p : X' ⟶ X) {V : X.Opens} (hinj : Function.Injective (pullU p V))
    {u v : Γ(X, V)ˣ} (h : ∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) : u = v :=
  hinj (unit_ext fun x' hx' => by
    rw [gm_pull (𝟙 X') p x' V hx', gm_pull (𝟙 X') p x' V hx', Category.id_comp]
    exact h x' hx')

end GlobalTheory.Pinch

namespace GlobalTheory.Pinch

theorem exists_lb_of_matching_gens : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB →
    ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ)
      (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) →
      (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) →
      (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  intro X X' Z Z' p i i' p' hsq hU L' N hL' hN w W a b hW ha hb hm
  have pt : ∀ z : Z', p (i' z) = i (p' z) := fun z => congrArg (fun f => f z) hsq
  have key : ∀ x y, ∃ g : Γ(X, W x ⊓ W y)ˣ, ∀ (x' : X') (k : L'.ι), p x' ∈ W x ⊓ W y → x' ∈ L'.U k →
      gm p x' _ g = gm (𝟙 X') x' _ (a y k) * (gm (𝟙 X') x' _ (a x k))⁻¹ := by
    intro x y
    obtain ⟨s, hs⟩ := ratio_unit hL' (V := p ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (ha x) (ha y)
    obtain ⟨t, ht⟩ := ratio_unit hN (V := i ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (hb x) (hb y)
    obtain ⟨u, hu⟩ := (hU (W x ⊓ W y)).2 s t (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
      obtain ⟨l, hl⟩ := exists_chart hN (p' z)
      have hz' : i (p' z) ∈ W x ⊓ W y := pt z ▸ hz
      rw [hs Z' i' z k hz hk, ht Z' p' z l hz' hl, hm x z k l hz.1 hz'.1 hk hl, hm y z k l hz.2 hz'.2 hk hl]
      exact alg_cancel _ _ _)
    refine ⟨u, fun x' k hx hk => ?_⟩
    have e := gm_pull (𝟙 X') p x' _ hx u
    rw [Category.id_comp] at e
    rw [← e, hu]
    exact hs X' (𝟙 X') x' k hx hk
  choose g hg using key
  have hL : (⟨X, W, g⟩ : LB X).IsLB :=
    { cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩
      g_self := fun x => eq_of_gm p (hU (W x)).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        refine (gm_res p x' _ hx _).trans ((hg x x x' k ⟨hx, hx⟩ hk).trans ?_)
        rw [mul_inv_cancel, map_one]
      cocycle := fun x y z => eq_of_gm p (hU _).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res p x' _ hx _).trans (hg x y x' k ⟨hx.1.1, hx.1.2⟩ hk))
          ((gm_res p x' _ hx _).trans (hg y z x' k ⟨hx.1.2, hx.2⟩ hk)))).trans
          ((alg_chain _ _ _).trans ((gm_res p x' _ hx _).trans (hg x z x' k ⟨hx.1.1, hx.2⟩ hk)).symm) }
  refine ⟨⟨X, W, g⟩, hL, ⟨fun P => res (fun x' hx' => ⟨mem_pull.1 hx'.2, hx'.1⟩ :
    L'.U P.1 ⊓ ((⟨X, W, g⟩ : LB X).pull p).U P.2 ≤ p ⁻¹ᵁ W (P.2 PUnit.unit) ⊓ L'.U P.1) (a (P.2 PUnit.unit) P.1)⟩, ?_⟩
  rintro ⟨k, J⟩ ⟨k', J'⟩
  apply unit_ext
  intro x' hx'
  have hJ : p x' ∈ W (J PUnit.unit) := mem_pull.1 hx'.1.2
  have hJ' : p x' ∈ W (J' PUnit.unit) := mem_pull.1 hx'.2.2
  have e : gm (𝟙 X') x' (((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J')
      (((⟨X, W, g⟩ : LB X).pull p).g J J') = gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 X') x' _ (∏ _k : PUnit, (res _ (pullU p _ (g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    have hq : x' ∈ ((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J' := ⟨hx'.1.2, hx'.2.2⟩
    exact (gm_res _ x' _ hq _).trans ((gm_pull (𝟙 X') p x' (W (J PUnit.unit) ⊓ W (J' PUnit.unit))
      (⟨hJ, hJ'⟩ : p x' ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit)) _).trans (congrArg (fun f => gm f x' _ (g (J PUnit.unit) (J' PUnit.unit))) (Category.id_comp p)))
  have hdiv : gm (𝟙 X') x' _ ((LB.div L' ((⟨X, W, g⟩ : LB X).pull p)).g (k, J) (k', J')) =
      gm (𝟙 X') x' _ (L'.g k k') * (gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x' _ hx' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ x' _ hx' _).trans e))))
  refine (gm_res _ x' _ hx' _).trans ((gm_res _ x' _ hx'.1 _).trans ?_)
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hdiv
    ((gm_res _ x' _ hx' _).trans (gm_res _ x' _ hx'.2 _)))).symm
  have h2 := hg (J PUnit.unit) (J' PUnit.unit) x' k' ⟨hJ, hJ'⟩ hx'.2.1
  rw [h2]
  exact (ha (J PUnit.unit) x' k k' hJ hx'.1.1 hx'.2.1).trans (alg_swap _ _ _)

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFinite
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem exists_smul_mem_span_away {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [AddCommGroup M] [Module S M] [Module.Invertible S M]
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ ∃ m : M, ∀ x : M, ∃ a : S, algebraMap R S r • x = a • m := by
  classical
  let Q : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let T := Localization Q
  letI : Algebra (Localization.AtPrime p) T := localizationAlgebra p.primeCompl S
  haveI : Module.Finite (Localization.AtPrime p) T :=
    Module.Finite.of_isLocalization R S p.primeCompl
  haveI : Finite (MaximalSpectrum T) :=
    GlobalTheory.finite_maximalSpectrum_of_finite (Localization.AtPrime p) T
  obtain ⟨z, hz⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum T (LocalizedModule Q M)
  induction z using LocalizedModule.induction_on with
  | h m s =>
  have hloc : ∀ x : M, ∃ q ∈ Q, q • x ∈ Submodule.span S {m} := by
    intro x
    obtain ⟨c, hc⟩ := hz.2 (LocalizedModule.mk x 1)
    induction c using Localization.induction_on with
    | H c =>
    obtain ⟨a, t⟩ := c
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨(u : S) * ((t : S) * (s : S)), Q.mul_mem u.2 (Q.mul_mem t.2 s.2), ?_⟩
    rw [mul_smul, mul_smul]
    have hu' : (u : S) • (((t * s : Q) : S)) • x = (u : S) • ((1 : Q) : S) • a • m := hu.symm
    rw [Submonoid.coe_mul] at hu'
    rw [mul_smul] at hu'
    rw [hu', Submodule.mem_span_singleton]
    exact ⟨(u : S) * a, by simp [mul_smul]⟩
  choose q hqQ hq using hloc
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := S) (M := M)
  let q₀ : S := ∏ x ∈ F, q x
  have hq₀ : q₀ ∈ Q := Q.prod_mem fun x _ => hqQ x
  have key : ∀ y ∈ Submodule.span S (F : Set M), q₀ • y ∈ Submodule.span S {m} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have : q₀ = (∏ x' ∈ F.erase x, q x') * q x := (Finset.prod_erase_mul F q hx).symm
      rw [this, mul_smul]
      exact Submodule.smul_mem _ _ (hq x)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
  obtain ⟨r, hr, hrq⟩ := hq₀
  refine ⟨r, hr, m, fun x => ?_⟩
  have := key x (hF ▸ Submodule.mem_top)
  rw [Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [hrq]; exact ha.symm⟩

theorem isFrame_res_of_smul_mem {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {U : X.Opens}
    (hU : IsAffineOpen U) (h : Γ(X, U)) (m : Γ(GlobalTheory.LB.toMod L, U))
    (hm : ∀ x : Γ(GlobalTheory.LB.toMod L, U), ∃ a : Γ(X, U), h • x = a • m) :
    GlobalTheory.LB.IsFrame ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m) := by
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  have hD : IsAffineOpen (X.basicOpen h) := hU.basicOpen h
  haveI := GlobalTheory.LB.invertible_sections hL hD
  rw [GlobalTheory.LB.isFrame_iff_bijective hD]
  have h₁ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (GlobalTheory.LB.toMod L) h).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen (GlobalTheory.LB.toMod L) hU h)).1
  refine Module.Invertible.bijective_of_surjective
    (f := LinearMap.toSpanSingleton Γ(X, X.basicOpen h) _
      ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m)) ?_
  intro s
  obtain ⟨n, t, ht⟩ := h₁ s
  obtain ⟨a, ha⟩ := hm t
  obtain ⟨u, hu⟩ := GlobalTheory.QCoh.isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl
  have e1 := GlobalTheory.LB.map_smul_resG (F := GlobalTheory.LB.toMod L) (X.basicOpen_le h) h t
  rw [ha, GlobalTheory.LB.map_smul_resG] at e1
  refine ⟨((u⁻¹ : Γ(X, X.basicOpen h)ˣ) : Γ(X, X.basicOpen h)) ^ (n + 1) *
    resG X (X.basicOpen_le h) a, ?_⟩
  rw [← hu] at ht
  have hu' : resG X (X.basicOpen_le h) h = (u : Γ(X, X.basicOpen h)) := hu.symm
  rw [hu', ← ht, ← mul_smul] at e1
  rw [LinearMap.toSpanSingleton_apply, mul_smul, e1, ← mul_smul, ← pow_succ', ← mul_pow,
    Units.inv_mul, one_pow, one_smul]

theorem exists_trivial_near_fibre : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB →
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  intro X Y f _ L hL y
  obtain ⟨W, hW, hyW, -⟩ : ∃ W ∈ Y.affineOpens, y ∈ W ∧ W ≤ ⊤ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let p : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom
  letI : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := f.finite_app W hW
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  haveI := GlobalTheory.LB.invertible_sections hL hU
  obtain ⟨r, hr, m, hm⟩ := exists_smul_mem_span_away (R := Γ(Y, W)) (S := Γ(X, f ⁻¹ᵁ W))
    (M := Γ(GlobalTheory.LB.toMod L, f ⁻¹ᵁ W)) p
  have he := isFrame_res_of_smul_mem hL hU (f.app W r) m hm
  have hpre : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r) := Scheme.preimage_basicOpen f r
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · rw [Scheme.mem_basicOpen (x := y) (hx := hyW)]
    by_contra hn
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 hn)
  let F := GlobalTheory.LB.toMod L
  let e : Γ(F, f ⁻¹ᵁ Y.basicOpen r) :=
    F.presheaf.map (homOfLE hpre.le).op (F.presheaf.map (homOfLE (X.basicOpen_le _)).op m)
  have he' : GlobalTheory.LB.IsFrame e := he.map hpre.le
  let u : ∀ i, Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ := fun i =>
    (GlobalTheory.LB.isFrame_chartSec hL i).unit he' inf_le_right inf_le_left
  have hu : ∀ i, ((u i : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ) : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)) =
      GlobalTheory.LB.coord e i := fun i => by
    rw [GlobalTheory.LB.IsFrame.val_unit]
    apply GlobalTheory.LB.IsFrame.repr_eq
    apply Subtype.ext
    funext j
    change GlobalTheory.LB.coord (GlobalTheory.LB.coord e i •
      (GlobalTheory.LB.toMod L).presheaf.map (homOfLE inf_le_right).op
        (GlobalTheory.LB.chartSec hL i)) j =
      GlobalTheory.LB.coord ((GlobalTheory.LB.toMod L).presheaf.map
        (homOfLE inf_le_left).op e) j
    simp only [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_map,
      GlobalTheory.LB.coord_chartSec, GlobalTheory.LB.resG_resG]
    rw [mul_comm]
    exact (GlobalTheory.LB.coord_rel e j i _ _ _).symm
  refine ⟨u, fun i j x hxV hi hj => ?_⟩
  have hxO : x ∈ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j := ⟨⟨hxV, hi⟩, hj⟩
  rw [← gm_res (𝟙 X) x (inf_le_left : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ _) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U j) hxO, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hu, hu]
  exact GlobalTheory.LB.coord_rel e i j _ _ _

end GlobalTheory.LBDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDenominator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory.Cartier

namespace GlobalTheory.DenominatorExistenceLemmas

variable {M W : Scheme.{0}}

theorem finite_app (f : M ⟶ W) [IsProper f] [IsLocallyNoetherian W] {L : ReciprocityTheory.ChartRestriction.G.Semi.LB M}
    (hL : IsAmpleLB L) {V : W.Opens} (hV : IsAffineOpen V) : (f.app V).hom.Finite := by
  obtain ⟨_, hfa⟩ := GlobalTheory.ProperFinite.isFiniteQC_pushforward f hL (structureModule M)
  exact hfa V hV

variable [IsIntegral M] [IsIntegral W]


omit [IsIntegral W] in
theorem gen_mem_preimage (f : M ⟶ W) [IsDominant f] {U : W.Opens} {y : W} (hy : y ∈ U) :
    genericPoint M ∈ f ⁻¹ᵁ U := by
  obtain ⟨m, hm⟩ := f.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
  exact gen_mem (U := f ⁻¹ᵁ U) (x := m) hm


omit [IsIntegral W] in
theorem fnOf_map {U V : M.Opens} (e : V ≤ U) (h : genericPoint M ∈ V) (a : Γ(M, U)) :
    fnOf V h (M.presheaf.map (homOfLE e).op a) = fnOf U (e h) a := by
  exact fnOf_resG e h a

theorem exists_denominator {V : W.Opens} (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) {ι : Type} [Finite ι]
    (c : ι → W.functionField) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ i, ∃ a : Γ(W, V), fnOf V hg a = fnOf V hg d * c i := by
  have : Nonempty V := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen W V hV
  obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(W, V)) c
  refine ⟨d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hdc i
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def] at ha
  exact ha

theorem exists_denominator_all (f : M ⟶ W) [IsDominant f] {V : W.Opens} (hV : IsAffineOpen V)
    (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) (hf : (f.app V).hom.Finite) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ j (b : Γ(M, f ⁻¹ᵁ V)), ∃ a : Γ(W, V),
      fnOf V hg a = fnOf V hg d * co j (fnOf (f ⁻¹ᵁ V) hg' b) := by
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(W, V) Γ(M, f ⁻¹ᵁ V) := hf
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(W, V)) (M := Γ(M, f ⁻¹ᵁ V))
  obtain ⟨d, hd0, hd⟩ := exists_denominator hV hg
    (fun p : Fin r × Fin n => co p.1 (fnOf (f ⁻¹ᵁ V) hg' (s p.2)))
  refine ⟨d, hd0, fun j b => ?_⟩
  have hb : b ∈ Submodule.span Γ(W, V) (Set.range s) := hs ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hd (j, k)
  | zero => exact ⟨0, by simp only [map_zero, mul_zero]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hx'
    exact ⟨a + a', by rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, ha', mul_add]⟩
  | smul t x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨t * a, ?_⟩
    have ht : fnOf (f ⁻¹ᵁ V) hg' (t • x) = functionFieldMap f (fnOf V hg t) * fnOf (f ⁻¹ᵁ V) hg' x := by
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra]
      congr 1
      exact GlobalTheory.Cartier.DomPull.fnOf_app f hg' t
    rw [ht, hco, map_mul, ha]
    ring

theorem exists_pow_mul_eq (f : M ⟶ W) [IsDominant f] [QuasiCompact f] [QuasiSeparatedSpace M] {V : W.Opens}
    (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) {y : W} (hy : y ∈ V)
    {V' : W.Opens} (hy' : y ∈ V') (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) :
    ∃ (u : W.functionField) (b : Γ(M, f ⁻¹ᵁ V)), UnitAt y u ∧
      fnOf (f ⁻¹ᵁ V) hg' b = functionFieldMap f u * fnOf (f ⁻¹ᵁ V') h z := by
  obtain ⟨g, hgV', hyg⟩ := hV.exists_basicOpen_le ⟨y, hy'⟩ hy
  have hle : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V' := by
    rw [← Scheme.preimage_basicOpen]
    exact fun x hx => hgV' hx
  have hgb : genericPoint M ∈ M.basicOpen (f.app V g) := by
    rw [← Scheme.preimage_basicOpen]
    exact gen_mem_preimage f hyg
  obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated M (f ⁻¹ᵁ V)
    (f.isCompact_preimage hV.isCompact) (IsQuasiSeparated.of_quasiSeparatedSpace _) (f.app V g) (M.presheaf.map (homOfLE hle).op z)
  have e0 : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V := M.basicOpen_le _
  have h1 : fnOf _ hgb (M.presheaf.map (homOfLE e0).op b) =
      fnOf _ hgb (M.presheaf.map (homOfLE e0).op (f.app V g)) ^ n *
        fnOf _ hgb (M.presheaf.map (homOfLE hle).op z) := by
    rw [← map_pow, ← map_mul]
    exact congrArg _ hb
  rw [fnOf_map, fnOf_map, fnOf_map] at h1
  refine ⟨fnOf V hg g ^ n, b, ?_, ?_⟩
  · have hu : UnitAt y (fnOf V hg g) := (unitAt_fnOf_iff hy hg g).2 hyg
    clear h1 hb
    induction n with
    | zero => simpa using unitAt_one y
    | succ n ih => rw [pow_succ]; exact ih.mul hu
  · rw [map_pow, ← GlobalTheory.Cartier.DomPull.fnOf_app f hg' g]
    exact h1


omit [IsIntegral M] [IsIntegral W] in
theorem exists_local_denominator (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    [IsProper f] [IsLocallyNoetherian W] (L : ReciprocityTheory.ChartRestriction.G.Semi.LB M) (hL : IsAmpleLB L) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) (y : W) :
    ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, ∀ V' : W.Opens, y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r),
        RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  obtain ⟨V, hVa, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian f
  have : TopologicalSpace.NoetherianSpace M := GlobalTheory.IsAmpleLB.noetherianSpace hL
  have hg' : genericPoint M ∈ f ⁻¹ᵁ V := gen_mem_preimage f hyV
  obtain ⟨d, hd0, hd⟩ := exists_denominator_all f hVa (gen_mem hyV) hg' (finite_app f hL hVa) co hco
  refine ⟨V, hyV, d, hd0, fun y' hy'V V' hy'V' h z j => ?_⟩
  obtain ⟨u, b, hu, hb⟩ := exists_pow_mul_eq f hVa (gen_mem hyV) hg' hy'V hy'V' h z
  obtain ⟨a, ha⟩ := hd j b
  have hz : fnOf (f ⁻¹ᵁ V') h z = functionFieldMap f u⁻¹ * fnOf (f ⁻¹ᵁ V) hg' b := by
    rw [hb, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu.ne_zero, map_one, one_mul]
  rw [hz, hco, mul_left_comm (fnOf V (gen_mem hyV) d), ← ha]
  exact hu.inv.regAt.mul (regAt_fnOf hy'V _ a)

end GlobalTheory.DenominatorExistenceLemmas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFormOfTensorSectionInChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsSec

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (J J' : PUnit → L.ι)
    (hj : F (f y) ∈ L.U (J PUnit.unit)) (hj' : F (f y) ∈ L.U (J' PUnit.unit)) :
    gm f y ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) y _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f y ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U _ ⊓ L.U _) ⟨hj, hj'⟩ _)

theorem exists_sec_of_chart {X X' : Scheme.{0}} (A B : LB X) (hB : B.IsLB) (σ : (CechPic.tens A B).Sec) (b : B.ι)
    (F : X' ⟶ X) (hb : ∀ y : X', F y ∈ B.U b) :
    ∃ t : (A.pull F).Sec, ∀ (j : (A.pull F).ι)
      (h : (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b)),
      t.f j = (F.appLE _ _ h).hom (σ.f (j PUnit.unit, b)) := by
  have hle : ∀ j : (A.pull F).ι, (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b) :=
    fun j y hy => ⟨mem_pull.1 hy, hb y⟩
  refine ⟨⟨fun j => (F.appLE _ _ (hle j)).hom (σ.f (j PUnit.unit, b)), fun j j' => ?_⟩, fun _ _ => rfl⟩
  apply TopCat.Presheaf.section_ext X'.sheaf
  intro y hy
  have hy' : (𝟙 X' : X' ⟶ X') y ∈ (A.pull F).U j ⊓ (A.pull F).U j' := hy
  have hj : F y ∈ A.U (j PUnit.unit) := mem_pull.1 hy.1
  have hj' : F y ∈ A.U (j' PUnit.unit) := mem_pull.1 hy.2
  have hp : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j PUnit.unit, b) := ⟨hj, hb y⟩
  have hq : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j' PUnit.unit, b) := ⟨hj', hb y⟩
  have e := gs_compat σ (𝟙 X' ≫ F) y hp hq
  have e₁ := CechPic.gm_tens A B (𝟙 X' ≫ F) y (j PUnit.unit, b) (j' PUnit.unit, b) hp hq
  rw [gm_self hB (𝟙 X' ≫ F) y hp.2, _root_.mul_one] at e₁
  rw [e₁] at e
  refine (gs_eq (𝟙 X') y _ hy' _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X') y _ hy' _))
  refine (gs_res _ y _ hy' _).trans ((gs_appLE F _ _ _ (𝟙 X') y hy'.1 _).trans (e.trans ?_))
  refine Eq.trans ?_ (gs_mul _ y _ hy' _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gs_res _ y _ hy' _).trans (gs_appLE F _ _ _ (𝟙 X') y hy'.2 _)).symm
  exact ((gs_unit _ y _ hy' _).trans (congrArg Units.val (gm_pull_g A F (𝟙 X') y j j' hj hj'))).symm

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  intro S G _ _ L δ σ i R _ ξ hδ hξ
  refine exists_sec_of_chart L.L (δ.pull G.hom) (LB.isLB_pull hδ _) σ (fun _ => i) (pullback.fst G.hom ξ) fun y => ?_
  refine mem_pull.2 ?_
  have h : (pullback.fst G.hom ξ ≫ G.hom) y ∈ δ.U i := by
    rw [pullback.condition]
    exact hξ (Set.mem_univ (pullback.snd G.hom ξ y))
  exact h

end GlobalTheory.KeyValsSec

end
end

