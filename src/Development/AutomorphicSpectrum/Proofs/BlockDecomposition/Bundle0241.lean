module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0238
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrTeichProd
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestZar

theorem idem_unit {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) (h : IsUnit u) : u = 1 :=
  h.mul_left_cancel (by rw [mul_one]; exact hu)

theorem factor_one {R R' ι : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : ι → R) (hb : ∀ i, IsIdempotentElem (b i))
    (S : Finset ι) (h : g (∏ i ∈ S, b i) = 1) {i : ι} (hi : i ∈ S) : g (b i) = 1 :=
  idem_unit ((hb i).map g) (isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem b hi)) (h ▸ isUnit_one))

theorem span_of_nil {R P ι : Type} [CommRing R] [CommRing P] (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) (g : ι → R)
    (π : P →+* R ⧸ I) (e : ι → P) (he : Ideal.span (Set.range e) = ⊤)
    (h : ∀ i, π (e i) = Ideal.Quotient.mk I (g i)) : Ideal.span (Set.range g) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) = ⊤ := by
    have e1 : (Ideal.Quotient.mk I) ∘ g = π ∘ e := funext fun i => (h i).symm
    rw [Ideal.map_span, ← Set.range_comp, e1, Set.range_comp, ← Ideal.map_span, he, Ideal.map_top]
  have h2 : (1 : R ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (hI _ hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Gen

open GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
  {R₀ : Type} [CommRing R₀] (c : R₀ →+* b.R) (r : ℕ)
  {C : Type*} [Category C] (G : C ⥤ Thick (F.cr b ht κ))

def locModG {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (f : Fin m → (G.obj T').B) (hf : Ideal.span (Set.range f) = ⊤)
    (h1 : ∀ S, ∀ k ∈ S, (G.map (lam S)).φ (f k) = 1)
    (hs : ∀ S, ∀ y ∈ (G.obj (Lc S)).pdPow r, ∃ x ∈ (G.obj T').pdPow r, (G.map (lam S)).φ x = y)
    (hk : ∀ S x, (G.map (lam S)).φ x = 0 → (∏ k ∈ S, f k) * x = 0) :
    LocMod (G ⋙ (pdS (F.cr b ht κ) c r).fn) T' Lc lam where
  Λ := (G.obj T').B
  f := f
  span := hf
  ρ₀ := mulR c r (G.obj T')
  ρ S := (mulR c r (G.obj (Lc S))).comp (G.map (lam S)).φ
  lam_ρ S a x := Subtype.ext (map_mul (G.map (lam S)).φ a (show (G.obj T').B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : (G.map t).φ.comp (G.map (lam S)).φ = (G.map (lam S')).φ := by
      have := congrArg Thick.Hom.φ (congrArg G.map ht')
      rw [G.map_comp] at this
      exact this
    refine Subtype.ext ?_
    change (G.map t).φ ((G.map (lam S)).φ a * (show (G.obj (Lc S)).B from x.1)) =
      (G.map (lam S')).φ a * (G.map t).φ (show (G.obj (Lc S)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply (G.map t).φ, e]
  unit S k hk' := by
    change Function.Bijective (mulR c r (G.obj (Lc S)) ((G.map (lam S)).φ (f k)))
    rw [h1 S k hk', map_one]
    exact Function.bijective_id
  surj S y := by
    obtain ⟨x, hx, e⟩ := hs S y.1 y.2
    refine ⟨0, ⟨x, hx⟩, ?_⟩
    rw [pow_zero, map_one]
    exact Subtype.ext e.symm
  ker S x hx := by
    have h0 : (G.map (lam S)).φ (show (G.obj T').B from x.1) = 0 := congrArg Subtype.val hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    exact hk S _ h0

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem step_onto {A B : PAlg l} (lam : A ⟶ B) (k : Bool) (n r : ℕ) (hs : Function.Surjective (mapAcr lam n))
    {y : B.Acr n} (hy : y ∈ fil (DD k B n) r) : ∃ x ∈ fil (DD k A n) r, mapAcr lam n x = y := by
  have hA := (_root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp A n).2.2.2.2.1 k r
  have hB := (_root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp B n).2.2.2.2.1 k r
  have e : (mapAcr lam n).comp (mapAcr A.fromBase n) = mapAcr B.fromBase n :=
    RingHom.ext fun x => mapAcr_fromBase lam n x
  rw [hB, ← e, ← Ideal.map_map, ← hA] at hy
  exact (Ideal.mem_map_iff_of_surjective _ hs).1 hy

theorem span_acr (A : PAlg l) (n : ℕ) {m : ℕ} (e : Fin m → A.A) (he : Ideal.span (Set.range e) = ⊤) :
    Ideal.span (Set.range fun i => A.toAcr n (WittVector.teichmuller l (e i))) = ⊤ := by
  obtain ⟨⟨π, hπ, -⟩, -, -, -, -, hnil, -⟩ := _root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp A n
  exact span_of_nil (A.PFil n) (fun x hx => (hnil x hx).1) _ π e he fun i => hπ _

theorem acr_teich_one {A B : PAlg l} (f : A ⟶ B) (n : ℕ) {a : A.A} (h : Hom.f f a = 1) :
    mapAcr f n (A.toAcr n (WittVector.teichmuller l a)) = 1 := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_one, map_one]

theorem acr_teich_prod (A : PAlg l) (n : ℕ) {ι : Type} (S : Finset ι) (a : ι → A.A) :
    A.toAcr n (WittVector.teichmuller l (∏ i ∈ S, a i)) = ∏ i ∈ S, A.toAcr n (WittVector.teichmuller l (a i)) := by
  rw [map_prod, map_prod]

section Fac

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def facObj (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : El (F.pt κ) :=
  (testι l ⋙ F.pt κ).elementsMk ⟨A', h⟩ ((F.pt κ).map lam T'.val)

def facHom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : T' ⟶ facObj F κ T' A' lam h :=
  ⟨ObjectProperty.homMk lam, rfl⟩

theorem fac_univ (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) (T'' : El (F.pt κ)) (ψ : T' ⟶ T'')
    (hu : ∃! χ : A' ⟶ T''.1.obj, lam ≫ χ = ψ.1.hom) :
    ∃! χ : facObj F κ T' A' lam h ⟶ T'', facHom F κ T' A' lam h ≫ χ = ψ := by
  obtain ⟨χ, hχ, huniq⟩ := hu
  refine ⟨⟨ObjectProperty.homMk χ, ?_⟩, Functor.Elements.hom_ext (ObjectProperty.hom_ext _ hχ), fun χ' h' =>
    Functor.Elements.hom_ext (ObjectProperty.hom_ext _ (huniq χ'.1.hom (congrArg (fun z => z.1.hom) h')))⟩
  change (F.pt κ).map χ ((F.pt κ).map lam T'.2) = T''.2
  rw [← Functor.map_comp_apply, hχ]
  exact ψ.2

theorem fac_loc (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ} (b : Fin m → T'.1.obj.A)
    (hspan : Ideal.span (Set.range b) = ⊤) (A' : Finset (Fin m) → PAlg l) (lam : ∀ S, T'.1.obj ⟶ A' S)
    (ht : ∀ S, (A' S).IsTest) (h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1)
    (hs : ∀ S, Function.Surjective (mapAcr (lam S) n))
    (hk : ∀ S x, mapAcr (lam S) n x = 0 → T'.1.obj.toAcr n (WittVector.teichmuller l (∏ i ∈ S, b i)) * x = 0) :
    Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T'
      (fun S => facObj F κ T' (A' S) (lam S) (ht S)) fun S => facHom F κ T' (A' S) (lam S) (ht S)) := by
  have hf : Ideal.span (Set.range fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) = ⊤ := span_acr _ n b hspan
  have hk' : ∀ S x, mapAcr (lam S) n x = 0 →
      (∏ i ∈ S, T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) * x = 0 := fun S x hx => by
    have h := hk S x hx
    rw [acr_teich_prod] at h
    exact h
  exact ⟨locModG (F := F) (b := bs l k n) (ht := rfl) (κ := κb κ k n) ((base l).cris n) r (gT F κ k n) T'
    (fun S => facObj F κ T' (A' S) (lam S) (ht S)) (fun S => facHom F κ T' (A' S) (lam S) (ht S))
    (fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) hf
    (fun S i hi => acr_teich_one (lam S) n (h1 S i hi))
    (fun S y hy => step_onto (lam S) k n r (hs S) hy) hk'⟩

theorem factors (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ}
    (b : Fin m → T'.1.obj.A) (hb : ∀ i, IsIdempotentElem (b i)) (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (Lc' : Finset (Fin m) → El (F.pt κ)) (lamE : ∀ S, T' ⟶ Lc' S),
      (∀ S, ∀ i ∈ S, Hom.f (lamE S).1.hom (b i) = 1) ∧
      (∀ S (T'' : El (F.pt κ)) (ψ : T' ⟶ T''), (∀ i ∈ S, Hom.f ψ.1.hom (b i) = 1) → ∃! χ : Lc' S ⟶ T'', lamE S ≫ χ = ψ) ∧
      Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T' Lc' lamE) := by
  have ha : ∀ S : Finset (Fin m), IsIdempotentElem (∏ i ∈ S, b i) := fun S =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h h' => h.mul h') IsIdempotentElem.one fun i _ => hb i
  choose A' lam htest hlam huniv hacr using fun S => _root_.GlobalTheory.CompanionTheory.IdemObj.directFactor T'.1.obj (∏ i ∈ S, b i) (ha S)
  have h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1 := fun S i hi => factor_one (Hom.f (lam S)) b hb S (hlam S) hi
  have ht : ∀ S, (A' S).IsTest := fun S => htest S T'.1.property
  refine ⟨fun S => facObj F κ T' (A' S) (lam S) (ht S), fun S => facHom F κ T' (A' S) (lam S) (ht S), h1,
    fun S T'' ψ h => fac_univ F κ T' (A' S) (lam S) (ht S) T'' ψ (huniv S T''.1.obj ψ.1.hom ?_),
    fac_loc F κ k n r T' b hspan A' lam ht h1 (fun S => (hacr S n).1) fun S => (hacr S n).2⟩
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi => h i hi

end Fac

theorem chart_of_one {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n : ℕ)
    {T T₁ : El (F.pt κ)} (ψ : T ⟶ T₁) (s : T.1.obj.U) (a : T.1.obj.A) (ha : T.1.obj.sharp a ∈ Ideal.span {s})
    (hcov : ∀ (B' : CommRingCat) (φ : CommRingCat.of T.1.obj.U ⟶ B'), IsUnit (φ.hom s) →
      ∃ α, (𝒜.V α).In (F.Pt.map φ T.2.1))
    (h : Hom.f ψ.1.hom a = 1) : ∃ α, (𝒜.V α).In ((gT F κ k n).obj T₁).y.1.2 := by
  have hu : IsUnit ((CommRingCat.ofHom (mapU ψ.1.hom)).hom s) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have h2 := congrArg (mapU ψ.1.hom) hc
    rw [map_mul, mapU_sharp, h, map_one] at h2
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h2)
  obtain ⟨α, hα⟩ := hcov _ _ hu
  have hpt : F.Pt.map (CommRingCat.ofHom (mapU ψ.1.hom)) T.2.1 = T₁.2.1 := congrArg Subtype.val ψ.2
  rw [hpt] at hα
  exact ⟨α, (𝒜.V α).in_map (CommRingCat.ofHom (uJ k T₁.1.obj n)) hα⟩

theorem zarCov_test : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d)
    (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn)
      fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 k n r
  refine ⟨fun T T' φ h => (GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜
    (Fact.out : l.Prime).ne_zero r).1 ((gT F κ k n).map φ) h, fun T => ?_⟩
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of T.1.obj.U) T.2.1
  obtain ⟨e, hidem, hspan, hes⟩ := _root_.GlobalTheory.CompanionTheory.TestCover.test_cover T.1.obj T.1.property s hs
  refine ⟨m, fun i _ ψ => Hom.f ψ.1.hom (e i) = 1, fun i T₁ T₂ ψ χ h => ?_,
    fun i T₁ ψ h => chart_of_one F κ 𝒜 k n ψ (s i) (e i) (hes i) (hcov i) h, fun T' φ => ?_⟩
  · have h' : Hom.f ψ.1.hom (e i) = 1 := h
    have e1 : Hom.f (ψ ≫ χ).1.hom (e i) = Hom.f χ.1.hom (Hom.f ψ.1.hom (e i)) := rfl
    exact e1.trans (by rw [h', map_one])
  have hspan' : Ideal.span (Set.range fun i => Hom.f φ.1.hom (e i)) = ⊤ := by
    have h := congrArg (Ideal.map (Hom.f φ.1.hom)) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  obtain ⟨Lc', lamE, h1, h2, h3⟩ := factors F κ k n r T' (fun i => Hom.f φ.1.hom (e i))
    (fun i => (hidem i).map (Hom.f φ.1.hom)) hspan'
  exact ⟨Lc', lamE, fun S i hi => h1 S i hi, fun S T'' ψ h => h2 S T'' ψ fun i hi => h i hi, h3⟩

end GlobalTheory.CompanionTheory.TestZar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegral
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.IntVal

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (z : Om l) (h : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hz : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  rw [← PadicAlgCl.spectralNorm_eq] at h
  unfold spectralNorm at h
  rw [spectralValue_le_one_iff (minpoly.monic hz)] at h
  have hlift : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hz)
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Om l), ← eval₂_map, hq, ← aeval_def]
  exact minpoly.aeval ℚ_[l] z

theorem mem_OL_of_norm_le_one (K : FinExt l) (x : ↥K.1) (h : ‖((x : ↥K.1) : Om l)‖ ≤ 1) :
    x ∈ OL K := by
  change x ∈ integralClosure ℤ_[l] ↥K.1
  rw [mem_integralClosure_iff]
  haveI : IsScalarTower ℤ_[l] ↥K.1 (Om l) := IsScalarTower.of_algebraMap_eq fun z => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l),
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1]
    rfl
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ_[l] ↥K.1 (Om l)) :=
    (algebraMap ↥K.1 (Om l)).injective
  exact (isIntegral_algHom_iff _ hinj).1 (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  have := K.2
  exact isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

theorem norm_le_one (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l))) (g : ↥(GK K)) :
    ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ≤ 1 := by
  haveI := compactSpace_GK K
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hpow : ∀ n : ℕ, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ^ n ≤ M := fun n => by
    have := hM _ ⟨g ^ n, rfl⟩
    simpa [map_pow, norm_pow] using this
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
  exact absurd (hpow n) (not_le.2 hn)

theorem integral_values {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) :
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := fun hc g =>
  ⟨⟨_, mem_OL_of_norm_le_one K _ (norm_le_one K χ hc g)⟩, rfl⟩

end GlobalTheory.CompanionTheory.LTPer.IntVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZarCap

attribute [local instance] MvPolynomial.gradedAlgebra

theorem inU_inf {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V W : X.Opens) (T : Thick (nlFun γ p X q κ)) :
    InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
  unfold InU
  rw [← le_inf_iff]
  exact Iff.rfl

theorem irrelevant_le_span (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  have h0 : AddMonoidAlgebra.coeff x 0 = 0 := by
    erw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero] at hx
    exact MvPolynomial.C_eq_zero.1 hx
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  have hm0 : m = 0 := Finsupp.ext fun i => by
    by_contra hi
    exact hne ⟨i, Set.mem_univ i, hi⟩
  subst hm0
  exact (MvPolynomial.mem_support_iff.1 hm) h0

theorem iSup_wch {K : Type} [Field K] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace K N) : (⨆ j, wch i j) = ⊤ := by
  have h := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun j => MvPolynomial.X j) (irrelevant_le_span K N)
  simp only [wch]
  rw [← Scheme.Hom.preimage_iSup, h, Scheme.Hom.preimage_top]

theorem resU_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    resU (sq (thFil L r) (thFil L r')) h = (incl h).sq (incl_fil h r) (incl_fil h r') := by
  unfold resU CrystallineSemistableComparison.Pb.SMor.sq
  congr 1
  funext T
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨z, hz⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

private theorem isHecke_div_and_resEtaPow_div {X : Scheme.{0}} {m N : ℕ} (u : Fin m → X.Opens) (w : Fin (N + 1) → X.Opens)
    (hw : (⨆ j, w j) = ⊤) (S : Finset (Fin m)) :
    (⨅ k ∈ S, u k) ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact le_iSup_of_le (fun _ => 0) (by simp)
  · intro a S ha ih
    rw [Finset.iInf_insert]
    calc u a ⊓ ⨅ k ∈ S, u k ≤ (⨆ j, u a ⊓ w j) ⊓ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) :=
          inf_le_inf (by rw [← inf_iSup_eq, hw, inf_top_eq]) ih
      _ = ⨆ j, ⨆ c : Fin m → Fin (N + 1), (u a ⊓ w j) ⊓ ⨅ k ∈ S, (u k ⊓ w (c k)) := by
          rw [iSup_inf_eq]
          simp_rw [inf_iSup_eq]
      _ ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ insert a S, (u k ⊓ w (c k)) := by
          refine iSup_le fun j => iSup_le fun c => le_iSup_of_le (Function.update c a j) ?_
          rw [Finset.iInf_insert]
          refine inf_le_inf (by simp) (le_iInf₂ fun k hk => (iInf₂_le k hk).trans ?_)
          have hka : k ≠ a := fun h => ha (h ▸ hk)
          simp [hka]

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  intro K _ X q N m i y s S hS r r' j
  classical
  have e : capS (wK q i y s) S = KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    funext T
    apply propext
    constructor
    · intro hT
      obtain ⟨k0, hk0⟩ := hS
      refine ⟨(hT k0 hk0).1, ?_⟩
      have hc : ∀ k, ∃ c : Fin (N + 1), k ∈ S → InU (uy i y k ⊓ wch i c) T := by
        intro k
        by_cases hk : k ∈ S
        · obtain ⟨_, V, ⟨c, rfl⟩, hV⟩ := hT k hk
          exact ⟨c, fun _ => hV⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose c hc using hc
      exact ⟨_, ⟨c, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).2 hc⟩
    · rintro ⟨hT, V, ⟨c, rfl⟩, hV⟩ k hk
      exact ⟨hT, _, ⟨c k, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk⟩
  rw [e]
  have hle : KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) ≤
      KS q s {⨅ k ∈ S, uy i y k} := by
    rintro T ⟨hT, V, ⟨c, rfl⟩, hV⟩
    refine ⟨hT, _, Set.mem_singleton _, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (uy i y) S _).2 fun k hk => ?_⟩
    exact ((inU_inf _ _ _).1 ((GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk)).1
  have hc : ∀ W ∈ ({⨅ k ∈ S, uy i y k} : Set X.Opens),
      W ≤ sSup (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rw [sSup_range]
    exact isHecke_div_and_resEtaPow_div (uy i y) (wch i) (iSup_wch N i) S
  refine ⟨hle, ?_⟩
  rw [resU_eq]
  exact (GlobalTheory.CompanionTheory.NlZar.zariski_descent (CrystallineSemistableComparison.Pb.TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) _ _ hle hc j).1 r r'

end GlobalTheory.CompanionTheory.ConeZarCap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcMor

theorem chart_mor : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  intro O A _ _ _ I γ X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hO hA hvO hvA
  have hptT : pt (((nmO γ q).mor 0).obj cA.D) = pt cA.D := Category.comp_id _
  have hT : InU V (((nmO γ q).mor 0).obj cA.D) := by
    unfold InU
    rw [hptT]
    exact cA.inV
  obtain ⟨g, hg, -⟩ := cO.rep (CommRingCat.of ((((nmO γ q).mor 0).obj cA.D).B ⧸ (((nmO γ q).mor 0).obj cA.D).J))
    (((nmO γ q).mor 0).obj cA.D).y hT
  have hg' : (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map (CommRingCat.ofHom g) cO.D.y =
      (((nmO γ q).mor 0).obj cA.D).y := hg
  let ι : O ⊗[O] Γ(X, V) →+* A ⊗[O] Γ(X, V) :=
    (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V))).toRingHom
  let φ : cO.D.B →+* cA.D.B := (eA.toRingHom.comp ι).comp eO.symm.toRingHom
  have hφ : ∀ f, φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := fun f => by
    change eA (ι (eO.symm (eO (1 ⊗ₜ f)))) = _
    rw [RingEquiv.symm_apply_apply]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (1 ⊗ₜ f)) = _
    simp
  have hf : ∀ r, φ (cO.D.i r) = (((nmO γ q).mor 0).obj cA.D).i r := fun r => by
    change eA (ι (eO.symm (cO.D.i r))) = cA.D.i (algebraMap O A r)
    rw [← hO r, RingEquiv.symm_apply_apply, ← hA]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (r ⊗ₜ 1)) = _
    simp [Algebra.ofId_apply]
  have hptg : pt (((nmO γ q).mor 0).obj cA.D) = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D := by
    unfold pt
    rw [← hg']
    rfl
  have hev : ∀ f, ev cA.D cA.inV f = g (ev cO.D cO.inV f) := fun f => by
    have key : ∀ (y : Spec (CommRingCat.of (cA.D.B ⧸ cA.D.J)) ⟶ X) (_ : y = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D)
        (h'' : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V h'' f = g (ev cO.D cO.inV f) := by
      intro y hy h''
      subst hy
      exact GlobalTheory.LogCris.evalAt_map _ (pt cO.D) cO.inV h'' f
    exact key _ (hptT.symm.trans hptg) cA.inV
  have hq : (Ideal.Quotient.mk (((nmO γ q).mor 0).obj cA.D).J).comp φ = g.comp (Ideal.Quotient.mk cO.D.J) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨f, rfl⟩ : ∃ f, x = eO (1 ⊗ₜ f) := by
      refine ⟨TensorProduct.lid O Γ(X, V) (eO.symm x), ?_⟩
      have e : (1 : O) ⊗ₜ[O] (TensorProduct.lid O Γ(X, V) (eO.symm x)) = eO.symm x :=
        (TensorProduct.lid O Γ(X, V)).symm_apply_apply (eO.symm x)
      rw [e, RingEquiv.apply_symm_apply]
    change Ideal.Quotient.mk cA.D.J (φ (eO (1 ⊗ₜ f))) = g (Ideal.Quotient.mk cO.D.J (eO (1 ⊗ₜ f)))
    rw [hφ, ← hvA, ← hvO, hev]
  exact ⟨GlobalTheory.CompanionTheory.ChartMaps.homOf cO (((nmO γ q).mor 0).obj cA.D) φ hf g hq hg', hφ⟩

end GlobalTheory.CompanionTheory.BcMor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordNear
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem coord_near : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] {V' : X.Opens}, IsAffineOpen V' → ∀ x : X, x ∈ V' →
    ∃ (f : Γ(X, V')) (e : ℕ) (c : Coord q (X.basicOpen f) e), x ∈ X.basicOpen f := by
  intro K _ X q _ V' hV x hx
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V' le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
  obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
    RingHom.isStandardSmooth_respectsIso q hV h hx
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨f, n, (GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he).some, hf⟩

end GlobalTheory.CompanionTheory.ConeLocal
end

