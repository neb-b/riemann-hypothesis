module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwAcrFromBase
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaGal

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dd_twAcr (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) :
    IsDPMorphism (DD k (tw σ A) n) (DD k A n) (twAcr σ A n) := by
  cases k
  exacts [dp_twAcr A σ n, dpP_twAcr A σ n]

theorem twAcr_fromBase (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (r : (base l).Acr n) :
    twAcr σ A n (mapAcr (tw σ A).fromBase n r) = mapAcr A.fromBase n (galBase σ n r) := by
  have e : (tw σ A).fromBase = baseTw σ ≫ twMap σ A.fromBase := (fromBase_comp _ (twMap σ A.fromBase)).symm
  rw [e, mapAcr_comp, twAcr_mapAcr]
  rfl

theorem uJ_tw (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (h) (x : (tw σ A).U) :
    Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n x) = uJ k A n (twU σ A x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n ((tw σ A).th w)) = uJ k A n (twU σ A ((tw σ A).th w))
  rw [uJ_th, twU_th, uJ_th, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) ((pdOk_twId σ A).acr_toAcr n w)

theorem map3 (P : CommRingCat.{0} ⥤ Type) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (e : A →+* D) (he : ∀ x, h (g (f x)) = e x) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom h) (P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y)) = P.map (CommRingCat.ofHom e) y := by
  have e' : CommRingCat.ofHom f ≫ CommRingCat.ofHom g ≫ CommRingCat.ofHom h = CommRingCat.ofHom e :=
    CommRingCat.hom_ext (RingHom.ext he)
  rw [← e', Functor.map_comp_apply, Functor.map_comp_apply]

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (σ : Gal(PadicAlgCl l/K))
  (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ)

def etaGal (T : El (F.pt κ)) :
    (gT F κ k n).obj ((elTw σ (ptTw F κ σ hσ)).obj T) ⟶ (SH.galM F κ σ hσ k n).obj ((gT F κ k n).obj T) :=
  crHom (twAcr σ T.1.obj n) (twAcr_fromBase σ T.1.obj n) (dd_twAcr k σ T.1.obj n) fun h =>
    map3 F.Pt (twUEquiv σ T.1.obj).symm.toRingHom (uJ k (tw σ T.1.obj) n) (Ideal.quotientMap _ (twAcr σ T.1.obj n) h)
      (uJ k T.1.obj n) (fun x => (uJ_tw k σ T.1.obj n h _).trans
        (congrArg (uJ k T.1.obj n) ((twUEquiv σ T.1.obj).apply_symm_apply x))) T.2.1

theorem β_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) := by
  intro l _ O _ F κ K σ hσ k n j x
  have h1 := pull_pull (ACris.galCris σ) (galMorC F κ σ hσ k n) (βMor F κ k n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMor F κ k n) (galMor σ (ptTw F κ σ hσ) n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (cr_pull_eq ((βMor F κ k n).comp (σ'' := ACris.galCris σ) (galMor σ (ptTw F κ σ hσ) n))
    ((galMorC F κ σ hσ k n).comp (σ'' := ACris.galCris σ) (βMor F κ k n)) (etaGal F κ σ hσ k n)
    (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.BetaGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidue
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem uniformiser_facts : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.algebraIsIntegral
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) :=
    (algebraMap_isIntegral_iff.mpr hi).isLocalHom hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have hnt : Nontrivial (↥(OL K) ⧸ Ideal.span {π}) := by
    refine Ideal.Quotient.nontrivial_iff.2 ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hπ.not_isUnit
  have h2 : 2 ≤ qOf π := Finite.one_lt_card
  have hord : addOrderOf (1 : ↥(OL K) ⧸ Ideal.span {π}) = l := by
    have h1 : (1 : ↥(OL K) ⧸ Ideal.span {π}) ≠ 0 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ne, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    refine addOrderOf_eq_prime ?_ h1
    rw [nsmul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {π})),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hq : l ∣ qOf π := by
    have := addOrderOf_dvd_natCard (1 : ↥(OL K) ⧸ Ideal.span {π})
    rwa [hord] at this
  have hl0 : ((l : ℕ) : ↥(OL K)) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) h
    simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
    exact hlp.ne_zero (by exact_mod_cast h2)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  have he : e ≠ 0 := by
    rintro rfl
    apply hl
    rw [pow_zero] at hu
    exact IsUnit.of_mul_eq_one _ hu
  have hnorm : ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
    intro μ
    rw [PadicComplex.norm_extends]
    have hint : ∀ x : ↥(OL K), ‖μ (x : ↥K.1)‖ ≤ 1 := by
      intro x
      rw [← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact (x.2 : IsIntegral ℤ_[l] (x : ↥K.1)).map (μ.restrictScalars ℤ_[l])
    have hpow : (π : ↥K.1) ^ e = (l : ↥K.1) * ((u : ↥(OL K)) : ↥K.1) := by
      have := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) hu
      simpa using this.symm
    have h3 : ‖μ (π : ↥K.1)‖ ^ e < 1 := by
      rw [← norm_pow, ← map_pow, hpow, map_mul, norm_mul, map_natCast,
        ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) Padic.norm_p_lt_one (hint _)
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 h3
  exact ⟨h2, hq, hdvd, hnorm K.1.val, hnorm⟩

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsAbs
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernComparison

open CrystallineSemistableComparison.CH

universe w w' u v u' v' u'' v''

section Coh
variable {R : Type} [CommRing R] {Th : Type u} [Category.{v} Th] {Ec : Type u'} [Category.{v'} Ec]
  {C : Type u''} [Category.{v''} C]

theorem pull_transport (F : Th ⥤ ModuleCat.{w} R) (F' : Ec ⥤ ModuleCat.{w'} R) (m : Mor F F' (RingHom.id R)) (G : C ⥤ Ec)
    (x : H F 2) (c : Cn ((G ⋙ m.G) ⋙ F) 2) (hc : d _ 2 c = 0)
    (h : (cx _).cls c hc = (Mor.restrict F (G ⋙ m.G)).pull 2 x) :
    ∃ hz : d (G ⋙ F') 2 (fun s => m.τ _ (c s)) = 0,
      (cx _).cls _ hz = (Mor.restrict F' G).pull 2 (m.pull 2 x) := by
  let m' : Mor ((G ⋙ m.G) ⋙ F) (G ⋙ F') (RingHom.id R) :=
    ⟨𝟭 _, fun T => m.τ (G.obj T), fun φ x => m.nat (G.map φ) x⟩
  have hz : d (G ⋙ F') 2 (fun s => m.τ _ (c s)) = 0 := by
    have := m'.d_pullC 2 c
    rw [hc, map_zero] at this
    exact this
  refine ⟨hz, ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 c hc hz
  have e2 : (Mor.restrict F' G).pull 2 (m.pull 2 x) = m'.pull 2 ((Mor.restrict F (G ⋙ m.G)).pull 2 x) := by
    have a := (CrystallineSemistableComparison.P.pull_comp m (Mor.restrict F' G) 2 x).1
    have b := (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F (G ⋙ m.G)) m' 2 x).1
    exact a.symm.trans b
  rw [e2, ← h]
  exact e1.symm

end Coh

section Line
variable {X : Scheme.{0}}

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem u_map (D : E.LineData X) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) (a' b' : Spec (CommRingCat.of B) ⟶ D.Y)
    (ha : a' = Spec.map (CommRingCat.ofHom f) ≫ a) (hb : b' = Spec.map (CommRingCat.ofHom f) ≫ b)
    (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (D.u a' b' h') =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (D.u a b h)) := by
  subst ha hb
  rw [D.nat (Spec.map (CommRingCat.ofHom f)) a b h, ← gamma_nat]
  rfl

theorem u_coc (D : E.LineData X) {U₀ U₁ U₂ : Type} [CommRing U₀] [CommRing U₁] [CommRing U₂]
    (f₁ : U₀ →+* U₁) (f₂ : U₁ →+* U₂) (f₃ : U₀ →+* U₂) (hf : f₃ = f₂.comp f₁)
    (p₀ : Spec (CommRingCat.of U₀) ⟶ D.Y) (p₁ : Spec (CommRingCat.of U₁) ⟶ D.Y) (p₂ : Spec (CommRingCat.of U₂) ⟶ D.Y)
    (h₁ : (Spec.map (CommRingCat.ofHom f₁) ≫ p₀) ≫ D.f = p₁ ≫ D.f)
    (h₂ : (Spec.map (CommRingCat.ofHom f₂) ≫ p₁) ≫ D.f = p₂ ≫ D.f)
    (h₃ : (Spec.map (CommRingCat.ofHom f₃) ≫ p₀) ≫ D.f = p₂ ≫ D.f) :
    f₂ ((Scheme.ΓSpecIso (CommRingCat.of U₁)).hom.hom (D.u _ _ h₁)) *
      (Scheme.ΓSpecIso (CommRingCat.of U₂)).hom.hom (D.u _ _ h₂) =
      (Scheme.ΓSpecIso (CommRingCat.of U₂)).hom.hom (D.u _ _ h₃) := by
  subst hf
  have e : Spec.map (CommRingCat.ofHom (f₂.comp f₁)) = Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h12 : (Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) ≫ p₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom f₂) ≫ p₁) ≫ D.f := by
    simpa only [Category.assoc] using congrArg (Spec.map (CommRingCat.ofHom f₂) ≫ ·) h₁
  have A := u_map D f₂ _ _ h₁ _ _ rfl rfl h12
  have c := D.coc _ _ _ h12 h₂
  have e3 : ∀ (a : Spec (CommRingCat.of U₂) ⟶ D.Y) (ha : a = Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) ≫ p₀)
      (hh : a ≫ D.f = p₂ ≫ D.f), D.u a p₂ hh = D.u _ p₂ (h12.trans h₂) := by
    intro a ha hh; subst ha; rfl
  rw [← A, ← map_mul, ← Units.val_mul, c, e3 _ (by rw [e, Category.assoc]) h₃]

theorem u_square (D : E.LineData X) {U U' Q Q' : Type} [CommRing U] [CommRing U'] [CommRing Q] [CommRing Q']
    (m : U →+* U') (g : U →+* Q) (g' : U' →+* Q') (t : Q →+* Q') (comm : t.comp g = g'.comp m)
    (pT : Spec (CommRingCat.of U) ⟶ D.Y) (pT' : Spec (CommRingCat.of U') ⟶ D.Y)
    (h' : (Spec.map (CommRingCat.ofHom m) ≫ pT) ≫ D.f = pT' ≫ D.f)
    (h : (Spec.map (CommRingCat.ofHom t) ≫ Spec.map (CommRingCat.ofHom g) ≫ pT) ≫ D.f =
      (Spec.map (CommRingCat.ofHom g') ≫ pT') ≫ D.f) :
    (Scheme.ΓSpecIso (CommRingCat.of Q')).hom.hom (D.u _ _ h) =
      g' ((Scheme.ΓSpecIso (CommRingCat.of U')).hom.hom (D.u _ _ h')) := by
  refine u_map D g' _ _ h' _ _ ?_ rfl h
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comm]

end Line

section Log
variable {l : ℕ} [Fact l.Prime]

theorem dxi_mem (k : Bool) (A : PAlg l) (n : ℕ) : A.dxi n 1 ∈ JJ k A n :=
  fil_le k A n (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem dd_dxi (k : Bool) (A : PAlg l) (n m : ℕ) : (DD k A n).dpow m (A.dxi n 1) = A.dxi n m := by
  cases k
  · exact A.dpow_dxi n m
  · have h := (A.dp_fil_pfil n).2 (A.dxi n 1) (Ideal.subset_span ⟨1, le_rfl, rfl⟩) (n := m)
    exact h.trans (A.dpow_dxi n m)

theorem isLog_dlog (k : Bool) (A : PAlg l) (n : ℕ) (u : A.A) (hu : A.sharp u = 1) (v : A.Acr n)
    (hv : v = A.toAcr n (WittVector.teichmuller l u)) :
    E.IsLog A n (WittVector.teichmuller l u) (dlog (DD k A n) (l * n) v) := by
  have h1 : WittVector.teichmuller l u - 1 ∈ Ideal.span {A.xi} := by
    have h0 : A.th (WittVector.teichmuller l u - 1) = 0 := by
      rw [map_sub, map_one]; exact sub_eq_zero.2 hu
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  refine ⟨fun m => algebraMap A.W A.Acr0 c ^ m * A.dxi0 m, fun m => ?_, ?_⟩
  · rw [← hc]
    change algebraMap A.W (Localization.Away (l : A.W)) c ^ m * dpw m A.xi = dpw m (c * A.xi)
    simp only [dpw, map_mul, mul_pow]; ring
  · have hd : v - 1 = A.toAcr n c * A.dxi n 1 := by
      rw [hv, ← toAcr_xi, ← map_mul, hc, map_sub, map_one]
    simp only [dlog, hd]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [DividedPowers.dpow_mul _ (dxi_mem k A n), dd_dxi, map_mul, map_pow]
    rfl

end Log

section Pts
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X}

theorem pt_hom {T T' : C} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (mapU (G.map φ).1.hom)) ≫ (G.obj T).2.1 = (G.obj T').2.1 :=
  congrArg Subtype.val (G.map φ).2

theorem lift_h (Λ : E.Lift G D) {T T' : C} (φ : T ⟶ T') :
    (Spec.map (CommRingCat.ofHom (mapU (G.map φ).1.hom)) ≫ Λ.p T) ≫ D.f = Λ.p T' ≫ D.f := by
  rw [Category.assoc, Λ.hp, Λ.hp]; exact pt_hom φ

theorem mapU_sharp' {A A' : PAlg l} (f : A ⟶ A') (a : A.A) : mapU f (A.sharp a) = A'.sharp (PAlg.Hom.f f a) := by
  change A'.th (mapW f (WittVector.teichmuller l a)) = _
  rw [mapW, WittVector.map_teichmuller]
  rfl

theorem sharp_r (Λ : E.Lift G D) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    (G.obj c₂).1.obj.sharp ((Units.map (PAlg.Hom.f (G.map b).1.hom).toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ :
      ((G.obj c₂).1.obj.A)ˣ) : (G.obj c₂).1.obj.A) = 1 := by
  subst hc
  have wa := Λ.hw a (lift_h Λ a)
  have wb := Λ.hw b (lift_h Λ b)
  have wc := Λ.hw (a ≫ b) (lift_h Λ (a ≫ b))
  have key := u_coc D (mapU (G.map a).1.hom) (mapU (G.map b).1.hom) (mapU (G.map (a ≫ b)).1.hom)
    (by rw [G.map_comp]; exact mapU_comp _ _) (Λ.p c₀) (Λ.p c₁) (Λ.p c₂) (lift_h Λ a) (lift_h Λ b) (lift_h Λ (a ≫ b))
  rw [← wa, ← wb, ← wc, mapU_sharp', ← map_mul] at key
  rw [Units.val_mul, Units.val_mul, map_mul]
  change (G.obj c₂).1.obj.sharp (PAlg.Hom.f (G.map b).1.hom (Λ.w a) * Λ.w b) * _ = 1
  rw [key, ← map_mul, Units.mul_inv, map_one]

end Pts

section Main
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X}

def tm (A : PAlg l) (n : ℕ) : A.A →* A.Acr n :=
  (A.toAcr n).toMonoidHom.comp (WittVector.teichmuller l)

variable (k : Bool) (n : ℕ)

abbrev gG (G : C ⥤ El (PX q κ)) : C ⥤ Thick (Lc (schFn q) κ k n) := G ⋙ gT (schFn q) κ k n

def lam (Λ : E.Lift G D) : CLift (gG k n G) D where
  p T := Spec.map (CommRingCat.ofHom (uJ k (G.obj T).1.obj n)) ≫ Λ.p T
  hp T := by
    rw [Category.assoc, Λ.hp]
    rfl
  w {T T'} φ := Units.map (tm (G.obj T').1.obj n) (Λ.w φ)
  hw {T T'} φ h := by
    have e := u_square D (mapU (G.map φ).1.hom) (uJ k (G.obj T).1.obj n) (uJ k (G.obj T').1.obj n)
      (Ideal.quotientMap _ (mapAcr (G.map φ).1.hom n) (jj_le k (G.map φ).1.hom n)) (uJ_map k (G.map φ).1.hom n)
      (Λ.p T) (Λ.p T') (lift_h Λ φ) h
    refine Eq.trans ?_ e.symm
    rw [← Λ.hw φ (lift_h Λ φ)]
    exact uJ_th k _ n (WittVector.teichmuller l (Λ.w φ).val) |>.symm

theorem units_abs {A₁ A₂ B₁ B₂ : Type} [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂] (t₁ : A₁ →* B₁) (t₂ : A₂ →* B₂)
    (f : A₁ →+* A₂) (g : B₁ →+* B₂) (h : ∀ x, g (t₁ x) = t₂ (f x)) (wa : A₁ˣ) (wb wc : A₂ˣ) :
    Units.map g.toMonoidHom (Units.map t₁ wa) * Units.map t₂ wb * (Units.map t₂ wc)⁻¹ =
      Units.map t₂ (Units.map f.toMonoidHom wa * wb * wc⁻¹) := by
  rw [map_mul, map_mul, map_inv]
  congr 2
  exact Units.ext (h _)

theorem tm_map {A A' : PAlg l} (f : A ⟶ A') (x : A.A) : mapAcr f n (tm A n x) = tm A' n (PAlg.Hom.f f x) := by
  change mapAcr f n (A.toAcr n (WittVector.teichmuller l x)) = A'.toAcr n (WittVector.teichmuller l (PAlg.Hom.f f x))
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem lam_r' (Λ : E.Lift G D) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) :
    Units.map ((gG k n G).map b).φ.toMonoidHom ((lam k n Λ).w a) * (lam k n Λ).w b * ((lam k n Λ).w c)⁻¹ =
      Units.map (tm (G.obj c₂).1.obj n) (Units.map (PAlg.Hom.f (G.map b).1.hom).toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹) :=
  units_abs (tm (G.obj c₁).1.obj n) (tm (G.obj c₂).1.obj n) (PAlg.Hom.f (G.map b).1.hom) (mapAcr (G.map b).1.hom n)
    (tm_map n (G.map b).1.hom) (Λ.w a) (Λ.w b) (Λ.w c)

theorem lam_r (Λ : E.Lift G D) (s : ComposableArrows C 2) :
    ((lam k n Λ).r s).val = (G.obj (s.obj (Fin.last 2))).1.obj.toAcr n (WittVector.teichmuller l (Λ.r s).val) :=
  congrArg Units.val (lam_r' k n Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2))

end Main

end GlobalTheory.CompanionTheory.FirstChernComparison
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsPullbackEmptyProductOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaPull

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄

theorem pull_square {R : Type} [CommRing R]
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R}
    {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (m : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₃ (RingHom.id R))
    (b' : CH.Mor F₁ F₄ (RingHom.id R)) (q : CH.Mor F₄ F₃ (RingHom.id R))
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x))
    (n : ℕ) (x : CH.H F₁ n) : b.pull n (m.pull n x) = q.pull n (b'.pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m b n x).1,
    ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b' q n x).1]
  exact CrystallineSemistableComparison.P.prism (m.comp b) (b'.comp q) η hτ n x

theorem pt_nat {P P' : CommRingCat.{0} ⥤ Type} (a : P ⟶ P') {B C : CommRingCat.{0}} (f : B ⟶ C)
    (g : C ⟶ C) (hg : g = 𝟙 C) (y : P.obj B) :
    P'.map g (a.app C (P.map f y)) = P'.map f (a.app B y) := by
  subst hg
  rw [P'.map_id]
  exact ConcreteCategory.congr_hom (a.naturality f) y

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
  (u : Fn.Map F F') (k : Bool) (n : ℕ)

theorem units_pullback_empty_product_one {B B' : Type} [CommRing B] [CommRing B'] (i : B' →+* B) (a : B'ˣ) (ha : a = 1)
    (e : Empty → Bˣ) : (1 : Bˣ) =
      (∏ j, e j) * Units.map (RingHom.id B).toMonoidHom ((1 : Bˣ) ^ 1 * (Units.map i.toMonoidHom a)⁻¹) := by
  subst ha
  simp

def cmpHom (T : El (F.pt κ)) :
    (gT F κ k n ⋙ (pullMorC κ u k n).G).obj T ⟶ ((pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G).obj T where
  φ := RingHom.id _
  u := fun j => j.elim
  comm _ := rfl
  dp := (DPMorphism.id _).isDPMorphism
  hle := fun _ h => h
  pt := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    · exact pt_nat u.u (CommRingCat.ofHom (uJ k T.1.obj n))
        (CommRingCat.ofHom (Ideal.quotientMap _ (RingHom.id _) fun _ h => h))
        (CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))) T.2.1
  hx := fun j => j.elim
  hs := units_pullback_empty_product_one _ _ rfl _
  hv := fun j => j.elim

def cmpNat : gT F κ k n ⋙ (pullMorC κ u k n).G ⟶ (pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G where
  app T := cmpHom κ u k n T
  naturality T T' f := Thick.Hom.ext rfl (funext fun j => j.elim)

theorem beta_pull {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
    (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j) :
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  pull_square (pullMorC κ u k n) (βMor F κ k n) (βMor F' κ k n) (pullMor (u.pt κ) n)
    (cmpNat κ u k n) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaPull
end
end

