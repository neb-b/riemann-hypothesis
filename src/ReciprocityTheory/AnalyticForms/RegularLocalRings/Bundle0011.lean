module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0008
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.EvalValChartCoord
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

namespace AffPres

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)} (P : AffPres s)

theorem secHom_surj : Function.Surjective P.secHom := by
  intro t
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).hom (P.iso.inv.appTop (P.V.topIso.inv t)))
  refine ⟨a, ?_⟩
  show P.V.topIso.hom (P.iso.hom.appTop ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk P.K a))) = t
  rw [ha, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply,
    ← CommRingCat.comp_apply P.iso.inv.appTop, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
    Scheme.Hom.id_appTop, CommRingCat.id_apply, ← CommRingCat.comp_apply P.V.topIso.inv, Iso.inv_hom_id,
    CommRingCat.id_apply]

theorem isAffineOpen_V' : IsAffineOpen P.V := by
  have : IsAffine P.V.toScheme := IsAffine.of_isIso P.iso.hom
  exact this

end AffPres

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)

theorem eval_val_chartCoord (p : (k : K) → ι k) (y : projX P hP) (hy : y ∈ (chartOpen hP p).1)
    (hc : IsClosed ({y} : Set (projX P hP))) (f : MvPolynomial (Σ k, ι k) ℂ) :
    eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy) f =
      val (toSpecC hP) ((gammaChart hP p).symm (Ideal.Quotient.mk _ f)) y hy := by
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 y hy hc
  have h := MvPolynomial.ringHom_ext
    (f := eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy))
    (g := φ.comp ((gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p)))) ?_ ?_
  · exact (RingHom.congr_fun h f).trans (hφ _)
  · intro a
    rw [eval_C, RingHom.comp_apply, RingHom.comp_apply, hφ]
    show a = val _ ((gammaChart hP p).symm (Ideal.Quotient.mk _ (C a))) y hy
    rw [gammaChart_symm_C, val_const _ _ y hy hc]
  · intro q
    rw [eval_X, RingHom.comp_apply, RingHom.comp_apply, hφ]
    rfl

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem iSup_chartOpen_eq_top {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    (⨆ p : (k : K) → ι k, ((chartOpen hP p).1 : (projX P hP).Opens)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hp⟩

theorem isNoetherianRing_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) : IsNoetherianRing Γ(projX P hP, (chartOpen hP p).1) :=
  isNoetherianRing_of_ringEquiv _ (gammaChart hP p).symm

theorem isReduced_away {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) (p : (k : K) → ι k) :
    letI := segreGraded hP
    _root_.IsReduced (HomogeneousLocalization.Away (segreGrading P) (segreW P p)) := by
  letI := segreGraded hP
  have : _root_.IsReduced (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (hrad.comap _)
  exact isReduced_of_injective (algebraMap _ (Localization.Away (segreW P p)))
    (HomogeneousLocalization.val_injective _)

theorem isReduced_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) (p : (k : K) → ι k) :
    _root_.IsReduced Γ(projX P hP, (chartOpen hP p).1) := by
  letI := segreGraded hP
  letI := isReduced_away hP hrad p
  exact isReduced_of_injective _ ((gammaChart hP p).trans (awayEquiv hP p)).injective

theorem qeRing_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) (p : (k : K) → ι k) : FinalTheorems.QERing Γ(projX P hP, (chartOpen hP p).1) := by
  letI : Algebra ℂ Γ(projX P hP, (chartOpen hP p).1) :=
    ((gammaChart hP p).symm.toRingHom.comp (algebraMap ℂ (chartRing P p))).toAlgebra
  let e : chartRing P p ≃ₐ[ℂ] Γ(projX P hP, (chartOpen hP p).1) :=
    AlgEquiv.ofRingEquiv (f := (gammaChart hP p).symm) (fun c => rfl)
  haveI : Algebra.FiniteType ℂ Γ(projX P hP, (chartOpen hP p).1) :=
    Algebra.FiniteType.equiv inferInstance e
  exact hQE Γ(projX P hP, (chartOpen hP p).1)

theorem isRegularLocalRing_stalk_fromSpec_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec y)) ↔
      IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
    (X.presheaf.stalk (hU.fromSpec y))
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun h => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩

theorem isOpen_regularLocus_of_cover {X : Scheme.{0}} {J : Type} (U : J → X.affineOpens)
    (hcov : ∀ x, ∃ i, x ∈ (U i).1)
    (h : ∀ i, IsOpen {Q : PrimeSpectrum Γ(X, (U i).1) |
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}) :
    IsOpen {x : X | IsRegularLocalRing (X.presheaf.stalk x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, hi⟩ := hcov x
  have hU : IsAffineOpen (U i).1 := (U i).2
  refine ⟨(⇑hU.fromSpec) '' {Q : PrimeSpectrum Γ(X, (U i).1) |
    IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : hU.fromSpec q ∈ (U i).1 := hU.range_fromSpec.le ⟨q, rfl⟩
    exact (isRegularLocalRing_stalk_fromSpec_iff hU q hq').mpr hq
  · exact (IsAffineOpen.fromSpec hU).isOpenEmbedding.isOpenMap _ (h i)
  · refine ⟨hU.primeIdealOf ⟨x, hi⟩, ?_, hU.fromSpec_primeIdealOf ⟨x, hi⟩⟩
    have h1 := hU.fromSpec_primeIdealOf ⟨x, hi⟩
    have h2 := isRegularLocalRing_stalk_fromSpec_iff hU (hU.primeIdealOf ⟨x, hi⟩) (by rw [h1]; exact hi)
    rw [h1] at h2
    exact h2.mp hx

theorem eval₂_smul_of_isMultiHomog' {R : Type} [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → R)
    (y : (Σ k, ι k) → R) :
    eval₂ g (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval₂ g y f := by
  classical
  rw [f.as_sum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo hmo => ?_
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_sigma]
  have hk : ∀ k, ∏ i, c k ^ mo ⟨k, i⟩ = c k ^ a k := by
    intro k
    rw [Finset.prod_pow_eq_pow_sum, hf mo hmo k]
  simp only [hk]
  ring

theorem isUnit_mapId_mk_iff {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (f : A) (x : ProjectiveSpectrum 𝒜)
    (H : Submonoid.powers f ≤ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    IsUnit (HomogeneousLocalization.mapId 𝒜 H (HomogeneousLocalization.mk z)) ↔
      z.num.1 ∉ x.asHomogeneousIdeal := by
  have hv : (HomogeneousLocalization.mapId 𝒜 H (HomogeneousLocalization.mk z)).val =
      IsLocalization.mk' (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (z.num : A)
        (⟨z.den, H z.den_mem⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
    rw [← Localization.mk_eq_mk']; rfl
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, hv, IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem evaluation_awayToSection_eq_zero_iff {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (f : A) (x : Proj 𝒜)
    (hx : x ∈ Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (Proj 𝒜).evaluation (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)) = 0 ↔
      z.num.1 ∈ ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := 𝒜) x := by
  have e1 : (Proj 𝒜).evaluation (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)) = 0 ↔
      ¬ IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))) :=
    (IsLocalRing.residue_eq_zero_iff _).trans (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact Iff.rfl)
  refine e1.trans ?_
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.mk z))
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f x hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  have h2 := (Iff.of_eq (congrArg IsUnit h)).trans
    (isUnit_map_iff (Proj.stalkIso' 𝒜 x).symm _)
  refine (Iff.not h2).trans ?_
  let x' : ProjectiveSpectrum 𝒜 := x
  have H : Submonoid.powers f ≤ x'.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr (by exact hx)
  exact (not_congr (isUnit_mapId_mk_iff 𝒜 f x' H z)).trans not_not

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultB
section
namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory MvPolynomial

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

theorem secHom_surjective (P : AffPres s) : Function.Surjective P.secHom := by
  unfold AffPres.secHom
  rw [RingHom.coe_comp, RingHom.coe_comp, RingHom.coe_comp]
  have i1 : IsIso P.iso.hom.appTop := by
    have : IsIso (Scheme.Γ.map P.iso.hom.op) := inferInstance
    simpa using this
  refine (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso P.iso.hom.appTop).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv).2.comp ?_
  exact Ideal.Quotient.mk_surjective

theorem isUnit_algebraMap_of_eval_ne_zero {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin n → ℂ) {g : MvPolynomial (Fin n) ℂ} (hg : eval p g ≠ 0) :
    IsUnit (algebraMap _ (locRing K p) g) := by
  have hg' : g ∉ ptIdeal p := fun h => hg (RingHom.mem_ker.mp h)
  have := (IsLocalization.map_units (locPt p) (⟨g, hg'⟩ : (ptIdeal p).primeCompl)).map
    (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K))
  rwa [Ideal.Quotient.mk_algebraMap] at this

theorem algebraMap_eq_zero_of_mem {n : ℕ} {K : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin n → ℂ)
    {k : MvPolynomial (Fin n) ℂ} (hk : k ∈ K) : algebraMap _ (locRing K p) k = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hk

theorem map_bd_eq_span {m : ℕ} {I bd : Ideal (MvPolynomial (Fin m) ℂ)} {p : Fin m → ℂ} {e rc : ℕ}
    (S : SncData I bd p e rc) :
    Ideal.map (algebraMap _ (locRing I p)) bd =
      Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by
  obtain ⟨v, hv⟩ := isUnit_algebraMap_of_eval_ne_zero I p S.eval_h
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    have h1 := S.le_span g hg
    have h3 : Ideal.map (algebraMap _ (locRing I p)) (Ideal.span {∏ l ∈ S.J, S.r l} ⊔ I) ≤
        Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_prod]
      refine sup_le le_rfl ?_
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, algebraMap_eq_zero_of_mem p hk]
      exact Ideal.zero_mem _
    have h2 := h3 (Ideal.mem_map_of_mem _ h1)
    rw [map_mul] at h2
    have he : algebraMap _ (locRing I p) g =
        ↑v⁻¹ * (algebraMap _ (locRing I p) S.h * algebraMap _ (locRing I p) g) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ h2
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 := Ideal.mem_map_of_mem (algebraMap _ (locRing I p)) S.mem_bd
    rw [map_mul, map_prod] at h1
    have he : ∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l) =
        ↑v⁻¹ * (algebraMap _ (locRing I p) S.h * ∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ h1

theorem stalkId_eq_span_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.stalkId Z x = Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))} := by
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  have hsecmap : Z.ideal P.affOpen = Ideal.map P.secHom (P.bdIdeal Z) :=
    (Ideal.map_comap_of_surjective _ (secHom_surjective P) _).symm
  have hcompψ : (((P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx)).comp
      (W.presheaf.germ P.V x hx).hom).comp P.secHom) =
      algebraMap _ (locRing P.K (P.coord x hx)) :=
    RingHom.ext hψ
  have e1 : Ideal.map (P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx))
      (FinalTheorems.stalkId Z x) =
      Ideal.map (P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx))
        (Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))}) := by
    have hZmap : FinalTheorems.stalkId Z x = Ideal.map (W.presheaf.germ P.V x hx).hom
        (Ideal.map P.secHom (P.bdIdeal Z)) := by
      rw [← hsecmap]; exact stalkId_eq_map_germ Z x P.affOpen hx
    rw [hZmap, Ideal.map_map, Ideal.map_map, hcompψ, map_bd_eq_span S,
      Ideal.map_span, Set.image_singleton, map_prod]
    simp only [RingHom.coe_coe, hψ]
  have := congrArg (Ideal.map ((P.stalkEquiv x hx hcl).symm :
    locRing P.K (P.coord x hx) →+* W.presheaf.stalk x)) e1
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem rsp_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (hdim : ringKrullDim (W.presheaf.stalk x) = e)
    (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.Rsp (W.presheaf.stalk x) e (fun l => W.presheaf.germ P.V x hx (P.secHom (S.r l))) := by
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  rw [P.rsp_iff x hx hcl]
  refine ⟨?_, ?_⟩
  · simp only [hψ]
    exact S.span_eq
  · rw [← P.ringKrullDim_stalk x hx hcl, hdim]

end ReciprocityTheory.AnForm.R.WMult
end

