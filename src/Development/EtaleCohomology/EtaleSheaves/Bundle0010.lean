module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0007
public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.LineHigh

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.CoverPf

def EmptyVan : Prop := A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ) (S : Type) [CommRing S], Subsingleton S →
  ∀ x : Ht q (sp S) (n + 1) i, x = 0

theorem pull_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (q : ℕ) (m i : ℤ)
    (x : Ht q (sp A) m i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  have : spMap (g.comp f) = spMap g ≫ spMap f := by simp [spMap]
  rw [this, pull_comp]

theorem dies_of_factor {S : Type} [CommRing S] {q : ℕ} {m i : ℤ} (x : Ht q (sp S) m i) (f : S)
    (hx : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    {T : Type} [CommRing T] (φ : S →+* T) (hu : IsUnit (φ f)) : pull _ (spMap φ) _ _ x = 0 := by
  have e : φ = (IsLocalization.Away.lift f (S := Localization.Away f) hu).comp (algebraMap S (Localization.Away f)) :=
    (IsLocalization.Away.lift_comp f (S := Localization.Away f) hu).symm
  rw [e, pull_comp', hx, map_zero]

theorem dies_add (hQ : QAClosed) (hM : MV) (h1 : A1) {q : ℕ} {i n : ℤ} (hk : MVHyp q i n)
    {S : Type} [CommRing S] (hS : QA S) (hq : IsUnit (q : S)) (x : Ht q (sp S) (n + 1) i) (f g : S)
    (hf : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    (hg : pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0) :
    pull _ (spMap (algebraMap S (Localization.Away (f + g)))) _ _ x = 0 := by
  set T := Localization.Away (f + g)
  set φ := algebraMap S T
  have hT : QA T := (hQ S hS).2.1 (f + g)
  have hqT : IsUnit (q : T) := by simpa using hq.map φ
  have hspan : Ideal.span {φ f, φ g} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := T) (f + g)
    have hmem : φ (f + g) ∈ Ideal.span {φ f, φ g} := by
      rw [map_add (f := _)]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    have : (1 : T) = ((u⁻¹ : Tˣ) : T) * φ (f + g) := by
      change (1 : T) = ((u⁻¹ : Tˣ) : T) * algebraMap S T (f + g)
      rw [← hu]; simp
    rw [this]; exact Ideal.mul_mem_left _ _ hmem
  have key := hM h1 (ZMod q) (tw q i) T (φ f) (φ g) hspan n (hk T hT hqT (φ f) (φ g) hspan)
    (pull _ (spMap φ) _ _ x)
  apply key
  · rw [← pull_comp']
    exact dies_of_factor x f hf _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))
  · rw [← pull_comp']
    exact dies_of_factor x g hg _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ g)) (φ g))

theorem Cover_of (hE : EmptyVan) : LateralTheory.E.AcycQAPf.Cover := by
  intro hQ hM h1 q _ i n hk S _ hS hq x hloc
  let I : Set S := {g | pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0}
  have hmul : ∀ a g, g ∈ I → a * g ∈ I := by
    intro a g hg
    refine dies_of_factor x g hg _ ?_
    exact isUnit_of_mul_isUnit_right (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a * g)) (a * g)
      |>.map (RingHom.id _) |> fun h => by simpa [map_mul] using h)
  have hadd : ∀ f g, f ∈ I → g ∈ I → f + g ∈ I := fun f g hf hg => dies_add hQ hM h1 hk hS hq x f g hf hg
  have hspan : Ideal.span I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM', hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hfM, hf⟩ := hloc ⟨M, hM'.isPrime⟩
    exact hfM (hle (Ideal.subset_span hf))
  have hP : ∀ y ∈ Ideal.span I, y ∈ I ∨ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Or.inl hy
    | zero => exact Or.inr rfl
    | add a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (hadd a b ha hb)
      · subst hb; simpa using Or.inl ha
      · subst ha; simpa using Or.inl hb
      · subst ha; subst hb; simp
    | smul a b _ hb =>
      rcases hb with hb | hb
      · exact Or.inl (hmul a b hb)
      · subst hb; simp
  rcases hP 1 (by rw [hspan]; trivial) with h | h
  · have := dies_of_factor x 1 h (RingHom.id S) isUnit_one
    have e : spMap (RingHom.id S) = 𝟙 _ := by simp [spMap]
    rwa [e, pull_id] at this
  · have : Subsingleton S := subsingleton_of_zero_eq_one h.symm
    exact hE h1 q i n S inferInstance x

end LateralTheory.E.CoverPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CxDescPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CxDescPf

abbrev tr {R : Type} [CommRing R] (K : Cx R) (N : ℕ) : Cx R :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

abbrev trm {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (N : ℕ) : tr K N ⟶ tr L N :=
  HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

def Good {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (m : ℤ) : Prop :=
  (∀ j : ℤ, j < m → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I m)

def stupid : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ((∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
    ∀ j : ℤ, Function.Bijective (cpull (trm g 0) I j)) ∧
  ∀ (m : ℤ) (N : ℕ), m + 1 ≤ (N : ℤ) → Good (trm g N) I m → Good g I m

def long : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ) (N : ℕ),
  Good ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) I m →
  Good (trm g N) I m → Good (trm g (N + 1)) I m

def shift : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (p : ℕ) (j : ℤ),
  (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j)) ∧
  (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j))

theorem CxDesc_of (hS : stupid) (hL : long) (hH : shift) : LateralTheory.E.DescStepPf.CxDesc := by
  intro R _ I _ hI K L _ _ g n hlow hn h0
  obtain ⟨hb, hlim⟩ := hS R I hI g
  have base : Good (trm g 0) I (n + 1) := ⟨fun j _ => hb h0 j, (hb h0 (n + 1)).1⟩
  have step : ∀ N : ℕ, Good (trm g N) I (n + 1) := by
    intro N
    induction N with
    | zero => exact base
    | succ N ih =>
      refine hL R I hI g (n + 1) N ⟨fun j hj => ?_, ?_⟩ ih
      · exact (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) j).1 (hlow (N + 1) (j - ((N + 1 : ℕ) : ℤ)) (by omega))
      · apply (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) (n + 1)).2
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          have e : n + 1 - ((0 + 1 : ℕ) : ℤ) = n := by omega
          rw [e]; exact hn (0 + 1)
        · exact (hlow (N + 1) _ (by omega)).1
  have hg := hlim (n + 1) (n + 2).toNat (by omega) (step _)
  exact ⟨hg.1, hg.2⟩

end LateralTheory.E.CxDescPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DomCoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

namespace LateralTheory.E.DomCoverPf

theorem aicFrac (R L : Type) [CommRing R] [CommRing L] (φ : R →+* L) (hR : AIC R)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) : AIC L :=
  _root_.UpperTheory.Reformulated.B.Qn19.aicFrac R L φ hR h

def IdemCover : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ t_E3Cut.SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧
    ∀ z : Localization.AtPrime r, ∃ a b : C, IsUnit (algebraMap D (Localization.AtPrime r) (g.hom b)) ∧
      z * algebraMap D (Localization.AtPrime r) (g.hom b) = algebraMap D (Localization.AtPrime r) (g.hom a)

theorem DomCover_of (h2 : IdemCover) : t_E3Cut.DomCover := by
  intro C hC
  obtain ⟨D, g, hi, hs, hr⟩ := h2 C
  refine ⟨D, g, hi, hs, fun r _ => ⟨(hr r).1, ?_⟩⟩
  exact aicFrac C (Localization.AtPrime r) ((algebraMap D (Localization.AtPrime r)).comp g.hom) hC (hr r).2

end LateralTheory.E.DomCoverPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DomOpenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.DomOpenPf

theorem algClosed_of_AIC (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) :
    IsAlgClosed (FractionRing T) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  set K := FractionRing T
  set f := algebraMap T K
  have hf : Function.Injective f := IsFractionRing.injective T K
  obtain ⟨b, hb₁, hb₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hdeg : q.natDegree = p.natDegree := by
    rw [← natDegree_map_eq_of_injective hf q, hb₂, ← IsScalarTower.algebraMap_smul K b p,
      natDegree_smul_of_smul_regular]
    exact IsSMulRegular.of_ne_zero (by simpa [f] using (map_ne_zero_iff f hf).mpr hb0)
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  have hq0 : q ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg; omega
  obtain ⟨a, ha⟩ := hT (integralNormalization q) (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  have hlc : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hf).mpr (leadingCoeff_ne_zero.mpr hq0)
  refine ⟨f a / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (p := q) (by omega) f (f a / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hlc, eval₂_at_apply, ha, map_zero] at key
  have h2 : q.eval₂ f (f a / f q.leadingCoeff) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hlc
    · exact h
  rw [eval₂_eq_eval_map, hb₂, ← IsScalarTower.algebraMap_smul K b p, eval_smul, smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_left ((map_ne_zero_iff f hf).mpr hb0)

theorem algebraMap_ne_zero_of_flat (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [Nontrivial D]
    [Algebra T D] [Module.Flat T D] {s : T} (hs : s ≠ 0) : algebraMap T D s ≠ 0 := by
  intro h
  have hr : IsSMulRegular D s := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  apply one_ne_zero (α := D)
  apply hr
  simp [Algebra.smul_def, h]

theorem exists_frac (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) (a : D) :
    ∃ s t : T, s ≠ 0 ∧ algebraMap T D s * a = algebraMap T D t := by
  classical
  haveI := algClosed_of_AIC T hT
  let M := nonZeroDivisors T
  let S := Localization (Algebra.algebraMapSubmonoid D M)
  have hle : Algebra.algebraMapSubmonoid D M ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (algebraMap_ne_zero_of_flat T D (nonZeroDivisors.ne_zero hs))
  have : IsDomain S := IsLocalization.isDomain_localization hle
  have : IsLocalization (M.map (algebraMap T D)) S := inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D M) S)
  have : Algebra.FormallyEtale (FractionRing T) S :=
    Algebra.FormallyEtale.localization_map M (Rₘ := FractionRing T) (Sₘ := S) (S := D)
  have : Algebra.EssFiniteType (FractionRing T) S := Algebra.EssFiniteType.of_comp T (FractionRing T) S
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) S
  have hsub : Subsingleton (PrimeSpectrum S) := by
    constructor
    intro p q
    by_contra hpq
    have h0 : ((fun r => if r = p then (1 : FractionRing T) else 0) * fun r => if r = q then 1 else 0) = 0 := by
      funext r; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all
    have : e.symm (fun r => if r = p then (1 : FractionRing T) else 0) * e.symm (fun r => if r = q then 1 else 0) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) p
      simp at this
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) q
      simp at this
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum S) := inferInstance
  set x := algebraMap D S a
  have hx : algebraMap (FractionRing T) S (e x p₀) = x := by
    apply e.injective
    funext p
    rw [AlgEquiv.commutes]
    simp [Subsingleton.elim p p₀]
  generalize e x p₀ = c at hx
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective M c
  change IsLocalization.mk' (FractionRing T) t s = c at hts
  refine ⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩
  apply IsLocalization.injective S hle
  rw [map_mul, ← IsScalarTower.algebraMap_apply T D S, ← IsScalarTower.algebraMap_apply T D S,
    show algebraMap D S a = x from rfl, ← hx, ← hts,
    IsScalarTower.algebraMap_apply T (FractionRing T) S (s : T), IsScalarTower.algebraMap_apply T (FractionRing T) S t,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

theorem isEpi (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) : Algebra.IsEpi T D := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  obtain ⟨s, t, hs, hst⟩ := exists_frac T D hT a
  have hr : IsSMulRegular (TensorProduct T D D) s :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  rw [← sub_eq_zero]
  apply hr
  change s • (1 ⊗ₜ[T] a - a ⊗ₜ[T] 1) = s • (0 : TensorProduct T D D)
  have hsa : s • a = t • (1 : D) := by rw [Algebra.smul_def, hst, Algebra.smul_def, mul_one]
  have e1 : s • ((1 : D) ⊗ₜ[T] a) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [← TensorProduct.tmul_smul, hsa, TensorProduct.tmul_smul]
  have e2 : s • (a ⊗ₜ[T] (1 : D)) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [TensorProduct.smul_tmul', hsa, ← TensorProduct.smul_tmul']
  rw [smul_zero, smul_sub, e1, e2, sub_self]

theorem DomOpen_of : LateralTheory.E.EtAICPf.DomOpen := by
  intro T D _ _ _ _ _ _ hT
  set f := CommRingCat.ofHom (algebraMap T D)
  have : Algebra.IsEpi T D := isEpi T D hT
  have : Epi f := CommRingCat.epi_iff_epi.mpr inferInstance
  have : Mono (Spec.map f) := inferInstanceAs (Mono (Scheme.Spec.map f.op))
  have : Flat (Spec.map f) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map f) :=
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact IsOpenImmersion.of_flat_of_mono _

end LateralTheory.E.DomOpenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangePolynomialInductionOfLimit
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.E.t_E3Cut

theorem etale_base_change_fraction_field_of_etale_polynomial_algebra (hC3 : C3) (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (hA : AIC T) (hq : IsUnit (q : T))
    (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C) (hc : Et c) :
    BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c) := by
  letI : Algebra (Polynomial T) C := c.hom.toAlgebra
  haveI : Algebra.Etale (Polynomial T) C := hc
  letI : Algebra T C := (pC (CommRingCat.of T) ≫ c).hom.toAlgebra
  haveI : IsScalarTower T (Polynomial T) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h3 := hC3 q T hA hq C i
  have hsq := CommRingCat.isPushout_tensorProduct T (FractionRing T) C
  let e : CommRingCat.of (FractionRing T) ≅ CommRingCat.of K :=
    (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv.toCommRingCatIso
  have hsq' : IsPushout (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c)
      (e.inv ≫ CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeRight.toRingHom) := by
    refine hsq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x
      simp [e]
    · rfl
    · simp
    · rfl
  exact BC.of_one hsq' h3

theorem etale_base_change_polynomial_induction_of_limit (hL : Limit) : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := by
  intro hH q _ i T K _ _ _ _ _ _ hA hq X h hIE
  have hC3 : C3 := hH.2.2.2.2.2.2.2.2.2.1
  let k := CommRingCat.ofHom (algebraMap T K)
  let φ := pushout.inr k (pC (CommRingCat.of T))
  have P1 : IsPushout k (pC (CommRingCat.of T)) (pushout.inl k (pC (CommRingCat.of T))) φ :=
    IsPushout.of_hasPushout _ _
  have hqX : IsUnit ((q : ℕ) : CommRingCat.of (Polynomial T)) := by
    have := hq.map (Polynomial.C : T →+* Polynomial T)
    simpa using this
  have hEt : ∀ (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C), Et c → BC q i φ c := by
    intro C c hc
    have hb := etale_base_change_fraction_field_of_etale_polynomial_algebra hC3 q i T K hA hq C c hc
    have P2 := IsPushout.of_hasPushout φ c
    exact BC.of_one P2 (hb _ _ _ (P1.paste_vert P2))
  have hB := hL hH q i φ hqX hEt X h hIE
  have P2 := IsPushout.of_hasPushout φ h
  exact BC.of_one (P1.paste_vert P2) (hB _ _ _ P2)

end LateralTheory.E.t_E3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibClosed
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FibPf

def FibClosed : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z S : Scheme.{0}}
  (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  Eqv _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem total (H : Hyp) (h0 : HZero) (hA : AICAcyc) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
    [QuasiSeparated c] (hZ : AICSch Z) (hS : AICSch S) : Eqv _ (sch.map c) (tw q i) := by
  obtain ⟨_, _⟩ := qcqs_of p
  obtain ⟨_, _⟩ := qcqs_of (c ≫ p)
  have : IsIntegral Z := hZ.1
  have : ConnectedSpace Z := inferInstance
  exact eqv_of H.a9 _ (h0 H q c hS this (unit_of hq p) i)
    (fun n hn => hA H q Z hZ (unit_of hq (c ≫ p)) n i hn) (fun n hn => hA H q S hS (unit_of hq p) n i hn)

theorem Fib_of (hF0 : FibClosed) (h0 : HZero) (hA : AICAcyc) : Fib := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZ hS hB
  have ec := total H h0 hA q i A hq c p hZ hS
  have em := hF0 H q i A hq c p hZ hS hB
  have sq : pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst p (cpt A)
      = pullback.fst (c ≫ p) (cpt A) ≫ c := pullback.lift_fst _ _ _
  have key : ∀ n x, pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n (pull _ (sch.map c) (tw q i) n x)
      = pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, sq]
  have fe : ∀ n, (pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)
      = (pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n) := fun n => funext (key n)
  constructor
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)) :=
      (h n).comp (ec n)
    rw [fe n] at h1
    exact (Function.Bijective.of_comp_iff' (em n) _).1 h1
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
        (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n)) := (em n).comp (h n)
    rw [← fe n] at h1
    exact (Function.Bijective.of_comp_iff _ (ec n)).1 h1

end LateralTheory.E.FibPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FinOpenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinOpenPf

theorem range_closed (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C)
    (he : IsIdempotentElem e) :
    IsClosed (Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) := by
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e,
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _
    (PrimeSpectrum.isClosed_zeroLocus _)

theorem FinOpen_of : LateralTheory.E.FinEtSectionPf.FinOpen := by
  intro S C _ _ _ _ e he hoi
  set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hoi.isOpen_range
  obtain ⟨ε, hε, hr⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨range_closed S C e he, hopen⟩
  refine ⟨ε, hε, hr, ?_⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))
  have H : Set.range g ⊆ Set.range f := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆
      Set.range (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]
  let l := IsOpenImmersion.lift f g H
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have key : CommRingCat.ofHom φ ≫ Spec.preimage l =
      CommRingCat.ofHom (algebraMap S (Localization.Away ε)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac f g H
  exact congrArg CommRingCat.Hom.hom key

end LateralTheory.E.FinOpenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlobalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.GlobalPf

def gam {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) : T ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V (by simp)

def Affine : Prop := ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K) {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens),
  IsAffineOpen V → BC q i k (gam p V) → Eqv _ (sch.map (pullback.fst p (Spec.map k) ∣_ V)) (tw q i)

def LocEt : Prop := ∀ {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p] (x : X),
  ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
    ∃ c : CommRingCat.of (MvPolynomial (Fin n) T) ⟶ Γ(X, V), Et c ∧
      CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T) ≫ c = gam p V

theorem Global_of (hZ : ZarLocal) (hA : Affine) (hL : LocEt) : Global := by
  intro H q i T K k hG X p _
  refine hZ H (ZMod q) (tw q i) (pullback.fst p (Spec.map k)) fun x => ?_
  obtain ⟨U, n, hx, hU⟩ := hL p x
  refine ⟨U, hx, fun V hV hVU => ?_⟩
  obtain ⟨c, hc, hcg⟩ := hU V hV hVU
  have hb := hG n _ c hc
  rw [hcg] at hb
  exact hA q i k p V hV hb

end LateralTheory.E.GlobalPf

end
end

