module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem idemLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ e₀ he₀
  obtain ⟨e, he⟩ := homLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' B' B₀' p' hs' hp' hker' e₀
  set J : Ideal B' := I.map (algebraMap R B') with hJ
  have hJ2 : ∀ x ∈ J, ∀ y ∈ J, x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hJ, ← Ideal.map_pow, hI] at this
    simpa using this
  have hu : ∀ c, e (e c) - e c ∈ J := by
    intro c
    rw [← hker']
    simp [map_sub, he, he₀]
  have hkill : ∀ x ∈ J, ∀ c, e (e (c * x)) - e (c * x) = 0 := by
    intro x hx
    rw [hJ, Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      have h1 : e (c * algebraMap R B' r) = e c * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      have h2 : e (e c * algebraMap R B' r) = e (e c) * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      rw [h1, h2, ← sub_mul]
      exact hJ2 _ (hu c) _ (Ideal.mem_map_of_mem _ hr)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have := hx c
      have := hy c
      rw [mul_add, map_add (f := _), map_add (f := _)]
      linear_combination hx c + hy c
    | smul a x _ hx =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact hx (c * a)
  have hrec : ∀ c, e (e (e (e c))) - 2 * e (e (e c)) + e (e c) = 0 := by
    intro c
    have := hkill _ (hu c) 1
    simp only [_root_.one_mul, map_sub] at this
    linear_combination this
  let e' : B' →ₐ[R] B' :=
    { toFun := fun b => 3 * e (e b) - 2 * e (e (e b))
      map_one' := by simp; norm_num
      map_mul' := by
        intro x y
        have h := hJ2 _ (hu (e x)) _ (hu (e y))
        simp only [map_mul]
        linear_combination (-6 : B') * h
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add (f := _)]; ring
      commutes' := by intro r; simp only [AlgHom.commutes]; ring }
  refine ⟨e', ?_, ?_⟩
  · intro b
    show 3 * e (e (3 * e (e b) - 2 * e (e (e b)))) - 2 * e (e (e (3 * e (e b) - 2 * e (e (e b))))) = 3 * e (e b) - 2 * e (e (e b))
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination (-3 : B') * hrec b + (-4 : B') * hrec (e b) + (4 : B') * hrec (e (e b))
  · intro b
    show p' (3 * e (e b) - 2 * e (e (e b))) = e₀ (p' b)
    simp only [map_sub, map_mul, map_ofNat, he, he₀]
    ring

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralProjectiveClosureOfLinearSystemPoi
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

private theorem exists_toField {Ω : Type} [Field Ω] {Y : Scheme.{0}} [IsIntegral Y] (g : Sp Ω ⟶ Y) [IsDominant g] :
    ∃ φ : Y.functionField →+* Ω, (∀ U : Y.Opens, genericPoint Y ∈ U → ⊤ ≤ g ⁻¹ᵁ U) ∧
      (∀ U : Y.Opens, ⊤ ≤ g ⁻¹ᵁ U → genericPoint Y ∈ U) ∧
      ∀ (U : Y.Opens) (h : genericPoint Y ∈ U) (e : ⊤ ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)),
        ProjSpace.fnOn ⊤ (φ (Cartier.fnOf U h s)) = (g.appLE U ⊤ e).hom s := by
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  let η := genericPoint (Sp Ω)
  have hb : Function.Bijective (Cartier.fnOf (X := Sp Ω) ⊤ trivial) := by
    refine ⟨fnOf_injective _ _, fun a => ?_⟩
    obtain ⟨U, hU, s, hs⟩ := (Sp Ω).presheaf.germ_exist (x := η) a
    obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim η x) ▸ hU
    exact ⟨s, hs⟩
  let e₁ := RingEquiv.ofBijective _ hb
  let e₂ := RingEquiv.ofBijective _ (ProjSpace.fnOn_top_bijective (A := Ω))
  refine ⟨(e₂.symm.toRingHom.comp e₁.symm.toRingHom).comp (functionFieldMap g), fun U hU x _ => ?_,
    fun U hU => gen_mem (x := g η) (hU trivial), fun U h e s => ?_⟩
  · obtain ⟨_, hz, z, rfl⟩ := g.denseRange.inter_open_nonempty U U.isOpen ⟨_, hU⟩
    exact (Subsingleton.elim z x) ▸ hz
  · change e₂ (e₂.symm (e₁.symm (functionFieldMap g _))) = _
    rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_eq]
    have hx : η ∈ g ⁻¹ᵁ U := e trivial
    change _ = Cartier.fnOf ⊤ trivial (resG _ e (g.app U s))
    refine Eq.trans ?_ (fnOf_resG e _ _).symm
    rw [← Cartier.algebraMap_germ (show g η ∈ U from hx), functionFieldMap_algebraMap,
      ← Cartier.algebraMap_germ hx]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply g U η hx s

private theorem dim_of_trdeg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp K) [LocallyOfFiniteType q] (e : Y.functionField ≃+* Ω)
    (he : ∀ a, e (toFunctionField q a) = algebraMap K Ω a) {D : ℕ} (hD : Algebra.trdeg K Ω = D) :
    topologicalKrullDim Y = D := by
  letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q)).hom.toAlgebra
  have hc : Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q) = CommRingCat.ofHom (toFunctionField q) :=
    Spec.map_injective ((Spec.map_preimage _).trans (genericFieldPoint_over q))
  let e' : Y.functionField ≃ₐ[K] Ω := { e with
    commutes' := fun a => (congrArg (fun f => e (CommRingCat.Hom.hom f a)) hc).trans (he a) }
  have ht : Algebra.trdeg K Y.functionField = D :=
    (le_antisymm (trdeg_le_of_injective e'.toAlgHom e'.injective)
      (trdeg_le_of_injective e'.symm.toAlgHom e'.symm.injective)).trans hD
  have h1 := GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq q ht
  have h2 : (q ⁻¹' {genericPoint (Spec (CommRingCat.of K))} : Set Y) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  rwa [h2, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph] at h1

private theorem eq_top_of_span {K V Ω ι : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (u : ι → V) (hu : Submodule.span K (Set.range u) = ⊤) (hg : GlobalTheory.DegVal.GenRatios ev)
    (L : Subfield Ω) (hc : ∀ a, algebraMap K Ω a ∈ L) (hr : ∀ k l, ev (u l) ≠ 0 → ev (u k) / ev (u l) ∈ L) :
    L = ⊤ := by
  obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
    by_contra! h0
    exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
  have key : ∀ v, ev v / ev (u l) ∈ L := fun v => by
    have hv : v ∈ Submodule.span K (Set.range u) := hu ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hr k l hl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_div]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def, mul_div_assoc]; exact mul_mem (hc a) hx
  have h : GlobalTheory.DegVal.ratioField ev ≤ L.toIntermediateField hc := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨v, w, rfl⟩
    rw [← div_div_div_cancel_right₀ hl]
    exact div_mem (key v) (key w)
  rw [hg.2] at h
  exact top_unique fun x _ => h (IntermediateField.mem_top (x := x))


open MvPolynomial in
private theorem trdeg_eq {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (D : ℕ) (hg : GlobalTheory.DegVal.GenRatios ev) (hD : 0 < imageDeg ev D) :
    Algebra.trdeg K Ω = D := by
  obtain ⟨N, b, F, hF⟩ := (imageDeg_pos_iff ev D).1 hD
  set y : Fin N → Ω := fun j => ev (b j) with hy
  have hy0 : y ≠ 0 := fun h0 => hg.1 (b.ext fun k => by simpa using congrFun h0 k)
  have hr : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤ :=
    eq_top_of_span ev b b.span_eq hg _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun k l _ => Subfield.subset_closure (Or.inr ⟨k, l, rfl⟩)
  have := isPrime_coneIdeal (K := K) y
  have hk : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (D + 1 : ℕ) :=
    GlobalTheory.ChowExists.ringKrullDim_of_isChowFormInt (P := coneIdeal K y) (fun g hg n =>
      (mem_coneIdeal_of_isHomogeneous y (homogeneousComponent_isHomogeneous n g)).2
        ((mem_coneIdeal_iff y g).1 hg n)) hF
  obtain ⟨d, hd, hd'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)
  obtain rfl : d = D + 1 := by exact_mod_cast hd.symm.trans hk
  let f := Ideal.kerLiftAlg (coneMap K y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hr A hXy
  have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain] at hd'
  exact Cardinal.add_one_inj.1 (by exact_mod_cast hd')

theorem _root_.GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D m : ℕ) (u : Fin (m + 1) → V),
    Submodule.span K (Set.range u) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
      IsProjOver q ∧ topologicalKrullDim Y = D ∧ (⨆ k, nonzeroLocus (t k) = ⊤) ∧ Function.Bijective ψ ∧
      (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i),
        ψ (ev (u k)) * fnOf _ h ((t l).f i) = ψ (ev (u l)) * fnOf _ h ((t k).f i) := by
  intro K V Ω _ _ _ _ _ ev D m u hu hg hD
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy : Ideal.span (Set.range y) = ⊤ := by
    obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
      by_contra! h0
      exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨l, rfl⟩) (Ne.isUnit hl)
  let p := ProjSpace.pt (algebraMap K Ω) y hy
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have hqc : QuasiCompact p := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  obtain ⟨Y, hY, g, j, hdom, hj, hgj⟩ : ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (g : Sp Ω ⟶ Y) (j : Y ⟶ PSpace K m),
      IsDominant g ∧ IsClosedImmersion j ∧ g ≫ j = p :=
    ⟨p.image, isIntegral_image p, p.toImage, p.imageι, inferInstance, inferInstance, p.toImage_imageι⟩
  obtain ⟨φ, hm₁, hm₂, hφ⟩ := exists_toField g
  let B := (ProjSpace.O1 K m).pull j
  let t : Fin (m + 1) → B.Sec := fun k => Cartier.secPull (ProjSpace.coord K m k) j
  have hU : ∀ i : PUnit → Fin (m + 1), g ⁻¹ᵁ B.U i = ProjSpace.spOpen (y (i ⟨⟩)) := fun i => by
    rw [← ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy]
    refine (congrArg (g ⁻¹ᵁ ·) (pull_U (ProjSpace.O1 K m) j i)).trans ?_
    exact (Scheme.Hom.comp_preimage g j _).symm.trans (congrArg (· ⁻¹ᵁ _) hgj)
  have hmem : ∀ i : PUnit → Fin (m + 1), genericPoint Y ∈ B.U i ↔ y (i ⟨⟩) ≠ 0 := fun i => by
    constructor
    · intro h h0
      have := (hm₁ _ h).trans (hU i).le (show genericPoint (Sp Ω) ∈ (⊤ : (Sp Ω).Opens) from trivial)
      rw [ProjSpace.mem_spOpen, h0] at this
      exact this (zero_mem _)
    · intro h
      refine hm₂ _ (le_of_le_of_eq (fun x _ => ?_) (hU i).symm)
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (Ne.isUnit h))
  have hrat : ∀ (i : PUnit → Fin (m + 1)) (h : genericPoint Y ∈ B.U i) (l : Fin (m + 1)),
      φ (Cartier.fnOf _ h ((t l).f i)) * y (i ⟨⟩) = y l := fun i h l => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    have e₁ := (resG_self _ _).symm.trans (ProjSpace.resG_secPull_coord j l i le_rfl)
    have h' : ⊤ ≤ p ⁻¹ᵁ ProjSpace.chart K m (i ⟨⟩) :=
      (hm₁ _ h).trans ((hU i).trans (ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy _).symm).le
    rw [map_mul, hφ _ h (hm₁ _ h), ← ProjSpace.pullRatio_pt_mul (algebraMap K Ω) y hy (i ⟨⟩) l h']
    congr 1
    refine (congrArg _ e₁).trans ?_
    rw [ProjSpace.appLE_pullRatio]
    exact ProjSpace.pullRatio_of_eq hgj _ _
  have hconst : ∀ a, φ (toFunctionField (j ≫ PSpace.str K m) a) = algebraMap K Ω a := fun a => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    refine (hφ ⊤ trivial le_top (((Scheme.ΓSpecIso (.of K)).inv ≫ (j ≫ PSpace.str K m).appTop).hom a)).trans ?_
    have e : g ≫ j ≫ PSpace.str K m = spMap (algebraMap K Ω) := by
      rw [reassoc_of% hgj]
      change ProjSpace.pt (algebraMap K Ω) y hy ≫ PSpace.str K m = _
      rw [ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
      congr 1
      ext1
      exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C (algebraMap K Ω) y r
    have e' : (j ≫ PSpace.str K m).appTop ≫ g.appTop = (spMap (algebraMap K Ω)).appTop := by
      rw [← Scheme.Hom.comp_appTop, e]
    have e'' := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K Ω))
    rw [← e'] at e''
    exact congrArg (resG (Sp Ω) le_top) (congrArg (fun f => f.hom a) e'').symm
  have hsurj : Function.Surjective φ := by
    rw [← RingHom.fieldRange_eq_top_iff]
    refine eq_top_of_span ev u hu hg _ (fun a => ⟨_, hconst a⟩) fun k l hl => ?_
    exact ⟨_, eq_div_of_mul_eq hl (hrat (fun _ => l) ((hmem (fun _ => l)).2 hl) k)⟩
  let e : Y.functionField ≃+* Ω := RingEquiv.ofBijective φ ⟨RingHom.injective _, hsurj⟩
  have hft : LocallyOfFiniteType (j ≫ PSpace.str K m) := inferInstance
  refine ⟨Y, hY, j ≫ PSpace.str K m, B, LB.isLB_pull (ProjSpace.O1_isLB K m) _, t,
    e.symm.toRingHom, ⟨m, j, hj, rfl⟩, dim_of_trdeg _ e hconst (trdeg_eq ev D hg hD),
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord K m) _, e.symm.bijective, fun a => ?_,
    fun k l i h => ?_⟩
  · apply e.injective
    change e (e.symm _) = φ _
    rw [RingEquiv.apply_symm_apply, ← hconst]
    simp [toFunctionField, Cartier.fnOf, algX, Scheme.Hom.appLE]
  · apply e.injective
    have hi := (hmem i).1 h
    change e (e.symm (y k) * _) = e (e.symm (y l) * _)
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    change y k * φ _ = y l * φ _
    rw [eq_div_of_mul_eq hi (hrat i h l), eq_div_of_mul_eq hi (hrat i h k)]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAddChiEq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CobChi

theorem exists_isAdd_chi_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (n : ℕ),
    (n : R) = 0 → ∀ (u f : Fn1 A) (g : Fn2 A), IsAdd u g → Cohom (whole A) u f →
    ∃ g' : Fn2 A, IsAdd f g' ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ n : Pt A D) = 1 → GlobalTheory.PtExt.chi n g' D x = GlobalTheory.PtExt.chi n g D x := by
  intro R _ A _ n hn u f g hu ⟨k, hk⟩
  have hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x)) := by
    intro D _ _ D' _ _ φ x
    have h := hk D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg] at h
    linear_combination -h
  refine ⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩
  · intro D _ _ D' _ _ φ x y
    have h1 := hu D D' φ x y
    simp only [hf, comp_mul, map_sub]
    linear_combination h1
  · intro D _ _ x hx
    have hnD : (n : D) = 0 := by
      rw [← map_natCast (algebraMap R D) n, hn, map_zero]
    have hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp_rw [← pow_succ]
      rw [Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul,
        hnD, zero_mul]
    simp only [GlobalTheory.PtExt.chi]
    rw [Finset.sum_sub_distrib, hs, sub_zero]

end GlobalTheory.CobChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivial
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem nonempty_ι_of_isLB (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (hP : P.IsLB) : Nonempty P.ι := by
  have hne : Nonempty (𝟙_ (Over (Sp R))).left := inferInstanceAs (Nonempty (PrimeSpectrum R))
  obtain ⟨p⟩ := hne
  let e : 𝟙_ (Over (Sp R)) ⟶ A ⊗ B := lift η[A] η[B]
  have h : e.left.base p ∈ (⨆ i, P.U i) := by rw [hP.cover]; trivial
  obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i⟩

theorem exists_isChoice : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  intro R _ _ A B _ _ P hP
  have hne := nonempty_ι_of_isLB R A B P hP
  classical
  refine ⟨fun D _ _ x ↦ if h : Sm (chartsA P) x then
    Classical.choose (show ∃ i, ⊤ ≤ x.left ⁻¹ᵁ chartsA P i from h)
  else Classical.choice hne, ?_⟩
  unfold IsChoice
  intro D _ _ x h
  simp only [dite_eq_left h]
  exact Classical.choose_spec (show ∃ i, ⊤ ≤ x.left ⁻¹ᵁ chartsA P i from h)

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompData

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ (∀ x, hD.xe x = xe x) ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ D'.P.A.left) (y : Y) (a : D.P.L.ι) (c : D'.P.L.ι), gw hD.w f y a c = gw w f y a c := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

end GlobalTheory.PullDegCompData

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldTopFormPairingRegularAtPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logVectorField_topForm_pairing_regular_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → (barComp TF.Y Z).ι x ∈ U.1 → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((b j).1 r)) → ∀ (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  first | exact @GlobalTheory.LogKSDiv.local_topPair | exact GlobalTheory.LogKSDiv.local_topPair | (intros; apply GlobalTheory.LogKSDiv.local_topPair <;> assumption)
end

