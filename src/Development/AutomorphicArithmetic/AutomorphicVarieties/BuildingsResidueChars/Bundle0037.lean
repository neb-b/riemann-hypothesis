module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SxExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0005
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BddFixOfBoundedComplex
section
open UpperTheory.V UpperTheory.V.Af.BA UpperTheory.V.KT Pointwise in
theorem UpperTheory.bddFix_of_bounded_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.ActRe → UpperTheory.V.Af.BA.SpanRe → UpperTheory.V.Af.BA.OrbRe → UpperTheory.V.Af.BA.MinStab → UpperTheory.V.Af.BA.BddFix := by
  intro hB hGood hAct hSpan hOrb hMin L _ _ _ N σ hσ
  obtain ⟨x, hx1, hx2⟩ := hAct L N σ hσ
  letI := x
  obtain ⟨hFC, hS0, hA⟩ := UpperTheory.V.ConeExtensionAcyclic.acyc_simp (hGood L N σ hσ)
  let K : Cx (Fix N σ) (UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) :=
    { S := UpperTheory.V.ConeExtensionAcyclic.simp (qr L N) (Tr L N)
      comp := fun f t ht => by
        obtain ⟨z, hz, hzt⟩ := ht
        exact ⟨z, hz, fun j => hzt (f j)⟩
      smul := fun g t ht => hx2 _ g t ht }
  refine hB _ _ K (fun m => UpperTheory.V.KT.faceexact _ _ hFC hS0 hA m) ?_ ?_
  · intro p
    obtain ⟨R, hRf, hR⟩ := hOrb L N σ hσ p
    refine ⟨{t : K.Tup p | (fun j => (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N)) ∈ R}, ?_, ?_⟩
    · refine hRf.preimage ?_
      intro a _ b _ hab
      apply Subtype.ext
      funext j
      exact Subtype.ext (Subtype.ext (congrFun hab j))
    · intro t
      obtain ⟨g, hg, hgR⟩ := hR t.1 t.2
      refine ⟨⟨g, hg⟩, ?_⟩
      have hfun : (fun j => ((((⟨g, hg⟩ : Fix N σ) • t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N))
          = fun j => g • (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N) :=
        funext fun j => hx1 _ _
      show (fun j => ((((⟨g, hg⟩ : Fix N σ) • t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N)) ∈ R
      rw [hfun]
      exact hgR
  · intro t
    set v : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N) := t.1 0 with hv
    set hh : UpperTheory.V.KT.HS L N := ((v : HR L N) : UpperTheory.V.KT.HS L N) with hhh
    have hRy : hh ∈ UpperTheory.V.KT.Ry L N := by
      intro y hy
      exact v.2.1 ⟨y, hy⟩
    have hsp := hSpan L N σ hσ 0 t.1 t.2
    have hmv : UpperTheory.V.KT.minVec hh = {y | ∀ j : Fin (0 + 1), UpperTheory.V.KT.q (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N) y = 1} := by
      ext y
      constructor
      · intro hy j
        have hj : j = 0 := Fin.ext (by omega)
        rw [hj]
        exact hy
      · intro hy
        exact hy 0
    have hsp' : UpperTheory.V.KT.Spans (UpperTheory.V.KT.minVec hh) := by
      rw [hmv]
      exact hsp
    haveI := hMin L N hh hRy hsp'
    refine Finite.of_injective
      (β := MulAction.stabilizer (UpperTheory.V.KT.Gm L N) (UpperTheory.V.KT.minVec hh))
      (fun g => ⟨((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N), ?_⟩) ?_
    · have hgt : (g.1 : Fix N σ) • t = t := g.2
      have hgv : (g.1 : Fix N σ) • v = v := congrArg (fun s : K.Tup 0 => s.1 0) hgt
      have hgh : ((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N) • hh = hh := by
        rw [hhh, ← hx1, hgv]
      rw [MulAction.mem_stabilizer_iff]
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show UpperTheory.V.KT.q hh (((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N)⁻¹ • z) = 1 ↔ UpperTheory.V.KT.q hh z = 1
      rw [← UpperTheory.V.KT.q_smul, hgh]
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext hab')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BoundedComplexOfBoundedSimplicialComplex
section
open NumberField UpperTheory.V UpperTheory.V.Af.BA

private noncomputable def cxK (L : Type) [Field L] [NumberField L] (N : ℕ) : Cx (KT.Gm L N) (KT.Vx L N) where
  S := ConeExtensionAcyclic.simp (KT.qc L N) (KT.Psd L N)
  comp := fun f t ht => by
    obtain ⟨y, hy, h⟩ := ht
    exact ⟨y, hy, fun j => h (f j)⟩
  smul := fun g t ht => KT.smul_mem_simp g ht

theorem UpperTheory.bounded_complex_of_bounded_simplicial_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.BddComplex := by
  intro H L _ _ _ N
  refine H (KT.Gm L N) (KT.Vx L N) (cxK L N) (fun m => ConeExtensionAcyclic.sx_exact L N m) (fun p => ?_) (fun t => ?_)
  · haveI : Finite (MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p)) := (KT.orb L N p).1
    refine ⟨Set.range (fun c : MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p) => Quotient.out c),
      Set.finite_range _, fun x => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (KT.Gm L N) ((cxK L N).Tup p)) x)))
    exact ⟨g, _, hg.symm⟩
  · haveI := KT.stabfin L N (t.1 0)
    refine Finite.of_injective (fun g : MulAction.stabilizer (KT.Gm L N) t =>
      (⟨g.1, congrFun (congrArg Subtype.val g.2) 0⟩ : MulAction.stabilizer (KT.Gm L N) (t.1 0))) fun g k e => ?_
    exact Subtype.ext (Subtype.mk.inj e)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingFixedPointsEquiv
section
theorem UpperTheory.building_fixed_points_equiv :
    UpperTheory.V.Af.BA.FixEquiv := by
  intro A B _ _ i σ N hi hσ
  have hmem : ∀ g : GL (Fin N) A, Matrix.GeneralLinearGroup.map (n := Fin N) i g ∈
      (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) := by
    intro g
    change Matrix.GeneralLinearGroup.map (n := Fin N) σ (Matrix.GeneralLinearGroup.map (n := Fin N) i g) =
      Matrix.GeneralLinearGroup.map (n := Fin N) i g
    ext a b
    exact (hσ _).2 ⟨g a b, rfl⟩
  have hM : ∀ X Y : Matrix (Fin N) (Fin N) A, X.map i = Y.map i → X = Y := by
    intro X Y h
    ext a b
    exact hi (congrFun (congrFun h a) b)
  have hpre : ∀ g : GL (Fin N) B,
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) →
      ∃ X : Matrix (Fin N) (Fin N) A, X.map i = (g : Matrix (Fin N) (Fin N) B) := by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (n := Fin N) σ g = g := hg
    have h1 : ∀ a b, ∃ x : A, i x = (g : Matrix (Fin N) (Fin N) B) a b := by
      intro a b
      refine (hσ _).1 ?_
      have := congrArg (fun k : GL (Fin N) B => (k : Matrix (Fin N) (Fin N) B) a b) hg'
      exact this
    choose X hX using h1
    exact ⟨Matrix.of X, by ext a b; exact hX a b⟩
  refine ⟨(MulEquiv.ofBijective
    ((Matrix.GeneralLinearGroup.map (n := Fin N) i).codRestrict _ hmem) ⟨?_, ?_⟩).symm⟩
  · intro g k h
    have h1 : Matrix.GeneralLinearGroup.map (n := Fin N) i g =
      Matrix.GeneralLinearGroup.map (n := Fin N) i k := congrArg Subtype.val h
    apply Units.ext
    apply hM
    exact congrArg Units.val h1
  · rintro ⟨g, hg⟩
    obtain ⟨X, hX⟩ := hpre g hg
    obtain ⟨Y, hY⟩ := hpre g⁻¹ (inv_mem hg)
    refine ⟨⟨X, Y, hM _ _ ?_, hM _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.mul_inv
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.inv_mul
    · apply Subtype.ext
      apply Units.ext
      exact hX
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CmInertiaRestrictionHolds
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

theorem UpperTheory.cm_inertia_restriction_holds : UpperTheory.V.Af.Cr.IneRes := by
  intro F₀ F Ω _ _ _ _ _ _ _ _ _ _
  classical
  unfold Ine IsPlaceOver Inertia
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω), IsIntegral ℤ x → A.valuation x ≤ 1 := by
    intro A x h
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h.tower_top : IsIntegral A x)
    exact A.valuation_le_one y
  obtain ⟨α₁, hα₁⟩ := Field.exists_primitive_element F₀ F
  have hα₁alg : IsAlgebraic ℤ α₁ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (.of_finite ℚ α₁)
  obtain ⟨m, hm0, hmint⟩ := hα₁alg.exists_integral_multiple
  set α : F := m • α₁ with hαdef
  set g : Polynomial ℤ := minpoly ℤ α with hgdef
  set f : Polynomial F₀ := g.map (algebraMap ℤ F₀) with hfdef
  have hgmonic : g.Monic := minpoly.monic hmint
  have hfα : Polynomial.aeval α f = 0 := by
    rw [hfdef, Polynomial.aeval_map_algebraMap, hgdef, minpoly.aeval]
  have hfsep : f.Separable := by
    have h1 : (minpoly ℚ α).Separable := Algebra.IsSeparable.isSeparable ℚ α
    have h2 := h1.map (f := algebraMap ℚ F₀)
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hmint, Polynomial.map_map] at h2
    have h3 : (algebraMap ℚ F₀).comp (algebraMap ℤ ℚ) = algebraMap ℤ F₀ := RingHom.ext_int _ _
    rw [h3] at h2
    exact h2
  set c : F := Polynomial.aeval α (Polynomial.derivative f) with hcdef
  have hc0 : c ≠ 0 := hfsep.aeval_derivative_ne_zero hfα
  have hcint : IsIntegral ℤ c := by
    have h1 : c = Polynomial.aeval α (Polynomial.derivative g) := by
      rw [hcdef, hfdef, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    have key := Polynomial.aeval_algHom_apply (integralClosure ℤ F).val
      (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)
    rw [h1]
    refine key ▸ ?_
    exact (Polynomial.aeval (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)).2
  set d : F₀ := Algebra.norm F₀ c with hddef
  have hdint : IsIntegral ℤ d := Algebra.isIntegral_norm F₀ hcint
  have hd0 : d ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc0
  set D : 𝓞 F₀ := ⟨d, hdint⟩ with hDdef
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    exact congrArg (fun x : 𝓞 F₀ => (x : F₀)) h
  have hspan : Ideal.span {D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hD0
  refine Filter.eventually_cofinite.mpr ((Ideal.finite_factors hspan).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hDv
  apply hv
  intro A hA σ hσ
  have hσ2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
  set α₀ : Ω := algebraMap F Ω α with hα₀def
  have h0 : Polynomial.aeval α₀ f = 0 := by
    rw [hα₀def, Polynomial.aeval_algebraMap_apply, hfα, map_zero]
  have hfix : σ α₀ = α₀ := by
    by_contra hne
    set fΩ : Polynomial Ω := f.map (algebraMap F₀ Ω) with hfΩ
    have hfΩ_monic : fΩ.Monic := (hgmonic.map _).map _
    have hfΩ0 : fΩ ≠ 0 := hfΩ_monic.ne_zero
    have hroot : ∀ y : Ω, Polynomial.aeval y f = 0 → y ∈ fΩ.roots := by
      intro y hy
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, Polynomial.eval_map_algebraMap]
      exact hy
    have hα₀root : α₀ ∈ fΩ.roots := hroot _ h0
    have hβroot : σ α₀ ∈ fΩ.roots := by
      apply hroot
      have := Polynomial.aeval_algHom_apply (σ : Ω ≃ₐ[F₀] Ω).toAlgHom α₀ f
      rw [h0, map_zero] at this
      exact this
    have hrootint : ∀ y ∈ fΩ.roots, IsIntegral ℤ y := by
      intro y hy
      refine ⟨g, hgmonic, ?_⟩
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, hfdef, Polynomial.map_map,
        ← Polynomial.eval₂_eq_eval_map] at hy
      have hZ : algebraMap ℤ Ω = (algebraMap F₀ Ω).comp (algebraMap ℤ F₀) := RingHom.ext_int _ _
      rw [hZ]
      exact hy
    have hder : algebraMap F Ω c = ((fΩ.roots.erase α₀).map (α₀ - ·)).prod := by
      rw [← (IsAlgClosed.splits fΩ).eval_root_derivative hfΩ_monic hα₀root]
      rw [hfΩ, Polynomial.derivative_map, Polynomial.eval_map_algebraMap, hcdef, hα₀def,
        Polynomial.aeval_algebraMap_apply]
    have hβmem : σ α₀ ∈ fΩ.roots.erase α₀ := (Multiset.mem_erase_of_ne hne).mpr hβroot
    have hcv : A.valuation (algebraMap F Ω c) < 1 := by
      rw [hder, ← Multiset.cons_erase hβmem, Multiset.map_cons, Multiset.prod_cons, Valuation.map_mul]
      have h1 : A.valuation (α₀ - σ α₀) < 1 := by
        rw [Valuation.map_sub_swap]
        exact hσ2 α₀ (hint A α₀ (hrootint α₀ hα₀root))
      have h2 : A.valuation (((fΩ.roots.erase α₀).erase (σ α₀)).map (α₀ - ·)).prod ≤ 1 := by
        apply hint
        apply IsIntegral.multiset_prod
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
        exact (hrootint α₀ hα₀root).sub
          (hrootint y (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hy)))
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) h1
    have hnorm := Algebra.norm_eq_prod_embeddings F₀ Ω c
    set φ₀ : F →ₐ[F₀] Ω := IsScalarTower.toAlgHom F₀ F Ω with hφ₀
    rw [← Finset.mul_prod_erase Finset.univ (fun φ : F →ₐ[F₀] Ω => φ c) (Finset.mem_univ φ₀)] at hnorm
    have hdv : A.valuation (algebraMap F₀ Ω d) < 1 := by
      rw [hddef, hnorm, Valuation.map_mul]
      have h2 : A.valuation (∏ φ ∈ Finset.univ.erase φ₀, φ c) ≤ 1 := by
        apply hint
        apply IsIntegral.prod
        intro φ _
        exact hcint.map φ.toRingHom.toIntAlgHom
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hcv
    exact hDv ((hA D).mp hdv)
  have hfix1 : σ (algebraMap F Ω α₁) = algebraMap F Ω α₁ := by
    have h : σ (algebraMap F Ω α) = algebraMap F Ω α := hfix
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    simp only [hαdef, zsmul_eq_mul, map_mul, map_intCast] at h
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hm0) h
  have hφ : ((σ : Ω ≃ₐ[F₀] Ω).toAlgHom).comp (IsScalarTower.toAlgHom F₀ F Ω) =
      IsScalarTower.toAlgHom F₀ F Ω := by
    have hadj : Algebra.adjoin F₀ {α₁} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic α₁), hα₁, IntermediateField.top_toSubalgebra]
    refine AlgHom.ext_of_adjoin_eq_top hadj ?_
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hfix1
  have hcomm : ∀ y : F, σ (algebraMap F Ω y) = algebraMap F Ω y := fun y => DFunLike.congr_fun hφ y
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[F₀] Ω).toRingEquiv) hcomm, ?_⟩
  ext x
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CoindRetractOfFiniteIndex
section
open CategoryTheory

private theorem term_congr {G : Type} [Group G] (S : Subgroup G) (A : Rep.{0} ℂ G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) {g g' : G}
    (h : (g : G ⧸ S) = (g' : G ⧸ S)) : A.ρ g (F.1 g⁻¹) = A.ρ g' (F.1 g'⁻¹) := by
  have hs : g⁻¹ * g' ∈ S := QuotientGroup.eq.mp h
  let s : S := ⟨g⁻¹ * g', hs⟩
  have hF : F.1 (S.subtype s⁻¹ * g⁻¹) = (Rep.res S.subtype A).ρ s⁻¹ (F.1 g⁻¹) := F.2 s⁻¹ g⁻¹
  have hg : S.subtype s⁻¹ * g⁻¹ = g'⁻¹ := by
    show (g⁻¹ * g')⁻¹ * g⁻¹ = g'⁻¹
    group
  rw [hg] at hF
  rw [hF]
  show _ = A.ρ g' (A.ρ (g⁻¹ * g')⁻¹ (F.1 g⁻¹))
  rw [← Module.End.mul_apply, ← map_mul, show g' * (g⁻¹ * g')⁻¹ = g by group]

private noncomputable def tr {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G) :
    Representation.coindV S.subtype (Rep.res S.subtype A).ρ →ₗ[ℂ] A :=
  ∑ q : G ⧸ S, A.ρ q.out ∘ₗ LinearMap.proj q.out⁻¹ ∘ₗ Submodule.subtype _

private theorem tr_apply {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) :
    tr S A F = ∑ q : G ⧸ S, A.ρ q.out (F.1 q.out⁻¹) := by
  rw [tr, LinearMap.sum_apply]
  rfl

private theorem tr_equiv {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G) (h : G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) :
    tr S A (Representation.coind S.subtype (Rep.res S.subtype A).ρ h F) = A.ρ h (tr S A F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tr_apply, tr_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ S)) _ _ ?_
  intro q
  have hq : ((h⁻¹ * q.out : G) : G ⧸ S) = (((MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ S)) q).out : G) := by
    rw [QuotientGroup.out_eq']
    show _ = h⁻¹ • q
    rw [← QuotientGroup.out_eq' q, MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rfl
  rw [← term_congr S A F hq]
  show A.ρ q.out (F.1 (q.out⁻¹ * h)) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv]

theorem UpperTheory.coind_retract_of_finite_index :
    UpperTheory.V.Af.BA.CoindRetract := by
  classical
  unfold UpperTheory.V.Af.BA.CoindRetract
  intro G _ S hS A
  haveI := hS
  haveI : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hn : (Fintype.card (G ⧸ S) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let P : A →ₗ[ℂ] Representation.coindV S.subtype (Rep.res S.subtype A).ρ :=
    { toFun := fun a => ⟨fun g => A.ρ g a, fun s g => by
        show A.ρ (S.subtype s * g) a = A.ρ (S.subtype s) (A.ρ g a)
        rw [map_mul, Module.End.mul_apply]⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add (A.ρ g) a b)
      map_smul' := fun c a => Subtype.ext (funext fun g => map_smul (A.ρ g) c a) }
  let π : A ⟶ Rep.coind S.subtype (Rep.res S.subtype A) :=
    Rep.ofHom ⟨P, fun h => LinearMap.ext fun a => Subtype.ext (funext fun g => by
      show A.ρ g (A.ρ h a) = A.ρ (g * h) a
      rw [map_mul, Module.End.mul_apply])⟩
  let ι : Rep.coind S.subtype (Rep.res S.subtype A) ⟶ A :=
    Rep.ofHom ⟨(Fintype.card (G ⧸ S) : ℂ)⁻¹ • tr S A, fun h => LinearMap.ext fun F => by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      exact congrArg (fun x => (Fintype.card (G ⧸ S) : ℂ)⁻¹ • x) (tr_equiv S A h F)⟩
  refine ⟨π, ι, ?_⟩
  apply Rep.hom_ext
  ext a
  show (Fintype.card (G ⧸ S) : ℂ)⁻¹ • tr S A (P a) = a
  rw [tr_apply]
  have hterm : ∀ q : G ⧸ S, A.ρ q.out ((P a).1 q.out⁻¹) = a := fun q => by
    show A.ρ q.out (A.ρ q.out⁻¹ a) = a
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallinePeriodRingProperties
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp

theorem UpperTheory.crystalline_period_ring_properties :
    UpperTheory.V.Af.Wd.BrFacts := by
  classical
  intro F Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hj
  refine ⟨fun c => ?_, fun L s => ?_, fun M hM => ?_⟩
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_one_iff.2 isFrob_frob) c
    simpa using h1
  · have h2 := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (UpperTheory.V.Loc.PP l) Bw.j _ _ (Bw.e_comm s)
    exact (congrArg (algebraMap ℚ_[l] (Om l)) h2)
  · have hM0 : M ≠ 0 := by omega
    have hfin : ({x : Om l | x ^ M = 1}).Finite := by
      refine (Polynomial.nthRoots M (1 : Om l)).toFinset.finite_toSet.subset fun x hx => ?_
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hM0)] using hx
    haveI := hfin.to_subtype
    have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    refine ⟨⟨_, hfd⟩, fun s hs ζ hζ => Bw.j.injective ?_⟩
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _
      (IntermediateField.subset_adjoin _ _ (show Bw.j ζ ^ M = 1 by rw [← map_pow, hζ, map_one]))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactBaseIntegralToComplex
section
open TensorProduct

private theorem ladder {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ)) (f' : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (h : ∀ x y, f' (Finsupp.single x 1) y = (f (Finsupp.single x 1) y : ℤ)) (u : ℂ ⊗[ℤ] (X →₀ ℤ)) :
    f' (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X u) = TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y (f.lTensor ℂ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul c v =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
    | single x n =>
      have e1 : TensorProduct.finsuppScalarRight ℤ ℤ ℂ X (c ⊗ₜ[ℤ] Finsupp.single x n)
          = ((n : ℂ) * c) • Finsupp.single x (1 : ℂ) := by
        ext x'
        rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
        by_cases hx : x = x'
        · subst hx; simp
        · simp [Finsupp.single_apply, hx]
      have e2 : Finsupp.single x n = n • Finsupp.single x (1 : ℤ) := by simp
      ext y
      rw [e1, map_smul, LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, e2, map_smul,
        Finsupp.smul_apply, Finsupp.smul_apply, h]
      simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring

theorem UpperTheory.exactBase_integral_to_complex :
    UpperTheory.V.Af.BA.ExactBase := by
  intro X Y Z f g f' g' hf hg hfg
  classical
  have hex := Module.Flat.lTensor_exact ℂ hfg
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Z).toAddEquiv
    (f₁₂ := (f.lTensor ℂ).toAddMonoidHom) (f₂₃ := (g.lTensor ℂ).toAddMonoidHom)
    (g₁₂ := f'.toAddMonoidHom) (g₂₃ := g'.toAddMonoidHom) ?_ ?_ hex
  · exact AddMonoidHom.ext fun u => ladder f f' hf u
  · exact AddMonoidHom.ext fun u => ladder g g' hg u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMIntegralOfExistsCM
section
open NumberField in
theorem UpperTheory.exists_CM_integral_of_exists_CM :
    UpperTheory.V.Af.BA.ExCM → UpperTheory.V.Af.BA.ExCMInt := by
  intro h F _ _ _
  obtain ⟨L, i1, i2, i3, i, s, hs, hfix⟩ := h F
  refine ⟨L, i1, i2, i3, RingOfIntegers.mapRingHom i, RingOfIntegers.mapRingHom s, ?_, ?_, ?_⟩
  · intro w x
    exact hs w.embedding (x : L)
  · intro x y hxy
    have h1 : i (x : F) = i (y : F) := congrArg (fun z : 𝓞 L => (z : L)) hxy
    exact RingOfIntegers.ext (i.injective h1)
  · intro x
    constructor
    · intro hx
      have h1 : s (x : L) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hx
      obtain ⟨y, hy⟩ := (hfix _).1 h1
      have hi : IsIntegral ℤ y := by
        have h2 : IsIntegral ℤ (i.toIntAlgHom y) := by
          have : i.toIntAlgHom y = (x : L) := hy
          rw [this]
          exact x.isIntegral_coe
        exact (isIntegral_algHom_iff i.toIntAlgHom i.injective).1 h2
      exact ⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩
    · rintro ⟨y, hy⟩
      have h1 : i (y : F) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hy
      exact RingOfIntegers.ext ((hfix _).2 ⟨_, h1⟩)
end

