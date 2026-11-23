module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUnitMulMemSpanOfReducedIsolatedZero
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

private theorem exists_algHom_complex_ker_eq_maximal (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (m : Ideal A) [m.IsMaximal] : ∃ e : A →ₐ[ℂ] ℂ, ∀ x, e x = 0 ↔ x ∈ m := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := A ⧸ m)
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun x => ?_⟩
  show φ.symm (Ideal.Quotient.mkₐ ℂ m x) = 0 ↔ _
  rw [map_eq_zero_iff _ φ.symm.injective, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

private theorem mem_of_reduced_vanishing_on_zeros (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (J : Ideal A) (hred : IsReduced (A ⧸ J)) (x : A)
    (hx : ∀ e : A →ₐ[ℂ] ℂ, (∀ y ∈ J, e y = 0) → e x = 0) : x ∈ J := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hj : x ∈ J.jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨hJm, hm⟩
    haveI := hm
    obtain ⟨e, he⟩ := exists_algHom_complex_ker_eq_maximal A m
    exact (he x).1 (hx e fun y hy => (he y).2 (hJm hy))
  rw [← Ideal.radical_eq_jacobson] at hj
  obtain ⟨n, hn⟩ := hj
  haveI := hred
  have hnil : IsNilpotent (Ideal.Quotient.mk J x) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 hnil.eq_zero

theorem UpperTheory.Cb.exists_unit_mul_mem_span_of_reduced_isolated_zero :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (d : ℕ) (t : Fin d → A), IsReduced (A ⧸ Ideal.span (Set.range t)) → Finite {e : A →ₐ[ℂ] ℂ // ∀ j, e (t j) = 0} → ∀ e : A →ₐ[ℂ] ℂ, (∀ j, e (t j) = 0) → ∀ b : A, e b = 0 → ∃ (c : A) (g : Fin d → A), e c ≠ 0 ∧ c * b = ∑ l, g l * t l := by
  intro A _ _ _ d t hred hfin e he b hb
  have key : ∀ s : {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0},
      ∃ a : A, e a ≠ 0 ∧ (s.1 ≠ e → s.1 a = 0) := by
    intro s
    by_cases hs : s.1 = e
    · exact ⟨1, by simp, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ : ∃ y, e y ≠ s.1 y := by
        by_contra hcon
        push_neg at hcon
        exact hs (AlgHom.ext fun y => (hcon y).symm)
      refine ⟨y - algebraMap ℂ A (s.1 y), ?_, fun _ => ?_⟩
      · rw [map_sub, AlgHom.commutes]
        exact sub_ne_zero.2 hy
      · rw [map_sub, AlgHom.commutes]
        exact sub_self _
  choose f hf using key
  haveI := Fintype.ofFinite {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0}
  refine ⟨∏ s, f s, ?_⟩
  have hmem : (∏ s, f s) * b ∈ Ideal.span (Set.range t) := by
    apply mem_of_reduced_vanishing_on_zeros A _ hred
    intro e' he'
    have ht : ∀ j, e' (t j) = 0 := fun j => he' _ (Ideal.subset_span ⟨j, rfl⟩)
    by_cases hee : e' = e
    · subst hee
      rw [map_mul, hb, mul_zero]
    · rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ ⟨e', ht⟩) ((hf ⟨e', ht⟩).2 hee),
        zero_mul]
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  refine ⟨g, ?_, hg.symm⟩
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.2 fun s _ => (hf s).1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFunctionFieldGermCompatOfSmooth
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

namespace UpperTheory

private theorem reduced_of_etale_proj (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsReduced R]
    [Algebra.Etale R S] [Module.Projective R S] : IsReduced S := by
  refine ⟨fun s hs => ?_⟩
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual R S, φ s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff R s).1 h)
  have hnil : φ s ∉ nilradical R := by
    rw [nilradical_eq_zero]; simpa using hφ
  rw [nilradical_eq_sInf, Ideal.mem_sInf] at hnil
  push_neg at hnil
  obtain ⟨p, hp, hsp⟩ := hnil
  haveI : p.IsPrime := hp
  let κ := p.ResidueField
  haveI : IsReduced (κ ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field κ (κ ⊗[R] S)
  have h0 : (1 : κ) ⊗ₜ[R] s = 0 := by
    have : IsNilpotent ((Algebra.TensorProduct.includeRight : S →ₐ[R] κ ⊗[R] S) s) := hs.map _
    simpa using this.eq_zero
  have h1 := congrArg ((TensorProduct.rid R κ).toLinearMap ∘ₗ LinearMap.lTensor κ φ) h0
  simp at h1
  rw [Algebra.smul_def, mul_one] at h1
  exact hsp (Ideal.algebraMap_residueField_eq_zero.1 h1)

private theorem reduced_quot (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
    [Module.Projective B B'] (I : Ideal B) [IsReduced (B ⧸ I)] : IsReduced (B' ⧸ I.map (algebraMap B B')) := by
  haveI : IsReduced ((B ⧸ I) ⊗[B] B') := reduced_of_etale_proj (B ⧸ I) ((B ⧸ I) ⊗[B] B')
  have e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' I
  haveI : IsReduced (B' ⊗[B] (B ⧸ I)) := isReduced_of_injective (Algebra.TensorProduct.comm B B' (B ⧸ I)).toRingEquiv (Algebra.TensorProduct.comm B B' (B ⧸ I)).injective
  exact isReduced_of_injective e.toRingEquiv e.injective

private theorem transfer {A A' B B' ι : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [Algebra A A']
    [Algebra.Etale A A'] [Module.Projective A A'] (eA : A ≃+* B) (eA' : A' ≃+* B') (t : ι → B) (t' : ι → B')
    (ht : ∀ j, eA' (algebraMap A A' (eA.symm (t j))) = t' j) (hr : IsReduced (B ⧸ Ideal.span (Set.range t))) :
    IsReduced (B' ⧸ Ideal.span (Set.range t')) := by
  let J : Ideal A := Ideal.span (Set.range fun j => eA.symm (t j))
  have hJ : Ideal.span (Set.range t) = J.map (eA : A →+* B) := by
    simp only [J, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp
  have eq1 : (A ⧸ J) ≃+* (B ⧸ Ideal.span (Set.range t)) := Ideal.quotientEquiv J _ eA hJ
  haveI : IsReduced (A ⧸ J) := isReduced_of_injective eq1 eq1.injective
  haveI := reduced_quot A A' J
  have hJ' : Ideal.span (Set.range t') = (J.map (algebraMap A A')).map (eA' : A' →+* B') := by
    simp only [J, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp [ht]
  have eq2 := Ideal.quotientEquiv (J.map (algebraMap A A')) _ eA' hJ'
  exact isReduced_of_injective eq2.symm eq2.symm.injective

private theorem cover_ring {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [Algebra k X.functionField] {ι : Type} [DecidableEq ι] {U : ι → X.Opens}
    {B : Finset ι → Subalgebra k X.functionField} (h : IsAffCover p U B) (i : ι) :
    IsAffineOpen (U i) ∧ ∃ hg : genericPoint X ∈ U i, ∀ y, y ∈ B {i} ↔
      ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y := by
  have key : ∀ (V : X.Opens) (_ : V = ({i} : Finset ι).inf U), IsAffineOpen V ∧
      ∃ hg : genericPoint X ∈ V, ∀ y, y ∈ B {i} ↔
        ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y := by
    rintro V rfl
    exact ⟨h.affine _ (Finset.singleton_nonempty i), h.ne _, h.ring _ (Finset.singleton_nonempty i)⟩
  exact key (U i) Finset.inf_singleton.symm

private noncomputable def chartEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [Algebra k X.functionField]
    (V : X.Opens) (hg : genericPoint X ∈ V) (B : Subalgebra k X.functionField)
    (h : ∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) : Γ(X, V) ≃+* B :=
  RingEquiv.ofBijective
    (((X.presheaf.germ V (genericPoint X) hg).hom).codRestrict B fun f => (h _).2 ⟨f, rfl⟩)
    (by
      refine ⟨fun a b e => ?_, fun y => ?_⟩
      · haveI : Nonempty V := ⟨⟨_, hg⟩⟩
        exact germ_injective_of_isIntegral X _ hg (congrArg Subtype.val e)
      · obtain ⟨f, hf⟩ := (h y.1).1 y.2
        exact ⟨f, Subtype.ext hf⟩)

end UpperTheory

theorem UpperTheory.Cb.finite_etale_function_field_germ_compat_of_smooth :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (c1 : Y ⟶ Z), c1 ≫ s = s' → IsFinite c1 → Etale c1 → ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField], inst = ffAlg s → inst' = ffAlg s' → ∀ [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c1.app V g)) → ∀ (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField] [Algebra F Y.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens), IsFinCover ℂ Z.functionField x → IsAffCover s U (rB ℂ Z.functionField x) → IsAffCover s' (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x) → IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → IsReduced ((rB ℂ Y.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Y.functionField x j⟩ : rB ℂ Y.functionField x {0})))) := by
  intro d Z Y _ _ s s' _ _ c1 hc hfin het inst inst' _ _ _ _ hcomp F _ _ _ _ _ _ _ x U _ hZ hY hred
  obtain ⟨hW, hg, hring⟩ := cover_ring hZ 0
  obtain ⟨-, hg', hring'⟩ := cover_ring hY 0
  letI : Algebra Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := (c1.app (U 0)).hom.toAlgebra
  haveI : Module.Finite Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := sec_finite (s := s) (s' := s') (f := c1) hW
  haveI : Algebra.Etale Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := sec_etale (s := s) (s' := s') (f := c1) hW
  haveI := projective_of_etale Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0)
  let eZ := chartEquiv (U 0) hg _ hring
  let eY := chartEquiv (c1 ⁻¹ᵁ U 0) hg' _ hring'
  refine transfer eZ eY _ _ (fun j => ?_) hred
  apply Subtype.ext
  obtain ⟨f, hf⟩ := eZ.surjective ⟨_, tco_mem ℂ Z.functionField x j⟩
  rw [← hf, RingEquiv.symm_apply_apply]
  have h1 : (Z.presheaf.germ (U 0) (genericPoint Z) hg).hom f = algebraMap F Z.functionField (x j.succ / x 0) :=
    congrArg Subtype.val hf
  have h2 := hcomp (U 0) hg hg' f
  rw [h1, ← IsScalarTower.algebraMap_apply] at h2
  exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

namespace UpperTheory.A

theorem generic_map {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) [Etale c] :
    c (genericPoint Y) = genericPoint Z := by
  have ho : IsOpenMap c := c.isOpenMap
  have hd : DenseRange c := by
    have : (Set.range c).Nonempty := Set.range_nonempty _
    exact (ho.isOpen_range.dense this)
  have h1 := (genericPoint_spec Y).image c.continuous
  rw [Set.image_univ] at h1
  have h2 : closure (Set.range c) = Set.univ := hd.closure_range
  rw [h2] at h1
  exact (h1.eq (genericPoint_spec Z))

noncomputable def ffHom {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) [Etale c] :
    Z.functionField ⟶ Y.functionField :=
  Z.presheaf.stalkSpecializes (specializes_of_eq (generic_map c)) ≫ c.stalkMap (genericPoint Y)

theorem germ_ffHom {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) [Etale c]
    (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) :
    Z.presheaf.germ V (genericPoint Z) hV ≫ ffHom c = c.app V ≫ Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV' := by
  rw [ffHom, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.Hom.germ_stalkMap c V (genericPoint Y) hV'

theorem exists_ffMap {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c : Y ⟶ Z)
    (hc : c ≫ p = p') [Etale c] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField]
    (hK : instK = ffAlg p) (hL : instL = ffAlg p') :
    ∃ ψ : Z.functionField →ₐ[ℂ] Y.functionField,
      ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g) := by
  have aK : ∀ r : ℂ, algebraMap ℂ Z.functionField r = (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    intro r; subst hK; rfl
  have aL : ∀ r : ℂ, algebraMap ℂ Y.functionField r = (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom
      (p'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    intro r; subst hL; rfl
  refine ⟨{ (ffHom c).hom with commutes' := fun r => ?_ }, fun V hV hV' g => ?_⟩
  · have h := germ_ffHom c ⊤ trivial trivial
    have h2 := congrArg (fun f => f.hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r))) h
    change (ffHom c).hom (algebraMap ℂ Z.functionField r) = _
    rw [aK, aL, ← hc, Scheme.Hom.comp_appTop]
    exact h2
  · have h := congrArg (fun f => f.hom g) (germ_ffHom c V hV hV')
    exact h

noncomputable def ringOn {Y : Scheme.{0}} [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [instL : Algebra ℂ Y.functionField]
    (hL : instL = ffAlg p') (W : Y.Opens) (hW : genericPoint Y ∈ W) : Subalgebra ℂ Y.functionField where
  carrier := {y | ∃ f : Γ(Y, W), (Y.presheaf.germ W (genericPoint Y) hW).hom f = y}
  mul_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, map_mul _ _ _⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, map_add _ _ _⟩
  algebraMap_mem' := by
    intro r
    subst hL
    refine ⟨(Y.presheaf.map (homOfLE le_top).op).hom (p'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), ?_⟩
    have := TopCat.Presheaf.germ_res Y.presheaf (homOfLE (le_top : W ≤ ⊤)) (genericPoint Y) hW
    exact congrArg (fun f => f.hom (p'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r))) this

def joinCover {Z Y : Scheme.{0}} {ι : Type} (c1 c2 : Y ⟶ Z) (U : ι → Z.Opens) : ι ⊕ₗ ι → Y.Opens :=
  fun i => Sum.elim (fun j => c1 ⁻¹ᵁ U j) (fun j => c2 ⁻¹ᵁ U j) (ofLex i)

theorem generic_mem_inf {Y : Scheme.{0}} [IsIntegral Y] {κ : Type} (V : κ → Y.Opens) (h : ∀ k, genericPoint Y ∈ V k)
    (I : Finset κ) : genericPoint Y ∈ I.inf V := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact ⟨h a, ih⟩

theorem generic_mem_join {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {ι : Type} (c1 c2 : Y ⟶ Z) [Etale c1] [Etale c2]
    (U : ι → Z.Opens) (hU : ∀ i, genericPoint Z ∈ U i) (k : ι ⊕ₗ ι) : genericPoint Y ∈ joinCover c1 c2 U k := by
  rcases h : ofLex k with j | j
  · simp only [joinCover, h, Sum.elim_inl]
    change c1 (genericPoint Y) ∈ U j
    rw [generic_map c1]; exact hU j
  · simp only [joinCover, h, Sum.elim_inr]
    change c2 (genericPoint Y) ∈ U j
    rw [generic_map c2]; exact hU j

theorem isSeparated_of_hom {Z Y : Scheme.{0}} [Z.IsSeparated] (c : Y ⟶ Z) [IsSeparated c] : Y.IsSeparated := by
  constructor
  have e : Limits.terminal.from Y = c ≫ Limits.terminal.from Z := Subsingleton.elim _ _
  rw [e]
  infer_instance

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_proj {Z : Scheme.{0}} (p : Z ⟶ Sp ℂ) (hP : IsProjOver p) : Z.IsSeparated := by
  obtain ⟨N, i, hi, -⟩ := hP
  haveI := hi
  haveI : (PSpace ℂ N).IsSeparated := isSeparated_of_hom (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ))
  exact isSeparated_of_hom i

theorem isAffineOpen_join {Z Y : Scheme.{0}} [Y.IsSeparated] {ι : Type} (c1 c2 : Y ⟶ Z) [IsFinite c1] [IsFinite c2]
    (U : ι → Z.Opens) (hU : ∀ i, IsAffineOpen (U i)) (I : Finset (ι ⊕ₗ ι)) (hI : I.Nonempty) :
    IsAffineOpen (I.inf (joinCover c1 c2 U)) := by
  classical
  have hk : ∀ k, IsAffineOpen (joinCover c1 c2 U k) := by
    intro k
    rcases h : ofLex k with j | j
    · simp only [joinCover, h, Sum.elim_inl]; exact (hU j).preimage c1
    · simp only [joinCover, h, Sum.elim_inr]; exact (hU j).preimage c2
  induction hI using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hk a
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.inf_insert]
    exact (hk a).inf ih

theorem isAffCover_join {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z)
    [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] (hP : IsProjOver p) [instK : Algebra ℂ Z.functionField]
    [instL : Algebra ℂ Y.functionField] (hL : instL = ffAlg p') {ι : Type} (U : ι → Z.Opens)
    (B : Finset ι → Subalgebra ℂ Z.functionField) (hU : IsAffCover p U B) :
    IsAffCover p' (joinCover c1 c2 U) fun I => ringOn p' hL (I.inf (joinCover c1 c2 U))
      (generic_mem_inf _ (generic_mem_join c1 c2 U fun i => by simpa using hU.ne {i}) I) := by
  haveI := isSeparated_of_proj p hP
  haveI : Y.IsSeparated := isSeparated_of_hom c1
  refine ⟨by subst hL; rfl, fun I hI => ?_, ?_, fun I => generic_mem_inf _ (generic_mem_join c1 c2 U fun i => by simpa using hU.ne {i}) I, fun I _ y => Iff.rfl⟩
  · exact isAffineOpen_join c1 c2 U (fun i => by simpa using hU.affine {i} ⟨i, by simp⟩) I hI
  · refine top_le_iff.1 fun x _ => ?_
    have hx : c1 x ∈ (⊤ : Z.Opens) := trivial
    rw [← hU.cover] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨toLex (Sum.inl i), hi⟩

end UpperTheory.A
end

