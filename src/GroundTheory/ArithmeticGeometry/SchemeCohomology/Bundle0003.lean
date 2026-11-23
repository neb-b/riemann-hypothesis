module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InjectiveCech
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistAway
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.Cartan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

section

variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

lemma res_congr {n : ℕ} (σ : Cochain P U n) {j₁ j₂ : Fin (n + 1) → ι} (h : j₁ = j₂)
    {V : Opens X} (h₁ : V ≤ inter U j₁) (h₂ : V ≤ inter U j₂) :
    res P h₁ (σ j₁) = res P h₂ (σ j₂) := by
  subst h
  rfl

lemma le_inter_const {n : ℕ} (a : ι) : U a ≤ inter U (fun _ : Fin n => a) := by
  intro x hx
  rw [mem_inter_iff]
  exact fun _ => hx

lemma inter_succ {n : ℕ} (i : Fin (n + 2) → ι) :
    inter U i = U (i 0) ⊓ inter U (i ∘ Fin.succ) := by
  ext x
  simp only [SetLike.mem_coe, Opens.mem_inf, mem_inter_iff, Fin.forall_fin_succ, Function.comp]

lemma d_zero_apply (σ : Cochain P U 0) (i : Fin 2 → ι) :
    d P U 0 σ i = res P (inter_le_comp U i (0 : Fin 2).succAbove) (σ (i ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U i (1 : Fin 2).succAbove) (σ (i ∘ (1 : Fin 2).succAbove)) := by
  rw [d_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

def constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) : Cochain P U 0 :=
  fun i => res P ((inter_le U i 0).trans (hUV (i 0))) s

lemma d_constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) :
    d P U 0 (constCochain P U hUV s) = 0 := by
  funext i
  rw [d_zero_apply]
  simp only [constCochain, res_res, sub_self]
  rfl

end

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)


include hP in
lemma exists_glue {ι : Type w} (U : ι → Opens X) (V : Opens X) (hUV : ∀ a, U a ≤ V)
    (hV : V ≤ iSup U) (τ : Cochain P U 0) (hτ : d P U 0 τ = 0) :
    ∃ t : P.obj (op V), ∀ i : Fin 1 → ι,
      res P ((inter_le U i 0).trans (hUV (i 0))) t = τ i := by
  let sf : ∀ j, P.obj (op (U j)) := fun j => res P (le_inter_const U j) (τ (fun _ => j))
  have compat : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    have h := congrFun hτ ![i, j]
    rw [d_zero_apply] at h
    have hle : U i ⊓ U j ≤ inter U ![i, j] := by
      intro x hx
      rw [mem_inter_iff]
      intro a
      fin_cases a
      · exact hx.1
      · exact hx.2
    rw [Pi.zero_apply] at h
    have h' := congrArg (res P hle) h
    rw [map_sub, res_res, res_res, map_zero, sub_eq_zero] at h'
    have e0 : (![i, j] ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => j := by
      funext a; fin_cases a; rfl
    have e1 : (![i, j] ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => i := by
      funext a; fin_cases a; rfl
    rw [res_congr P U τ e0 _ ((inf_le_right).trans (le_inter_const U j)),
      res_congr P U τ e1 _ ((inf_le_left).trans (le_inter_const U i))] at h'
    change res P inf_le_left (sf i) = res P inf_le_right (sf j)
    simp only [sf, res_res]
    exact h'.symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    U V (fun a => homOfLE (hUV a)) hV sf compat
  refine ⟨t, fun i => ?_⟩
  have hi : (fun _ : Fin 1 => i 0) = i := funext fun a => by rw [Subsingleton.elim a 0]
  have ht' : res P (hUV (i 0)) t = sf (i 0) := ht (i 0)
  rw [← res_res P (inter_le U i 0) (hUV (i 0)), ht']
  simp only [sf, res_res]
  exact (res_congr P U τ hi _ le_rfl).trans (res_refl _ _ _)


variable {P} in
lemma CechAcyclic.of_shortExact' {ι : Type w} (U : ι → Opens X)
    {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q) (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by
  intro n σ hσ
  choose τ hτ using fun i => hsurj i (σ i)
  have hτ' : push U g (n + 1) τ = σ := funext hτ
  have h0 : push U g (n + 2) (d I U (n + 1) τ) = 0 := by rw [push_d, hτ', hσ]
  choose ρ hρ using fun j => hex j _ (congrFun h0 j)
  have hρ' : push U f (n + 2) ρ = d I U (n + 1) τ := funext hρ
  have hρc : d F U (n + 2) ρ = 0 := by
    apply push_injective U f (n + 3) (fun j => hinj j)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨α, hα⟩ := hF (n + 1) ρ hρc
  have hc : d I U (n + 1) (τ - push U f (n + 1) α) = 0 := by
    rw [map_sub, ← push_d, hα, hρ', sub_self]
  obtain ⟨β, hβ⟩ := hI n _ hc
  refine ⟨push U g n β, ?_⟩
  rw [← push_d, hβ, map_sub, hτ', push_comp, hfg, push_zero', sub_zero]

section

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

include hS in
lemma app_injective_of_shortExact (W : (Opens X)ᵒᵖ) : Function.Injective (S.f.hom.app W) := by
  have : Mono S.f := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this W)

include hS in
lemma app_exact_of_shortExact (W : Opens X) (y : S.X₂.obj.obj (op W))
    (hy : S.g.hom.app (op W) y = 0) : ∃ x, S.f.hom.app (op W) x = y :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.1 hS.2 y hy

set_option backward.isDefEq.respectTransparency false in
lemma comp_hom_eq_zero : S.f.hom ≫ S.g.hom = 0 := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, S.zero]
  rfl

lemma app_comp_apply_eq_zero (W : (Opens X)ᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, comp_hom_eq_zero]
  rfl

end

variable (B : Opens X → Prop)

def CechCondition (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), (∀ a, B (U a)) → iSup U = V →
    CechAcyclic F.obj U

variable {B}

lemma inter_mem (hinf : ∀ V W, B V → B W → B (V ⊓ W)) {ι : Type w} (U : ι → Opens X)
    (hU : ∀ a, B (U a)) {n : ℕ} (i : Fin (n + 1) → ι) : B (inter U i) := by
  induction n with
  | zero =>
    have : inter U i = U (i 0) := le_antisymm (inter_le U i 0) (by
      intro x hx
      rw [mem_inter_iff]
      intro a
      rwa [Fin.fin_one_eq_zero a])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [inter_succ]
    exact hinf _ _ (hU _) (ih _)

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A] (n : ℕ)

abbrev grading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  homogeneousSubmodule (Fin (n + 1)) A

end ProjSpace

open ProjSpace

abbrev projectiveSpace (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

def stdOpen (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) : (projectiveSpace A n).Opens :=
  Proj.basicOpen (grading A n) (X j)

def xprod {p : ℕ} (i : Fin p → Fin (n + 1)) : MvPolynomial (Fin (n + 1)) A := ∏ a, X (i a)

lemma xprod_mem {p : ℕ} (i : Fin p → Fin (n + 1)) : xprod (A := A) i ∈ grading A n p := by
  have := IsHomogeneous.prod (Finset.univ : Finset (Fin p)) (fun a => (X (i a) : MvPolynomial _ A))
    (fun _ => 1) (fun a _ => isHomogeneous_X A (i a))
  simpa [xprod] using this

lemma X_mem (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) A) ∈ grading A n 1 :=
  isHomogeneous_X A j

lemma xprod_succ {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    xprod (A := A) i = X (i 0) * xprod (A := A) (i ∘ Fin.succ) := by
  simp [xprod, Fin.prod_univ_succ]

lemma inter_stdOpen {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i =
      Proj.basicOpen (grading A n) (xprod i) := by
  ext x
  change x ∈ inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i ↔ _
  rw [mem_inter_iff]
  change (∀ a, x ∈ stdOpen A n (i a)) ↔ x ∈ Proj.basicOpen (grading A n) (xprod i)
  change (∀ a, X (i a) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    (∏ a, X (i a)) ∉ x.asHomogeneousIdeal.toIdeal
  have := x.isPrime
  rw [Ideal.IsPrime.prod_mem_iff]
  simp

lemma isAffineOpen_inter {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    IsAffineOpen (inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i) := by
  rw [inter_stdOpen]
  exact Proj.isAffineOpen_basicOpen (grading A n) (xprod i) (xprod_mem i) (Nat.succ_pos p)

lemma isAffineOpen_stdOpen (j : Fin (n + 1)) : IsAffineOpen (stdOpen A n j) :=
  Proj.isAffineOpen_basicOpen (grading A n) (X j) (X_mem j) Nat.one_pos

lemma iSup_stdOpen : ⨆ j, stdOpen A n j = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing

universe u

theorem IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by
  have : IsDomain R := IsRegularLocalRing.isDomain
  have hreg := (isRegularLocalRing_iff R).mp inferInstance
  have hle : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [← hreg] at h; exact_mod_cast h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · have hbot : maximalIdeal R = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have : IsDiscreteValuationRing R := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp (by
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; exact h1)
    infer_instance

theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : UniqueFactorizationMonoid R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one h
  inferInstance

theorem IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsIntegrallyClosed R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one h
  inferInstance

theorem ringKrullDim_localization_le_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (Localization.AtPrime (Q.under P)) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  have h : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact hmap
  calc ringKrullDim (Localization.AtPrime Q)
      ≤ (maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
        ringKrullDim_le_spanFinrank_maximalIdeal _
    _ ≤ (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
        rw [← h]
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _
          (maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
    _ = ringKrullDim (Localization.AtPrime p) :=
        (isRegularLocalRing_iff (Localization.AtPrime p)).mp inferInstance

open AlgebraicGeometry CategoryTheory

theorem ringKrullDim_stalk_le_of_smoothOfRelativeDimension {X : Scheme.{u}} {k : Type u} [Field k]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hUtop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ Subsingleton.elim (f.base x) y ▸ e hx
  subst hUtop
  let eΓ := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have : IsRegularRing Γ(Spec (.of k), ⊤) := IsRegularRing.of_ringEquiv eΓ.symm
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) := isNoetherianRing_of_ringEquiv k eΓ.symm
  have hdim0 : ringKrullDim Γ(Spec (.of k), ⊤) = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv eΓ, ringKrullDim_eq_zero_of_field]
  algebraize [(f.appLE ⊤ V e).hom]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n
    Γ(Spec (.of k), ⊤) Γ(X, V)
  algebraize [g.toRingHom]
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV.isLocalization_stalk ⟨x, hx⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, V)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv]
  refine (ringKrullDim_localization_le_of_etale (P := MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))
    P).trans ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (P.under (MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))) (Localization.AtPrime _)]
  refine (Ideal.height_le_ringKrullDim_of_isPrime).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hdim0]
  simp

end GroundTheory.Arith.SchemeCoh
end

