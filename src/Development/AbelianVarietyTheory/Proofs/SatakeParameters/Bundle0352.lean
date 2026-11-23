module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem exists_basis_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ)
    (hb : letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ]))) :
    ∃ g : Fin d → A, (∀ j, e (g j) = 0) ∧
      (∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  obtain ⟨b⟩ := hb
  have hs : Function.Surjective (algebraMap A ℂ) := fun c => ⟨algebraMap ℂ A c, he c⟩
  have key : ∀ (c : ℂ) (w : Ω[A⁄ℂ]), (1 : ℂ) ⊗ₜ[A] (c • w) = c • ((1 : ℂ) ⊗ₜ[A] w) := by
    intro c w
    rw [← algebraMap_smul A c w, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    exact he c
  let φ : A →ₗ[ℂ] ℂ ⊗[A] Ω[A⁄ℂ] :=
    { toFun := fun a => (1 : ℂ) ⊗ₜ[A] D ℂ A a
      map_add' := fun a b => by rw [map_add (f := _), TensorProduct.tmul_add]
      map_smul' := fun c a => by rw [(D ℂ A).map_smul c a, key]; rfl }
  have hφ : ∀ x : RingHom.ker (algebraMap A ℂ), φ x =
      kerCotangentToTensor ℂ A ℂ ((RingHom.ker (algebraMap A ℂ)).toCotangent x) :=
    fun x => (kerCotangentToTensor_toCotangent ℂ A ℂ x).symm
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective ℂ A ℂ hs
  have hsurj : ∀ v, ∃ x : RingHom.ker (algebraMap A ℂ), φ x = v := by
    intro v
    obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ A ℂ hs v).mp (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    exact ⟨x, (hφ x).trans hy⟩
  have hker : ∀ x : RingHom.ker (algebraMap A ℂ), φ x = 0 → (x : A) ∈ RingHom.ker e ^ 2 := by
    intro x hx
    rw [hφ, ← map_zero (kerCotangentToTensor ℂ A ℂ), hinj.eq_iff, Ideal.toCotangent_eq_zero] at hx
    exact hx
  choose g hg using fun j => hsurj (b j)
  have hmemg : ∀ c : Fin d → ℂ, ∑ j, c j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) := fun c =>
    Ideal.sum_mem _ fun j _ => by rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (g j).2
  have hφg : ∀ c : Fin d → ℂ, φ (∑ j, c j • (g j : A)) = ∑ j, c j • b j := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp only [map_smul, hg]
  refine ⟨fun j => g j, fun j => (g j).2, ?_, ?_⟩
  · intro a ha
    refine ⟨fun j => b.repr (φ a) j, ?_⟩
    have hmem : a - ∑ j, b.repr (φ a) j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) :=
      Ideal.sub_mem _ ha (hmemg _)
    refine hker ⟨_, hmem⟩ ?_
    change φ (a - _) = 0
    rw [map_sub, hφg, b.sum_repr, sub_self]
  · intro c hc
    have h0 : φ (∑ j, c j • (g j : A)) = 0 := by
      have h1 := hφ ⟨_, hmemg c⟩
      rw [(Ideal.toCotangent_eq_zero _ _).2 hc, map_zero] at h1
      exact h1
    rw [hφg] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h0 i

end GlobalTheory.CotDim

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem nonempty_basis_fibre {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ) (t : A) (ht : e t ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away t)] :
    letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ])) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  let et : Localization.Away t →+* ℂ := IsLocalization.Away.lift t (isUnit_iff_ne_zero.2 ht)
  letI : Algebra (Localization.Away t) ℂ := et.toAlgebra
  haveI : IsScalarTower A (Localization.Away t) ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq t (isUnit_iff_ne_zero.2 ht) a).symm
  haveI : Nontrivial (Localization.Away t) := et.domain_nontrivial
  haveI : Algebra.FormallyEtale A (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.IsStandardSmooth ℂ (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := ℂ) (S := Localization.Away t) d
  haveI : Module.Finite (Localization.Away t) Ω[Localization.Away t⁄ℂ] := Module.finite_of_rank_eq_nat hr
  let b0 := Module.finBasisOfFinrankEq (Localization.Away t) Ω[Localization.Away t⁄ℂ]
    (Module.finrank_eq_of_rank_eq hr)
  let b1 : Module.Basis (Fin d) ℂ (ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ]) := b0.baseChange ℂ
  let E1 : ℂ ⊗[Localization.Away t] (Localization.Away t ⊗[A] Ω[A⁄ℂ]) ≃ₗ[ℂ]
      ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
      (tensorKaehlerEquivOfFormallyEtale ℂ A (Localization.Away t))
  let E2 := TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) ℂ ℂ Ω[A⁄ℂ]
  exact ⟨(b1.map E1.symm).map E2⟩

end GlobalTheory.CotDim

theorem GlobalTheory.CotDim.exists_cotangent_basis : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (U : X.Opens), IsAffineOpen U → ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
    let e : Sec p U →+* ℂ := CxPts.evHom hy; ∃ g : Fin d → Sec p U, (∀ j, e (g j) = 0) ∧
      (∀ a : Sec p U, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  intro X p d _ U hU y hy e
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c => by
    exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hts, ht⟩ : ∃ t : Sec p U, t ∈ s ∧ e t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (↑s : Set Γ(X, U)) ≤ RingHom.ker (e : Γ(X, U) →+* ℂ) :=
      Ideal.span_le.2 fun t ht => hcon t ht
    have h1 : (1 : Γ(X, U)) ∈ RingHom.ker (e : Γ(X, U) →+* ℂ) := hle (by rw [hs]; exact Submodule.mem_top)
    have h2 : e 1 = 0 := h1
    rw [map_one] at h2
    exact one_ne_zero h2
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
    (@h t hts (Localization.Away t) _ (inferInstance : Algebra (Sec p U) (Localization.Away t))
      (by exact (inferInstance : IsLocalization (Submonoid.powers t) (Localization.Away t))))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away (t : Sec p U)) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq ℂ (Sec p U) (Localization.Away (t : Sec p U))]
    first
      | exact h₁
      | (convert h₁ using 1 <;> rfl)
  exact GlobalTheory.CotDim.exists_basis_mod_sq e he d (GlobalTheory.CotDim.nonempty_basis_fibre e he d t ht)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioLinear
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatLin

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac MvPolynomial

theorem frac_smul {N : ℕ} (V : (PSpace ℂ N).Opens) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) (hV : V ≤ Proj.basicOpen (grading ℂ N) g) (c : ℂ)
    (hcf : c • f ∈ grading ℂ N 1) :
    frac (grading ℂ N) V (c • f) g hcf hg hV =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c *
        frac (grading ℂ N) V f g hf hg hV := by
  rw [← algebraMap_sections_eq]
  refine ext fun x hx => ?_
  obtain ⟨i, hi⟩ := exists_mem_chart ℂ N x
  have hW : V ⊓ chart ℂ N i ≤ V := inf_le_left
  have hxW : x ∈ V ⊓ chart ℂ N i := ⟨hx, hi⟩
  rw [← ev_resG hW x hxW, ← ev_resG hW x hxW, map_mul, resG_algebraMap, resG_frac, resG_frac,
    ← formOn_C (hi := (inf_le_right : V ⊓ chart ℂ N i ≤ chart ℂ N i)), formOn]
  congr 1
  refine (frac_mul_eq ?_).symm
  rw [smul_eq_C_mul]
  ring

theorem app_const {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) (hι : ι ≫ PSpace.str ℂ N = p)
    (V : (PSpace ℂ N).Opens) (c : ℂ) :
    (ι.app V).hom (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c) =
      algebraMap ℂ (Sec p (ι ⁻¹ᵁ V)) c := by
  subst hι
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (ι ≫ PSpace.str ℂ N).appLE ⊤ (ι ⁻¹ᵁ V) _).hom c
  rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE]
  rfl

theorem fRatio_add {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (f₁ f₂ g : MvPolynomial (Fin (N + 1)) ℂ)
    (h₁ : f₁ ∈ grading ℂ N 1) (h₂ : f₂ ∈ grading ℂ N 1) (h : f₁ + f₂ ∈ grading ℂ N 1)
    (hg : g ∈ grading ℂ N 1) :
    fRatio ι (f₁ + f₂) g h hg = fRatio ι f₁ g h₁ hg + fRatio ι f₂ g h₂ hg := by
  unfold fRatio
  rw [frac_add (ha := h₁) (ha₂ := h₂)]
  exact map_add _ _ _

theorem fRatio_zero {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (g : MvPolynomial (Fin (N + 1)) ℂ)
    (h : (0 : MvPolynomial (Fin (N + 1)) ℂ) ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    fRatio ι 0 g h hg = 0 := by
  unfold fRatio
  rw [frac_zero]
  exact map_zero _

theorem fRatio_smul {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : ι ≫ PSpace.str ℂ N = p) (f g : MvPolynomial (Fin (N + 1)) ℂ) (c : ℂ)
    (hf : f ∈ grading ℂ N 1) (h : c • f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    (show Sec p (fOpen ι g) from fRatio ι (c • f) g h hg) = c • (show Sec p (fOpen ι g) from fRatio ι f g hf hg) := by
  have e := app_const p ι hι (Proj.basicOpen (grading ℂ N) g) c
  refine Eq.trans ?_ (Algebra.smul_def (A := Sec p (fOpen ι g)) c _).symm
  refine Eq.trans ?_ (congrArg (· * (show Sec p (fOpen ι g) from fRatio ι f g hf hg)) e)
  unfold fRatio
  rw [frac_smul _ f g hf hg le_rfl c h]
  exact map_mul _ _ _

end GlobalTheory.EtProj.RatLin


open GlobalTheory.EtProj.RatLin in
theorem GlobalTheory.EtProj.fRatio_linear : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (c : Fin (N + 1) → ℂ) (hf : (∑ l, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1), let U := GlobalTheory.EtProj.fOpen ι g; let q : Sec p U := GlobalTheory.EtProj.fRatio ι (∑ l, c l • MvPolynomial.X l) g hf hg; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; q = ∑ l, c l • r l := by
  intro X p N ι hι g hg c hf U q r
  have key : ∀ (s : Finset (Fin (N + 1)))
      (h : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1),
      (show Sec p U from GlobalTheory.EtProj.fRatio ι (∑ l ∈ s, c l • MvPolynomial.X l) g h hg) = ∑ l ∈ s, c l • r l := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact fRatio_zero ι g _ hg
    | insert a s ha ih =>
      intro h
      have hs : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N l)
      have ha' : (c a • MvPolynomial.X a : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N a)
      simp only [Finset.sum_insert ha]
      rw [fRatio_add ι _ _ g ha' hs _ hg, ← ih hs]
      congr 1
      exact fRatio_smul p ι hι _ g (c a) (GlobalTheory.ProjSpace.X_mem ℂ N a) ha' hg
  exact key Finset.univ hf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibFin

variable (k : Type) [Field k] {F : Type} (K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} (x : Fin (d + 1) → F)

abbrev coordIdeal : Ideal (rB k K x {0}) :=
  Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))

def incl : rA k x {0} →ₐ[k] rB k K x {0} where
  toFun a := ⟨algebraMap F K a, (integralClosure (rA k x {0}) K).algebraMap_mem a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by ext; simp [← IsScalarTower.algebraMap_apply]

theorem coe_incl (a : rA k x {0}) : (incl k K x a : K) = algebraMap F K a := rfl

theorem mk_incl (hpd : IsPd k x) : ∃ ε : rA k x {0} →ₐ[k] k,
    (Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x) = (Algebra.ofId k _).comp ε := by
  obtain ⟨e, he⟩ := GlobalTheory.PD.rA_single_polyEquiv k F d x hpd 0
  refine ⟨(MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom, ?_⟩
  have key : ((Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x)).comp e.toAlgHom =
      ((Algebra.ofId k _).comp ((MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom)).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : incl k K x (e (MvPolynomial.X j)) = (⟨_, tco_mem k K x j⟩ : rB k K x {0}) := by
      apply Subtype.ext
      rw [coe_incl, he j, Fin.succAbove_zero]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk _ (incl k K x (e (MvPolynomial.X j))) =
      Algebra.ofId k _ (MvPolynomial.aeval (0 : Fin d → k) (e.symm (e (MvPolynomial.X j))))
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X, Pi.zero_apply, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
  ext a
  have := congrArg (fun φ : MvPolynomial (Fin d) k →ₐ[k] _ => φ (e.symm a)) key
  simpa using this

theorem finite_quot (h : IsFinCover k K x) : Module.Finite k (rB k K x {0} ⧸ coordIdeal k K x) := by
  haveI := h.smooth 0
  haveI : Algebra.FiniteType k (rB k K x {0} ⧸ coordIdeal k K x) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨ε, hε⟩ := mk_incl k K x h.pd
  have hε' : (algebraMap k (rB k K x {0} ⧸ coordIdeal k K x)).comp ε.toRingHom =
      (Ideal.Quotient.mk (coordIdeal k K x)).comp (incl k K x).toRingHom :=
    RingHom.ext fun a => by simpa using (AlgHom.congr_fun hε a).symm
  have hcomp : (rB k K x {0}).val.toRingHom.comp (incl k K x).toRingHom = algebraMap (rA k x {0}) K :=
    RingHom.ext fun a => rfl
  haveI : Algebra.IsIntegral k (rB k K x {0} ⧸ coordIdeal k K x) := ⟨fun q => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA k x {0}) (b : K) := b.2
    have hq : Polynomial.eval₂ (incl k K x).toRingHom b p = 0 := by
      apply Subtype.ext
      change (rB k K x {0}).val.toRingHom (Polynomial.eval₂ (incl k K x).toRingHom b p) = (0 : K)
      rw [Polynomial.hom_eval₂, hcomp]
      exact hp
    refine ⟨p.map ε.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hε', ← Polynomial.hom_eval₂, hq, map_zero]⟩
  exact Algebra.IsIntegral.finite

theorem fib_finite_and_sep [IsAlgClosed k] (h : IsFinCover k K x)
    (hred : IsReduced (rB k K x {0} ⧸ coordIdeal k K x)) :
    Finite (fib k K x) ∧ ∀ f : rB k K x {0}, (∀ e : fib k K x, e.1 f = 0) → f ∈ coordIdeal k K x := by
  haveI := finite_quot k K x h
  have hker : ∀ e : fib k K x, coordIdeal k K x ≤ RingHom.ker e.1 := fun e => by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact e.2 j
  let L : fib k K x → (rB k K x {0} ⧸ coordIdeal k K x →ₐ[k] k) := fun e =>
    Ideal.Quotient.liftₐ _ e.1 (fun a ha => hker e ha)
  have hL : ∀ e f, L e (Ideal.Quotient.mk _ f) = e.1 f := fun e f => rfl
  refine ⟨Finite.of_injective L fun e₁ e₂ he => Subtype.ext (AlgHom.ext fun f => by rw [← hL, ← hL, he]),
    fun f hf => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsArtinianRing (rB k K x {0} ⧸ coordIdeal k K x) := IsArtinianRing.of_finite k _
  have hmem : Ideal.Quotient.mk (coordIdeal k K x) f ∈ Ideal.jacobson (⊥ : Ideal (rB k K x {0} ⧸ coordIdeal k K x)) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    haveI := hm.isPrime
    haveI : Module.Finite k (_ ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
    haveI : Algebra.IsIntegral k (_ ⧸ m) := Algebra.IsIntegral.of_finite k _
    have hbij : Function.Bijective (algebraMap k (_ ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let ψ := (AlgEquiv.ofBijective (Algebra.ofId k (_ ⧸ m)) hbij).symm
    let χ := (ψ.toAlgHom.comp (Ideal.Quotient.mkₐ k m)).comp (Ideal.Quotient.mkₐ k (coordIdeal k K x))
    have hχ : ∀ j : Fin d, χ ⟨_, tco_mem k K x j⟩ = 0 := fun j => by
      have hz : Ideal.Quotient.mkₐ k (coordIdeal k K x) ⟨_, tco_mem k K x j⟩ = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2
          (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
      simp only [χ, AlgHom.comp_apply, hz, map_zero]
    have h0 : ψ (Ideal.Quotient.mk m (Ideal.Quotient.mk (coordIdeal k K x) f)) = 0 := hf ⟨χ, hχ⟩
    rw [map_eq_zero_iff _ ψ.injective, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := rB k K x {0} ⧸ coordIdeal k K x)
  have hpow : (Ideal.Quotient.mk (coordIdeal k K x) f) ^ n = 0 := by
    have := Ideal.pow_mem_pow hmem n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  exact IsNilpotent.eq_zero ⟨n, hpow⟩

end GlobalTheory.PD.FibFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteComplexPointsTransversalZeros
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TransvZeros

theorem mem_minimalPrimes_of_le_sup_sq {A : Type} [CommRing A] {I m : Ideal A} [hm : m.IsMaximal]
    (hfg : m.FG) (hI : I ≤ m) (hsq : m ≤ I ⊔ m ^ 2) : m ∈ I.minimalPrimes := by
  refine ⟨⟨hm.isPrime, hI⟩, fun P hP hPm => ?_⟩
  obtain ⟨hPp, hIP⟩ := hP
  let π := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcm : (m.map π).comap π = m := by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.2 hI]
  have hcP : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.2 hIP]
  have hidem : IsIdempotentElem (m.map π) := by
    refine le_antisymm Ideal.mul_le_left ?_
    have h1 : m.map π ≤ (I ⊔ m ^ 2).map π := Ideal.map_mono hsq
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, pow_two] at h1
    exact h1
  obtain ⟨e, he, hme⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (hfg.map π)).1 hidem
  have hPq : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ
    (by rw [Ideal.mk_ker]; exact hIP)
  have hem : e ∈ m.map π := hme ▸ Ideal.mem_span_singleton_self e
  have hne : 1 - e ∉ P.map π := by
    intro h
    have h' : 1 - e ∈ m.map π := Ideal.map_mono hPm h
    have h1 : (1 : A ⧸ I) ∈ m.map π := by simpa using Ideal.add_mem _ h' hem
    have h2 : (1 : A) ∈ m := by
      rw [← hcm, Ideal.mem_comap, map_one]; exact h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have heP : e ∈ P.map π := by
    have h0 : e * (1 - e) ∈ P.map π := by
      rw [mul_sub, mul_one, he.eq, sub_self]; exact Ideal.zero_mem _
    exact (hPq.mem_or_mem h0).resolve_right hne
  have hle : m.map π ≤ P.map π := by
    rw [hme, Ideal.span_le, Set.singleton_subset_iff]; exact heP
  rw [← hcm, ← hcP]
  exact Ideal.comap_mono hle

theorem eq_of_evHom_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) (e : CxPts.evHom hy = CxPts.evHom hz) : y = z := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact Subtype.ext ((cancel_epi _).1 a).symm

theorem evHom_algX {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {y : CxPts p (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U) (c : ℂ) : CxPts.evHom hy (algX p U c) = c :=
  (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)

theorem eq_of_ker_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (e : RingHom.ker (CxPts.evHom hy) = RingHom.ker (CxPts.evHom hz)) : y = z := by
  refine eq_of_evHom_eq hU hy hz (RingHom.ext fun f => ?_)
  have h1 : f - algX p U (CxPts.evHom hy f) ∈ RingHom.ker (CxPts.evHom hy) := by
    rw [RingHom.mem_ker, map_sub, evHom_algX, sub_self]
  rw [e, RingHom.mem_ker, map_sub, evHom_algX, sub_eq_zero] at h1
  exact h1.symm

theorem finite_transv_zeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ (k : ℕ) (φ : Fin k → Γ(X, U)), {z : CxPts p (RingHom.id ℂ) | ∃ hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U,
      (∀ j, CxPts.evHom hz (φ j) = 0) ∧
        RingHom.ker (CxPts.evHom hz) ≤ Ideal.span (Set.range φ) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2}.Finite := by
  intro X p _ U hU k φ
  have h1 := LocallyOfFiniteType.finiteType_appLE p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℂ _
  classical
  let F : CxPts p (RingHom.id ℂ) → Ideal Γ(X, U) := fun z =>
    if hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U then RingHom.ker (CxPts.evHom hz) else ⊥
  refine Set.Finite.of_finite_image (f := F)
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span (Set.range φ))).subset ?_) ?_
  · rintro _ ⟨z, ⟨hz, hv, hsq⟩, rfl⟩
    simp only [F, dif_pos hz]
    haveI : (RingHom.ker (CxPts.evHom hz)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algX p U c, evHom_algX hz c⟩
    refine mem_minimalPrimes_of_le_sup_sq (IsNoetherian.noetherian _) ?_ hsq
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hv j
  · rintro y ⟨hy, -⟩ z ⟨hz, -⟩ e
    simp only [F, dif_pos hy, dif_pos hz] at e
    exact eq_of_ker_eq hU hy hz e

end GlobalTheory.TransvZeros
end
end

