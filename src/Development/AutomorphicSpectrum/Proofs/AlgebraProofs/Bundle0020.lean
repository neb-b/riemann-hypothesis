module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOfTestIdeal
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaTest

theorem mem_of_test_ideal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ (L : AddSubgroup Ω), LocFree R 1 L → ∀ v : Ω, (∃ m : ℕ, (p : Ω) ^ m * v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → algebraMap Ω C v ∈ spanOver RC (algebraMap Ω C '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI L hL v hm htest
  let e : Ω ≃ₗ[Ω] (Unit → Ω) := (LinearEquiv.funUnique Unit Ω Ω).symm
  have hL' : LocFree R 1 (L.map e.toLinearMap.toAddMonoidHom) :=
    LatticeGoodness.locFree_map_equiv R e hL
  have hmem : ∀ x : Ω, e x ∈ L.map e.toLinearMap.toAddMonoidHom ↔ x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine (hmem v).1 (_root_.GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI 1 _ hL' (e v) ?_ ?_)
  · obtain ⟨m, hm⟩ := hm
    refine ⟨m, ?_⟩
    have : (p : Ω) ^ m • e v = e ((p : Ω) ^ m * v) := by
      rw [← smul_eq_mul, map_smul]
    rw [this]
    exact (hmem _).2 hm
  · intro C _ _ _ _ RC ht
    let g : C →+ (Unit → C) :=
      (LinearEquiv.funUnique Unit C C).symm.toLinearMap.toAddMonoidHom
    have hg : bcMap Ω C Unit (e v) = g (algebraMap Ω C v) := by
      funext u
      simp [bcMap, e, g]
    rw [hg]
    have h1 := AddSubgroup.mem_map_of_mem g (htest C RC ht)
    unfold spanOver at h1 ⊢
    rw [AddMonoidHom.map_closure] at h1
    refine (AddSubgroup.closure_mono ?_) h1
    rintro _ ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, bcMap Ω C Unit (e x), ⟨e x, (hmem x).2 hx, rfl⟩, ?_⟩
    funext u
    simp [bcMap, e, g]

end GlobalTheory.CompanionTheory.Ar.Num.HaTest
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g hL' hSE
  obtain ⟨hf, hfg, hg, hL, hL''⟩ := hSE
  have hsub := _root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V' L' (LinearMap.range f) hL'
  obtain ⟨e1, he1⟩ : ∃ e : V ≃ₗ[K] LinearMap.range f, ∀ x, (e x : V') = f x :=
    ⟨LinearEquiv.ofInjective f hf, fun x => by simp⟩
  have hker : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  obtain ⟨e2, he2⟩ : ∃ e : (V' ⧸ LinearMap.range f) ≃ₗ[K] V'',
      ∀ y, e (Submodule.Quotient.mk y) = g y :=
    ⟨(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective g hg),
      fun y => by simp [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]⟩
  have hc1 : ∀ (i : C.I) (x : LinearMap.range f),
      x ∈ GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f) i ↔ e1.symm x ∈ L i := by
    intro i x
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.sub, AddSubgroup.mem_comap]
    rw [hL i, ← he1, LinearEquiv.apply_symm_apply]
    exact Iff.rfl
  have hc2 : ∀ (i : C.I) (z : V' ⧸ LinearMap.range f),
      z ∈ GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f) i ↔ e2 z ∈ L'' i := by
    intro i z
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.quot]
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h2 : e2 (Submodule.Quotient.mk y) ∈ L'' i := by
        rw [he2]
        exact (hL'' i (g y)).2 ⟨y, hy, rfl⟩
      exact h2
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (hL'' i _).1 hz
      refine ⟨y, hy, e2.injective ?_⟩
      have h3 : e2 (Submodule.Quotient.mk y) = e2 z := by rw [he2, hyz]
      exact h3
  obtain ⟨hLb, hdL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C (LinearMap.range f) V
    (GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f)) L e1.symm hsub.1 hc1
  obtain ⟨hL''b, hdL''⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C (V' ⧸ LinearMap.range f) V''
    (GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f)) L'' e2 hsub.2 hc2
  refine ⟨hLb, hL''b, ?_⟩
  rw [_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot K C V' L' (LinearMap.range f) hL']
  unfold GlobalTheory.CompanionTheory.Ar.Crv.subDeg
  rw [hdL, hdL'']

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacter
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem eigencomponents_scalars : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) :=
  @PositivityTheory.HtPt.Rb.proj_props

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLength
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealD_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) :=
  @PositivityTheory.HtPt.Rd.a_pow

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DimZero

theorem isIso_hom_of_relDim_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension 0 A.hom) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Etale A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hd
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  haveI : IsOpenImmersion e :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) e A.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal A.hom))) (by rw [he]; infer_instance)
  have hs : ∀ y : S, A.hom (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsIso e := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_unique fun a _ => ?_)
    have hc := (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
    have hcl : IsClopen (Set.range e) :=
      ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    exact hc.subset_isClopen hcl ⟨e (A.hom a), hs _, _, rfl⟩ rfl
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem over_hom_eq_of_mono {S : Scheme.{0}} {T A : Over S} [Mono A.hom] (x y : T ⟶ A) : x = y := by
  ext1
  rw [← cancel_mono A.hom, Over.w x, Over.w y]

theorem eq_one_of_g_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (hg : P.g = 0) (z : sp (R₀ := R) R ⟶ P.A) :
    z = 1 := by
  have hd : SmoothOfRelativeDimension 0 P.A.hom := hg ▸ P.smoothDim
  haveI := isIso_hom_of_relDim_zero P.A P.isAb hd
  exact over_hom_eq_of_mono _ _

end GlobalTheory.CompanionTheory.Ar.DimZero
end
end

