module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0006
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ArtinTransferDecompositionHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

theorem artinTransferDecomposition_holds : ArtinTransferDecompositionCharacter := by
  unfold ArtinTransferDecompositionCharacter
  intro E Ω _ _ _ _ _ A w h a ha n χ hχ
  have hs : ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h))) := by
    intro i
    have hc : Continuous fun σ : ReciprocityTheory.Gal.Ine A =>
        Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ) :=
      continuous_subtype_val.subtype_mk _
    exact (hχ i).preimage hc
  choose μ hμ hμe using fun i => ha.factor _ (hs i)
  exact ⟨μ, hμ, fun i σ => DFunLike.congr_fun (hμe i) σ⟩

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DistinctCharacterUnits
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace DistinctCharacterUnits

theorem exists_unit_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {μ ν : kˣ →* ℂˣ} (hne : res μ ≠ res ν) : ∃ u : 𝒪[k]ˣ, μ (unitIncl k u) ≠ ν (unitIncl k u) := by
  by_contra hh
  push Not at hh
  exact hne (MonoidHom.ext hh)

end DistinctCharacterUnits

theorem distinctOnInertia_holds : DistinctOnUnitsDistinctOnInertia := by
  intro hA E Ω _ _ _ _ _ A w h a ha n G b c hbc
  obtain ⟨u, hu⟩ := DistinctCharacterUnits.exists_unit_ne (G.dist b c hbc)
  obtain ⟨t, ht⟩ := (hA E Ω A w h a ha).2 (unitIncl _ u) (valuation_eq_one_iff.mpr ⟨u, rfl⟩)
  exact ⟨t, by rw [ht]; exact hu⟩

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetFiniteLength2
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace JacquetFiniteLength₂

variable {n : ℕ} (G : Grp k n)

theorem hasFiniteLength_jacU (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π) (hfl : HasFiniteLength π) :
    HasFiniteLength (jacU G.e π) :=
  (GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff (jacU G.e π) (deltaHalf k _)⁻¹).1
    ((hBZ k).2.1 _ _ _ G.e V π hπ hfl)

end JacquetFiniteLength₂

theorem step_jacFin {n : ℕ} (G : Grp k n) : G.JacquetModuleFiniteProp := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.LocalArtinBlockProduct
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace LocalArtinBlockProduct

theorem prod_blocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (G : Grp k n) {M : Type*} [CommMonoid M] (f : Fin G.s → M) :
    ∏ i, f (G.bl i) = ∏ b, f b ^ G.d b := by
  calc ∏ i, f (G.bl i) = ∏ p : (Σ a, Fin (G.d a)), f (G.bl (G.e p)) := (G.e.prod_comp (fun i => f (G.bl i))).symm
    _ = ∏ p : (Σ a, Fin (G.d a)), f p.1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      show f ((G.e.symm (G.e p)).1) = f p.1
      rw [Equiv.symm_apply_apply]
    _ = ∏ b, f b ^ G.d b := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun b _ => ?_
      show ∏ _y : Fin (G.d b), f b = f b ^ G.d b
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem exists_unit (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    ∃ u, unitIncl (w.adicCompletion E) u = a (ineIncl h t) := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact valuation_eq_one_iff.mp (ord_eq_zero_iff.mp h0)

end LocalArtinBlockProduct

theorem localArtinCharacterProduct_holds : LocalArtinCharacterProduct := by
  intro E Ω _ _ _ _ _ A w h a ha n χ ho μ hμ G σ hG s
  obtain ⟨u, hu⟩ := LocalArtinBlockProduct.exists_unit ha s
  have key : ∀ i, ((χ i (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h s)) : ℂˣ) : ℂ) =
      ((G.chi (σ.symm i) (a (ineIncl h s)) : ℂˣ) : ℂ) := by
    intro i
    have e := DFunLike.congr_fun (hG (σ.symm i)) u
    simp only [MonoidHom.comp_apply, Equiv.apply_symm_apply] at e
    rw [hμ i, ← hu, e]
  simp only [xOf, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd, MonoidHom.comp_apply]
  rw [Finset.prod_congr rfl fun i _ => by rw [key i]]
  rw [Equiv.prod_comp σ.symm (fun j => X - C ((G.chi j (a (ineIncl h s)) : ℂˣ) : ℂ))]
  exact LocalArtinBlockProduct.prod_blocks G (fun b => X - C ((G.μ b (a (ineIncl h s)) : ℂˣ) : ℂ))

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NeedCProps
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

theorem jacProd_of (hjF : G.JacquetModuleFiniteProp) (hsub : G.SubquotientProp) (hten : G.TensorProductProp) (hsupp : G.SupportOfProductProp) :
    G.JacquetProductProp := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩

end Grp

def CSteps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.JacquetModuleFiniteProp ∧ G.SubquotientProp ∧ G.TensorProductProp ∧ G.SupportOfProductProp


open UpperTheory.NonzeroTypeTheory in
theorem need_CMain (hC : CSteps) (hlL : LeviSubgroupRestriction) (L : GlobalTheory.Mem.LiteralAutomorphy.LitN) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of hjF hsub hten hsupp) L V ρ hs hi hx


open UpperTheory.NonzeroTypeTheory in
theorem need_CProps (hC : CSteps) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem


open UpperTheory.NonzeroTypeTheory in
theorem need_Grp (hC : CSteps) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SpecialLatticeProp : Prop :=
  ∀ (Γ V : Type) [Group Γ] [AddCommGroup V] [Module ℂ V] (I : Representation ℂ Γ V) (d : Subrepresentation I → ℕ),
    Monotone d → (∀ X Y, d (X ⊔ Y) + d (X ⊓ Y) = d X + d Y) → d ⊤ ≤ 1 →
    ∀ (A B : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (α : Representation ℂ Γ A) (β : Representation ℂ Γ B), α.IsIrreducible → β.IsIrreducible →
      (∃ X Y : Subrepresentation I, X ≤ Y ∧ d X < d Y ∧ Nonempty ((subQuot Y X).Equiv α)) →
      (∃ X Y : Subrepresentation I, X ≤ Y ∧ d X < d Y ∧ Nonempty ((subQuot Y X).Equiv β)) →
      Nonempty (α.Equiv β)

namespace Grp

variable {n : ℕ} (G : Grp k n)

def etaSp {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W) :
    Submodule ℂ W :=
  ⨅ (m : Levi k fun a : Fin G.s => Fin (G.d a)) (_ : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))),
    LinearMap.ker (ρ m - G.eta m • LinearMap.id)

def SphericalVectorUniqueness : Prop :=
  SpecialLatticeProp →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : Representation ℂ (GL (Fin n) k) V), IsSmooth I →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e I)) → Module.finrank ℂ ↥(G.etaSp (jacU G.e I)) ≤ 1 →
    ∀ (A B : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (α : Representation ℂ (GL (Fin n) k) A) (β : Representation ℂ (GL (Fin n) k) B),
      α.IsIrreducible → β.IsIrreducible → IsSubquotient α I → IsSubquotient β I →
      G.HasEtaVec (jacU G.e α) → G.HasEtaVec (jacU G.e β) → Nonempty (α.Equiv β)

def SpecialLiftProp : Prop :=
  ∀ (W X : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W)
    (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth ρ → IsSubquotient σ ρ → G.HasEtaVec σ → G.HasEtaVec ρ

def SpecialCountProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) → (∀ i, res (c i) = res (G.chi i)) →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ∧
      Module.finrank ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ≤ 1

def twD {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s) :
    Representation ℂ (GL (Fin (G.d a)) k) (Y a) :=
  twist (τ a) (detChar (Fin (G.d a)) (absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))))

def cOf (ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ :=
  ν (G.e.symm i).1 (G.e.symm i).2 * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) (G.e.symm i).1 : ℂ) / 2))

def NonzeroBasicTwistOfSpecialForm : Prop :=
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a))
    (a : Fin G.s), IsSmooth (τ a) → (τ a).IsIrreducible → HasDetVec (τ a) (G.μ a) →
    IsSmooth (G.twD τ a) ∧ (G.twD τ a).IsIrreducible ∧ HasDetVec (G.twD τ a) (G.μ a)

def SpecialRestrictionProp : Prop :=
  ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, res (ν a j) = res (G.μ a)) → ∀ i, res (G.cOf ν i) = res (G.chi i)

def SpecialRepresentationEtaProp : Prop :=
  G.SpecialLiftProp →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, HasDetVec (τ a) (G.μ a)) →
    G.HasEtaVec (jacU G.e (multiProd G.e (G.twD τ)))

def SpecialOrderProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) →
    ∀ σ : Equiv.Perm (Fin n), IsSubquotient π (prinSeries (fun i => c (σ i))) → IsSubquotient π (prinSeries c)

def SpecialRepresentationSubProp : Prop :=
  SpecialOrderProp (k := k) (n := n) → GlobalTheory.Mem.LiteralAutomorphy.LitN →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
    ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
    (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
    (multiProd G.e (G.twD τ)).IsIrreducible →
    IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries (G.cOf ν))

def SpecialSupportProp : Prop :=
  SpecialOrderProp (k := k) (n := n) → GlobalTheory.Mem.LiteralAutomorphy.LitN →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
      ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
      (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsSubquotient π (prinSeries (G.cOf ν))

def NonzeroTopOfSpecialForm : Prop :=
  SpecialLatticeProp → G.SphericalVectorUniqueness → G.SpecialCountProp → G.SpecialLiftProp → G.NonzeroBasicTwistOfSpecialForm → G.SpecialRestrictionProp → G.SpecialRepresentationEtaProp →
    SpecialOrderProp (k := k) (n := n) → G.SpecialRepresentationSubProp → G.SpecialSupportProp → CuspidalSupportProp → ProductIrreducibleProp → TensorProductVectors →
    G.SupportOfProductProp

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfSteps
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

theorem typeData_of (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : GMain) (ge : GEmb) (gi : ArtinInertiaProp) (cm : GlobalTheory.Mem.LiteralAutomorphy.LitN → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) :
    TypeData := by
  intro E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨μ, hμs, hμ⟩ := a1 E Ω A w h a ha n χ ho
  obtain ⟨G, σ, hG⟩ := gr (w.adicCompletion E) n μ hμs
  have hcond : ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π ↔ IsTwSphProd π.ρ G.d G.hd G.μ := by
    intro π
    have e := gm E Ω A w h a ha ε rc H P.loc G.s G.d G.μ G.smooth (a6 gi E Ω A w h a ha n G)
      (IrrGL.of π.ρ π.smooth π.irred) G.hd
    rw [← a5 _ n π.V π.ρ π.smooth π.irred G.s G.d G.hd G.μ, ← e]
    unfold Cond
    refine and_congr_right fun _ => forall_congr' fun s => ?_
    rw [a3 E Ω A w h a ha n χ ho μ hμ G σ hG s]
  obtain ⟨hJK, h1J, hmul, hinv, hne, hKCo, h1KC, hKCJ, hlam1, hst, hfin, hv0m, hv00, hv0e⟩ := cp (w.adicCompletion E) n G
  have hK : KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := SphCompletion.KO_completion w n
  let T (K : Subgroup (GL (Fin n) (w.adicCompletion E))) : Prop :=
    ∃ (J : Subgroup ↥K) (lam : ↥J →* ℂˣ) (m : ℕ) (V0 : Representation ℂ ↥K (Fin m → ℂ))
        (v0 : Fin m → ℂ), IsOpen (J : Set ↥K) ∧ IsOpen (lam.ker : Set ↥J) ∧ GlobalTheory.PRep.IsSmooth V0 ∧
        v0 ≠ 0 ∧ (∀ j : ↥J, V0 (j : ↥K) v0 = ((lam j : ℂˣ) : ℂ) • v0) ∧
        (∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
          (∃ x : π.V, x ≠ 0 ∧ ∀ j : ↥J, π.ρ ((j : ↥K) : GL (Fin n) (w.adicCompletion E)) x = ((lam j : ℂˣ) : ℂ) • x) →
            Cond h rc χ ho π) ∧
        ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π →
          ∃ f : (Fin m → ℂ) →ₗ[ℂ] π.V, Function.Injective f ∧ ∀ k v, f (V0 k v) = π.ρ k (f v)
  change T _
  rw [← hK]
  dsimp only [T]
  let J : Subgroup ↥(KO (w.adicCompletion E) (Fin n)) :=
    { carrier := {j | (j : GL (Fin n) (w.adicCompletion E)) ∈ G.JSet}
      mul_mem' := fun {x y} hx hy => (hmul _ hx _ hy).1
      one_mem' := h1J
      inv_mem' := fun {x} hx => hinv _ hx }
  let lam : ↥J →* ℂˣ :=
    { toFun := fun j => Units.mk0 (G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E))) (hne _ j.2)
      map_one' := Units.ext (by simpa using hlam1 1 h1KC)
      map_mul' := fun x y => Units.ext (by simpa using (hmul _ x.2 _ y.2).2) }
  have hlamv : ∀ j : ↥J, ((lam j : ℂˣ) : ℂ) = G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E)) :=
    fun _ => rfl
  obtain ⟨m, V0, e, he, hre, heq, hsm⟩ := a4 _ G.V0sp hfin (fun φ hφ k' => hst φ hφ k') (a7 _ n G hKCo h1KC)
  obtain ⟨v0, hv0⟩ : G.v0 ∈ LinearMap.range e := hre ▸ hv0m
  have hU : IsOpen {j : ↥(KO (w.adicCompletion E) (Fin n)) | (j : GL (Fin n) (w.adicCompletion E)) ∈ KC _ n G.lev} :=
    hKCo.preimage continuous_subtype_val
  refine ⟨J, lam, m, V0, v0, ?_, ?_, hsm, fun h0 => hv00 (by rw [← hv0, h0, map_zero]), fun j => he ?_, ?_, ?_⟩
  · exact Subgroup.isOpen_of_mem_nhds J (Filter.mem_of_superset (hU.mem_nhds (show (1 : ↥(KO (w.adicCompletion E) (Fin n))) ∈ _ from h1KC)) fun j hj => hKCJ hj)
  · exact Subgroup.isOpen_of_mem_nhds lam.ker (Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds (show (1 : ↥J) ∈ _ from h1KC)) fun j hj => MonoidHom.mem_ker.2 (Units.ext (by
        rw [hlamv]; exact hlam1 _ hj)))
  · rw [heq, hv0, hv0e _ j.2, map_smul, hv0, hlamv]
  · rintro π ⟨x, hx, hxj⟩
    rw [hcond]
    refine cm P _ n G π.V π.ρ π.smooth π.irred ⟨x, hx, fun g hg => ?_⟩
    have := hxj ⟨⟨g, hJK hg⟩, hg⟩
    rwa [hlamv] at this
  · intro π hc
    rw [hcond] at hc
    obtain ⟨f, hf, hfeq⟩ := ge _ n G π.V π.ρ hc
    let e' : (Fin m → ℂ) →ₗ[ℂ] ↥G.V0sp := LinearMap.codRestrict G.V0sp e fun v => hre ▸ LinearMap.mem_range_self e v
    refine ⟨f ∘ₗ e', hf.comp fun v v' hvv => he (congrArg Subtype.val hvv), fun κ v => ?_⟩
    exact hfeq κ (e' v) (e' (V0 κ v)) (heq κ v)

theorem nz_of_steps (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (k2 : SmoothRepIrreducibleSubcontainingVector) (k3 : SmoothRepMinimalSubrepresentation) (k4 : SchurInjectiveFromIrreducible) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct)
    (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia) (a7 : SmoothVectorsFixedByCongruence) (gm : GMain) (ge : GEmb) (gi : ArtinInertiaProp)
    (cm : GlobalTheory.Mem.LiteralAutomorphy.LitN → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) : NZ :=
  nz_of_typeData k2 k3 k4 (typeData_of P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr)

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TranslationCoordinates
section
noncomputable section

open GlobalTheory.PRep

namespace UpperTheory.NonzeroTypeTheory

namespace TranslationCoordinates

variable {K : Type} [Group K] (W : Submodule ℂ (K → ℂ))
  (hW : ∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W)

def rW : Representation ℂ K W := sub (rightReg ℂ K ℂ) W (fun k φ hφ => hW φ hφ k)

def coord {m : ℕ} (c : W ≃ₗ[ℂ] (Fin m → ℂ)) : Representation ℂ K (Fin m → ℂ) where
  toFun k := c.toLinearMap ∘ₗ rW W hW k ∘ₗ c.symm.toLinearMap
  map_one' := by ext v i; simp
  map_mul' a b := by ext v i; simp [map_mul]

end TranslationCoordinates

theorem finiteDimensionalTranslation_holds : FiniteDimensionalTranslationCoordinates := by
  intro K _ _ W hfin hW hsm
  have := hfin
  let c := (Module.finBasis ℂ W).equivFun
  let V0 := TranslationCoordinates.coord W hW c
  let e : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (K → ℂ) := W.subtype ∘ₗ c.symm.toLinearMap
  have he : ∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v) := by
    intro k v
    simp [e, V0, TranslationCoordinates.coord, TranslationCoordinates.rW, sub]
  have hinj : Function.Injective e := W.injective_subtype.comp c.symm.injective
  refine ⟨_, V0, e, hinj, ?_, he, ?_⟩
  · ext φ
    constructor
    · rintro ⟨v, rfl⟩
      simp [e]
    · intro hφ
      exact ⟨c ⟨φ, hφ⟩, by simp [e]⟩
  · intro v
    have hset : {g : K | V0 g v = v} = {g : K | rightReg ℂ K ℂ g (e v) = e v} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      rw [← he]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hsm _ (by simp [e])

end UpperTheory.NonzeroTypeTheory
end
end

