module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumNegHomEqVacuumMovedLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

private theorem isVacO_move {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS MS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT MT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLS : IsSelfDualC S LS) (hMS : IsSelfDualC S MS) (hLT : IsSelfDualC T LT) (hMT : IsSelfDualC T MT)
    (g : GA D S) (hg : g ∈ GfC S) (h : GA D T) (hh : h ∈ GfC T)
    (mg : GlobalTheory.FinPl.Moves S g LS MS (fun _ => True)) (mh : GlobalTheory.FinPl.Moves T h LT MT (fun _ => True))
    (f : WO S T → ℂ) (hf : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ S T sS sT MS MT (om (g, h) f) := by
  have hθ : IsInfFam θ := hf.2.inf
  refine GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul]) (fun u => ?_) f hf
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hLS hMS hLT hMT mg mh
  have back : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
    have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ u
    rwa [inv_inv, inv_inv] at this
  refine ⟨fun hu => ⟨actO S T g⁻¹ h⁻¹ u, (key _).2 (by rwa [back]), back.symm⟩, ?_⟩
  rintro ⟨u₀, hu₀, rfl⟩
  exact (key _).1 hu₀

theorem _root_.GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    IsVacO ψ θ (neg A) WW (fun τ => -(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s τ) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mg mg' mh t₀ r r' hr hrt hrt'
  have hWd : IsWeilDatumO ψ (neg A) WW _ _ ((Y.ω t₀).toSgn true) := hY.weil t₀
  have hg₁ : (GlobalTheory.Grid.ofSgn true A).symm g ∈ GfC (neg A) := hg
  have mg₁ : GlobalTheory.FinPl.Moves (neg A) ((GlobalTheory.Grid.ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mg
  have key := isVacO_move ψ θ (neg A) WW _ _ ((Y.ω t₀).toSgn true) hWd (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ ΛA Y.rW.Λ ΛW
    (GlobalTheory.RowTest.isSelfDualC_neg' hY.rigA.1) (GlobalTheory.RowTest.isSelfDualC_neg' hA) hY.rigW.1 hW
    ((GlobalTheory.Grid.ofSgn true A).symm g) hg₁ h hh mg₁ mh Y.vac hY.isVac
  have e : ((Y.ω t₀).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm g, h) Y.vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e] at key
  have e1 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s = Y.rA.s := rfl
  have e2 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s = Y.rW.s := rfl
  have e3 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ = ΛA := rfl
  have e4 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ = ΛW := rfl
  have e5 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e1, e2, e3, e4, e5]
  exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.NormDown

theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {x y : V} (hxy : h x ∣ h y) : x ∣ y := by
  rcases ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩
  · exact hd
  · by_cases hy : y = 0
    · simp [hy]
    obtain ⟨e, he⟩ := hxy
    have hy' : h y ≠ 0 := fun h0 => hy (hi (by rw [h0, map_zero]))
    have h1 : h y * 1 = h y * (h c * e) := by rw [mul_one, ← mul_assoc, ← map_mul, ← he]
    have hu : IsUnit (h c) := isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩
    have hc : IsUnit c := (isUnit_map_iff h c).1 hu
    exact ⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem map_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {I I' : Ideal V} (e : I.map h = I'.map h) : I = I' := by
  obtain ⟨x, rfl⟩ : ∃ x, I = Ideal.span {x} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  have idlAlong_eq_map_local {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local J χ ⟨U, hU⟩ hle, idlAlong_eq_map_local J _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := _root_.GlobalTheory.NormSheaf.normDescentSheaf X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1
    (by rw [hπ]; exact hWc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := _root_.GlobalTheory.Poinc.traitExtSt g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i := by
    intro χ hχ
    rw [Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'),
      jK_spMap f fK hfK, Category.assoc, hgen, hy₂]
    simp only [Category.assoc]
  obtain ⟨a₀, ha₀, h₀⟩ := hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord T₂ _ (hover (ψ j) (hψ j))
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.NormDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder Matrix

namespace GlobalTheory.OneParamOrbit

theorem eps_true_of_posDef {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) (i : Fin X.rank) : B.ε τ i = true := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hinj : Function.Injective ((B.fr τ)⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))
  have hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ) := by
    rw [← B.fr_gram τ]
    have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * (B.fr τ)⁻¹
        = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hpos := (hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)
  rw [hJ] at hpos
  by_contra hne
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos
  norm_num at hpos

theorem conj_mem_Kset {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) {E : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hE : Eᴴ * gramAt D X τ * E = gramAt D X τ) :
    B.fr τ * E * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hJ1 : Formalism.REAL.Jm (B.ε τ) = 1 := by
    have : B.ε τ = fun _ => true := funext (eps_true_of_posDef B τ hG)
    rw [this]; simp [Formalism.REAL.Jm]
  have hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ := by
    rw [← B.fr_gram τ, hJ1, Matrix.mul_one]
  refine ⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
  calc (B.fr τ * E * (B.fr τ)⁻¹)ᴴ * (B.fr τ * E * (B.fr τ)⁻¹)
      = ((B.fr τ)⁻¹)ᴴ * (Eᴴ * ((B.fr τ)ᴴ * B.fr τ) * E) * (B.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by
        rw [hgram, hE, ← hgram]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem orbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  intro D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ
  have hG : (gramAt D X τ).PosDef := GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : fockF ψ θ false A B 0 P = 0 := by
        have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart
          A.onb B.onb 0 0 P
        rwa [zero_smul, zero_smul] at this
      refine ⟨⊥, inferInstance, fun t => ?_⟩
      rw [h0, map_zero]; exact zero_mem _
    · obtain ⟨a, b, ha, hb⟩ := hexp τ
      obtain ⟨x, y, -, -, hK⟩ := GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X
        (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0
      refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f),
        inferInstance, fun t => ?_⟩
      have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
      have hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ :=
        GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t
      have hk := conj_mem_Kset B τ hG hE
      have hA1 : (frSgn false A).elt θ τ 1 = 1 := by
        have hAu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)
        show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ
      have hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t := by
        show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _
        rw [show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ
            = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by
              simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hω1 : ω (1, oneP θ X τ Y t)
          = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹)) := by
        rw [hA1, hBk]
        show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)
        rw [map_one]
      have key := hK 1 (GlobalTheory.Chain.RealIt.one_mem_Kset _) _ hk P
      have hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P := rfl
      rw [hfock, hω1, key]
      refine Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨V₁, h₁, hV₁⟩ := hx
    obtain ⟨V₂, h₂, hV₂⟩ := hy
    exact ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by
      rw [map_add]; exact add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩
  | smul c x _ hx =>
    obtain ⟨V, h, hV⟩ := hx
    exact ⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩

end GlobalTheory.OneParamOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSqStOfClaims
section
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw)

noncomputable section

namespace GlobalTheory.SqTop.OneSqProof

theorem vw_ratio_le {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e p q e0 h0 : ℕ)
    (he : e0 + p = e + q) (hle : e0 ≤ h0) (rq ζ γ zA zA' : K) (tk : Fin (p + q) → K) (ρ : ℤ → K) (a n0 : ℤ → ℝ)
    (er dl B : ℝ)
    (heq : rq * ∏ k ∈ range q, ρ ((e : ℤ) + k + 1) = ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k))
    (hρ0 : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ (h0 : ℤ) + p + q → ρ s ≠ 0)
    (hζ : ζ ≠ 0 ∧ vw w ζ = 0) (ht : ∀ k, tk k ≠ 0 ∧ |(vw w (tk k) : ℝ)| ≤ B) (hγ : γ ≠ 0) (hzA : zA ≠ 0)
    (hγv : (vw w γ : ℝ) ≤ vw w (zA * ∏ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s) + vw w zA' + 6 * dl)
    (her : 0 ≤ er)
    (hs : ∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q →
      0 ≤ a s ∧ 0 ≤ n0 s ∧ (vw w (ρ s) : ℝ) ≤ a s + er ∧ -(vw w (ρ s) : ℝ) ≤ a s + n0 s)
    (hsym : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) :
    rq ≠ 0 ∧ (vw w rq : ℝ) ≤ |(vw w zA : ℝ)| + |(vw w zA' : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) +
      ((2 * (h0 + p + q) : ℕ) : ℝ) * er + 6 * dl + ((p + q : ℕ) : ℝ) * B := by
  have hq0 : ∀ k ∈ range q, ρ ((e : ℤ) + k + 1) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hp0 : ∀ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hI0 : ∀ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s ≠ 0 := fun s hs => by
    rw [mem_Icc] at hs; exact hρ0 _ hs.1 (by omega)
  have hT : ∀ k ∈ (univ : Finset (Fin (p + q))), tk k ≠ 0 := fun k _ => (ht k).1
  have hPq := prod_ne_zero_iff.2 hq0
  have hPp := prod_ne_zero_iff.2 hp0
  have hPT := prod_ne_zero_iff.2 hT
  have hPI := prod_ne_zero_iff.2 hI0
  have hR : ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp
  have hrq : rq ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact hR heq.symm
  refine ⟨hrq, ?_⟩
  have hv := congrArg (vw w) heq
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hrq hPq, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hq0,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hζ.1 hPT) hγ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hζ.1 hPT,
    Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hT, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hp0, hζ.2] at hv
  have hz := Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hzA hPI
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hI0] at hz
  rw [hz] at hγv
  have hc := GlobalTheory.Square.count_factors e p q e0 h0 he hle (fun s => (vw w (ρ s) : ℝ)) a n0 er her
    (fun s h1 h2 => hs s h1 h2) (fun s h1 h2 => by simp only [hsym s h1 h2])
  have hvR : (vw w rq : ℝ) + ∑ k ∈ range q, (vw w (ρ ((e : ℤ) + k + 1)) : ℝ) =
      (∑ k, (vw w (tk k) : ℝ)) + vw w γ + ∑ k ∈ range p, (vw w (ρ ((e : ℤ) + q - k)) : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hv
    push_cast at this
    linarith
  have hTB : (∑ k, (vw w (tk k) : ℝ)) ≤ ((p + q : ℕ) : ℝ) * B := by
    calc (∑ k, (vw w (tk k) : ℝ)) ≤ ∑ _k : Fin (p + q), B :=
          sum_le_sum fun k _ => (le_abs_self _).trans (ht k).2
      _ = ((p + q : ℕ) : ℝ) * B := by simp
  have hIc : ((∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), vw w (ρ s) : ℤ) : ℝ) =
      ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ) := by push_cast; rfl
  have hγv' : (vw w γ : ℝ) ≤ vw w zA + (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ)) + vw w zA' + 6 * dl := by
    have := hγv; push_cast at this; linarith
  have a1 := le_abs_self (vw w zA : ℝ)
  have a2 := le_abs_self (vw w zA' : ℝ)
  linarith

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem wt_at {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ} {l : ℕ}
    (hS : ∀ l' ∈ S, l'.Prime) (hl : l.Prime) (hw : (l : 𝓞 K) ∈ w.asIdeal) (hc : l ∉ S → c l = 0) :
    Formalism.PairingDivisionLocalBalance.wt S c w = c l * (vw w (l : K) : ℝ) := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : l ∈ S
  · refine sum_eq_single_of_mem l h fun l' hl' hne => ?_
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp
  · rw [hc h, zero_mul]
    refine sum_eq_zero fun l' hl' => ?_
    have hne : l' ≠ l := fun e => h (e ▸ hl')
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp

theorem wt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ}
    (hc : ∀ l ∈ S, 0 ≤ c l) : 0 ≤ Formalism.PairingDivisionLocalBalance.wt S c w :=
  sum_nonneg fun l hl => mul_nonneg (hc l hl) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w l)

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem exists_prime_mem' {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar _))

end GlobalTheory.SqTop.OneSqProof

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop

namespace GlobalTheory.SqTop.OneSqProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SqTop.OneSqProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

def ptOverClosureIso (K : Type) [Field K] [IsAlgClosed K] :
    ptOver K (AlgebraicClosure K) ≅ 𝟙_ (Over (Sp K)) := by
  let σ : K ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hI : IsIso (spMap (algebraMap K (AlgebraicClosure K))) := by
    change IsIso (Spec.map σ.toCommRingCatIso.hom)
    infer_instance
  exact Over.isoMk (asIso (spMap (algebraMap K (AlgebraicClosure K)))) (by
    change spMap _ ≫ 𝟙 _ = spMap _
    exact Category.comp_id _)

def ptClosureEquiv {K : Type} [Field K] [IsAlgClosed K] (B : AbVar K) :
    B.Pt ≃* (𝟙_ (Over (Sp K)) ⟶ B.X) where
  toFun x := (ptOverClosureIso K).inv ≫ x
  invFun y := (ptOverClosureIso K).hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ x y

end GlobalTheory.PushEigen
end
end

