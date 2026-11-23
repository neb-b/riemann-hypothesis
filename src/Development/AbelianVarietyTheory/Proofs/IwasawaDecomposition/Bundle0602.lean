module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Formalism.LocalToGlobal.Divisibility.MemberDIV
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isE_of_heq {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit 𝒮 K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt 𝒮 K, q.Is D O ∧ EntC q.x.ker := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx⟩

theorem exists_isE_pt {𝒮 : Slots} (H : WitMv 𝒮) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {O : Obj2 (w.D Z)} (x : Wit 𝒮 K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact exists_isE_of_heq (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

theorem witExE_of_witMv : ∀ 𝒮 : Slots, WitMv 𝒮 → WitExE 𝒮 := fun 𝒮 H _ β hβ =>
  positionOf_ind (P := GoodE 𝒮) (R := fun K X _ _ c => ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker)
    (fun _ _ _ _ _ _ _ g => g.1.elim fun b hb => exists_isE_pt H (b.wit g.2) hb) hβ β.Y β.hY β.p

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellClass

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁]

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ γ) (e : X ≃ₗ[O] X₁) : IsCell bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pull r : LinearMap.BilinForm ℤ X₁ → LinearMap.BilinForm ℤ X) := by
  intro β β' h
  refine LinearMap.ext₂ fun a b => ?_
  obtain ⟨a, rfl⟩ := hr a
  obtain ⟨b, rfl⟩ := hr b
  exact LinearMap.congr_fun₂ h a b

theorem linearIndependent_pull_equiv {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : LinearIndependent ℤ γ)
    (e : X ≃ₗ[O] X₁) : LinearIndependent ℤ fun i => pull e.toLinearMap (γ i) :=
  h.map' (pullLin e.toLinearMap) (LinearMap.ker_eq_bot.2 (pull_injective e.surjective))

theorem isPrim_pull_equiv (e : X ≃ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : β ∈ balForms bar X₁)
    (h : IsPrim bar (⟨β, hβ⟩ : balForms bar X₁)) :
    IsPrim bar (⟨pull e.toLinearMap β, pull_mem _ hβ⟩ : balForms bar X) := by
  intro k β' hk
  refine h k ⟨pull e.symm.toLinearMap β'.1, pull_mem _ β'.2⟩ (Subtype.ext (LinearMap.ext₂ fun a b => ?_))
  have := LinearMap.congr_fun₂ (congrArg Subtype.val hk) (e.symm a) (e.symm b)
  simpa using this

end Transport

theorem perModule {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hX : IsPolyFanOn H.bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell H.bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      ∃ e : X ≃ₗ[𝓞 E] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms H.bar X, IsPrim H.bar (⟨t, ht⟩ : balForms H.bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := _root_.GlobalTheory.PolFan.isPrim_ray_eq H.bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone (bar := H.bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell H.bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone H.bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (_root_.GlobalTheory.PolFan.cell_gen_mem_cone_of_smul H.bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  intro E _ _ _ H q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := _root_.GlobalTheory.exists_fin_reps_projective_finrank_le E q
  have key : ∀ k, letI := (hR k).1; ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell H.bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar (R k))) →
        ∃ e : (R k) ≃ₗ[𝓞 E] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    letI := (hR k).1
    haveI := (hR k).2.1
    exact perModule H φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily (𝓞 E) := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  letI := (hR k).1
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell H.bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim H.bar (⟨δ' i, hcell'.mem i⟩ : balForms H.bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.PolFan.CellClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem exists_moved {K T : Type} [Field K] {σ : K →+* ℂ} {n : ℕ} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {a b : T} (h : a = b) (E : V ≃ₗ[ℂ] A b) (j : (Fin n → K) →ₛₗ[σ] A a)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ j' : (Fin n → K) →ₛₗ[σ] V, (∀ y, j' y = E.symm (h ▸ j y)) ∧ (LinearIndependent ℂ fun i => j' (Pi.single i 1)) ∧
      Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤ := by
  subst h
  refine ⟨E.symm.toLinearMap.comp j, fun _ => rfl, li.map' E.symm.toLinearMap E.symm.ker, ?_⟩
  have := congrArg (Submodule.map E.symm.toLinearMap) sp
  rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem exists_read_fam {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) {T : Type} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {b : T} (E : V ≃ₗ[ℂ] A b) (tup : TupF TU → T) (h0 : tup (mu0F TU) = b)
    (inj : Function.Injective tup)
    (j : ∀ t : TupF TU, (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr) → X.K) →ₛₗ[σ] A (tup t))
    (li : ∀ t, LinearIndependent ℂ fun i => j t (Pi.single i 1))
    (sp : ∀ t, Submodule.span ℂ (Set.range fun i => j t (Pi.single i 1)) = ⊤)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ),
      (∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅) y,
        ∃ (F' : (mtildeKGSD W Ch sel t.1).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun),
          HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F')
            (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
              ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
                (lvlIdem P.grp P.chr)).mulVec y)) ∧
          ι (E.symm (ht ▸ j t y)) = zOfRow W Ch sel t.1 hQ P σ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
        (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K),
        ∃ hm : (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun,
          ι (E.symm (ht ▸ j t ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) =
            zOfRow W Ch sel t.1 hQ P σ hM ⟨_, hm⟩ := by
  have hQ0 := Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := X) (S := S) sel
  obtain ⟨j', hj, li', sp'⟩ := exists_moved (A := A) h0 E (j (mu0F TU)) (li _) (sp _)
  obtain ⟨ι, hι⟩ := exists_read W Ch sel (mu0F TU).1 hX P hQ0 σ hM j' li' sp'
  refine ⟨ι, fun t e hQ y => ?_, fun t e hQ F => ?_⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι y
    exact ⟨F', hm, heq_of_eq e1, (congrArg ι (hj y)).symm.trans e2⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)
    have e3 : F' = (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs (mu0F TU) F).1 :=
      ((mtildeKGSD W Ch sel (mu0F TU).1).res (mtildeKOk W Ch sel (mu0F TU).1 hX)).injective
        (e1.trans (evC_res_lvl W Ch sel hX v0 TU Xg S0 xiVal trIv P hOk Zs (mu0F TU) F).symm)
    subst e3
    exact ⟨hm, (congrArg ι (hj _)).symm.trans e2⟩

end Gen

section Main

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem tup_heq (ht : I.IsTw) (U : Set I.ι) (X' : Fields) (hx : X' = B.fields) (Pr : Primes X')
    (sel : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S : Set ℕ) (tup : I.ι → Tup X'.F X'.E X'.K S)
    (cst : ∀ a, LocCst X' (rowSG Pr sel (tup a))) (idx : ∀ a, ChIdx X' Pr B.R (QE sel (tup a : Chr X'.F X'.E X'.K)))
    (h1 : HEq Pr (B.primes X)) (h2 : HEq sel I.sel) (h3 : S = I.S) (h4 : HEq tup I.tup) (h5 : HEq cst I.cst) (h6 : HEq idx I.idx) :
    HEq (fun t : TupU I U => t.1) (fun t => tup (ixOf I U t)) ∧ HEq (fun t : TupU I U => cstT I t.1) (fun t => cst (ixOf I U t)) ∧
      HEq (fun t : TupU I U => idxT I t.1) (fun t => idx (ixOf I U t)) := by
  subst hx h3
  cases h1
  cases h2
  cases h4
  cases h5
  cases h6
  refine ⟨heq_of_eq (funext fun t => (tup_ixOf I t).symm), Function.hfunext rfl fun t t' e => ?_, Function.hfunext rfl fun t t' e => ?_⟩
  · cases e
    rw [← cstT_tup ht, tup_ixOf]
  · cases e
    rw [← idxT_tup ht, tup_ixOf]

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}

theorem iT_heq {t : KerEntTied ex} (hS : I.StdKer l Z t) (τ : (I.rec7 l Z).what₂.Tau) : HEq (t.seam.iT.symm τ) τ := by
  have key : ∀ (X' : Fields) (_ : X' = B.fields) (s : Seam (I.rec7 l Z) X'),
      HEq s (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) → HEq (s.iT.symm τ) τ := by
    intro X' hx s hs
    subst hx
    cases hs
    rfl
  exact key _ hS.X_eq _ hS.seam

abbrev colRecK (t : KerEntTied ex) : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) :=
  colRecC h hp l Z ht hJ t.χ (ker_chi_eq I l Z t) hX U Xg tr

section Pins

variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : Formalism.L2.TiedDataSK ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}

end Pins

end Main


end GlobalTheory.Mem.R3.SelC

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.SelC

theorem pack_heq {D : D7} (p q : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
      (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D) (_ : Algebra C.Q.c.F D.what₂.LL)
      (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3), G0 R.Pg D.R.r ≃* G0g D.nd) (e : p = q) :
    letI := p.2.1; letI := p.2.2.1; letI := p.2.2.2.2.2.2.2.2.1; letI := q.2.1; letI := q.2.2.1; letI := q.2.2.2.2.2.2.2.2.1
    (p.1 = q.1 ∧ HEq p.2.1 q.2.1 ∧ p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧ p.2.2.2.2.2.1 = q.2.2.2.2.2.1 ∧
      HEq p.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1) ∧
    (HEq p.2.2.2.2.2.2.2.2.2.2.1.P0 q.2.2.2.2.2.2.2.2.2.2.1.P0 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ0 q.2.2.2.2.2.2.2.2.2.2.1.ψ0 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.P1 q.2.2.2.2.2.2.2.2.2.2.1.P1 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ1 q.2.2.2.2.2.2.2.2.2.2.1.ψ1 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.Dc q.2.2.2.2.2.2.2.2.2.2.1.Dc ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.Sp q.2.2.2.2.2.2.2.2.2.2.1.Sp) ∧
    HEq (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1) (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1)).Mem =
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)).Mem := by
  subst e
  exact ⟨⟨rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl⟩, ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem heq_app {A M M' : Type} (e : M = M') {f : A → M} {g : A → M'} (h : HEq f g) (u : A) : HEq (f u) (g u) := by
  subst e
  cases h
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}


variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}




attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.Mem.R3.SelC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.FlagEmb.cells_glue : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  intro O K _ _ _ β X s T _ m M B _ V α c D P p0 p h hs hX hC hP
  have hLN : ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp O), IsProjOver g → IsLocallyNoetherian Y := by
    intro Y g hg
    obtain ⟨N, ι, _, rfl⟩ := hg
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  haveI : IsLocallyNoetherian X := hLN s hs
  haveI : IsLocallyNoetherian P := hLN _ hP.proj
  have hW : ∀ b w, ∃ W, IsCellOpen p0 p (V b) (D b) w W := fun b w =>
    GlobalTheory.FlagEmb.CellOpen.exists_isCellOpen O X P T m M p0 p (V b) (D b) w
  choose W hW using hW
  have hcl := fun b w => _root_.GlobalTheory.FlagEmb.CellClosed.cell_closed O K β X s T m M B V α c D P p0 p h hC hP inferInstance hs b w (W b w) (hW b w)
  choose h' hh' hci using hcl
  have hred : ∀ b, AlgebraicGeometry.IsReduced (Sp (CR m (V b))) := by
    intro b
    have hn := (GlobalTheory.FlagEmb.cell_smooth_normal X T m (V b) hX).2
    haveI := fun x => (hn x).1
    exact isReduced_of_isReduced_stalk _
  let ι := B × Pm m
  haveI : Finite (Pm m) := Pi.finite
  haveI : ∀ a : ι, IsAffine (Sp (CR m (V a.1))) := fun a => inferInstance
  haveI : ∀ a : ι, AlgebraicGeometry.IsReduced (Sp (CR m (V a.1))) := fun a => hred a.1
  obtain ⟨F, f, i, hf, hio, hcomp, hcov⟩ := GlobalTheory.MemberGlue.exists_immersion_of_closed_pieces P ι
    (fun a => Sp (CR m (V a.1))) (fun a => h a.1 a.2) (fun a => W a.1 a.2) (fun a => h' a.1 a.2) inferInstance
    (fun a => hh' a.1 a.2) (fun a => hci a.1 a.2)
    (fun a a' => GlobalTheory.FlagEmb.Overlap.range_inter_cellOpen_subset O K β X s T m M B V α c D P p0 p h hC hP a.1 a.2
      (W a.1 a.2) (hW a.1 a.2) a'.1 a'.2)
  refine ⟨F, f, fun b w => i (b, w), hf, fun b w => hio (b, w), fun b w => hcomp (b, w), fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨a.1, a.2, ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

namespace GlobalTheory.BaseDim

theorem two_card_psi (E : Type) [Field E] [NumberField E] [IsCMField E] {r : ℕ} (D : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * D.Ψ.card = Module.finrank ℚ E := Formalism.L2.Pj.DatLin.two_card D.cmType

theorem eq_of_smooth_two {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (m n : ℕ) (hm : SmoothOfRelativeDimension m f) (hn : SmoothOfRelativeDimension n f) : m = n := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := genericPoint X) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  algebraize [α.hom]
  have t₁ := trdeg_eq_of_smoothOfRelativeDimension K X f m hm Γ(X, U) hU.fromSpec inferInstance hα.symm
  have t₂ := trdeg_eq_of_smoothOfRelativeDimension K X f n hn Γ(X, U) hU.fromSpec inferInstance hα.symm
  exact_mod_cast t₁.symm.trans t₂

theorem card_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ Φ k X j f f₀ Eb A₀ hj hL
  have hoi : IsOpenImmersion j := hL.1
  have hs : SmoothOfRelativeDimension Dw.dim (genStr T.Z) := T.smooth
  have hi : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have h0 : SmoothOfRelativeDimension 0 (spMap e.toRingHom) := inferInstance
  have h2 : SmoothOfRelativeDimension (Dw.dim + 0) (genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [Nat.add_zero] at h2
  have h1 : SmoothOfRelativeDimension (0 + Dw.dim) (j ≫ genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [hj, Nat.zero_add] at h1
  have hd : Dw.dim = X.dim := eq_of_smooth_two X.X X.str Dw.dim X.dim h1 X.smooth
  rw [← hd, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim, ← two_card_psi E (U.X k), Nat.mul_div_cancel_left _ two_pos]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.add_sub_cancel_left, Nat.mul_assoc]

end GlobalTheory.BaseDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := H.bar) (X := X) := by
  first | exact @GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg | exact GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg | (intros; apply GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg <;> assumption)
end

