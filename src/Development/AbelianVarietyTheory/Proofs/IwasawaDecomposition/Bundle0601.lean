module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
public import Formalism.LocalToGlobal.HermitianColumns.FullSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFan
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m : ℕ}

theorem StrictWith.mul {N t : ℕ} (ht : 0 < t) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X} (h : StrictWith bar φ N ℓ u) :
    StrictWith bar φ (t * N) ((t : ℤ) • ℓ) u := by
  obtain ⟨h1, h2, h3⟩ := h
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => h3 β hβ hp ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, h1 i, Nat.cast_mul]; ring
  · have := mul_le_mul_of_nonneg_left (h2 β hβ hp) ht'.le
    simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    linarith
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
    have : (t : ℝ) * (N * φ.evalZ β) = t * ℓ β := by linarith
    exact mul_left_cancel₀ ht'.ne' this

theorem StrictWith.of_pull {N : ℕ} {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X₁} (h : StrictWith bar φ N ℓ fun i => pull r (u i)) :
    StrictWith bar φ N (ℓ ∘ₗ { toFun := pull r, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }) u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => (h1 i).trans (by rw [evalZ_pull φ hr]), fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← evalZ_pull φ hr]
    exact h2 _ (pull_mem r hβ) fun y => hp _
  · rw [← evalZ_pull φ hr] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem r hβ) (fun y => hp _) he
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

end GlobalTheory.PolCell


open Classical in
theorem GlobalTheory.PolCell.exists_common_den : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ),
    IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ)
      (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧
      StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  intro X _ _ φ hφ
  obtain ⟨S, hS, hSc⟩ := hφ.finite
  haveI : Finite S := hS.to_subtype
  let K := Σ m : Fin (Nat.card S + 1), (Fin m → S)
  haveI : Fintype K := Fintype.ofFinite K
  let D : K → ℕ := fun k =>
    if h : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) then Classical.choose h.strict else 1
  have hD : ∀ k, 0 < D k := fun k => by
    simp only [D]
    split_ifs with h
    · exact (Classical.choose_spec (Classical.choose_spec h.strict)).1
    · exact one_pos
  refine ⟨∏ k, D k, Finset.prod_pos fun k _ => hD k, fun B hB => ?_⟩
  obtain ⟨m, γ, c, hγ, hc, rfl⟩ := hφ.cover B hB
  obtain ⟨e, he⟩ := hSc m γ hγ
  have hγ' := hγ.pull_equiv e
  have hm : m < Nat.card S + 1 := by
    have := Nat.card_le_card_of_injective (fun i : Fin m => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rw [Nat.card_fin] at this
    exact Nat.lt_succ_of_le this
  let k : K := ⟨⟨m, hm⟩, fun i => ⟨_, he i⟩⟩
  have hk : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) := hγ'
  have hDk : D k = Classical.choose hk.strict := dif_pos hk
  obtain ⟨ℓ, -, hℓ⟩ := Classical.choose_spec hk.strict
  obtain ⟨t, ht⟩ : D k ∣ ∏ k, D k := Finset.dvd_prod_of_mem D (Finset.mem_univ k)
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · have := Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hD k
      rw [ht, h, mul_zero] at this; exact absurd this (lt_irrefl 0)
    · exact h
  have h1 : StrictWith (id : ℤ → ℤ) φ (t * D k) ((t : ℤ) • ℓ) fun i => pull e.toLinearMap (γ i) := by
    rw [hDk]; exact StrictWith.mul ht0 hℓ
  have h2 := StrictWith.of_pull e.surjective h1
  obtain ⟨w, hw⟩ := exists_linW_eq X (((t : ℤ) • ℓ) ∘ₗ
    { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  refine ⟨m, γ, w, hγ, ?_, c, hc, rfl⟩
  rw [hw, ht, mul_comm]
  exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainComple
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.LieBase.UnifExists

open Formalism.MJ ReciprocityTheory.ChartRestriction.G.AR.Up

theorem flat_inj {ι : Type} {p q : ℕ} {z z' : ι → Matrix (Fin p) (Fin q) ℂ} (h : flat z = flat z') : z = z' := by
  funext t a b
  exact congrFun h (t, a, b)

theorem exists_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hoi, hfj, -⟩ := hL
  haveI := hoi
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := first_index_eq_of_unfolded U hU rfl k
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hrange : ∀ x : (U.X k).dom, Set.range (cxPt T.Z (U.un k x)).1 ⊆ Set.range j := by
    rintro x _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := Φ.label k x s
    refine ⟨f y, ?_⟩
    show (f ≫ j) y = _
    rw [hfj]
    exact hy
  let lf : (U.X k).dom → CxPts X.str (σ.comp e.toRingHom) := fun x =>
    ⟨IsOpenImmersion.lift j (cxPt T.Z (U.un k x)).1 (hrange x), by
      rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, (cxPt T.Z (U.un k x)).2,
        ← Spec.map_comp]
      rfl⟩
  have hlf : ∀ x, cxOf e σ hj (lf x) = cxPt T.Z (U.un k x) := fun x =>
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwell : ∀ x x' : (U.X k).dom,
      domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x.1 = domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x'.1 →
      cxPt T.Z (U.un k x) = cxPt T.Z (U.un k x') := by
    intro x x' h
    have h5 : ∀ τ, moeb (frameCo (U.X k) hle x.1 τ) 0 = moeb (frameCo (U.X k) hle x'.1 τ) 0 :=
      fun τ => congrFun h τ
    exact cxPt_congr (PointWell.pt_eq_of_block hU hσ k x x'
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x.2 x'.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x'.2 x.2 τ (h5 τ).symm))
  let x0 : (U.X k).dom := ⟨x0F (U.X k), IW.orth_mem_dom (U.X k) _ (isOrth_x0F (U.X k))⟩
  refine ⟨fun v => if h : ∃ x : (U.X k).dom,
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) = v then lf h.choose else lf x0,
    fun x => ?_⟩
  have h : ∃ x' : (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1) =
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) := ⟨x, rfl⟩
  simp only [dif_pos h]
  rw [hlf]
  exact hwell _ _ (flat_inj h.choose_spec)

end GlobalTheory.LieBase.UnifExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcrete
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack

namespace GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable (D : D7) (L0 : LevelData D)

def Companion : Prop :=
  ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
    (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0

def stdBasis (hS : Formalism.L2.Herm.StdTied D) : GL (Fin D.R.k) D.host.E := Classical.choose (exists_stdB_of_tied D hS)

theorem stdBasis_std (hS : Formalism.L2.Herm.StdTied D) : Cmp.StdB D (stdBasis D hS) := Classical.choose_spec (exists_stdB_of_tied D hS)

def placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  locIdStd D u w hg (Classical.choose (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)) (stdBasis D hS) (stdBasis_std D hS)
    (Classical.choose (hC u)) (Classical.choose_spec (hC u))

def embK (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg))

def embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))

theorem embK_embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (z : D.what₂.LL) : embK D L0 u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) = lamV (embAlg D L0 u w hg) (D.what₂.embLL z) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).1 z

def awayChar (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ :=
  Classical.choose (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg)

def gatOf (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (sc : Scale) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GAtP (D.what₂.places.resChar w) :=
  (packC D (fun u => L0 u) I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc 1 (D.what₂.places.resChar w))

set_option maxHeartbeats 4000000 in
theorem gatOf_d (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (I) (ψ) (sc : Scale) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (gatOf D L0 I ψ sc u w h).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
  have e := GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h (I u w h) (ψ u w h) (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))
  rw [pack_eq] at e
  exact e

section Main

variable {D L0}

set_option maxHeartbeats 4000000 in
theorem posOK_placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0)
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (packC D (fun u => L0 u) (placeId D L0 hS hC) ψ u w hg).posOK (embK D L0 u w hg) (embAlg D L0 u w hg) := by
  have e := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).2 (ψ u w hg)
  unfold LocPack.posOK at e ⊢
  exact e

end Main

section Main2

variable {D L0}

end Main2

theorem gPlTiedS_of {X : D7} {Gt : GatTies X} (H0 : Formalism.L2.Herm.Herm0 X)
    (hpl : ∀ u w hg (v : Fin (X.gat u w hg).P.nV) (s : Fin ((X.gat u w hg).P.n' v)) (x : 𝓞 X.host.F),
      x ∈ ((H0.g u w hg).pl v).1.asIdeal ↔
        (0 : WithTop ℤ) < X.what₂.places.val w (tauLL X (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap X.host.F X.host.E (x : X.host.F))))
    (B : Formalism.L2.Herm.HermColsCh X) (gS : Formalism.L2.Herm.SymmetricGroupCompatibility X B) (hB : B.lev0 = H0.lev0) (hg : HEq gS H0.g) :
    Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces X B gS Gt := by
  obtain ⟨l, g⟩ := H0
  dsimp only at hB hg hpl
  subst hB
  obtain rfl := eq_of_heq hg
  exact hpl

end GlobalTheory.Mem.ConcreteRecord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem unitOn_injective : Function.Injective (unitOn (R := ℂ)) := by
  intro c c' h
  ext
  have := congrArg (fun u : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (u : Γ(Sp ℂ, ⊤))) h
  simpa [unitOn] using this

theorem unitOn_one : unitOn (1 : ℂˣ) = 1 := by simp [unitOn]

theorem map_nsmul_eq_pow {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) (N : ℕ) (u : Fin g → ℂ) : f ((N : ℂ) • u) = f u ^ N := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Nat.cast_succ, add_smul, one_smul, hf, ih, pow_succ]

theorem pow_eq_one_of_map {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) {N : ℕ} (hN : 0 < N) {v : Fin g → ℂ} (hv : f v = 1) : f ((N : ℂ)⁻¹ • v) ^ N = 1 := by
  rw [← map_nsmul_eq_pow f hf h0, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_smul, hv]

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisati
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifSlice

open Matrix Formalism.DegreeFormula GlobalTheory.TrueCx ReciprocityTheory.ChartRestriction.G.FD

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := _root_.GlobalTheory.LocInj.locInj

theorem domPt_rel_of_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : Formalism.L2.PjFree.IsUnf U) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (k : U.Comp) {j : ℕ} (hj : j ≤ r) (hp : (U.X k).p0 = r - j) {Tau : Type} [Fintype Tau] (κ : Tau ≃ (U.X k).Ψ)
    (x x' : (U.X k).dom) (h : (U.un k x).x = (U.un k x').x) :
    ∃ γ ∈ (U.X k).Γ, domPt (U.X k) hj κ x'.1 = moebI (toUpq (U.X k) hj κ γ) (domPt (U.X k) hj κ x.1) := by
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k x') h
  obtain ⟨γ, hγ, b', hb', e⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ x').1 ⟨t, ht⟩
  have e' : x'.1 = rmul (lact γ (rmul x.1 b)) b' := eq_of_heq (Sigma.mk.inj e).2
  refine ⟨γ, hγ, ?_⟩
  rw [e', domPt_rmul _ hj κ hb', domPt_lact _ hj κ hp γ hm,
    GlobalTheory.PointOfFrames.domPt_rmul_block _ hj κ _ b hb (by rw [← hp]; exact hb0)]

theorem flat_unflat {ι : Type} {p q : ℕ} (v : ι × Fin p × Fin q → ℂ) : flat (unflat v) = v := by
  funext ⟨i, a, b⟩; rfl

theorem unflat_flat {ι : Type} {p q : ℕ} (z : ι → Matrix (Fin p) (Fin q) ℂ) : unflat (flat z) = z := by
  funext i; ext a b; rfl

theorem continuous_unflat {ι : Type} {p q : ℕ} :
    Continuous (unflat : (ι × Fin p × Fin q → ℂ) → ι → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_pi fun _ => continuous_matrix fun _ _ => continuous_apply _

theorem exists_slice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  intro E _ _ _ H Dw l Xo c σ U hσ hU k x₀ n hn
  classical
  have hj : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  have hcard : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = n := by
    rw [hn, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel_left]
  let f : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let L : V n ≃L[ℂ] ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) :=
    (EuclideanSpace.equiv (Fin n) ℂ).trans (LinearEquiv.funCongrLeft ℂ ℂ f).toContinuousLinearEquiv
  set z₀ := domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 with hz₀
  have hz₀D : z₀ ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) := domPt_mem (U.X k) hj _ hp x₀.2
  obtain ⟨O, hO, hz₀O, hinj⟩ := locInj E (Dw.p + Dw.q) Dw.p (U.X k) hj (U.X k).Ψ (Equiv.refl _) hp z₀ hz₀D
  let ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q) := fun w => SecFrame.frameAt (U.X k) hj (Equiv.refl _) (unflat (L w))
  have hdom : ∀ w, unflat (L w) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ψ w ∈ (U.X k).dom := fun w hw =>
    SecFrame.frameAt_mem (U.X k) hj _ hp hw
  have hpt : ∀ w, domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ w) = unflat (L w) := fun w => SecFrame.domPt_frameAt (U.X k) hj _ _
  refine ⟨{w | unflat (L w) ∈ O} ∩ L ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L.symm (flat z₀), ψ,
    (hO.preimage (continuous_unflat.comp L.continuous)).inter
      (GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage L.continuous), ?_, fun w hw => hdom w hw.2,
    fun τ i i' => ((SecFrame.differentiable_frameAt (U.X k) hj (Equiv.refl _) τ i i').comp L.differentiable).differentiableOn,
    fun h => ?_, fun w hw w' hw' h h' e => ?_⟩
  · refine ⟨?_, ?_⟩
    · show unflat (L (L.symm (flat z₀))) ∈ O
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀O
    · show unflat (L (L.symm (flat z₀))) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀D
  · have e0 : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ (L.symm (flat z₀))) = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 := by
      rw [hpt, L.apply_symm_apply, unflat_flat]
    have h5 : ∀ τ, Formalism.MJ.moeb (frameCo (U.X k) hj (ψ (L.symm (flat z₀))) τ) 0 = Formalism.MJ.moeb (frameCo (U.X k) hj x₀.1 τ) 0 :=
      fun τ => congrFun e0 τ
    exact PointWell.pt_eq_of_block hU hσ k ⟨_, h⟩ x₀
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp h x₀.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp x₀.2 h τ (h5 τ).symm)
  · obtain ⟨γ, hγ, hγe⟩ := domPt_rel_of_pt_eq U hU hσ k hj hp (Equiv.refl (U.X k).Ψ) ⟨_, h⟩ ⟨_, h'⟩ e
    have hγe' : unflat (L w') = moebI (toUpq (U.X k) hj (Equiv.refl (U.X k).Ψ) γ) (unflat (L w)) := by
      rw [← hpt w', ← hpt w]; exact hγe
    have h1 := hinj _ ⟨hw.1, hw.2⟩ _ ⟨hw'.1, hw'.2⟩ γ hγ hγe'
    have h2 : L w = L w' := by rw [← flat_unflat (L w), h1, flat_unflat]
    exact L.injective h2

end GlobalTheory.UnifSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_of_inRCone_cell {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (hlin : φ.LinearOn G) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (G i) : ℝ) = N * φ.evalZ (G i))
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone G β) : (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff φ G).1 hlin c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring

theorem inRCone_of_nat_rel {X : Type} [AddCommGroup X] {n : ℕ} {δ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin n → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • δ i) : InRCone δ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * δ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * (β a b : ℝ) = ∑ i, (c i : ℝ) * (δ i a b : ℝ) := by exact_mod_cast h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ i, (c i : ℝ) * (δ i a b : ℝ)) / k from by rw [← h2]; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_cut_of_cell_le : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ,
      (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  intro O _ bar φ X _ _ _ m n G δ hG hδ hin
  obtain ⟨NG, ℓG, hNG, g1, -, -⟩ := hG.strict
  obtain ⟨Nδ, ℓδ, hNδ, d1, d2, d3⟩ := hδ.strict
  have hNG' : (0 : ℝ) < NG := by exact_mod_cast hNG
  have key : ∀ β : LinearMap.BilinForm ℤ X, InRCone G β → (ℓG β : ℝ) = NG * φ.evalZ β :=
    fun β hβ => apply_eq_of_inRCone_cell hG.linear g1 hβ
  have hval : ∀ β : LinearMap.BilinForm ℤ X, (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) β : ℤ)) : ℝ) = NG * ℓδ β - Nδ * ℓG β :=
    fun β => by simp
  refine ⟨(NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG, fun j => ?_, fun k => ?_, fun β hβ hp hc h0 => ?_⟩
  · have h1 : (0 : ℝ) ≤ (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (G j) : ℤ)) : ℝ) := by
      rw [hval, g1 j]
      have := d2 (G j) (hG.mem j) (hG.nonneg j)
      nlinarith
    exact_mod_cast h1
  · have h1 : (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (δ k) : ℤ)) : ℝ) = 0 := by
      rw [hval, key _ (hin k), d1 k]; ring
    exact_mod_cast h1
  · have h1 := hval β
    rw [h0, key β hc] at h1
    have h2 : (Nδ : ℝ) * φ.evalZ β = ℓδ β := by
      have : (NG : ℝ) * ((Nδ : ℝ) * φ.evalZ β - ℓδ β) = 0 := by push_cast at h1; linarith
      have := (mul_eq_zero.1 this).resolve_left hNG'.ne'
      linarith
    obtain ⟨k, c, hk, e⟩ := d3 β hβ hp h2
    exact inRCone_of_nat_rel hk e

end GlobalTheory.PolFan
end
end

