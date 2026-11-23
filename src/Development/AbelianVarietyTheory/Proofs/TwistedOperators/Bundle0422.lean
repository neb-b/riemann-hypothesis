module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0418
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def datumA (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeBig t i j)) :
    WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := negSp (G.V (.grid (i + 1) (j + 1)))) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid (i + 1) (j + 1))) (G.V (.grid (i + 1) j)) y))

def datumB (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeSmall t i j)) :
    WO (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))

def IsGridFr (W : G.Weil) (X : Node) (A : Fr (G.V X)) : Prop :=
  ∀ τ, A.onb τ = W.onb X τ ∧ A.cart τ = W.cart X τ

theorem exists_isGridFr (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) : ∃ A : Fr (G.V X), IsGridFr W X A := by
  choose ε hε using W.onb_is X hX
  have hu : ∀ τ, IsUnit (W.onb X τ) := fun τ => by
    have h1 : IsUnit ((W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ) := by
      rw [(hε τ).1]
      refine ⟨⟨Formalism.REAL.Jm (ε τ), Formalism.REAL.Jm (ε τ), ?_, ?_⟩, rfl⟩ <;>
      · ext a b
        by_cases h : a = b
        · subst h; cases h' : ε τ a <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h', Matrix.one_apply]
        · simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h, Matrix.one_apply]
    rw [Matrix.isUnit_iff_isUnit_det] at h1 ⊢
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨⟨ε, fun τ => (W.onb X τ)⁻¹, fun τ => (Matrix.isUnit_nonsing_inv_iff).2 (hu τ), fun τ => ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    rw [← (hε τ).1, Matrix.conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (by simpa [Matrix.det_conjTranspose] using hd.star), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ = W.onb X τ
    exact Matrix.nonsing_inv_nonsing_inv _ hd
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (W.onb X τ)⁻¹ = W.cart X τ
    rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← (hε τ).2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

def zact {S X : HSp D} (ω : GlobalTheory.Grid.WRep S X) (z : GA D S →₀ ℂ) (Φ : WO S X → ℂ) : WO S X → ℂ :=
  z.sum fun k c => c • ω (k, 1) Φ

end GlobalTheory.SquareDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHomApproxHalfModIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosRatApprox

open GlobalTheory.FunObj.Comparison₂

theorem infPart_idemSum_mul {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (a : AE D) :
    infPart D (e * a) = 0 := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  rw [(infPart D).map_mul, e0, zero_mul]


set_option maxHeartbeats 1000000 in
theorem exists_rat_approx : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsFullLattice D.host.E Λ → Submodule.IsFullLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  intro D m n Λ Λ' 𝔪 h𝔪 hΛ hΛ' e P he z hz hzmem
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E n Λ hΛ
  obtain ⟨β', hβ'⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E m Λ' hΛ'
  have hz' : z ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat Λ Λ') := by rwa [Submodule.top_smul]
  obtain ⟨-, hs⟩ := (mem_hatMx_iff hβ hβ' ⊤ z).1 hz'
  choose s _ hs' using hs
  obtain ⟨x₀, hx₀, ht⟩ := GlobalTheory.FunObj.HatFrame.homLat_approx_mod Λ Λ' β β' hβ hβ' 𝔪 h𝔪 s
  choose t htI htv using ht
  have k1 : ∀ i j, (z - e • x₀.map (incA D)) i j = e * (z i j - incA D (x₀ i j)) :=
    fun i j => by rw [mul_sub, hz i j]; rfl
  have k2 : ∀ i j, fr β' β ((z - e • x₀.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr β' β (z.map (toEAf D)) i j - fr β' β (x₀.map (eToEAf D)) i j) := fun i j => by
    have : (z - e • x₀.map (incA D)).map (toEAf D) = toEAf D e • (z.map (toEAf D) - x₀.map (eToEAf D)) :=
      Matrix.ext fun i j => by rw [Matrix.map_apply, k1, RingHom.map_mul, RingHom.map_sub]; rfl
    rw [this, fr_smul, fr_sub]; rfl
  refine ⟨⟨x₀, hx₀⟩, ?_⟩
  show z - e • x₀.map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')
  refine (mem_hatMx_iff hβ hβ' 𝔪 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [k1 i j]; exact infPart_idemSum_mul he _
  · let eS : {x // x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E} := ⟨toEAf D e, GlobalTheory.CosToCoset.idem_mem_OA he⟩
    refine ⟨eS * -t i j, Ideal.mul_mem_left _ eS (neg_mem (htI i j)), ?_⟩
    rw [k2, ← hs' i j]
    show toEAf D e * -((t i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = _
    rw [htv i j, neg_sub]

end GlobalTheory.CosRatApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeLevelEqUnitaryInfFrameStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.LatLevEq

theorem conj_apply_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B) (β : GL (Fin n) B)
    (X : Matrix (Fin n) (Fin n) B)
    (hX : ∀ w : Fin n → B, (∀ i, ((β⁻¹).val *ᵥ w) i ∈ S) → ∀ i, ((β⁻¹).val *ᵥ (X *ᵥ w)) i ∈ S) :
    ∀ i j, ((β⁻¹).val * X * β.val) i j ∈ S := by
  intro i j
  have hw : ∀ k, ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) k ∈ S := by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := hX _ hw i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  exact this

theorem exists_integral_conj {B : Type} [CommRing B] {n : ℕ} (S : Subring B) (β x : GL (Fin n) B)
    (h1 : ∀ i j, ((β⁻¹).val * x.val * β.val) i j ∈ S) (h2 : ∀ i j, ((β⁻¹).val * (x⁻¹).val * β.val) i j ∈ S) :
    ∃ y : GL (Fin n) S, β.val * y.val.map S.subtype * (β⁻¹).val = x.val := by
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (β⁻¹).val * x.val * β.val := by ext i j; rfl
  have hM' : M'.map S.subtype = (β⁻¹).val * (x⁻¹).val * β.val := by ext i j; rfl
  have key : ∀ (P Q : Matrix (Fin n) (Fin n) S), P.map S.subtype * Q.map S.subtype = 1 → P * Q = 1 := by
    intro P Q h
    apply Matrix.map_injective Subtype.val_injective
    have e := Matrix.map_mul (f := S.subtype) (L := P) (M := Q)
    have e1 := Matrix.map_one S.subtype (map_zero _) (map_one _) (n := Fin n)
    exact e.trans (h.trans e1.symm)
  have hu : ∀ a b : GL (Fin n) B, a * b = 1 → ((β⁻¹).val * a.val * β.val) * ((β⁻¹).val * b.val * β.val) = 1 := by
    intro a b hab
    have : β⁻¹ * a * β * (β⁻¹ * b * β) = 1 := by
      calc β⁻¹ * a * β * (β⁻¹ * b * β) = β⁻¹ * (a * b) * β := by group
        _ = 1 := by rw [hab]; group
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val this
  refine ⟨⟨M, M', key M M' ?_, key M' M ?_⟩, ?_⟩
  · rw [hM, hM']; exact hu x x⁻¹ (mul_inv_cancel x)
  · rw [hM, hM']; exact hu x⁻¹ x (inv_mul_cancel x)
  · show β.val * M.map S.subtype * (β⁻¹).val = x.val
    rw [hM]
    have : β * (β⁻¹ * x * β) * β⁻¹ = x := by group
    simpa only [Units.val_mul] using congrArg Units.val this

end GlobalTheory.LatLevEq

namespace GlobalTheory.LatLevEq

theorem latLev_eq_UA_inf_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → GlobalTheory.Mass.Levels.latLev V = Formalism.L2.DIV.UA D.sp.cm V.gram ⊓ Formalism.L2.DIV.St β := by
  intro D V β Λ hβ
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hu
    refine ⟨(GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).2, ?_⟩
    set x : GL (Fin V.rank) (Lev.EAf D) :=
      ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) :
        GL (Fin V.rank) (Lev.EAf D)) with hxdef
    have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
      have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
      exact h1.symm
    have hst := (GlobalTheory.Mass.Levels.mem_latStab V g).1 hg
    have tr : ∀ w : Fin V.rank → Lev.EAf D,
        (fun i => GlobalTheory.LevelActionPinned.sw D
          (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ
            fun i => (GlobalTheory.LevelActionPinned.sw D).symm (w i)) i)) = x.val *ᵥ w := by
      intro w
      rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hmat]
      simp only [RingEquiv.apply_symm_apply]
    have hz : ∀ w : Fin V.rank → Lev.EAf D,
        (fun i => GlobalTheory.LevelActionPinned.sw D ((GlobalTheory.LevelActionPinned.sw D).symm (w i))) = w := by
      intro w; funext i; simp only [RingEquiv.apply_symm_apply]
    have h1 := conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β x.val fun w hw => by
      have hzm := (hP _).2 (by rw [hz]; exact hw)
      have := (hP _).1 ((hst _).1 hzm)
      rwa [tr] at this
    have h2 := conj_apply_mem (GlobalTheory.LevelActionPinned.SI D) β (x⁻¹).val fun w hw => by
      have hw' : ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D
          (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ
            fun i => (GlobalTheory.LevelActionPinned.sw D).symm (((x⁻¹).val *ᵥ w) i)) i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
        rw [tr, show x.val *ᵥ ((x⁻¹).val *ᵥ w) = w by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]]
        exact hw
      have := (hP _).1 ((hst _).2 ((hP _).2 hw'))
      rwa [hz] at this
    obtain ⟨y, hy⟩ := exists_integral_conj (GlobalTheory.LevelActionPinned.SI D) β x h1 h2
    exact ⟨y, Units.ext hy⟩
  · rintro x ⟨hUA, hSt⟩
    obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
    obtain ⟨t, ht⟩ := hSt
    let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
    let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
    have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
      simp only [g, MulEquiv.apply_symm_apply, u]
    have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
      have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
      rw [← hg]
      exact h1.symm
    refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
    refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
    constructor
    · intro hy
      exact GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
        (by rw [hmat, ← ht]; rfl) y hy
    · intro hy
      let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
      have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
        ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
      have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
        apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
        have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
          (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
        have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
        refine (e.trans ?_).trans e1.symm
        change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
        rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 := GlobalTheory.LevelInLatStab.mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
        (by rw [hm', ← ht']; rfl) _ hy
      rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LatLevEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.FockCount

open NumberField

theorem incM_map_piInf' {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = J.map τ.1 := by
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    GlobalTheory.AdelicU.infEmb_tmul]

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := _root_.Basis.piTensorProduct (R := ℂ)
    (fun _ : InfinitePlace F => MvPolynomial.basisMonomials (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ)
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem rank_pol_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW _hM
  classical
  have hcm := hB.cm
  have hstd := hB.std
  have hFr : ∀ w, ∃ A : Matrix (Fin n) (Formalism.BasicNotions.TH.Ix r s) ℂ,
      GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) A ∧ X.θ w * A = A * Formalism.BasicNotions.TH.Jm r s := by
    intro w
    rw [incM_map_piInf', one_smul]
    exact _root_.GlobalTheory.RealLift.frameEx_holds n r s _ _ (hX.sig w) (hX.cartan w)
  have hFrW : ∀ w, ∃ C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix r' s') ℂ,
      GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) C ∧
        W.θ w * C = C * Formalism.BasicNotions.TH.Jm r' s' := by
    intro w
    rw [incM_map_piInf']
    exact _root_.GlobalTheory.RealLift.frameEx_holds d r' s' _ _ (hW.sig w) (hW.cartan w)
  choose A hA hAθ using hFr
  choose C hC hCθ using hFrW
  have hFramed : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, hA, hC⟩
  have hder := _root_.GlobalTheory.HeisDer.derEx
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hder F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb (incM F X.J)
    (incM F W.J) M.co 1 Complex.I A C hcm hstd hFramed
  have hrange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder) F E σ n d r s r' s' X W M B.ψ B.emb A C Φ
    hcm hstd hFramed hAθ hCθ hΦ
  rw [← hrange]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')

end GlobalTheory.FockCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_down {D : D7} {X : ProvA} (h : GlobalTheory.ArchRec.Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) (τ : D.what₂.Tau) (V W : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ForAllAt τ V W aS aT S S' fun MS MT A B pt =>
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.LiftLaw MT τ B pt MS A ∧ ∀ ip, GlobalTheory.ArchRec.IsIp V W ip → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaLaw MT τ B pt MS A ip := by
  obtain ⟨al, be, ga, de, hd, -, rfl, rfl⟩ := hp
  intro ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf
  obtain ⟨hm, e, u, hk⟩ := GlobalTheory.ArchRec.tie_small h hd.1 MS τ true false p1
  obtain ⟨e', u', hk'⟩ := GlobalTheory.ArchRec.tie_large h hd.1 MT τ false true p2
  obtain ⟨κ, hR⟩ := GlobalTheory.ArchRec.exists_real hω hS hT (GlobalTheory.ArchRec.isFrameOf_model MS τ) (GlobalTheory.ArchRec.isFrameOf_model MT τ) hf
    hk.ord.1 hk'.ord.1
  exact GlobalTheory.ArchRec.lift_down h h1 h3 hd hm hk hk' hR

theorem pairPar_of_upPair {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) :
    GlobalTheory.PairLift.PairPar S S' aS aT ∧ GlobalTheory.PairLift.PairPar S' S aT aS := by
  obtain ⟨al, be, ga, de, hd, hfar, rfl, rfl⟩ := hp
  have hT : GlobalTheory.PairLift.ThetaPar t (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) (GlobalTheory.Chain.signed (al ++ block t ++ de) (ga ++ be) aS) aT aS :=
    ⟨al, be, ga, de, rfl, Or.inl ⟨hd, rfl⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + aT := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨⟨t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩, ⟨t, _, _, rfl, rfl, Or.inr hT⟩⟩

theorem upPair_arch : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ),
    UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X →
      Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  intro hDS hHC D t S S' aS aT hp
  refine ⟨fun τ V W => ?_, fun X h3 h4 h5 => ?_⟩
  · obtain ⟨X, hX, h1, -, h3, -, -⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
    have h : GlobalTheory.ArchRec.Good D X :=
      ⟨hX, GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX, hHC.admQ5_of_harishChandraModules X, _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D⟩
    have down := upPair_down h h1 h3 hp τ V W
    exact ⟨fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).1,
      fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf μ 𝓕 m1 m2 =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).2 _ ⟨μ, 𝓕, m1, m2, rfl⟩⟩
  · obtain ⟨q1, q2⟩ := pairPar_of_upPair hp
    exact ⟨GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q1, GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q2⟩

end GlobalTheory.EvenOnto

end
end

