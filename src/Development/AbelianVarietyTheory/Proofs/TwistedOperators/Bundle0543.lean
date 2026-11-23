module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0538

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClassSumSchwartzProductsGridPath
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

open GlobalTheory.FunObj.LocTensor
open scoped ValuativeRel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem locArg_eq_locM (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ (β : GL (Fin (G.pT a.pair).rank) (Lev.EAf D)) (β' : GL (Fin (G.pS a.pair).rank) (Lev.EAf D)), ∀ w,
      ∃ (f : Fin ((locGrid G t w).rank (edgeOf a).tgt) → Fin (G.pS a.pair).rank)
        (g : Fin ((locGrid G t w).rank (edgeOf a).src) → Fin (G.pT a.pair).rank),
        f.Surjective ∧ g.Surjective ∧ ∀ x r c, locArg B t w a x r c = locM β β' w x (g c) (f r) := by
  have sur : ∀ {m n : ℕ} (h : m = n), (Fin.cast h).Surjective := fun h y => ⟨Fin.cast h.symm y, by simp⟩
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · refine ⟨B.β i j, B.β (i + 1) j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i + 1, j)) ⟨hi, hj⟩),
      Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi.le, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.right i j) x = B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨hi.le, hj⟩ ⟨hi, hj⟩
        (x.map fun c => cpt w (toEAf D c)) := dite_eq_left ⟨hi, hj⟩
    rw [e]
    rfl
  · refine ⟨B.β i (j + 1), B.β i j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi, hj.le⟩),
      Fin.cast (rank_vertex G t w (X := (i, j + 1)) ⟨hi, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.down t i j) x = B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨hi, hj⟩ ⟨hi, hj.le⟩
        (x.map fun c => cpt w (toEAf D c)) := dite_eq_left ⟨hi, hj⟩
    rw [e]
    rfl

theorem locArg_add (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) (w : Pl D.host.E)
    (x u : WO (G.pS a.pair) (G.pT a.pair)) : locArg B t w a (x + u) = locArg B t w a x + locArg B t w a u := by
  obtain ⟨β, β', h⟩ := locArg_eq_locM B ha
  obtain ⟨f, g, -, -, h⟩ := h w
  ext r c
  rw [Matrix.add_apply, h, h, h, locM_add, Matrix.add_apply]

theorem arrow_sb {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {a : Arrow T} (ha : IsGridArrow D.R.m t a) {Y : Type}
    (F : WO (G.pS a.pair) (G.pT a.pair) → Y → ℂ)
    (h1 : ∀ x u y, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) → F (x + u) y = F x y)
    (h2 : ∀ x y, F x y ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w]) :
    ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
      (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧ ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
  obtain ⟨hS, hT, -⟩ := arrow_data ρ hL ha
  obtain ⟨β, β', hβ⟩ := locArg_eq_locM B ha
  obtain ⟨k, hk, k1, k2⟩ := exists_mult
    (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hT) he β β' n
  exact exists_sb hS.1.fg hT.1.fg (GlobalTheory.PlaceVec.idemSum_mul_self he) F hk
    (fun u hu x y => h1 x (k • u) y fun w hw r c => by
      obtain ⟨f, g, -, -, h⟩ := hβ w
      rw [h]
      exact k1 u hu w hw _ _)
    fun x y hx h0 => k2 x hx fun w hw i j => by
      obtain ⟨f, g, hf, hg, h⟩ := hβ w
      obtain ⟨c, rfl⟩ := hg i
      obtain ⟨r, rfl⟩ := hf j
      rw [← h]
      exact h2 x y h0 w hw r c

theorem exists_classSum_schwartzProducts_pathInduction {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p →
    (edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ),
    (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) →
    (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
      x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → ArgT G p), (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧
      ∀ (x : ArgT G p) (y : U), HalfAll e p x →
        K (fun w => pathArgs B t w p x) y = ∑ κ ∈ s, famProd p (φ κ) x * K (fun w => pathArgs B t w p (r κ)) y := by
  intro Y p
  induction p with
  | nil =>
    intro _ _ U K _ _
    refine ⟨Unit, {()}, fun _ => (), fun _ => (), fun _ => (), fun _ _ => trivial, fun x y _ => ?_⟩
    rw [Finset.sum_singleton]
    exact (one_mul _).symm
  | snoc a p ih =>
    intro hg hnd U K hK1 hK2
    have hnd' : (edges p ++ [edgeOf a]).Nodup :=
      edges_snoc a p ▸ (hnd : (edges (.snoc a p)).Nodup)
    have hnd1 : (edges p).Nodup := hnd'.of_append_left
    have hne : edgeOf a ∉ edges p :=
      List.disjoint_right.mp hnd'.disjoint (List.mem_singleton_self _)
    have ha : IsGridArrow D.R.m t a := hg.last
    let F (x : WO (G.pS a.pair) (G.pT a.pair)) (z : ArgT G p × U) : ℂ :=
      K (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) z.2
    have hF1 : ∀ x u z, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) →
        F (x + u) z = F x z := by
      intro x u z hu
      have e1 : (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a (x + u))) =
          (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) +
            fun w => Function.update (0 : (locGrid G t w).Args) (edgeOf a) (locArg B t w a u) := by
        funext w b
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · simp only [Pi.add_apply, Function.update_self, locArg_add B ha]
        · simp only [Pi.add_apply, Function.update_of_ne hb, Pi.zero_apply, add_zero]
      dsimp only [F]
      rw [e1]
      refine hK1 _ _ _ fun w hw b => ?_
      rcases eq_or_ne b (edgeOf a) with rfl | hb
      · rw [Function.update_self]
        exact GivenAdm.mem_matLat_smul.2 (hu w hw)
      · rw [Function.update_of_ne hb]
        exact zero_mem _
    have hF2 : ∀ x z, F x z ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w] := by
      intro x z h0 w hw r c
      have hm : edgeOf a ∈ edges (.snoc a p) := by
        rw [edges_snoc]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have h := hK2 (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x))
        z.2 h0 w hw (edgeOf a) hm
      rw [Function.update_self] at h
      exact GlobalTheory.SplitFlip.mem_matLat_stdLat.1 h r c
    have hArrowExpansion :
        ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
          (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧
            ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
      exact arrow_sb (W := W) B ρ (μ₀ := μ₀) hL (t := t) (e := e) he n (a := a) ha
        (Y := ArgT G p × U) F hF1 hF2
    obtain ⟨ι₁, s₁, φa, r₁, hφa, hexp⟩ := hArrowExpansion
    let K' (x : ∀ w, (locGrid G t w).Args) (y : ι₁ × U) : ℂ :=
      K (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) y.2
    have hK'1 : ∀ x z y, (∀ w ∈ locPl G t, ∀ b,
        z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
        K' (x + z) y = K' x y := by
      intro x z y hz
      have e1 : (fun w => Function.update ((x + z) w) (edgeOf a) (locArg B t w a (r₁ y.1))) =
          (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) +
            fun w => Function.update (z w) (edgeOf a) 0 := by
        funext w b
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · simp only [Pi.add_apply, Function.update_self, add_zero]
        · simp only [Pi.add_apply, Function.update_of_ne hb]
      dsimp only [K']
      rw [e1]
      refine hK1 _ _ _ fun w hw b => ?_
      rcases eq_or_ne b (edgeOf a) with rfl | hb
      · rw [Function.update_self]
        exact zero_mem _
      · rw [Function.update_of_ne hb]
        exact hz w hw b
    have hK'2 : ∀ x y, K' x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
        x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _) := by
      intro x y h0 w hw b hb
      have hm : b ∈ edges (.snoc a p) := by
        rw [edges_snoc]
        exact List.mem_append_left _ hb
      have h := hK2 (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) y.2 h0 w hw b hm
      have hba : b ≠ edgeOf a := fun hEq => hne (hEq ▸ hb)
      rwa [Function.update_of_ne hba] at h
    obtain ⟨ι₂, s₂, φ₂, d₂, r₂, hv, hexp₂⟩ := ih hg.init hnd1 (U := ι₁ × U) K' hK'1 hK'2
    obtain ⟨Tm, hTm, -, -⟩ := exists_arrowModel ρ hL he ha
    refine ⟨ι₂ × ι₁, s₂ ×ˢ s₁, fun κ => (φ₂ κ.1, φa κ.2), fun κ => (d₂ κ.1, Tm (φa κ.2)), fun κ => (r₂ κ.1, r₁ κ.2),
      fun κ hκ => ?_, fun x y hx => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hκ
      exact ⟨hv _ h1, (hTm _ _).2 ⟨hφa _ h2, rfl⟩⟩
    · have hx' : HalfAll e p x.1 ∧ IsHalf e x.2 := hx
      have e1 : (fun w => pathArgs B t w (.snoc a p) x) =
          fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) :=
        funext fun w => pathArgs_snoc B t w a p x
      calc K (fun w => pathArgs B t w (.snoc a p) x) y
          = ∑ i ∈ s₁, φa i x.2 * K (fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a (r₁ i))) y := by
            rw [e1]
            exact hexp x.2 (x.1, y) hx'.2
        _ = ∑ i ∈ s₁, φa i x.2 * ∑ κ ∈ s₂, famProd p (φ₂ κ) x.1 *
              K (fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i))) y :=
            Finset.sum_congr rfl fun i _ => congrArg _ (hexp₂ x.1 (i, y) hx'.1)
        _ = _ := by
            rw [Finset.sum_product_right]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun κ _ => ?_
            have e2 : (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) =
                fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i)) :=
              funext fun w => pathArgs_snoc B t w a p _
            show _ = famProd p (φ₂ κ) x.1 * φa i x.2 * K (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) y
            rw [e2]
            ring

theorem exists_classes_path : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y :=
  by
  intro D T L sc G μ₀ hL W B ρ t e he n X Y p hg hnd U K hK1 hK2
  exact exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg hnd K hK1 hK2

end GlobalTheory.FlipRun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel


set_option maxHeartbeats 4000000 in
theorem exists_isGen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hS : S.gram = 1 := C.m.gS
  obtain ⟨γ, hγ, s, hs, h1, h2'⟩ := _root_.GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice D T.rank C.X.Λ ΛT hAA (Pg ∪ Q)
  obtain ⟨t, ht, hte⟩ := _root_.GlobalTheory.HalfUnit.exists_int_inv_half D (Pg ∪ Q) e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hecinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf : ∀ x : WO S T, IsHalf (cA D e) x → IsFinPt x := by
    intro x hx
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, hecinf, zero_mul]
  have hmulA : ∀ (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, ((s : D.host.E) * c) • v ∈ L2) →
      ∀ x : WO S T, IsHalf (cA D e) x → x ∈ hatA S T (tens (stdL D.host.E S.rank) L1) →
        incA D c • x ∈ hatA S T (tens (stdL D.host.E S.rank) L2) := by
    intro L1 L2 c hc x hx hxm
    have h3 := GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup D S T _ L1 L2 _ hc x hxm
    have h4 := smul_mem_hatA_of_int (fun o y hy => HatLat.smul_mem_tens _ _ o hy) ht h3
    convert h4 using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    have hxij := hx i j
    calc incA D c * x i j = incA D c * (cA D e * x i j) := by rw [hxij]
      _ = (t * incA D (s : D.host.E) * cA D e) * (incA D c * x i j) := by rw [hte]; ring
      _ = t * (incA D (s : D.host.E) * incA D c * (cA D e * x i j)) := by ring
      _ = t * (incA D (s : D.host.E) * incA D c * x i j) := by rw [hxij]
  have hsc : ∀ (I : Ideal (𝓞 D.host.E)) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) →
      ∀ v ∈ I • L1, c • v ∈ I • L2 := by
    intro I L1 L2 c hc v hv
    refine Submodule.smul_induction_on hv (fun i hi w hw => ?_) (fun a b ha hb => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hi (hc w hw)
    · rw [smul_add]; exact add_mem ha hb
  refine ⟨e * incA D (star γ⁻¹), ⟨e * incA D (star γ), ?_⟩, ?_⟩
  · have hu : incA D (star γ⁻¹) * incA D (star γ) = 1 := by
      rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hγ), map_one]
    calc e * incA D (star γ⁻¹) * (e * incA D (star γ)) = (e * e) * (incA D (star γ⁻¹) * incA D (star γ)) :=
          mul_mul_mul_comm _ _ _ _
      _ = e := by rw [hu, mul_one, hee]
  intro x hx
  have hadj : adjA S T βS βT (e * incA D (star γ⁻¹)) x = adjA S T βS βT 1 (incA D γ⁻¹ • x) :=
    GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul D S T βS βT e γ⁻¹ x hx
  have hy : IsHalf (cA D e) (incA D γ⁻¹ • x) := by
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hx i j]
  have hyf := hinf _ hy
  have hback : incA D γ • (incA D γ⁻¹ • x) = x := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_smul]
  rw [hadj]
  obtain ⟨hsq, hle, hconj⟩ := _root_.GlobalTheory.primeProd_squarefree_le_conj D (Pg ∪ Q)
  have hmem : ∀ (I : Ideal (𝓞 D.host.E)),
      (incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • ΛT)) ↔
        x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • C.X.Λ))) := by
    intro I
    constructor
    · intro hm
      have := hmulA (I • ΛT) (I • C.X.Λ) γ (hsc I ΛT C.X.Λ _ h2') _ hy hm
      rwa [hback] at this
    · intro hm
      exact hmulA (I • C.X.Λ) (I • ΛT) γ⁻¹ (hsc I C.X.Λ ΛT _ h1) x hx hm
  have hctop : conjI (⊤ : Ideal (𝓞 D.host.E)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    unfold conjI
    exact Ideal.subset_span ⟨1, Submodule.mem_top, by simp⟩
  constructor
  · have hB := _root_.GlobalTheory.DualRed.adj_int_iff D S T hS ΛT hsd βS βT hβT ⊤ (by rw [← Ideal.one_eq_top]; exact squarefree_one) _ hyf
    rw [hctop, Submodule.top_smul] at hB
    have h5 := hmem ⊤
    rw [Submodule.top_smul, Submodule.top_smul] at h5
    rw [← h5, ← hB]
    constructor
    · intro h; exact ⟨h, fun PP hPP => absurd (top_le_iff.mp hPP) PP.isPrime.ne_top⟩
    · intro h; exact h.1
  · have hB := _root_.GlobalTheory.DualRed.adj_int_iff D S T hS ΛT hsd βS βT hβT _ hsq _ hyf
    rw [hconj] at hB
    have hB' : (IsIntM (adjA S T βS βT 1 (incA D γ⁻¹ • x)) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E,
        (∏ PP ∈ Pg ∪ Q, PP.asIdeal) ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 (incA D γ⁻¹ • x)) = 0) ↔
        incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • ΛT)) := hB
    have h5 := hmem (liftI Pg Q)
    rw [← h5, ← hB']
    simp only [hle]

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_columnRowKernelPairing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∃ M : MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => thSub W (.top t j))
        (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  intro D T L sc G W U S t x y Ψ₀ F₀
  have chain {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] :
      ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
        (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
        ∃ M : MultilinearMap (RingHom.id ℂ) A (V 0 →ₗ[ℂ] V m), ∀ fs,
          M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
    intro m
    induction m with
    | zero =>
      intro A _ _ k
      exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
    | succ m ih =>
      intro A _ _ k
      obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
      let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
      refine ⟨MultilinearMap.uncurryRight
        (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M),
        fun fs => ?_⟩
      show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
      rw [hM]
      beta_reduce
      rw [dite_eq_left (Nat.lt_succ_self m)]
      congr 1
      refine GlobalTheory.ArrowMultilinear.chainTo_congr m fun j hj => ?_
      rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
      rfl
  obtain ⟨Mc, hc⟩ := chain (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.top t j)
        (x j * S.N.u _) (x (j + 1) * S.N.u _))
  obtain ⟨Mr, hr⟩ := chain (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.chi i D.R.m : Pair T)
        (y i * S.N.u _) (y (i + 1) * S.N.u _))
  let col := (LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc
  let row := (LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr
  have hcol (fs : ∀ j : Fin D.R.m, thSub W (.top t j)) :
      col fs = colMapV S (t := t) (fun j => (fs j : WO _ _ → ℂ)) x Ψ₀ := by
    show Mc fs _ = _
    rw [hc]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have hrow (gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) :
      row gs = rowMapV S (fun i => (gs i : WO _ _ → ℂ)) y F₀ := by
    show Mr gs _ = _
    rw [hr]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  let β := brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))
  let pairWithRow : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ :=
    { toFun := fun v => (β v).compMultilinearMap row
      map_add' := fun v v' => by
        ext gs
        change β (v + v') (row gs) = β v (row gs) + β v' (row gs)
        simp only [map_add]
        rfl
      map_smul' := fun c v => by
        ext gs
        change β (c • v) (row gs) = c • β v (row gs)
        simp only [map_smul]
        rfl }
  refine ⟨pairWithRow.compMultilinearMap col, fun fs gs => ?_⟩
  show β (col fs) (row gs) = _
  rw [hcol, hrow]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensional
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.FockVac

theorem span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  by_cases h : ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧ g ≠ 0
  · obtain ⟨g, hg, hg0⟩ := h
    have hle : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {g} := by
      refine Submodule.span_le.2 fun f hf => ?_
      obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M B.ψ B.emb hP.base.cm hP.base.std
        (fun w => (hP.herm.cartan w).1) (fun w => (hP.skew.cartan w).1) f g hg hg0 hf
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  · push_neg at h
    have hb : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} = ⊥ :=
      Submodule.span_eq_bot.2 fun f hf => by_contra fun h0 => h0 (h f hf)
    rw [hb]
    infer_instance

end GlobalTheory.FockVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointJacobiFunctionUnfolded
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem fb_base_th_fl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ ∀ y : WO J.W₀ B.L → ℂ, GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) Ψ, IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (rat x₀) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
  intro D ψ σ J B s
  obtain ⟨x₀, hx, hbase, hR, -, -⟩ := _root_.GlobalTheory.Asc.FBL.basePoint_spec D σ B
  refine ⟨x₀, hx, hbase, hR, fun y hy => ⟨_root_.GlobalTheory.th_isTh_lev D ψ s.weil.std σ J B y hy x₀ hx, fun vb vL Ψ hΨ => ?_⟩⟩
  rw [hx]
  exact (_root_.GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract D ψ σ J B s vb vL y Ψ hy hΨ).1

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRungStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_thetaTower_bottom_rung : FockTot → Rung0 := by
  first | exact @GlobalTheory.AscBottom.rung0 | exact GlobalTheory.AscBottom.rung0 | (intros; apply GlobalTheory.AscBottom.rung0 <;> assumption)
end

