module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjective
section
open NumberField

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx Topology Filter

noncomputable section

namespace GlobalTheory.LocInj

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domI : IsOpen (DomI ι p q) := by
  have hc : Continuous (flat : (ι → Matrix (Fin p) (Fin q) ℂ) → ι × Fin p × Fin q → ℂ) :=
    continuous_pi fun x => (continuous_apply x.1).matrix_elem x.2.1 x.2.2
  exact GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage hc

theorem continuousAt_moeb (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (hu : IsUnit (M.toBlocks₂₁ * z + M.toBlocks₂₂).det) :
    ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => moeb M w) z := by
  unfold moeb
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have h1 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => A * w + B) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have h2 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => C * w + D) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have hi : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℂ → Matrix (Fin q) (Fin q) ℂ) (C * z + D) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  have h3 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (C * w + D)⁻¹) z :=
    ContinuousAt.comp (g := Inv.inv) hi h2.continuousAt
  have hm : Continuous (fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact ContinuousAt.comp (g := fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2)
    (f := fun w => (A * w + B, (C * w + D)⁻¹)) hm.continuousAt (h1.continuousAt.prodMk h3)

theorem continuousAt_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : ι → Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ DomI ι p q) : ContinuousAt (moebI g) z := by
  refine continuousAt_pi.2 fun t => ?_
  have hu := GlobalTheory.HodgeDomain.kapQ_isUnit (hg t trivial) (hz t)
  exact ContinuousAt.comp (g := fun w => moeb ((g t : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) w)
    (continuousAt_moeb _ _ hu) (continuous_apply t).continuousAt

theorem moebI_one (z : ι → Matrix (Fin p) (Fin q) ℂ) : moebI (1 : ι → GL (Fin p ⊕ Fin q) ℂ) z = z := by
  funext t
  simp [moebI, GlobalTheory.TrueCx.PointWell.moeb_one]

end GlobalTheory.LocInj

namespace GlobalTheory.LocInj

open GlobalTheory.ShFam.SecFrame

theorem continuous_frameAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) {Tau : Type} (κ : Tau ≃ X.Ψ) : Continuous (frameAt X hj κ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun z : Tau → Matrix (Fin j) (Fin (r - j)) ℂ =>
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1)
  refine continuous_const.matrix_mul ?_
  simp only [reindex_symm, reindex_apply, Equiv.symm_symm]
  exact (continuous_const.matrix_fromBlocks (continuous_apply _) continuous_const continuous_const).matrix_submatrix _ _

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  intro E _ _ _ r j X hj Tau _ κ hp z₀ hz₀
  haveI : LocallyCompactSpace (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Tau → Fin j → Fin (r - j) → ℂ))

  obtain ⟨C, hCn, hCD, hCc⟩ := local_compact_nhds (isOpen_domI.mem_nhds hz₀)
  set K := frameAt X hj κ '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_frameAt X hj κ)
  have hKd : K ⊆ X.dom := by
    rintro _ ⟨z, hz, rfl⟩
    exact frameAt_mem X hj κ hp (hCD hz)
  have hS := _root_.GlobalTheory.BlockTransporter.finite_blockTransporter E r X K hKc hKd
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
    (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
    (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
    ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b} with hSdef

  have hev : ∀ γ ∈ S, ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, γ ≠ 1 → moebI (toUpq X hj κ γ) w.1 ≠ w.2 := by
    intro γ hγS
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    have hne : moebI (toUpq X hj κ γ) z₀ ≠ z₀ := by
      intro h
      have hx := frameAt_mem X hj κ hp hz₀
      refine h1 (GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq E r j X hj Tau κ hp γ hγS.1 _ hx ?_)
      rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, h]
    have hc : ContinuousAt (fun w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) =>
        moebI (toUpq X hj κ γ) w.1) (z₀, z₀) :=
      ContinuousAt.comp (g := moebI (toUpq X hj κ γ))
        (continuousAt_moebI (gammaU_le X hj κ hp ⟨γ, hγS.1, rfl⟩) hz₀) continuous_fst.continuousAt
    have hO : IsOpen {w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) |
        w.1 ≠ w.2} := isOpen_ne_fun continuous_fst continuous_snd
    have := (hc.prodMk continuous_snd.continuousAt).preimage_mem_nhds (hO.mem_nhds hne)
    rw [nhds_prod_eq] at this
    exact Filter.mem_of_superset this fun w hw _ => hw
  have hCC : C ×ˢ C ∈ 𝓝 z₀ ×ˢ 𝓝 z₀ := Filter.prod_mem_prod hCn hCn
  have hall : ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, (fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b) w.1 w.2 :=
    (Filter.Eventually.and hCC ((Filter.eventually_all_finite hS).2 hev)).mono fun w h => ⟨h.1.1, h.1.2, h.2⟩
  obtain ⟨t, ht, htP⟩ := (Filter.eventually_prod_self_iff (la := 𝓝 z₀)
    (r := fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b)).1 hall
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  rintro z ⟨hzt, hzD⟩ z' ⟨hzt', hzD'⟩ γ hγ e
  obtain ⟨hzC, hzC', hmove⟩ := htP z (interior_subset hzt) z' (interior_subset hzt')
  have hx := frameAt_mem X hj κ hp hzD
  have hy := frameAt_mem X hj κ hp hzD'
  have hgx := KU.lact_dom X hγ hx
  set x := frameAt X hj κ z
  set y := frameAt X hj κ z'
  have hpt : domPt X hj κ (lact γ x) = domPt X hj κ y := by
    rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, domPt_frameAt, e]
  have hblk : ∀ τ (a c : Fin r), X.p0 ≤ a → (c : ℕ) < X.p0 → ((mat y τ)⁻¹ * mat (lact γ x) τ) a c = 0 := by
    intro τ
    refine GlobalTheory.TrueCx.PointWell.block_of_moeb_eq X hj hp hy hgx τ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    exact (congrFun hpt s).symm
  have hγS : γ ∈ S := by
    refine ⟨hγ, x, ⟨z, hzC, rfl⟩, y, ⟨z', hzC', rfl⟩, fun τ => (mat y τ)⁻¹ * mat (lact γ x) τ, fun τ => ?_,
      fun τ a c hc ha => hblk τ a c (not_lt.1 ha) hc, ?_⟩
    · show ((mat y τ)⁻¹ * mat (lact γ x) τ).det ≠ 0
      rw [det_mul, det_nonsing_inv]
      exact mul_ne_zero (by rw [Ring.inverse_eq_inv']; exact inv_ne_zero (hy τ).1) (hgx τ).1
    · funext τ
      show mat (lact γ x) τ = mat y τ * ((mat y τ)⁻¹ * mat (lact γ x) τ)
      rw [mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]
  by_contra hne
  by_cases h1 : γ = 1
  · subst h1
    apply hne
    rw [e, map_one, moebI_one]
  · exact hmove γ hγS h1 e.symm

end GlobalTheory.LocInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImageStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  first | exact @GlobalTheory.ShFam.CarriesAt.carries_iff | exact GlobalTheory.ShFam.CarriesAt.carries_iff | (intros; apply GlobalTheory.ShFam.CarriesAt.carries_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.CauchyBinet

theorem lform_plk (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h1 : ∑ q, lform D ρ q * plk u e q =
      ∑ f : Fin k → Fin (M + 1), (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det :=
    Equiv.sum_comp (plE M k)
      (fun f : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det)
  rw [h1]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

variable {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {M : ℕ} {D c : Let m → Fin (M + 1) → S}

theorem pair_cellVec (w : Pm m) (x : CellVar m → S) (y z : Let m) :
    ∑ r, D y r * cellVec c w x z r = ∑ i, cell x z.1 i z.2 * ∑ r, D y r * c ⟨z.1, w z.1 i⟩ r := by
  simp only [cellVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem pair_same (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (a b : Fin (m τ)) :
    ∑ r, D (wLet w ⟨τ, a⟩) r * cellVec c w x ⟨τ, b⟩ r = cell x τ a b := by
  rw [pair_cellVec, Finset.sum_eq_single a]
  · rw [h]
    simp [wLet]
  · intro i _ hi
    rw [h, if_neg, mul_zero]
    intro he
    simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
    exact hi ((w τ).injective he).symm
  · simp

theorem pair_ne (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y.1 ≠ z.1) :
    ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  rw [pair_cellVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [h, if_neg, mul_zero]
  intro he
  have h2 := congrArg Sigma.fst he
  exact hne h2

theorem pair_self (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (z : Let m) :
    ∑ r, D (wLet w z) r * cellVec c w x z r = 1 := by
  obtain ⟨τ, a⟩ := z
  rw [pair_same h]
  simp [cell]

theorem pair_zero (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y ≠ z)
    (hle : (y.2 : ℕ) ≤ z.2) : ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  by_cases h1 : y.1 = z.1
  · obtain ⟨τ, a⟩ := y
    obtain ⟨τ', b⟩ := z
    dsimp only at h1 hle
    subst h1
    rw [pair_same h]
    have hab : a ≠ b := fun e => hne (by rw [e])
    have hlt : ¬ b < a := not_lt.2 hle
    simp [cell, hab, hlt]
  · exact pair_ne h w x y z h1

theorem det_eq_one_of_unitri {k : ℕ} (N : Matrix (Fin k) (Fin k) S) (b : Fin k → ℕ) (h1 : ∀ l, N l l = 1)
    (h0 : ∀ l l', l ≠ l' → b l' ≤ b l → N l l' = 0) : N.det = 1 := by
  have hb : N.BlockTriangular b := fun l l' hl =>
    h0 l l' (fun e => by subst e; exact lt_irrefl _ hl) hl.le
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : N.toSquareBlock b a = 1 := by
    ext ⟨l, hl⟩ ⟨l', hl'⟩
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    split_ifs with he
    · obtain rfl : l = l' := congrArg Subtype.val he
      exact h1 l
    · exact h0 l l' (fun e => he (Subtype.ext e)) (by rw [hl, hl'])
  rw [this, Matrix.det_one]

theorem lform_plk_down (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (k : ℕ) (e : Fin k → Let m)
    (he : Down e) : ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1 := by
  rw [lform_plk]
  refine det_eq_one_of_unitri _ (fun l => ((e l).2 : ℕ)) (fun l => pair_self h w x (e l)) fun l l' hl hb => ?_
  exact pair_zero h w x (e l') (e l) (fun e' => hl (he.1 e').symm) hb

theorem lform_plk_coord (hD : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) (h : j < i) :
    ∑ q, lform D (fun l : Fin (j + 1) =>
        wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q *
      plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  rw [lform_plk]
  simp only [std, pair_same hD]
  rw [Matrix.det_of_upperTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · have : Fin.castLE (Nat.succ_le_of_lt j.2) (Fin.last j) = j := Fin.ext rfl
      simp only [Matrix.of_apply, Fin.val_last, if_true, this, cell, dif_pos h]
    · intro l _
      have hl : ((l.castSucc : Fin (j + 1)) : ℕ) ≠ j := ne_of_lt l.2
      simp only [Matrix.of_apply, if_neg hl, cell, lt_irrefl, dif_neg, if_true, not_false_eq_true]
  · intro l l' hl
    have hl2 : (l' : ℕ) < l := hl
    have hl' : (l' : ℕ) ≠ j := by have := l.2; omega
    have hn : ¬ Fin.castLE (Nat.succ_le_of_lt j.2) l < Fin.castLE (Nat.succ_le_of_lt j.2) l' :=
      not_lt.2 (le_of_lt hl2)
    have hne : Fin.castLE (Nat.succ_le_of_lt j.2) l' ≠ Fin.castLE (Nat.succ_le_of_lt j.2) l :=
      ne_of_lt hl2
    simp only [Matrix.of_apply, if_neg hl', cell, dif_neg hn, if_neg hne]

theorem main : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ :=
  ⟨lform_plk, fun _ _ _ _ _ _ _ w x h =>
    ⟨lform_plk_down h w x, lform_plk_coord h w x⟩⟩

end GlobalTheory.FlagEmb.CauchyBinet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCocycleHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Models (LevComp)

namespace GlobalTheory.LocM.Cocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem exists_sab_of_isTrans {i i₂ : Idx H p} {τ : (Y i₂).X ⟶ (Y i).X} {mu : SABMap (Y i₂).t (Y i).t τ}
    (h : IsTrans i i₂ τ mu) :
    ∃ (b : i.c.V W →+* i₂.c.V W) (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c) (ν : SABMap (Y i₂).oF.t (Y i).oF.t r),
      IsIncl b ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧ τ ≫ (Y i).s = (Y i₂).s ≫ spMap b ∧
      ν.φ ≫ (Y i).m.φ = (Y i₂).m.φ ≫ mu.φ ∧ LevComp (Y i₂).oF (Y i).oF r ν := by
  obtain ⟨b, π', r, hb, h₁, h₂, -, h₃, h₄, h₅⟩ := h
  have e : τ ≫ (Y i).s = (Y i₂).s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y i₂).m mu h₃
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel (Y i).m n r rfl
  refine ⟨b, r, ν, hb, h₃, e, hν.trans hn, fun a => ?_, fun a => ?_⟩
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₄ a)
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₅ a)

end GlobalTheory.LocM.Cocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FrameBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem lieBasis_iff {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) (G' : Over (Sp S)) [GrpObj G']
    (φ : G'.left ⟶ t.G.left) (hp : IsGrpPullback G' t.G x φ) :
    (∀ w : (Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧
    ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ ((∀ i, IsTanAtG t x ((v i).left ≫ φ)) ∧
      ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x (fun i => (v i).left ≫ φ) a w) := by
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left,
      w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAtG t x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAtG t x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (GlobalTheory.Frames.spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

theorem tanBasis_baseChange {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sp S ⟶ X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hv' : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x v a w) :
    (∀ i, IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v i)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ x) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) a w := by
  have := t.semi.comm
  have := t.semi.smooth
  have h₁ := isGrpPullback_pullback t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := lieBasis_iff t x _ _ h₁
  obtain ⟨-, b₃⟩ := lieBasis_iff t _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv i)
  have hb : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hv'⟩
  have hs : Smooth ((Over.pullback x).obj t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
      spMap (dualMap φ) ≫ v i := fun i => by
    rw [← Category.assoc, hu', e, Category.assoc, hu]
  refine ⟨fun i => e' i ▸ key.1 i, ?_⟩
  rw [← funext e']
  exact key.2

end GlobalTheory.LocM.FrameBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem spMap_fromSpec_mem_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [Field K]
    (ψ : Γ(X, U) →+* K) (p : Γ(X, U)) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ X.basicOpen p ↔ ψ p ≠ 0 := by
  have h : spMap ψ s ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen p ↔ ψ p ≠ 0 := by
    rw [hU.fromSpec_preimage_basicOpen]
    change ψ p ∉ (show PrimeSpectrum K from s).asIdeal ↔ _
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from s).asIdeal, Ideal.mem_bot]
  exact h

theorem spMap_fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [CommRing K]
    (ψ : Γ(X, U) →+* K) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ U := by
  have h : hU.fromSpec (spMap ψ s) ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨_, rfl⟩
  exact h

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenspaceFrameLocalRingBaseChange
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_eigFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z R R' _ hR _ _ φ x f ψ
  exact GlobalTheory.ShFam.EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z R φ x f hR R' ψ
end

