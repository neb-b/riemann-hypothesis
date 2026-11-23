module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

theorem Frame.exists_of_vecMul {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (β : Matrix (Fin N) Y k) (hc : Fintype.card Y = N) (h : ∀ v, v ᵥ* β = 0 → v = 0) :
    ∃ F : GlobalTheory.LocMod.Frame k N Y, F.β = β := by
  obtain ⟨g, hg⟩ := β.vecMulLinear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 h)
  have h1 : β * LinearMap.toMatrixRight' g = 1 := by
    ext i j
    have := congrFun (LinearMap.congr_fun hg (Pi.single i 1)) j
    have h2 : ∀ x, g x = x ᵥ* LinearMap.toMatrixRight' g := fun x => by
      conv_lhs => rw [← LinearMap.toMatrixRight'.symm_apply_apply g]
      rfl
    rw [LinearMap.comp_apply, h2, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.single_one_vecMul] at this
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this
  exact ⟨⟨β, _, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hc])).1 h1⟩, rfl⟩

theorem Frame.card_eq {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) : Fintype.card Y = N := by
  have h1 := Matrix.rank_mul_le_left F.β F.γ
  have h2 := Matrix.rank_mul_le_left F.γ F.β
  rw [F.βγ, Matrix.rank_one] at h1
  rw [F.γβ, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width F.β
  have h4 := Matrix.rank_le_card_width F.γ
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem Frame.eq_zero {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) {v : Fin N → k} (h : v ᵥ* F.β = 0) : v = 0 := by
  rw [← Matrix.vecMul_one v, ← F.βγ, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

theorem hyp_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {v : Fin S.rank → k} (h1 : v ᵥ* d.e.map f = 0) (h2 : v ᵥ* d.i₀.map f = 0) (h3 : v ᵥ* d.e'.map f = 0) : v = 0 := by
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) d.sum_eq_one_rat
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h2, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem orth_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S A L : HSp D} (o : OrthDec S A L)
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    {v : Fin S.rank → k} (h1 : v ᵥ* o.iA.map f = 0) (h2 : v ⬝ᵥ (f ∘ vecB o ζ) = 0) : v = 0 := by
  have h3 : v ᵥ* o.iB.map f = 0 := by
    funext j
    have hs : Subsingleton (Fin L.rank) := by rw [hζ.1]; infer_instance
    have hj : ζ j ≠ 0 := fun h0 => hζ.2 (by
      have : ζ = 0 := funext fun i => by rw [Subsingleton.elim i j, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero])
    have h4 : f ∘ vecB o ζ = o.iB.map f *ᵥ (f ∘ ζ) := funext fun i => RingHom.map_mulVec f o.iB ζ i
    rw [h4, Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_subsingleton _ j] at h2
    exact (mul_eq_zero.1 h2).resolve_right ((map_ne_zero f).2 hj)
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) o.iA_qA_add
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem dot_eq_zero_of_smul {k : Type} [Field k] {N : ℕ} {v w : Fin N → k} {c : k} (hc : c ≠ 0)
    (h : v ⬝ᵥ (fun r => c * w r) = 0) : v ⬝ᵥ w = 0 := by
  have : v ⬝ᵥ (c • w) = 0 := h
  rw [dotProduct_smul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

namespace Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} {s : k}

theorem xi_ne_zero : p.xi ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne_zero (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 B.line.2

theorem exists_isCoreFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F, p.IsCoreFrame B s FA F := by
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul (N := B.V₀.rank) (Y := n ⊕ Unit)
    (Matrix.of fun r => Sum.elim (fun a => (B.o.iA.map p.pr * FA.β) r a) fun _ => s * p.pr (vecB B.o B.ζ r))
    (by rw [Fintype.card_sum, FA.card_eq, ← B.o.rank_add, B.line.1]; rfl) (fun v hv => by
      refine orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) (dot_eq_zero_of_smul hs ?_)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · exact congrFun hv (Sum.inr ()))
  exact ⟨F, fun r a => by rw [hF]; rfl, fun r => by rw [hF]; rfl⟩

theorem exists_isJacFrame (hs : s ≠ 0) (J : JacLev D ρ) {hh : k} (hh0 : hh ≠ 0) (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin J.W.rank) (n ⊕ Fin (2 * ρ)) k :=
    Matrix.of fun r => Sum.elim (fun a => (J.d.i₀.map p.pr * F₀.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (J.d.e r ⟨j.val, h⟩)
      else s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) * p.pr (J.d.e' r ⟨2 * ρ - 1 - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i + 1 = 2 * ρ) r
    obtain rfl : i = 2 * ρ - 1 - j := by omega
    exact dif_neg (show ¬ j < ρ by omega)
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, F₀.card_eq, ← J.d.rank_add, Fintype.card_fin]) (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) J.d ?_ (F₀.eq_zero ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero hh0 hx)) (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b2⟩

theorem exists_isBesFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin B.V.rank) (n ⊕ Fin (2 * ρ + 1)) k :=
    Matrix.of fun r => Sum.elim (fun a => ((B.d.i₀ * B.o.iA).map p.pr * FA.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (B.d.e r ⟨j.val, h⟩)
      else if h' : j.val = ρ then s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)
      else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - j.val)) * p.pr (B.d.e' r ⟨2 * ρ - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b0 : ∀ j : Fin (2 * ρ + 1), j.val = ρ → ∀ r, β r (Sum.inr j) = s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) := by
    rintro ⟨j, hj⟩ (h : j = ρ) r
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_pos h)
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i.val = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i = 2 * ρ) r
    obtain rfl : i = 2 * ρ - j := by omega
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_neg (show ¬ j = ρ by omega))
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, FA.card_eq, ← B.d.rank_add, ← B.o.rank_add, B.line.1, Fintype.card_fin]; omega)
    (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) B.d ?_
        (orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.map_mul]
        funext a; exact congrFun hv (Sum.inl a)
      · have := congrFun hv (Sum.inr ⟨ρ, by omega⟩)
        rw [← Matrix.dotProduct_mulVec]
        refine dot_eq_zero_of_smul hs ?_
        refine Eq.trans ?_ this
        refine congrArg (v ⬝ᵥ ·) (funext fun r => ((b0 _ rfl r).trans ?_).symm)
        exact congrArg (s * ·) (RingHom.map_mulVec (p.π.comp (incA D)) _ _ r)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero (neg_ne_zero.2 (p.hz_ne_zero B)) hx))
            (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b0, by rw [hF]; exact b2⟩

end Place

theorem normalFrames_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F :=
  fun _ _ _ _ _ _ p _ _ _ _ _ hs =>
    ⟨fun B FA => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA, p.hz_ne_zero B⟩,
      fun J _ hh0 F₀ => p.exists_isJacFrame hs J hh0 F₀⟩

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinear
section
namespace I195MixedCoordinates_f836602dbb4c79f519e0538a

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_f836602dbb4c79f519e0538a

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatLin

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.source d) T ψ v.μ v.𝓕 (f + g) x = (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.source d) T ψ v.μ v.𝓕 f x + (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.source d) T ψ v.μ v.𝓕 g x := by
  funext w
  have h := integral_add (d.integrableOn_mixS hψ.1.1 v.covol hf x w) (d.integrableOn_mixS hψ.1.1 v.covol hg x w)
  change (∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) (f + g))) 0 ∂v.μ) =
    (∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 ∂v.μ) +
    (∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) g)) 0 ∂v.μ)
  simp_rw [d.integrandS_eq, Pi.add_apply, mul_add]
  simp_rw [d.integrandS_eq] at h
  exact h

theorem cont_bdd_of_tame {Z : Type} [TopologicalSpace Z] {F : Z → ℂ}
    (t : GlobalTheory.Unf.EvalCont.Tame fun (_ : Unit) (q : Unit × Z) => F q.2) : Continuous F ∧ ∃ C : ℝ, ∀ w, ‖F w‖ ≤ C := by
  refine ⟨t.1.comp ((continuous_const (y := ())).prodMk ((continuous_const (y := ())).prodMk continuous_id)), ?_⟩
  obtain ⟨C', hC'⟩ := t.2 ()
  exact ⟨C', fun w => hC'.self_of_nhds ((), w)⟩

theorem mixS_cont_bdd (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) :
    Continuous ((_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.source d) T ψ v.μ v.𝓕 f x) ∧ ∃ C : ℝ, ∀ w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ ≤ C := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ f hf
  have t := GlobalTheory.Unf.EvalCont.tame_mixS (B := Unit) (Z := Unit) hψ d v x (F := fun _ _ => f)
    (GlobalTheory.Unf.EvalCont.tame_of_bounded (C := C) (hf.cont.comp continuous_snd.snd) fun _ q => hC q.2)
  exact cont_bdd_of_tame t

theorem integrableOn_mixT (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank)
    {f : WO S T → ℂ} (hf : Continuous f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (y : Mx D S.rank ρ) (w₀ : WO S T₀) :
    IntegrableOn (fun ξ => ψ (symplOH S T (d.incX S ξ) (d.incAdj S y)) * f (d.incX S ξ + d.incAdj S y + d.inc0 S w₀))
      v.𝓕 v.μ := by
  obtain ⟨hc, C, hC⟩ := hf
  obtain ⟨j1, -⟩ := lattice_Mx D T.rank S.rank
  have : BorelSpace (Mx D ρ S.rank) := ⟨rfl⟩
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, v.covol.2.2]; exact ENNReal.one_lt_top⟩
  have hY : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) C (.of_forall fun ξ => ?_)
  · exact (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH hY continuous_const)).mul
      (hc.comp ((hY.add continuous_const).add continuous_const))
  · rw [norm_mul, hψ.1.2.1, one_mul]; exact hC _

theorem mixT_add (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank)
    {f g : WO S T → ℂ} (hf : Continuous f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (hg : Continuous g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C)
    (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.target d) S ψ v.μ v.𝓕 (f + g) y = (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.target d) S ψ v.μ v.𝓕 f y + (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.target d) S ψ v.μ v.𝓕 g y := by
  funext w
  have h := integral_add (integrableOn_mixT hψ d v hf y w) (integrableOn_mixT hψ d v hg y w)
  change (∫ ξ in v.𝓕, heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) (f + g))) 0 ∂v.μ) =
    (∫ ξ in v.𝓕, heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) f)) 0 ∂v.μ) +
    (∫ ξ in v.𝓕, heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) g)) 0 ∂v.μ)
  simp_rw [d.integrandT_eq, Pi.add_apply, mul_add]
  exact h

theorem evalAt_add (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hg : IsThetaFunO ψ V W g) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) :
    GlobalTheory.MixPer.evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (f + g) x y =
      GlobalTheory.MixPer.evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 f x y + GlobalTheory.MixPer.evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 g x y := by
  unfold GlobalTheory.MixPer.evalAt
  change (_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.target dW) V₀ ψ vT.μ vT.𝓕 ((_root_.I195MixedCoordinates_f836602dbb4c79f519e0538a.source dV) W ψ vS.μ vS.𝓕 (f + g) x) y = _
  rw [mixS_add hψ dV vS hf hg, mixT_add hψ dW vT (mixS_cont_bdd hψ dV vS hf x) (mixS_cont_bdd hψ dV vS hg x)]

theorem flatAt_add (hF : FlatLaw D) (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ)
    (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : LinearIndependent D.host.E x.transpose) (y : Mx D V₀.rank σ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) :
    GlobalTheory.MixPer.flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y (f + g) =
      GlobalTheory.MixPer.flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y f +
        GlobalTheory.MixPer.flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y g := by
  funext w
  have h := integral_add ((hF ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y f hf).1 w)
    ((hF ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y g hg).1 w)
  rw [Pi.add_apply, GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatAt, ← h]
  congr 1
  funext u
  simp only [GlobalTheory.MixPer.flatFun, evalAt_add hψ dV dW vS vT hf hg, Pi.add_apply, mul_add]

theorem flatBF_linear : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (f g : WO B.V J.W → ℂ) (a : ℂ), IsThetaFunO ψ B.V J.W f → IsThetaFunO ψ B.V J.W g → flatBF st (f + g) = flatBF st f + flatBF st g ∧ flatBF st (a • f) = a • flatBF st f := by
  intro D hF ψ ρ B J st f g a hf hg
  exact ⟨flatAt_add hF st.weil.std B.d J.d st.vS st.vT st.vU J.d.e (isIsoSub_e J.d).1 _ hf hg,
    GlobalTheory.HandHom.flatBF_smul st a f⟩

end GlobalTheory.FlatLin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselWittDecomposition
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel Filter Topology
open GlobalTheory.LocMod GlobalTheory.LocMod.Witness
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatFBCompare

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem val_lt_one_iff (x : K) : valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ (not_lt.1 hx)
  exact absurd hn (not_lt.2 h2)

end Val

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  [Fintype Z'] [DecidableEq Z'] {S T : HSp D}

section Scal

variable {K : Type} [Field K] {γ t : Kˣ} {s : K} {σ : ℕ}

end Scal

section Frames

variable {q : GlobalTheory.FinPl.SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {σ : ℕ}
  {γ t : kˣ} {s : k} (hγ : (γ : k) = (Place.ofSplitPt q).xi) (ht : (t : k) = s * γ ^ (σ + 1))
include hγ ht

end Frames

section Local

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

variable [MeasurableSpace k] [BorelSpace k] {c : ℕ}

end Local

section Change

variable {q : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {σ : ℕ} {γ γ' t : kˣ}

end Change

section Rename₂

variable {n m A B : Type} [Fintype n] [DecidableEq n] [Unique A] [Unique B] (a : k)

end Rename₂

end GlobalTheory.FlatFBCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BrkSumRepsOrth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem brk_sum_reps_orth : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SB : Finset V, Formalism.L2.Th1.H.IsReps Λ B SB → ∀ w ∈ Λ ⊓ A, ∑ y ∈ SB, brk H y w = if w ∈ B then (SB.card : ℂ) else 0 := by
  intro V _ _ H α A B Λ hyp SB hSB w hw
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, -⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hwΛ : w ∈ Λ := (AddSubgroup.mem_inf.1 hw).1
  by_cases hwB : w ∈ B
  · rw [if_pos hwB, Finset.sum_congr rfl fun y hy => brk_one_of_int H (hBint hwB y (hSB.1 y hy))]
    simp
  · rw [if_neg hwB]
    have hnd : w ∉ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hwB
    have hex : ∃ y₀ ∈ B, ¬ ∃ m : ℤ, Formalism.L2.Th1.H.altE H w y₀ = (m : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hnd (fun y hy => hcon y hy)
    obtain ⟨y₀, hy₀B, hy₀⟩ := hex
    exact char_sum_zero hSB (fun y => brk H y w) (fun u v => brk_add_left H u v w)
      (fun m _ hmΛ => brk_one_of_int H (hΛint hwΛ m hmΛ)) (x₀ := y₀) hy₀B
      (fun h => hy₀ (int_of_brk_one H h))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CntOnSingleton
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem cntOn_singleton : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ c : ℝ, CntOn {c} := by
  intro hM c Cg cb Cu cT CT
  obtain ⟨C1a, hC1⟩ := GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT c 1 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT c 1
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT c 1
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT c 1
  refine ⟨c3, cH, cS, c4, 1, fun C0 hC0 C' Cl _ hl D large₂ u => ?_⟩
  rw [Set.mem_singleton_iff] at hC0
  subst hC0
  refine ⟨fun C hC => ?_, ?_, ?_, ?_⟩
  · exact hC3 C hC _ _ u u _ _ hl (GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u _ _ Cg cb Cu cT CT C0 1 hl)
  · exact hHH _ _ u u _ _ hl
  · exact hSW _ _ u u _ _ hl
      (GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u _ _ Cg cb Cu cT CT C0 1 (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u _ _ hl

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatioStatement
section
theorem GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover :=
  GlobalTheory.CoverDS.discreteSeriesCover_of_classification
end

