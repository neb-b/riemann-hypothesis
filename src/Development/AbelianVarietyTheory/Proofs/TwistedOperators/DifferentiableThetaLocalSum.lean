module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

noncomputable section

namespace GlobalTheory.RatMoveFock

section SlopeTestRemainingChoices

open Matrix

variable {D : D7}

private theorem mem_globLat_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (A : Matrix (Fin n) (Fin n) E)
    (hg : g.val = A.map (Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))) (Λ : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E) : A *ᵥ y ∈ Formalism.UG.CS.globLat (g * h) Λ ↔ y ∈ Formalism.UG.CS.globLat h Λ := by
  have e : (fun i => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((A *ᵥ y) i)) =
      g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (y i) := by
    funext i
    rw [hg]
    exact RingHom.map_mulVec _ _ _ i
  unfold Formalism.UG.CS.globLat
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [e, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

private theorem latAt_rat {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E)
    (h : RatCoord (G.V X) (S.N.fr X) r U) (x : FinPt G X) :
    GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  obtain ⟨γ, -, h2, h3⟩ := h
  have hg : (finG (G.V X) r).val = ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL _ _).1).map
      (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    have e : (finG (G.V X) r).val = (Formalism.L2.Theta.mt (G.V X) γ).map (toEAf D) :=
      Matrix.ext fun i j => congrArg (fun x : GL (Fin (G.V X).rank) _ =>
        Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (x.1 i j)) h2.symm
    rw [e, h3]
    rfl
  have key : ∀ y, U.1 *ᵥ y ∈ GlobalTheory.SumSize.latAt S X (r * x) ↔ y ∈ GlobalTheory.SumSize.latAt S X x := fun y => by
    unfold GlobalTheory.SumSize.latAt
    rw [Submodule.mem_comap, Submodule.mem_comap, map_mul, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    have e : (S.N.fr X).1 *ᵥ (U.1 *ᵥ y) =
        ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL _ _).1) *ᵥ ((S.N.fr X).1 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (S.N.fr X).1, Units.inv_mul, Matrix.mul_one]
    rw [e]
    exact mem_globLat_mul _ _ _ hg (G.Λ X) _
  ext z
  constructor
  · intro hz
    have e : U.1 *ᵥ (star U.1 *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]
    exact ⟨_, (key _).1 (e.symm ▸ hz), e⟩
  · rintro ⟨y, hy, rfl⟩
    exact (key y).2 hy

private def NormOne {F : Type} [NormedField F] (lam : Qbar →+* F) (x : ℂ) : Prop := ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ = 1

section
variable {F : Type} [NormedField F] {lam : Qbar →+* F}

private theorem NormOne.one : NormOne lam 1 := ⟨one_mem _, by rw [show (⟨1, one_mem _⟩ : Qbar) = 1 from rfl, map_one, norm_one]⟩

private theorem NormOne.mul {x y : ℂ} (hx : NormOne lam x) (hy : NormOne lam y) : NormOne lam (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  refine ⟨mul_mem h1 h3, ?_⟩
  rw [show (⟨x * y, mul_mem h1 h3⟩ : Qbar) = ⟨x, h1⟩ * ⟨y, h3⟩ from rfl, map_mul, norm_mul, h2, h4, one_mul]

private theorem NormOne.pow {x : ℂ} (hx : NormOne lam x) (n : ℕ) : NormOne lam (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact NormOne.one
  | succ n ih => rw [pow_succ]; exact ih.mul hx

private theorem NormOne.prod {ι : Type} [Fintype ι] (f : ι → ℂ) (h : ∀ i, NormOne lam (f i)) : NormOne lam (∏ i, f i) :=
  Finset.prod_induction f (NormOne lam) (fun _ _ => NormOne.mul) NormOne.one fun i _ => h i

private theorem NormOne.of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (hx : NormOne lam (x ^ n)) : NormOne lam x := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : x ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h1))
  refine ⟨h3, ?_⟩
  rw [show (⟨x ^ n, h1⟩ : Qbar) = ⟨x, h3⟩ ^ n from rfl, map_pow, norm_pow] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

private theorem normOne_emb (lam : Qbar →+* F) {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) (a : E)
    (h : ∀ φ : E →+* F, ‖φ a‖ = 1) : NormOne lam (τ a) := by
  have hm : ∀ b : E, τ b ∈ Qbar := fun b =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) b).algHom τ.toRatAlgHom)
  exact ⟨hm a, h (lam.comp (τ.codRestrict Qbar hm))⟩

end

private theorem mem_smulLat {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (y : Fin N → D.host.E) : y ∈ SDLat.smulLat γ L ↔ ∃ x ∈ L, γ.mulVec x = y := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  rfl

private theorem norm_natCast_coprime {p : ℕ} [Fact p.Prime] {n : ℕ} (h : Nat.Coprime n p) : ‖(n : ℂ_[p])‖ = 1 := by
  have e : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p]) := (map_natCast _ n).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

private theorem det_mul_star {N : ℕ} (U : Matrix.unitaryGroup (Fin N) D.host.E) : U.1.det * (star U.1).det = 1 := by
  rw [← Matrix.det_mul, U.2.2, Matrix.det_one]

private theorem norm_det_complex {N : ℕ} (U : Matrix.unitaryGroup (Fin N) D.host.E) (φ : D.host.E →+* ℂ) : ‖φ U.1.det‖ = 1 := by
  have hs : φ (star U.1.det) = starRingEnd ℂ (φ U.1.det) := by
    have := D.host.isCMField_hostE
    exact IsCMField.complexEmbedding_complexConj D.host.E φ _
  have h := congrArg (fun a => ‖φ a‖) (det_mul_star U)
  rw [star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  simp only [map_mul, norm_mul, hs, Complex.norm_conj, map_one, norm_one] at h
  exact (mul_self_eq_one_iff.1 h).resolve_right fun e => by linarith [norm_nonneg (φ U.1.det)]

private theorem norm_det_le {N q : ℕ} [Fact q.Prime] (A : Matrix (Fin N) (Fin N) D.host.E) {s : ℕ} (hs : s.Coprime q)
    (h : ∀ x ∈ stdL D N, ((s : D.host.E) • A) *ᵥ x ∈ stdL D N) (φ : D.host.E →+* ℂ_[q]) : ‖φ A.det‖ ≤ 1 := by
  have h1 : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap _ D.host.E b = ((s : D.host.E) • A) i j := fun i j => by
    have h2 := h (Pi.single j 1) (fun k _ => by
      by_cases e : k = j
      · subst e; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]; exact zero_mem _) i (Set.mem_univ _)
    rw [Matrix.mulVec_single_one] at h2
    exact Submodule.mem_one.1 h2
  choose B hB using h1
  have e : algebraMap _ D.host.E (Matrix.of B).det = (s : D.host.E) ^ N * A.det := by
    rw [RingHom.map_det, show (algebraMap _ D.host.E).mapMatrix (Matrix.of B) = (s : D.host.E) • A from
      Matrix.ext hB, Matrix.det_smul, Fintype.card_fin]
  have h3 := GlobalTheory.Proof.IdempotentLatticeSequence.norm_int_le φ (Matrix.of B).det
  change ‖φ (algebraMap _ D.host.E _)‖ ≤ 1 at h3
  rwa [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_natCast_coprime hs, one_pow, one_mul] at h3

private theorem norm_det_padic {N q : ℕ} [Fact q.Prime] (U : Matrix.unitaryGroup (Fin N) D.host.E)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h1 : EqAt D q M (stdL D N))
    (h2 : EqAt D q (SDLat.smulLat U.1 M) (stdL D N)) (φ : D.host.E →+* ℂ_[q]) : ‖φ U.1.det‖ = 1 := by
  obtain ⟨s, hs, a1, a2⟩ := h1
  obtain ⟨t, ht, b1, b2⟩ := h2
  have c1 := norm_det_le U.1 (Nat.Coprime.mul_left ht hs) (fun x hx => by
    have := b1 _ ((mem_smulLat _ _ _).2 ⟨_, a2 x hx, rfl⟩)
    rwa [Matrix.mulVec_smul, smul_smul, ← Nat.cast_mul, ← Matrix.smul_mulVec] at this) φ
  have c2 := norm_det_le (star U.1) (Nat.Coprime.mul_left hs ht) (fun x hx => by
    obtain ⟨y, hy, e⟩ := (mem_smulLat _ _ _).1 (b2 x hx)
    have e2 : y = (t : D.host.E) • (star U.1 *ᵥ x) := by
      rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, U.2.1, Matrix.one_mulVec]
    have := a1 y hy
    rwa [e2, smul_smul, ← Nat.cast_mul, ← Matrix.smul_mulVec] at this) φ
  have h := congrArg (fun a => ‖φ a‖) (det_mul_star U)
  simp only [map_mul, norm_mul, map_one, norm_one] at h
  nlinarith [norm_nonneg (φ U.1.det), norm_nonneg (φ (star U.1).det)]

end SlopeTestRemainingChoices

open Matrix GlobalTheory.AdForm.RatMove
open scoped ComplexOrder

variable {D : D7}

private theorem detPlus_def {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} (hs : s = 1 ∨ s = -1) :
    ∃ e : ℕ, ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ),
      GlobalTheory.WeilParts.detPlus s 1 a b = (b.det ^ n * a.det ^ m) ^ e := by
  rcases hs with rfl | rfl
  · refine ⟨1, fun a b => ?_⟩
    unfold GlobalTheory.WeilParts.detPlus
    rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, add_mul, one_mul, ← two_smul ℂ,
      smul_smul, Matrix.det_smul, Matrix.det_kronecker]
    simp
  · refine ⟨0, fun a b => ?_⟩
    unfold GlobalTheory.WeilParts.detPlus
    have e : Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2) (1 : Matrix (Fin m) (Fin m) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
      rw [← Matrix.one_kronecker_one, Matrix.transpose_neg, Matrix.transpose_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, mul_neg]
    rw [e, add_neg_cancel, zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    simp

private theorem sq_exp {θ : InfFam D} (hθ : IsInfFam θ) {χ η : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h1 : IsHeckeChar D χ)
    (h2 : ResEta D χ n) (hη : ∀ τ, HasInfExp D η τ (1 / 2)) (k : ℕ) :
    ∃ c : D.what₂.Tau → ℤ, ∀ τ, HasInfExp D ((χ * (η ^ k)⁻¹) * (χ * (η ^ k)⁻¹)) τ (c τ) := by
  have key : ∀ τ, ∃ c : ℤ, HasInfExp D ((χ * (η ^ k)⁻¹) * (χ * (η ^ k)⁻¹)) τ c := fun τ => by
    obtain ⟨a, ha⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ h1 h2
    have hb := GlobalTheory.VacuumCharacter.hasInfExp_twist ha (hη τ) k
    obtain ⟨c, hc, -⟩ := id hb
    refine ⟨c, ?_⟩
    rw [hc, two_mul]
    exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul hb hb
  exact ⟨_, fun τ => (key τ).choose_spec⟩

private theorem NormOne.inv' {F : Type} [NormedField F] {lam : Qbar →+* F} {x : ℂ} (hx : NormOne lam x) : NormOne lam x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨inv_mem h1, ?_⟩
  rw [show (⟨x⁻¹, inv_mem h1⟩ : Qbar) = (⟨x, h1⟩ : Qbar)⁻¹ from rfl, map_inv₀, norm_inv, h2, inv_one]

private theorem NormOne.zpow' {F : Type} [NormedField F] {lam : Qbar →+* F} {x : ℂ} (hx : NormOne lam x) (n : ℤ) :
    NormOne lam (x ^ n) := by
  cases n with
  | ofNat n => simpa using hx.pow n
  | negSucc n => rw [zpow_negSucc]; exact NormOne.inv' (hx.pow _)

private theorem vac_scalar {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : s = 1 ∨ s = -1)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) s) (hT : ∀ τ, IsCartanInv (gramAt D T τ) 1)
    {g : Formalism.L2.Theta.GA D S} (hg : g ∈ GinfC S) {h : Formalism.L2.Theta.GA D T} (hh : h ∈ GinfC T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO s 1) f) :
    ∃ c : ℂ, om (g, h) f = c • f ∧ ∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
      (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt S g)).det) → (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt T h)).det) →
        NormOne lam c := by
  obtain ⟨η, e1, e2, e3, e4⟩ := _root_.GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S (fun τ => hdet (hS τ)) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ T (fun τ => hdet (hT τ)) h hh
  obtain ⟨e, he⟩ := detPlus_def (m := T.rank) hs
  obtain ⟨a, ha⟩ := sq_exp hθ hW.hecT hW.resT e2 T.rank
  obtain ⟨b, hb⟩ := sq_exp hθ hW.hecS hW.resS e2 S.rank
  refine ⟨_, _root_.GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => s) (fun _ => 1) hS hT g hg h hh
    (fun τ => by rcases hs with rfl | rfl <;> simp) (fun τ => by rw [one_mul, mul_one]) x y hx hy f hf hv,
    fun F _ lam h1 h2 => ?_⟩
  have inv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)).det = ((compAt θ τ (Formalism.L2.Theta.mt S g)).det)⁻¹ := fun τ => by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have k1 := hxv _ a ha
  have k2 := hyv _ b hb
  rw [MonoidHom.mul_apply, Circle.coe_mul, ← pow_two] at k1 k2
  rw [Circle.coe_mul, Circle.coe_inv]
  refine NormOne.mul (NormOne.mul (NormOne.inv' (NormOne.of_pow two_pos ?_)) (NormOne.of_pow two_pos ?_))
    (NormOne.prod _ fun τ => ?_)
  · rw [k1]; exact NormOne.prod _ fun τ => NormOne.zpow' (h1 τ) _
  · rw [k2]; exact NormOne.prod _ fun τ => NormOne.zpow' (h2 τ) _
  · rw [he, inv]
    exact (((h2 τ).pow _).mul ((NormOne.inv' (h1 τ)).pow _)).pow _

private theorem mt_mul_inv (V : HSp D) (g : Formalism.L2.Theta.GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

private theorem om_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {γ : Formalism.L2.Theta.GA D S} (hγ : γ ∈ GQ S) {γ' : Formalism.L2.Theta.GA D T} (hγ' : γ' ∈ GQ T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)) :
    om (γ, γ') f w = f (Formalism.L2.Theta.mt T γ'⁻¹ * w * Formalism.L2.Theta.mt S γ : Matrix _ _ _) := by
  have hrat : ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w := fun w => by
    have h1 := hW.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf w)
    rw [hW.om_heis _ _ _ _ hf] at h1
    simpa [heisO, symplOH, symplO, hO] using h1
  rw [← hrat]
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

private theorem move_fin {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : s = 1 ∨ s = -1)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) s) (hT : ∀ τ, IsCartanInv (gramAt D T τ) 1)
    {γ r g : Formalism.L2.Theta.GA D S} (hγ : γ ∈ GQ S) (hr : infHom S r = 1) (hγr : finHom S γ = finHom S r)
    {γ' r' h : Formalism.L2.Theta.GA D T} (hγ' : γ' ∈ GQ T) (hr' : infHom T r' = 1) (hγr' : finHom T γ' = finHom T r')
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T (om (g, h) f)) (hf' : IsThetaFunO ψ S T (om (r * g, r' * h) f))
    (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO s 1) (om (r * g, r' * h) f)) :
    ∃ c : ℂ, (∀ w : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D),
      c * om (r * g, r' * h) f w = om (g, h) f (Formalism.L2.Theta.mt T γ'⁻¹ * w * Formalism.L2.Theta.mt S γ : Matrix _ _ _)) ∧
      ∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
      (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt S γ)).det) → (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt T γ')).det) →
        NormOne lam c := by
  have key : ∀ (V : HSp D) (γ r : Formalism.L2.Theta.GA D V), infHom V r = 1 → finHom V γ = finHom V r →
      γ * r⁻¹ ∈ GinfC V ∧ ∀ τ, compAt θ τ (Formalism.L2.Theta.mt V (γ * r⁻¹)) = compAt θ τ (Formalism.L2.Theta.mt V γ) := by
    intro V γ r h1 h2
    refine ⟨?_, fun τ => ?_⟩
    · change finHom V _ = 1
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    · have h3 : infHom V (γ * r⁻¹) = infHom V γ := by rw [map_mul, map_inv, h1, inv_one, mul_one]
      exact congrArg (fun x : GL (Fin V.rank) _ => x.1.map (θ τ)) h3
  obtain ⟨a1, a2⟩ := key S γ r hr hγr
  obtain ⟨b1, b2⟩ := key T γ' r' hr' hγr'
  obtain ⟨c, hc, hn⟩ := vac_scalar hθ hW hs hS hT a1 b1 hf' hv
  simp only [a2, b2] at hn
  refine ⟨c, fun w => ?_, hn⟩
  rw [← om_rat hW hγ hγ' hf]
  have e : om (γ, γ') (om (g, h) f) = om (γ * r⁻¹, γ' * r'⁻¹) (om (r * g, r' * h) f) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_assoc, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_left]
  rw [e, hc]
  rfl

private theorem jets_scale {N N' : ℕ} (δ a : ℂ) {Θ : VC D N N' → ℂ} (hΘ : Differentiable ℂ Θ) (k : FVar D N' N →₀ ℕ) :
    a * ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ) =
      ((((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ k.sum fun _ n => n) *
        Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => a * Θ (δ • z) := by
  have hd : Differentiable ℂ fun z : VC D N N' => Θ (δ • z) := hΘ.comp (differentiable_id.const_smul δ)
  rw [GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
    GlobalTheory.FockPos.taylor_comp_smul' D _ hΘ]
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
      δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
    intro τ
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
      (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, mul_pow]
  ring

private theorem sum_norm_sq {m n : ℕ} (y : Matrix (Fin m) (Fin n) ℂ) : ∑ i, ∑ j, ((‖y i j‖ ^ 2 : ℝ) : ℂ) = (y * yᴴ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj']

private theorem sum_norm_sq_unitary {m n : ℕ} (y : Matrix (Fin m) (Fin n) ℂ) {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) :
    ∑ i, ∑ j, ((‖(Bᴴ * y * A) i j‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ((‖y i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [sum_norm_sq, sum_norm_sq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc A, hA, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ B,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.one_mul]

private theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ = (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) ∧
    (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) * GlobalTheory.FockPos.frAt fr τ = 1 ∧
    GlobalTheory.FockPos.frAt fr τ * (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) = 1 := by
  have h1 : (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) * GlobalTheory.FockPos.frAt fr τ = 1 := by
    unfold GlobalTheory.FockPos.frAt
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨Matrix.inv_eq_left_inv h1, h1, mul_eq_one_comm.1 h1⟩

private theorem jets_subst {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    {LS LS' : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)} {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f) (hf' : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS' LT' f')
    (U : Matrix.unitaryGroup (Fin S.rank) D.host.E) (U' : Matrix.unitaryGroup (Fin T.rank) D.host.E) {c : ℂ} (hc : c ≠ 0)
    {MT : Matrix (Fin T.rank) (Fin T.rank) (Formalism.L2.Theta.AE D)} {MS : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)}
    (hMT : MT = (frT.1 * star U'.1 * (frT⁻¹ : GL _ _).1).map (incA D)) (hMS : MS = (frS.1 * U.1 * (frS⁻¹ : GL _ _).1).map (incA D))
    (hsub : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D), c * f' w = f (MT * w * MS : Matrix _ _ _))
    (cc : Ideal (𝓞 D.host.K)) (δ a : ℂ) {Θ : VC D S.rank T.rank → ℂ} (hΘ : Differentiable ℂ Θ)
    (hj : ∀ k : FVar D T.rank S.rank →₀ ℕ,
      pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f (MvPolynomial.monomial k 1) 0 =
        a * ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ))
    (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f' (MvPolynomial.monomial k 1) 0 =
      a * ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
        fun z => c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z)) := by
  have hθ := hf.2.inf
  obtain ⟨Φ, hΦ, hr⟩ := _root_.GlobalTheory.FockPos.vacuum_real_entire ψ θ S T frS frT _ _ hS hT f hf
  obtain ⟨Φ', hΦ', hr'⟩ := _root_.GlobalTheory.FockPos.vacuum_real_entire ψ θ S T frS frT _ _ hS hT f' hf'
  have hs : (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ≠ 0 := by
    have hx : 0 < Formalism.L2.Pj.xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (mul_pos Real.two_pi_pos hx)).ne')
  have e1 : Φ = fun z => a * Θ (δ • z) := by
    refine GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq _ _ hΦ
      ((hΘ.comp (differentiable_id.const_smul δ)).const_mul a) fun k => ?_
    have h1 := _root_.GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T frS frT hf.1 hθ hS hT f Φ hΦ hr k
    rw [hj, jets_scale δ a hΘ] at h1
    exact (mul_left_cancel₀ (pow_ne_zero _ hs) h1).symm
  have hd : Differentiable ℂ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1) :=
    (LinearMap.toContinuousLinearMap (IsLinearMap.mk' (R := ℂ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1)
      ⟨fun x y => funext fun τ => by
        change ((U'.1.map (tauE D τ))ᴴ * (Matrix.of (x τ) + Matrix.of (y τ)) * U.1.map (tauE D τ) : Matrix _ _ ℂ) =
          (U'.1.map (tauE D τ))ᴴ * Matrix.of (x τ) * U.1.map (tauE D τ) + (U'.1.map (tauE D τ))ᴴ * Matrix.of (y τ) * U.1.map (tauE D τ)
        rw [Matrix.mul_add, Matrix.add_mul],
      fun c x => funext fun τ => by
        change ((U'.1.map (tauE D τ))ᴴ * (c • Matrix.of (x τ)) * U.1.map (tauE D τ) : Matrix _ _ ℂ) =
          c • ((U'.1.map (tauE D τ))ᴴ * Matrix.of (x τ) * U.1.map (tauE D τ))
        rw [Matrix.mul_smul, Matrix.smul_mul]⟩)).differentiable
  have e2 : Φ' = fun z => a * (c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 (δ • z))) := by
    funext z
    obtain ⟨s1, s2⟩ := realPt_spec hθ fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹
    generalize GlobalTheory.AdForm.realPt θ _ = w at s1 s2
    have z1 : GlobalTheory.FockPos.zCo θ frS frT w = z := by
      funext τ
      change (GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ w * GlobalTheory.FockPos.frAt frS τ = Matrix.of (z τ)
      rw [s2, (frAt_inv frT τ).1, (frAt_inv frS τ).1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (frAt_inv frT τ).2.1,
        Matrix.one_mul, Matrix.mul_assoc, (frAt_inv frS τ).2.1, Matrix.mul_one]
    have h0 := hsub w
    obtain ⟨w₁, hw₁⟩ : ∃ w₁ : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D),
        w₁ = HMul.hMul (HMul.hMul MT w : Mx D T.rank S.rank) MS := ⟨_, rfl⟩
    rw [← hw₁] at h0
    have t1 : w₁.map (finPart D) = 0 := by
      rw [hw₁, Matrix.map_mul, Matrix.map_mul, s1, Matrix.mul_zero, Matrix.zero_mul]
    have z2 : ∀ τ, GlobalTheory.FockPos.zCo θ frS frT w₁ τ =
        ((U'.1.map (tauE D τ))ᴴ * Matrix.of (z τ) * U.1.map (tauE D τ) : Matrix _ _ ℂ) := fun τ => by
      change (GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ w₁ * GlobalTheory.FockPos.frAt frS τ = _
      have a1 : (star U'.1).map (tauE D τ) = (U'.1.map (tauE D τ))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.tauE_star τ _
      rw [hw₁, compAt_mul, compAt_mul, s2, hMT, hMS, compAt_rat hθ, compAt_rat hθ, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
        Matrix.map_mul, a1, (frAt_inv frT τ).1, (frAt_inv frS τ).1]
      have b1 := (frAt_inv frT τ).2.1
      have b2 := (frAt_inv frS τ).2.1
      change _ * (GlobalTheory.FockPos.frAt frT τ * _ * _ * _ * (GlobalTheory.FockPos.frAt frS τ * _ * _)) * _ = _
      simp only [Matrix.mul_assoc]
      rw [b2, Matrix.mul_one, ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frS τ), b2, Matrix.one_mul,
        ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frT τ), b1, Matrix.one_mul,
        ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frT τ), b1, Matrix.one_mul]
    have z3 : GlobalTheory.FockPos.zCo θ frS frT w₁ = Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z := funext z2
    have g1 : GlobalTheory.FockPos.gaussO θ frS frT w₁ = GlobalTheory.FockPos.gaussO θ frS frT w := by
      unfold GlobalTheory.FockPos.gaussO
      rw [z1]
      congr 2
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [z2]
      exact sum_norm_sq_unitary (Matrix.of (z τ)) (map_unitary τ U) (map_unitary τ U')
    have g0 : GlobalTheory.FockPos.gaussO θ frS frT w ≠ 0 := Complex.exp_ne_zero _
    rw [hr w₁ t1, hr' w s1, g1, z1, z3, e1] at h0
    beta_reduce at h0
    rw [Formalism.L2.KerInert.PullbackComparison.tPull_smul]
    refine mul_left_cancel₀ (mul_ne_zero hc g0) ?_
    rw [mul_assoc, h0]
    field_simp
  have hd2 : Differentiable ℂ fun z => c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z) := (hΘ.comp hd).const_mul _
  rw [jets_scale δ a hd2, _root_.GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T frS frT hf.1 hθ hS hT f' Φ' hΦ' hr' k, e2]

private theorem coord_data {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {fr : GL (Fin V.rank) D.host.E} {r : GfC V}
    {U : Matrix.unitaryGroup (Fin V.rank) D.host.E} (h : RatCoord V fr r U) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V (r : Formalism.L2.Theta.GA D V) ∧
      Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL _ _).1).map (incA D) ∧
      Formalism.L2.Theta.mt V γ⁻¹ = (fr.1 * star U.1 * (fr⁻¹ : GL _ _).1).map (incA D) ∧
      ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V γ)).det = tauE D τ U.1.det := by
  obtain ⟨γ, h1, h2, h3⟩ := h
  refine ⟨γ, h1, h2, h3, ?_, fun τ => ?_⟩
  · have : Formalism.L2.Theta.mt V γ⁻¹ = ((matHom V γ)⁻¹).1 := congrArg Units.val (map_inv (matHom V) γ)
    rw [this]
    refine Units.inv_eq_of_mul_eq_one_left ?_
    change _ * Formalism.L2.Theta.mt V γ = 1
    rw [h3, ← Matrix.map_mul, Matrix.mul_assoc fr.1 U.1, Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_assoc,
      ← Matrix.mul_assoc (star U.1), U.2.1, Matrix.one_mul, Units.mul_inv,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  · rw [h3, compAt_rat hθ]
    refine (RingHom.map_det (tauE D τ) _).symm.trans (congrArg _ ?_)
    rw [Matrix.det_mul_right_comm, Units.mul_inv, Matrix.one_mul]

private theorem arith {N N' : ℕ} (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E) {c : ℂ}
    (h : ∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
      (∀ τ, NormOne lam (tauE D τ U.1.det)) → (∀ τ, NormOne lam (tauE D τ U'.1.det)) → NormOne lam c) :
    Mod1All c ∧ ‖c‖ = 1 ∧ ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q c := by
  have hc : ∀ σ : Qbar →+* ℂ, NormOne σ c := fun σ =>
    h ℂ σ (fun τ => normOne_emb σ _ _ (norm_det_complex U)) fun τ => normOne_emb σ _ _ (norm_det_complex U')
  refine ⟨⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, (hc (algebraMap Qbar ℂ)).2, fun M M' q _ a1 a2 a3 a4 lam => ?_⟩
  obtain ⟨h3, h4⟩ := h ℂ_[q] lam (fun τ => normOne_emb lam _ _ (norm_det_padic U a1 a3))
    fun τ => normOne_emb lam _ _ (norm_det_padic U' a2 a4)
  rw [lamC, dite_eq_left h3]
  exact h4

end GlobalTheory.RatMoveFock

end
