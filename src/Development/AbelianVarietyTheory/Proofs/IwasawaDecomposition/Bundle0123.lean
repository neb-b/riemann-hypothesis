module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.LRank


open scoped TensorProduct in
theorem natCard_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

theorem finrank_of_card {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {n : ℕ}
    (h : Nat.card V = Nat.card F ^ n) : Module.finrank F V = n := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite F V := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := F) (V := V)
  rw [h] at h2
  exact (Nat.pow_right_injective h1 h2).symm


set_option maxHeartbeats 800000 in
theorem finrank_red {E : Type} [Field E] [NumberField E] {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (P : HeightOneSpectrum (𝓞 E)) :
    Module.finrank (Res P) (TDat.Red N P) = n := by
  let : Submodule.IsFullLattice E N := hN
  have : Module.Finite (𝓞 E) N := Submodule.IsLattice.finite E N
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N = n := by
    exact (Submodule.IsFullLattice.finrank_eq E N).trans (Module.finrank_fin_fun E)
  have h := natCard_quot (R := 𝓞 E) (N := N) P.asIdeal
  rw [hr] at h
  exact finrank_of_card (F := Res P) h


set_option maxHeartbeats 1600000 in
theorem ranks : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  intro E K _ _ _ _ n S ST A T _ h
  exact ⟨fun P c => finrank_red _ (h.N_lat c.1 (S.rep c)) P.1,
    fun P c => finrank_red _ (h.dnN_lat c.1 (S.rep c) P) P.1⟩

end GlobalTheory.Mem.Col2.LRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBound
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.PsiFix

end GlobalTheory.Mem.An.PsiFix

namespace GlobalTheory.Mem.An

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameAtOfLocalizationEq
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

noncomputable section

namespace GlobalTheory.SameAtOfLoc

theorem exists_smul_mem_of_le_locP {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (𝓞 E) W] (Q : HeightOneSpectrum (𝓞 E)) {A B : Submodule (𝓞 E) W} (hA : A.FG)
    (h : A ≤ localization₂ Q.asIdeal B) : ∃ s ∉ Q.asIdeal, ∀ x ∈ A, s • x ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  have key : ∃ s ∉ Q.asIdeal, ∀ a ∈ S, s • a ∈ B := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Formalism.L2.DIV.lc_one_notMem Q, by simp⟩
    | insert a S ha ih =>
      obtain ⟨s, hs, hS⟩ := ih (le_trans (Submodule.span_mono (by
        rw [Finset.coe_insert]; exact Set.subset_insert _ _)) h)
      obtain ⟨t, ht, hta⟩ := (Formalism.L2.DIV.lc_mem_locP Q B a).1
        (h (Submodule.subset_span (by simp)))
      refine ⟨t * s, Formalism.L2.DIV.lc_mul_notMem Q ht hs, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact B.smul_mem s hta
      · rw [mul_smul]; exact B.smul_mem t (hS b hb)
  obtain ⟨s, hs, hS⟩ := key
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact B.smul_mem r hx

end GlobalTheory.SameAtOfLoc

namespace GlobalTheory


open GlobalTheory.SameAtOfLoc in
theorem sameAt_of_localized_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A →
    Submodule.IsLattice E B → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B → SameAt Q A B := by
  intro E _ _ _ n Q A B hA hB h
  obtain ⟨a, ha, h1⟩ := exists_smul_mem_of_le_locP Q hB.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q B)
  obtain ⟨a', ha', h2⟩ := exists_smul_mem_of_le_locP Q hA.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q A)
  exact ⟨a, ha, a', ha', h1, h2⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanImageSpan
section
open NumberField

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

theorem relSet_eq {n : ℕ} (S : Set (Fin n → K)) :
    {x' : Fin n → K' | ∃ x ∈ S, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' S := by
  ext x'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨x, hx, funext fun k => (h k k rfl).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]⟩

theorem span_image_span {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun x k => φ (x k)) '' (Submodule.span (𝓞 K) S : Set (Fin n → K))) =
      Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [SetLike.mem_coe]
      convert Submodule.zero_mem (Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S)) using 1
      funext k; simp
    | add y z _ _ hy hz =>
      rw [SetLike.mem_coe] at hy hz ⊢
      convert Submodule.add_mem _ hy hz using 1; funext k; simp
    | smul a y _ hy =>
      rw [SetLike.mem_coe] at hy ⊢
      convert Submodule.smul_mem _ (RingOfIntegers.mapRingHom φ a) hy using 1
      funext k
      simp [Pi.smul_apply, Algebra.smul_def, map_mul]
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem span_image_inf {n : ℕ} (X : Submodule (𝓞 K) (Fin n → K)) (V : Submodule K (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' (X : Set (Fin n → K))) ⊓
      (Submodule.span K' ((fun (x : Fin n → K) k => φ (x k)) '' (V : Set (Fin n → K)))).restrictScalars (𝓞 K') =
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) ''
      ((X ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  classical
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  set ψ : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom φ with hψdef
  have hψ : ∀ a : 𝓞 K, ((ψ a : 𝓞 K') : K') = φ (a : K) := fun a => rfl
  apply le_antisymm
  · rintro y ⟨hyX, hyV⟩

    let bQ := Module.finBasis K ((Fin n → K) ⧸ V)
    let ℓ : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → (Fin n → K) →ₗ[K] K := fun r => (bQ.coord r).comp V.mkQ
    have hℓV : ∀ x, x ∈ V ↔ ∀ r, ℓ r x = 0 := by
      intro x
      constructor
      · intro hx r
        simp [ℓ, (Submodule.Quotient.mk_eq_zero V).2 hx]
      · intro h
        have : V.mkQ x = 0 := bQ.ext_elem fun r => by simpa [ℓ] using h r
        exact (Submodule.Quotient.mk_eq_zero V).1 this
    let q : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → Fin n → K := fun r k => ℓ r (Pi.single k 1)
    have hℓ : ∀ r x, ℓ r x = ∑ k, q r k * x k := by
      intro r x
      rw [LinearMap.pi_apply_eq_sum_univ (ℓ r) x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hyℓ : ∀ r, ∑ k, φ (q r k) * y k = 0 := by
      intro r
      have key : ∀ z ∈ Submodule.span K' (Φ '' V), ∑ k, φ (q r k) * z k = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨x, hx, rfl⟩ := hw
          have h0 := (hℓV x).1 hx r
          rw [hℓ] at h0
          have := congrArg φ h0
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a b _ hb =>
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [show ∑ k, φ (q r k) * (a * b k) = a * ∑ k, φ (q r k) * b k by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hb, mul_zero]
      exact key y hyV
    obtain ⟨m, r0, g, hg⟩ := Submodule.mem_span_set'.1 hyX
    choose x hxX hx using fun i => (g i).2
    have hy : ∀ k, y k = ∑ i, (r0 i : K') * φ (x i k) := by
      intro k
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, ← hx i]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
      (fun z : Fin m × Fin (Module.finrank K ((Fin n → K) ⧸ V)) => ℓ z.2 (x z.1))
    choose b hb using hd
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hb' : ∀ i r, ((b (i, r) : 𝓞 K) : K) = ((d : 𝓞 K) : K) * ℓ r (x i) := fun i r => by
      have := hb (i, r)
      rw [Algebra.smul_def] at this
      exact this
    letI : Algebra (𝓞 K) (𝓞 K') := ψ.toAlgebra
    have hinj : Function.Injective ψ := fun a a' h => by
      have := congrArg (fun z : 𝓞 K' => (z : K')) h
      simp only [hψ] at this
      exact RingOfIntegers.ext (φ.injective this)
    haveI : Module.Flat (𝓞 K) (𝓞 K') := by
      rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
      rintro z ⟨a, ha⟩
      have ha' : ψ a * z = 0 := ha
      rcases mul_eq_zero.1 ha' with h | h
      · exact absurd (hinj (h.trans (map_zero ψ).symm)) (nonZeroDivisors.coe_ne_zero a)
      · exact h
    obtain ⟨N, a, yv, hr, ha⟩ := GlobalTheory.Proof.IdempotentLatticeSequence.flat_system (fun i r => b (i, r)) r0 (fun r => by
      apply RingOfIntegers.ext
      have h1 : ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, φ (b (i, r) : K) * (r0 i : K') := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, ((b (i, r) • r0 i : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      rw [h1]
      simp only [hb', map_mul]
      have h2 := hyℓ r
      simp only [hy, Finset.mul_sum] at h2
      rw [Finset.sum_comm] at h2
      change _ = (0 : K')
      rw [← mul_zero (φ ((d : 𝓞 K) : K)), ← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hℓ, map_sum]
      simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring)
    let u : Fin N → Fin n → K := fun l => ∑ i, a i l • x i
    have huX : ∀ l, u l ∈ X := fun l => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
    have huV : ∀ l, u l ∈ V := by
      intro l
      rw [hℓV]
      intro r
      have h1 := congrArg (fun z : 𝓞 K => (z : K)) (ha l r)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hb', map_zero] at h1
      apply mul_left_cancel₀ hd0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [mul_zero, ← h1, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def]
      ring
    have hyu : y = ∑ l, yv l • Φ (u l) := by
      funext k
      rw [hy, Finset.sum_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Pi.smul_apply, hΦ, u, Finset.sum_apply, map_sum, Algebra.smul_def]
      have h2 : ∀ i, ((r0 i : 𝓞 K') : K') = ∑ l, φ (a i l : K) * (yv l : K') := by
        intro i
        rw [hr i]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show ((∑ l, a i l • yv l : 𝓞 K') : K') = ∑ l, ((a i l • yv l : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      simp only [h2, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      change _ = (algebraMap (𝓞 K') K' (yv l)) * φ (((a i l) : K) * x i k)
      rw [map_mul]
      change φ (a i l : K) * (yv l : K') * φ (x i k) = (yv l : K') * (φ (a i l : K) * φ (x i k))
      ring
    rw [hyu]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u l, ⟨huX l, huV l⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxV⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hxX, rfl⟩, Submodule.subset_span ⟨x, hxV, rfl⟩⟩

end GlobalTheory.Mem.R3.LiftForms

namespace GlobalTheory.Mem.R3.LiftForms
variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

theorem span_rel_inf {n n' : ℕ} (hn : n = n') (S : Set (Fin n → K)) (V : Submodule K (Fin n → K))
    (S' : Set (Fin n' → K')) (V' : Submodule K' (Fin n' → K'))
    (hS : S' = {x' | ∃ x ∈ S, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)})
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    Submodule.span (𝓞 K') S' ⊓ V'.restrictScalars (𝓞 K') =
      Submodule.span (𝓞 K') {x' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
        ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)} := by
  subst hn hS hV
  have e1 : {x' : Fin n → K' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' (V : Set (Fin n → K)) := relSet_eq φ (V : Set (Fin n → K))
  have e2 : {x' : Fin n → K' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
      ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' ((Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) :
        Set (Fin n → K)) := relSet_eq φ _
  rw [relSet_eq, e1, e2, ← span_image_span φ S]
  exact span_image_inf φ _ V

end GlobalTheory.Mem.R3.LiftForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAtZeroFree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem frm_free_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K (R.N 0) Pr.vGs) (hΛ : Λ = colLev Ch 0) (Θ : LevQFam X.E X.K (R.N 0) Q) (g : FrmG Λ Θ)
    (p : DecoF X.E (R.N 0) (Pr.vT u) Pr.vGs Q) (hp : FrmG.incl Λ Θ g • p = p) : g = 1 := by
  subst hΛ
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp g.2.1.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  have ha : ((g.1, (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs))) : UF X.E (R.N 0) × GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) • p.deco = p.deco :=
    congrArg DecoF.deco hp
  have h1 : ((g.1, (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs))) : UF X.E (R.N 0) × GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) = 1 :=
    DecoSet.decoration_stabilizer_trivial_unipotent hX hPr p.deco ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
      (isNilpotent_of_mem_HX_zero hN.le hmem)
  apply GlobalTheory.FramedForms.incl_injective
  rw [map_one]
  exact GlobalTheory.FramedForms.stab_inj p hp (one_smul _ p) (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp h1).2

theorem stepAt_zero_free {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hL : ∀ b, L.levG 0 b = colLev Ch 0) :
    (stepAt sel mu cst L Tp u 0).Free := by
  intro b g d hd
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hΛ : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
    obtain ⟨b, hb⟩ := b
    obtain ⟨b0, rfl⟩ := Option.isSome_iff_exists.mp (hb.mpr hm)
    exact hL b0
  exact frm_free_zero Ch hX hPr hbig u _ hΛ _ g d.1.1 (congrArg (fun x => x.1.1) hd)

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeIntegralColumnMinorExpansion
section
open MvPolynomial

namespace GlobalTheory.WeylIntExpansion

theorem weyl_int_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  intro N Y hY hrep f hf
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  set N0 := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) with hN0
  have hN0ne : N0 ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti _ _ hab
  have hfQ : Formalism.GradedWeylDivisibility.intQ N N f ∈ Formalism.GradedWeylDivisibility.bDual N N le_rfl μ ((Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ).map (Formalism.GradedWeylDivisibility.intQ N N)) := by
    rw [← GlobalTheory.StdDual.weylEqDualNabla N N le_rfl μ hanti]
    exact ⟨f, hf, rfl⟩
  have hmem : ∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ := by
    intro J
    rw [hμ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY]
    exact Submodule.subset_span ⟨J, rfl⟩
  have hz : ∀ J, ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) = z * N0 :=
    fun J => hfQ.2 _ ⟨_, hmem J, rfl⟩
  choose z hz using hz
  refine ⟨z, hz, ?_⟩
  have hmap : ∀ J, map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) =
      GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J => by
    unfold GlobalTheory.WeylMinorDual.colProd
    exact Formalism.L2.DIV.fk_map_bidet _ _ _ _
  have h := hrep (map (Int.castRingHom ℚ) f) hfQ.1
  have hc : ∀ J, Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) (map (Int.castRingHom ℚ) f) = z J * N0 :=
    fun J => by rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← hmap, hz]
  simp only [hc] at h
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply smul_right_injective _ hN0ne
  simp only
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [map_zsmul, hmap, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm]

end GlobalTheory.WeylIntExpansion
end

