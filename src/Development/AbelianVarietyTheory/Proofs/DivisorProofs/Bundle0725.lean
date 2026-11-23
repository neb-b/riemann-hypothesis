module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfTotallyBoundedSupNormBall
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDimensional_of_totallyBounded_supBall :
    ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) →
      (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) →
        ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  intro T V B hinj hbdd htb
  classical
  have hmem : ∀ φ : V, Memℓp (fun x : B => (φ : T → ℂ) x) (⊤ : ENNReal) := by
    intro φ
    obtain ⟨M, hM⟩ := hbdd φ φ.2
    apply memℓp_infty
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hM x x.2
  let L : V →ₗ[ℂ] lp (fun _ : B => ℂ) (⊤ : ENNReal) :=
    { toFun := fun φ => ⟨fun x : B => (φ : T → ℂ) x, hmem φ⟩
      map_add' := fun φ ψ => lp.ext (funext fun _ => rfl)
      map_smul' := fun c φ => lp.ext (funext fun _ => rfl) }
  have hLapp : ∀ (φ : V) (x : B), (L φ) x = (φ : T → ℂ) x := fun _ _ => rfl
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun φ hφ => ?_
    have h0 : ∀ x ∈ B, (φ : T → ℂ) x = 0 := by
      intro x hx
      rw [← hLapp φ ⟨x, hx⟩, hφ]
      rfl
    exact Subtype.ext (hinj φ φ.2 h0)
  haveI : FiniteDimensional ℂ (LinearMap.range L) := by
    by_contra hfin
    obtain ⟨R, f, hR, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
    have hRpos : 0 < R := by linarith
    obtain ⟨F, hF⟩ := htb (1 / (3 * R)) (by positivity)
    have hpre : ∀ n, ∃ φ : V, L φ = (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)) := fun n => (f n).2
    choose φ hφ using hpre
    have hφle : ∀ n, ∀ x ∈ B, ‖(φ n : T → ℂ) x‖ ≤ R := by
      intro n x hx
      rw [← hLapp (φ n) ⟨x, hx⟩, hφ n]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _).trans (hfR n)
    have hball : ∀ n, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 1 := by
      intro n x hx
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
      rw [inv_mul_le_iff₀ hRpos, mul_one]
      exact hφle n x hx
    have hch : ∀ n, ∃ ψ ∈ F, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ x‖ ≤ 1 / (3 * R) :=
      fun n => hF _ (V.smul_mem _ (φ n).2) (hball n)
    choose ψ hψF hψ using hch
    obtain ⟨m, n, hmn, hmn'⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨ψ k, hψF k⟩ : F))
    have hψeq : ψ m = ψ n := congrArg Subtype.val hmn'
    have hpt : ∀ x ∈ B, ‖(φ m : T → ℂ) x - (φ n : T → ℂ) x‖ ≤ 2 / 3 := by
      intro x hx
      have h1 := hψ m x hx
      have h2 := hψ n x hx
      rw [hψeq] at h1
      have h3 : ‖((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 2 / (3 * R) := by
        calc _ = ‖(((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ψ n x) - (((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ n x)‖ := by
                congr 1; ring
          _ ≤ _ := norm_sub_le _ _
          _ ≤ 1 / (3 * R) + 1 / (3 * R) := add_le_add h1 h2
          _ = 2 / (3 * R) := by ring
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg hRpos.le] at h3
      rw [inv_mul_le_iff₀ hRpos] at h3
      calc _ ≤ R * (2 / (3 * R)) := h3
        _ = 2 / 3 := by field_simp
    have hnorm : ‖f m - f n‖ ≤ 2 / 3 := by
      show ‖((f m : lp (fun _ : B => ℂ) (⊤ : ENNReal)) - (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)))‖ ≤ 2 / 3
      rw [← hφ m, ← hφ n]
      refine lp.norm_le_of_forall_le (by norm_num) fun x => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, hLapp, hLapp]
      exact hpt x x.2
    have := hsep hmn
    linarith
  exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective L hL).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FloorCastOfInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes
open Formalism.MainNotions.DIV.Inh (aPlusQ_anti aMinusQ_mono)

namespace GlobalTheory.BlockRows

theorem floor_cast_of_int {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem one_le_aPlusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : 1 ≤ DV.aPlusQ D j τ i := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  exact (DV.aPlusQ_last D j h1 h2 τ).trans
    (aPlusQ_anti D j τ (show i.1 ≤ D.R.k + j - 1 - 1 by omega) (by omega))

theorem one_le_aMinusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c < D.R.m) :
    1 ≤ DV.aMinusQ D j τ c :=
  (DV.aMinusQ_last D j h1 (by omega) τ).trans (aMinusQ_mono D j τ (Nat.zero_le c) hc)

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem aPlus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (i : Fin (D.R.sigW j).1) : DV.aPlus D j τ i ≤ 3 * L.sc.b ^ 2 := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  have h0 : 0 < D.R.k - 1 := by omega
  have a1 := aPlusQ_anti D j τ (Nat.zero_le i.1) (by omega)
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aPlusQ D j τ 0 ≤ (D.hc τ).v ⟨0, h0⟩ + (D.hc τ).e ⟨j - 1, hj⟩ := by
    rw [DV.aPlusQ_eq]
    unfold DV.sigPar DV.eQ
    rw [dite_eq_left h0, dite_eq_left ⟨h1, h2⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hk' : (2 : ℚ) ≤ D.R.k := by exact_mod_cast (show 2 ≤ D.R.k by omega)
    have hj' : (0 : ℚ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith
  have a3 : DV.aPlus D j τ i ≤ (((D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aPlus
    exact_mod_cast a1.trans a2
  have b1 := (L.cloud_v τ ⟨0, h0⟩).2
  have b2 := L.b_le τ ⟨j - 1, hj⟩
  have b3 := (abs_le.1 (L.be_close τ ⟨j - 1, hj⟩ ⟨j - 1, hj⟩)).1
  have b4 := one_le_b L.sc
  push_cast at b3
  have := hL.1
  have := hL.2
  nlinarith

theorem aMinus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (c : ℕ) (hc : j + c < D.R.m) : DV.aMinus D j τ c ≤ 3 * L.sc.b ^ 2 := by
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aMinusQ D j τ c ≤ (D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ := by
    unfold DV.aMinusQ DV.eQ
    rw [dite_eq_left hc, dite_eq_left ⟨h1, by omega⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hc' : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    linarith
  have a3 : DV.aMinus D j τ c ≤ (((D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aMinus
    exact_mod_cast a2
  have b3 := (abs_le.1 (L.be_close τ ⟨j + c, hc⟩ ⟨j - 1, hj⟩)).2
  have b4 := one_le_b L.sc
  have := hL.1
  nlinarith

theorem rows_sizes : ∀ (D : D7) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, (Antitone (rowsP D j τ) ∧ (∀ i, 1 ≤ rowsP D j τ i) ∧ ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i) ∧ (Antitone (rowsM D j τ) ∧ (∀ i, 1 ≤ rowsM D j τ i) ∧ ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)) ∧ ∀ L : SizeData₂ D, WindowsLe L → (∀ i, (rowsP D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2) ∧ ∀ i, (rowsM D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2 := by
  intro D j h1 h2 τ
  have hk := D.R.m_add_three_le_k
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  have hM : ∀ i : Fin (D.R.sigW j).2, j + ((D.R.sigW j).2 - 1 - i) < D.R.m := by
    intro i
    have := i.2
    omega
  have eP : ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i := by
    intro i
    have := floor_cast_of_int (DV.aPlusQ_int D j τ i) (one_le_aPlusQ D j h1 h2 τ i)
    unfold DV.aPlus rowsP
    rw [← this]
    simp
  have eM : ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i) := by
    intro i
    have := floor_cast_of_int (DV.aMinusQ_int D j τ _) (one_le_aMinusQ D j h1 τ _ (hM i))
    unfold DV.aMinus rowsM
    rw [← this]
    simp
  refine ⟨⟨?_, ?_, eP⟩, ⟨?_, ?_, eM⟩, fun L hL => ⟨fun i => ?_, fun i => ?_⟩⟩
  · intro a b hab
    have hb : b.1 < D.R.k + j - 1 := b.2
    exact Nat.floor_le_floor (aPlusQ_anti D j τ (show a.1 ≤ b.1 from hab) (by omega))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aPlusQ D j h1 h2 τ i)
  · intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    exact Nat.floor_le_floor (aMinusQ_mono D j τ (by omega) (hM a))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aMinusQ D j h1 τ _ (hM i))
  · rw [eP]
    exact aPlus_le D j h1 h2 τ L hL i
  · rw [eM]
    exact aMinus_le D j h1 τ L hL _ (hM i)

end GlobalTheory.BlockRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGermBaseChange
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.DescentAll

theorem mem_zpowers_of_prime {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hl : (Module.finrank F F').Prime) (hs : s ≠ 1) :
    ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F' := Fintype.ofFinite F'
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  have hc : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  intro t
  rw [zpowers_eq_top_of_prime_card hc hs]
  exact Subgroup.mem_top t

theorem isCl_cusp (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) :
    IsCl (cusp θ m k) := by
  intro x y
  have h := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 m (fun _ => 1) (fun _ => 1)).2.2 (rootSum θ k)).1 x y
  simp only [cusp]
  rw [h]

end GlobalTheory.Shin.DescentAll

namespace GlobalTheory.Shin.DescentAll

theorem kills_liftAll : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L →
    Kills (shLift s (J (pullθ ι θ) L n)) (J θ (liftAll (Nat.card F) (Module.finrank F F') L) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F' := Fintype.ofFinite F'
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hgen := mem_zpowers_of_prime s hl hs
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hq2 : 2 ≤ q := by
    rw [hqdef, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hqdef, hldef, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hlist := GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ
  have happ : ∀ (A B : List (ℕ × ℕ)) (a b : ℕ), deg A = a → deg B = b →
      J θ (A ++ B) (a + b) = hc a b (J θ A a) (J θ B b) (a + b) := by
    intro A B a b ha hb
    subst ha hb
    exact hlist.2.1 A B _ rfl
  intro L
  induction L with
  | nil =>
    intro _ n hn
    obtain rfl : n = 0 := hn
    have hlift : liftAll q l ([] : List (ℕ × ℕ)) = [] := by simp [liftAll]
    rw [hlift]
    have h1 : shLift s (J (pullθ ι θ) [] 0) = J θ [] 0 := by
      funext δ
      have hδ : δ = 1 := by ext i j; exact i.elim0
      unfold shLift
      rw [dite_eq_left ⟨1, by rw [hδ]; exact isNorm_one s 0⟩]
      rfl
    rw [h1]
    exact GlobalTheory.T.isInCharacterIsotypicPart_self _ _ (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ [] (by simp) 0 rfl)
  | cons p L ih =>
    intro hL n hn
    have hp := hL p List.mem_cons_self
    have hLt : ∀ x ∈ L, 0 < x.1 ∧ Reg q x.1 x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    obtain rfl : n = p.1 + deg L := hn.trans hdeg
    set A : List (ℕ × ℕ) := (if l ∣ p.1 then liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))])
      with hAdef
    have hsplit : liftAll q l (p :: L) = A ++ liftAll q l L := by simp [liftAll, hAdef]
    have hA1 : liftAll q l [p] = A := by simp [liftAll, hAdef]
    obtain ⟨hdA, hRA⟩ := GlobalTheory.T.lift_all_preserves_degree_and_regularity q l [p] hq2 hl (by simpa using hp)
    obtain ⟨hdB, hRB⟩ := GlobalTheory.T.lift_all_preserves_degree_and_regularity q l L hq2 hl hLt
    rw [hA1] at hdA hRA
    have hdA' : deg A = p.1 := by rw [hdA]; simp [deg]
    have hKA : Kills (shLift s (cusp (pullθ ι θ) p.1 p.2)) (J θ A p.1) := by
      by_cases h : l ∣ p.1
      · have := GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree F F' s hl hs ι θ hθ p.1 p.2 hp.1 h hp.2
        rw [hAdef, if_pos h]
        simpa only [Prod.mk.eta] using this
      · rw [hAdef, if_neg h]
        have hu := GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd F F' s hl hs ι θ hθ p.1 p.2 hp.1 h hp.2
        have hJ : J θ [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] p.1 =
            cusp θ p.1 (p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i)) := by
          rw [J_cons]
          exact (GlobalTheory.T.harishChandraInductionGL_one_left_right_unit F' p.1 _ (isCl_cusp F' θ _ _)).2
        rw [hJ]
        exact hu
    have hRA' : ∀ x ∈ A, 0 < x.1 ∧ Reg (Nat.card F') x.1 x.2 := by rw [hcard']; exact hRA
    have hRB' : ∀ x ∈ liftAll q l L, 0 < x.1 ∧ Reg (Nat.card F') x.1 x.2 := by rw [hcard']; exact hRB
    have hcharA := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ A hRA' p.1 hdA'.symm
    have hcharB := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftAll q l L) hRB' (deg L) hdB.symm
    rw [J_cons, GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen p.1 (deg L) _ rfl _ _ (isCl_cusp F _ _ _)
      ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F (pullθ ι θ)).1 L (deg L)), hsplit, happ A (liftAll q l L) p.1 (deg L) hdA' hdB]
    exact GlobalTheory.T.twistedHarishChandra_isotypic_part F' (s : F' →+* F') p.1 (deg L) _ rfl _ _ _ _ hcharA hcharB hKA (ih hLt (deg L) rfl)

end GlobalTheory.Shin.DescentAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMem
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem stable_sym_mem (F : IntermediateField ℚ ℂ) (L : PeriodPair) (ι : Type) [Fintype ι] (T : ι → ℂ) :
    L.g₂ ∈ F → L.g₃ ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice) →
    (∑ i, L.weierstrassP (T i)) ∈ F ∧ (∑ i, L.derivWeierstrassP (T i) / 2) ∈ F ∧
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) ∈ F ∧
    ((∀ i, 2 * T i ∉ L.lattice) → (∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i))) ∈ F) := by
  intro h₂ h₃ hS hT
  have key : ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι,
      (∀ i, σ (L.weierstrassP (T i)) = L.weierstrassP (T (e i))) ∧
      (∀ i, σ (L.derivWeierstrassP (T i)) = L.derivWeierstrassP (T (e i))) ∧
      ((∀ i, 2 * T i ∉ L.lattice) → ∀ i, σ (L.weierstrassP (2 * T i)) = L.weierstrassP (2 * T (e i))) ∧
      σ L.g₂ = L.g₂ := by
    intro σ hσ
    obtain ⟨e, he⟩ := hS σ hσ
    have g₂e : L.g₂ = σ L.g₂ := (hσ _ h₂).symm
    have g₃e : L.g₃ = σ L.g₃ := (hσ _ h₃).symm
    refine ⟨e, fun i ↦ ?_, fun i ↦ ?_, fun h2 i ↦ ?_, hσ _ h₂⟩
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.1).symm
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.2).symm
    · have := GlobalTheory.ConjPoint.IsConj.add g₂e g₃e (he i) (he i)
      rw [← two_mul, ← two_mul] at this
      exact ((this.resolve_left fun h ↦ h2 i h.1).2.2.1).symm
  refine ⟨_root_.GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed F _ fun σ hσ ↦ ?_, _root_.GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed F _ fun σ hσ ↦ ?_,
    _root_.GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed F _ fun σ hσ ↦ ?_, fun h2 ↦ _root_.GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed F _ fun σ hσ ↦ ?_⟩
  · obtain ⟨e, a, -, -, -⟩ := key σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp only [a]; exact Equiv.sum_comp e (fun i ↦ L.weierstrassP (T i))
  · obtain ⟨e, -, b, -, -⟩ := key σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp only [map_div₀, map_ofNat, b]
    exact Equiv.sum_comp e (fun i ↦ L.derivWeierstrassP (T i) / 2)
  · obtain ⟨e, a, b, -, g⟩ := key σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_div₀, map_add (f := _), map_mul, map_pow, map_neg, map_ofNat, a, b, g]
    exact Equiv.sum_comp e (fun i ↦ (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2)))
  · obtain ⟨e, a, -, c, -⟩ := key σ hσ
    rw [map_prod]; simp only [map_sub, a, c h2]
    exact Equiv.prod_comp e (fun i ↦ L.weierstrassP (T i) - L.weierstrassP (2 * T i))

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfParts
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem taylor_congr {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    {f f' : (I → ℂ) → ℂ} (h : f =ᶠ[nhds 0] f') : GlobalTheory.PeriodFamily.taylor N t f = GlobalTheory.PeriodFamily.taylor N t f' := by
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem isAb_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A) : IsAbelianScheme A' :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h

theorem gaussManinPeriods_of_parts : ∀ ε : ℤˣ, GlobalTheory.PeriodFamily.FamUnif → PExist → PHom → PSpan → PLie → PEnd → PChern ε → PFix → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  intro ε HF HE HH HS HL HEn HC HX HT
  have pm : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ (L : LB A.left), L.IsLB → ∀ (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P → IsPeriodMap ε u P :=
    fun A _ g hA hg L hL u P hP ↦ ⟨(HS A g hA hg L u P hP).1, (HS A g hA hg L u P hP).2, HL A g hA hg L u P hP,
      fun α _ M ↦ HEn A g hA L u P hP α M, fun H χ ψ ↦ HC A g hA L u P hP L u hL rfl H χ ψ⟩
  refine ⟨ε, fun B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0 hy A _ φ hφ m L hL A₀ _ φ₀ hφ₀ L₀ hL₀ u₀ ↦ ?_⟩
  obtain ⟨r, u, τ, hr, hrU, hhol, ⟨W, hW, hW0⟩, c1, c2, c3, c4⟩ :=
    HF B 𝒜 g h𝒜 hg I U y hU h0 hy A φ hφ L hL A₀ φ₀ hφ₀ L₀ u₀
  have hA : ∀ z, IsAbelianScheme (A z) := fun z ↦ isAb_pull (hφ z) h𝒜
  have hA₀ : IsAbelianScheme A₀ := isAb_pull hφ₀ h𝒜
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have gA : ∀ z, SmoothOfRelativeDimension g (A z).hom := fun z ↦
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (hφ z).1 hg
  have gA₀ : SmoothOfRelativeDimension g A₀.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hφ₀.1 hg
  choose P hP using fun z ↦ HH (A z) g (hA z) (L z) (u z)
  obtain ⟨P₀, hP₀⟩ := HH A₀ g hA₀ L₀ u₀
  let V : Opens (I → ℂ) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have V0 : (0 : I → ℂ) ∈ V := Metric.mem_ball_self hr
  let F : Fam I g u₀.Λ :=
    { V := V
      τ := { toFun x z := (τ z x : Fin g → ℂ)
             map_zero' := funext fun z ↦ congrArg Subtype.val ((τ z).map_zero)
             map_add' a b := funext fun z ↦ congrArg Subtype.val ((τ z).map_add a b) }
      hol x := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (c3 x) }
  have ya : ∀ b, AnalyticOnNhd ℂ (fun z ↦ y z b) V := fun b ↦
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball ((hy b).mono hrU)
  let σ : B →ₐ[ℂ] Hol F.V :=
    { toFun b := Hol.mk _ (ya b)
      map_one' := Subtype.ext (funext fun z ↦ map_one (y z))
      map_mul' a b := Subtype.ext (funext fun z ↦ map_mul (y z) a b)
      map_zero' := Subtype.ext (funext fun z ↦ map_zero (y z))
      map_add' a b := Subtype.ext (funext fun z ↦ map_add (y z) a b)
      commutes' a := Subtype.ext (funext fun z ↦ (y z).commutes a) }
  have hσ : ∀ b, ∀ z ∈ V, (σ b).fn z = y z b := fun b z hz ↦ Hol.fn_mk _ (ya b) hz
  let e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V) :=
    { E q := (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1
      w p hp := by
        have e1 : (show Sp ℂ ⟶ (A p.1).left from ((u p.1).ex p.2).left) ≫ (A p.1).hom = 𝟙 _ := Over.w ((u p.1).ex p.2)
        rw [Category.comp_id, Category.assoc, (hφ p.1).1.w, ← Category.assoc, e1, Category.id_comp]
        rfl
      per l p _ := by
        have : (u p.1).ex (p.2 + (τ p.1 l : Fin g → ℂ)) = (u p.1).ex p.2 := by
          rw [(u p.1).ex_add, ((u p.1).ker _).2 (τ p.1 l).2, _root_.mul_one]
        exact congrArg (fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A p.1 ↦ (show Sp ℂ ⟶ (A p.1).left from x.left) ≫ φ p.1) this
      hol U' f := by
        have := hhol U' f
        simp only [Set.mem_prod, Set.mem_univ, and_true] at this
        exact this }
  haveI : IsSeparated (𝒜.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]
    haveI := h𝒜.proper
    infer_instance
  choose per hper using HE I g u₀.Λ F B 𝒜.left _ _ e ⟨W, hW, hW0⟩
  have fix : ∀ x (c : primDR 𝒜), ∀ z ∈ V, P z (τ z x) ((m z).pull c) = (per c.1 x).fn z := fun x c z hz ↦
    HX I g u₀.Λ F B 𝒜 h𝒜 _ e z hz _ (fun b ↦ (hσ b z hz).symm) (A z) (hA z) (φ z) (m z) (L z) (u z) (fun _ ↦ rfl)
      (τ z).toAddMonoidHom (fun _ ↦ rfl) (P z) (hP z) c _ (hper c.1) x
  have nV : (V : Set (I → ℂ)) ∈ nhds (0 : I → ℂ) := V.isOpen.mem_nhds V0
  refine ⟨Metric.ball 0 r, u, τ, P, P₀, Metric.isOpen_ball, V0, hrU, pm A₀ g hA₀ gA₀ L₀ hL₀ u₀ P₀ hP₀,
    fun z _ ↦ pm _ g (hA z) (gA z) _ (hL z) _ _ (hP z), c1, c2, c3, c4,
    fun x c ↦ (per c.1 x).analytic.differentiableOn.congr (fix x c), ?_⟩
  intro D _ _ π κ hκ hπ N t ht hN j hj A' _ φ' hφ' m' i h hi k x d hd c
  rw [HT I g B 𝒜 h𝒜 hg (y 0) A₀ φ₀ hφ₀ L₀ u₀ F σ e V0 (fun b ↦ (hσ b 0 V0).symm) c1 (fun x ↦ c2 x) P₀ hP₀ D π κ hκ hπ N t ht hN j
    (fun b ↦ (hj b).trans (taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (hσ b z hz).symm)))
    A' φ' hφ' m' i h hi k x d hd c _ (hper c.1)]
  exact taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (fix x c z hz).symm)

end GlobalTheory.AnPer
end
end

