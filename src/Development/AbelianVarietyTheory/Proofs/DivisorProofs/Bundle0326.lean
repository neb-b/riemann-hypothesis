module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariant
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagUnitary

def Pm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 1 else 0

def Qm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 0 else 1

lemma Pm_eq {n : ℕ} (ε : Fin n → Bool) : Pm ε = (1/2 : ℂ) • (1 + Jm ε) := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Jm, hε] <;> norm_num
  · simp [Pm, Jm, h, diagonal_apply_ne _ h, one_apply_ne h]

lemma Qm_eq {n : ℕ} (ε : Fin n → Bool) : Qm ε = 1 - Pm ε := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Qm, hε]
  · simp [Pm, Qm, h, diagonal_apply_ne _ h, one_apply_ne h]

lemma comm_Pm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Pm ε = Pm ε * a := by
  rw [Pm_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h,
    Matrix.mul_one, Matrix.one_mul]

lemma comm_Qm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Qm ε = Qm ε * a := by
  rw [Qm_eq, Matrix.mul_sub, Matrix.sub_mul, comm_Pm h, Matrix.mul_one, Matrix.one_mul]

lemma sum_sq_norm_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = trace (Mᴴ * M) := by
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma trace_unitary_conj {n : ℕ} (a b h : Matrix (Fin n) (Fin n) ℂ) (ha : aᴴ * a = 1)
    (hb : bᴴ * b = 1) : trace ((a * h * b)ᴴ * (a * h * b)) = trace (hᴴ * h) := by
  have hb' : b * bᴴ = 1 := mul_eq_one_comm.mp hb
  have e : (a * h * b)ᴴ * (a * h * b) = bᴴ * ((hᴴ * h) * b) := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (hᴴ * aᴴ) * (a * h * b) = bᴴ * (hᴴ * (aᴴ * a) * h * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, trace_mul_comm, Matrix.mul_assoc, hb', Matrix.mul_one]

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2
      = ∑ i, ∑ j, ‖(Pm ε * M * Qm ε) i j‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
      (by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pm, Qm, diagonal_mul, mul_diagonal]
  cases ε i <;> cases ε j <;> simp

end GlobalTheory.OffDiagUnitary

open GlobalTheory.OffDiagUnitary in
theorem GlobalTheory.offDiag_sum_sq_norm_unitary_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (a b g : Matrix (Fin n) (Fin n) ℂ), aᴴ * a = 1 → a * Jm ε = Jm ε * a → bᴴ * b = 1 → b * Jm ε = Jm ε * b → ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(a * g * b) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε a b g ha haJ hb hbJ
  rw [off_sum_eq, off_sum_eq]
  have e : Pm ε * (a * g * b) * Qm ε = a * (Pm ε * g * Qm ε) * b := by
    calc Pm ε * (a * g * b) * Qm ε = (Pm ε * a) * g * (b * Qm ε) := by simp only [Matrix.mul_assoc]
      _ = (a * Pm ε) * g * (Qm ε * b) := by rw [comm_Pm haJ, comm_Qm hbJ]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  apply Complex.ofReal_injective
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, trace_unitary_conj _ _ _ ha hb]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralVanishesOfFibre
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem integral_tw_eq_zero_of_fibre_eq_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by
  intro k _ _ _ _ _ _ ν β a b Φ hF Y hY
  obtain ⟨h, hYh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (k := k) finSumFinEquiv Y).1 (by rw [hY, Fintype.card_fin])
  have e := congrFun hF h
  have hC : (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have key : ∀ g : GL (Fin a) k, omA ν β 1 h Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
      apow (gdet g) (((a + b : ℕ) : ℂ) / 2) = ((β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2)) *
      (Φ (g.val * Y) * tw ν (a + b) g) := by
    intro g
    have hm : g.val * Y = (((((1 : GL (Fin a) k)⁻¹).val * ((g.val * X0 k finSumFinEquiv : Matrix (Fin a) (Fin (a + b)) k))
        : Matrix (Fin a) (Fin (a + b)) k)) * (invT h).val : Matrix (Fin a) (Fin (a + b)) k) := by
      rw [inv_one, Units.val_one, Matrix.one_mul, hYh]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [hm]
    simp only [omA, tw, Fintype.card_fin, map_one, inv_one, Units.val_one, apow_one]
    ring
  simp only [fibre, Pi.zero_apply, key, integral_const_mul] at e
  exact (mul_eq_zero.1 e).resolve_left hC

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivSubgroupQuotientTowerRSEqSRes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair.QuotIsog

variable {p : ℕ} {O : Type} [CommRing O] {G H : PDivGroup p O} (τ : QuotTower G)

theorem j_injective (m : ℕ) : Function.Injective (τ.j m) := fun a b h => by
  rw [← τ.ρ_j m a, ← τ.ρ_j m b, h]

theorem pDivSubgroupQuotientTower_r_s_eq_s_res (m : ℕ) (a : G.A (m + 1)) : τ.r m (τ.s (m + 1) a) = τ.s m (G.res m a) := by
  apply j_injective τ m
  rw [τ.j_r, τ.j_s, τ.j_s, G.res_mulP, G.mulP_res]

theorem s_res_j (m : ℕ) (b : τ.B m) : τ.s m (G.res m (τ.j m b)) = mulBy O _ p b := by
  apply j_injective τ m
  rw [τ.j_s, G.mulP_res, map_mulBy]

theorem ker_le (m : ℕ) : torsionIdeal (R := O) (A := τ.B m) (p ^ m) ≤
    RingHom.ker (((G.res m).comp (τ.j m) : τ.B m →ₐc[O] G.A m) : τ.B m →ₐ[O] G.A m) := by
  refine (kerIdeal_le_ker_iff _ _).2 fun c => ?_
  change ((G.res m).comp (τ.j m)) (mulBy O _ (p ^ m) c) = _
  rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]

variable [Fact p.Prime]

def toQuot (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : G ⟶ H where
  app m := liftSurj (q m) (hs m) ((G.res m).comp (τ.j m)) ((hk m).le.trans (ker_le τ m))
  comm n := BialgHom.ext fun c => by
    obtain ⟨b, rfl⟩ := hs (n + 1) c
    rw [BialgHom.comp_apply, BialgHom.comp_apply, hc, liftSurj_apply, liftSurj_apply,
      BialgHom.comp_apply, BialgHom.comp_apply, ← τ.j_r]

theorem toQuot_app_q (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) (m : ℕ) (b : τ.B m) :
    (toQuot τ q hs hk hc).app m (q m b) = G.res m (τ.j m b) :=
  liftSurj_apply ..

def fromQuot (q : ∀ m, τ.B m →ₐc[O] H.A m)
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : H ⟶ G where
  app m := (q m).comp (τ.s m)
  comm n := BialgHom.ext fun a => by
    change H.res n (q (n + 1) (τ.s (n + 1) a)) = q n (τ.s n (G.res n a))
    rw [hc, pDivSubgroupQuotientTower_r_s_eq_s_res]

end GlobalTheory.HTPair.QuotIsog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingCuspidalCharacterGLRootPowerSumCharacter
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem deg_map_const_fst (m : ℕ) (e : ℕ → ℕ) (L : List ℕ) :
    deg (L.map fun i => (m, e i)) = m * L.length := by
  induction L with
  | nil => simp [deg]
  | cons a L ih =>
    simp only [deg, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem pair_prod_split {F : Type} [Field F] [Fintype F] {a b : ℕ} (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (r : ℕ → F[X] → ℂ) (hr : ∀ j, IsAdditive (r j)) (T : Finset ℕ) :
    ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y *
      star ((fun P => ∏ j ∈ T, r j P) (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) *
        Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) =
    ∑ U ∈ T.powerset, (∑ᶠ x : GL (Fin a) F, α x * star (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F)))) *
      (∑ᶠ y : GL (Fin b) F, β y * star (chG (fun P => ∏ j ∈ T \ U, r j P) b y)) := by
  simp only [finsum_eq_sum_of_fintype, chG]
  have e1 : ∀ (x : GL (Fin a) F) (y : GL (Fin b) F),
      ∏ j ∈ T, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) =
      ∑ U ∈ T.powerset, (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F))) *
        ∏ j ∈ T \ U, r j (Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) := by
    intro x y
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun j _ => hr j _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _)
  simp only [e1, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_powerset_single (i : ℕ) (S T : Finset ℕ) (hiS : i ∉ S) (hT : T.card ≤ S.card + 1)
    (f g : Finset ℕ → ℂ) (A B : ℂ) (hf0 : f ∅ = 0) (hf1 : ∀ j ∈ T, f {j} = if i = j then A else 0)
    (hg : ∀ U ∈ T.powerset, U ≠ ∅ → g U = if T \ U = S then B else 0) :
    ∑ U ∈ T.powerset, f U * g U = if T = insert i S then A * B else 0 := by
  have hz : ∀ U ∈ T.powerset, U ≠ {i} → f U * g U = 0 := by
    intro U hU hUi
    by_cases h0 : U = ∅
    · rw [h0, hf0, zero_mul]
    rw [hg U hU h0]
    split_ifs with hc
    · have hsub : U ⊆ T := Finset.mem_powerset.1 hU
      have h1 := Finset.card_sdiff_add_card_eq_card hsub
      rw [hc] at h1
      have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h0)
      have hU1 : U.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hU1
      have hjT : j ∈ T := hsub (Finset.mem_singleton_self j)
      rw [hf1 j hjT, if_neg (fun h => hUi (by rw [h])), zero_mul]
    · rw [mul_zero]
  by_cases hiT : i ∈ T
  · have hmem : {i} ∈ T.powerset := Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hiT)
    rw [Finset.sum_eq_single_of_mem {i} hmem hz, hf1 i hiT, if_pos rfl,
      hg {i} hmem (Finset.singleton_ne_empty i)]
    have hiff : (T \ {i} = S) ↔ T = insert i S := by
      constructor
      · intro h
        rw [← h, Finset.sdiff_singleton_eq_erase, Finset.insert_erase hiT]
      · intro h
        rw [h, Finset.sdiff_singleton_eq_erase, Finset.erase_insert hiS]
    by_cases hc : T = insert i S
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, mul_zero]
  · rw [Finset.sum_eq_zero fun U hU => hz U hU (fun h => hiT (by
      rw [h] at hU; exact Finset.singleton_subset_iff.1 (Finset.mem_powerset.1 hU)))]
    rw [if_neg (fun h => hiT (by rw [h]; exact Finset.mem_insert_self i S))]

theorem pair_J_prod_rootSum : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  intro F _ _ θ m e ε h1 N h2 L
  induction L with
  | nil =>
    intro T _ _ _ hT n hn
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by simpa using hT)
    subst hT0
    simp only [List.length_nil, mul_zero] at hn
    subst hn
    haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Unique (GL (Fin 0) F) := ⟨⟨1⟩, fun a => Subsingleton.elim _ _⟩
    simp [J_nil, chG, finsum_unique]
  | cons i L ih =>
    intro T hnd hLN hTN hT n hn
    haveI : Fintype F := Fintype.ofFinite F
    have hiS : i ∉ L.toFinset := by simpa using (List.nodup_cons.1 hnd).1
    have hnd' : L.Nodup := (List.nodup_cons.1 hnd).2
    have hb := deg_map_const_fst m e L
    have hn' : n = m + deg (L.map fun i => (m, e i)) := by rw [hn, hb, List.length_cons]; ring
    have hmass := GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction F m (deg (L.map fun i => (m, e i))) n hn' (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i)))) (fun P => ∏ j ∈ T, rootSum θ (e j) P)
    have hs := pair_prod_split (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))))
      (fun j => rootSum θ (e j)) (fun j => (rootSum_isAdditive_and_pow_X_sub_one F θ (e j)).1) T
    have hiN : i < N := hLN i (List.mem_cons_self ..)
    have hsum := sum_powerset_single i L.toFinset T hiS
      (by rw [List.toFinset_card_of_nodup hnd']; simpa using hT)
      (fun U => ∑ᶠ x : GL (Fin m) F, cusp θ m (e i) x *
        star (∏ j ∈ U, rootSum θ (e j) (Matrix.charpoly (x : Matrix (Fin m) (Fin m) F))))
      (fun U => ∑ᶠ y : GL (Fin (deg (L.map fun i => (m, e i)))) F,
        J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))) y *
          star (chG (fun P => ∏ j ∈ T \ U, rootSum θ (e j) P) (deg (L.map fun i => (m, e i))) y))
      ((ε : ℂ) * Nat.card (GL (Fin m) F))
      ((ε : ℂ) ^ L.length * Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F))
      (by simpa using h1 i)
      (fun j hj => by simpa [chG] using h2 i j hiN (hTN j hj))
      (fun U hU hU0 => by
        have hsub := Finset.mem_powerset.1 hU
        have hc := Finset.card_sdiff_add_card_eq_card hsub
        have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hU0)
        simp only [List.length_cons] at hT
        exact ih (T \ U) hnd' (fun k hk => hLN k (List.mem_cons_of_mem _ hk))
          (fun k hk => hTN k (Finset.mem_sdiff.1 hk).1) (by omega) _ hb)
    beta_reduce at hmass hs hsum
    rw [hs, hsum] at hmass
    have hG : ((Nat.card (GL (Fin m) F) : ℂ) *
        (Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F) : ℂ)) ≠ 0 := by
      apply mul_ne_zero <;> exact_mod_cast Nat.card_pos.ne'
    apply mul_left_cancel₀ hG
    refine hmass.trans ?_
    rw [List.toFinset_cons, List.length_cons]
    split_ifs <;> ring

end GlobalTheory.Shin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem perCl_injective (K : Charts F) (hK : K.Rich) (per per' : Λ →+ Hol F.V)
    (h : K.perCl per = K.perCl per') : per = per' := by
  obtain ⟨G, hG⟩ := (H1.mk_eq_mk (F := K.Oc)).1 h

  have hd : ∀ (T T' : K.Obj) (φ : T ⟶ T'), G T' - φ.φ (G T) =
      algebraMap (Hol F.V) T'.C (per φ.deg) - algebraMap (Hol F.V) T'.C (per' φ.deg) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hG T) T') φ
    exact this

  have h0 : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T) := by
    intro T T' φ hφ
    have := hd T T' φ
    simp only [hφ, map_zero, sub_zero] at this
    exact sub_eq_zero.1 this
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible K hK G h0

  have hv : ∀ (T T' : K.Obj) (φ : T ⟶ T'), algebraMap (Hol F.V) T'.C (per φ.deg - per' φ.deg) = 0 := by
    intro T T' φ
    have := hd T T' φ
    rw [hp T, hp T', AlgHom.commutes, sub_self] at this
    exact ((algebraMap (Hol F.V) T'.C).map_sub (per φ.deg) (per' φ.deg)).trans this.symm
  ext l : 1
  rw [← sub_eq_zero]
  refine _root_.GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable K hK l 0 (per l - per' l) fun k k' k'' e e' ↦ ?_
  have h1 : K.cst k' (per l - per' l) = 0 := hv _ _ (ptHom (K.triv k') e)
  rw [← sh_cst e' (per l - per' l), h1, map_zero]

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffEl
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredElements

theorem preservesFilteredColimits_modules_iff_elements :
    ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  intro Λ _ N
  have hP : PreservesColimitsOfSize.{0, 0} (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 1, 0, 0} Λ
  have h1 : PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) := by
    constructor
    · intro h
      exact comp_preservesFilteredColimits N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
    · intro h
      constructor
      intro J _ _
      have hR : ReflectsColimitsOfShape J (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
        ModuleCat.reflectsColimitsOfShape.{1, 1, 0, 0} Λ J
      constructor
      intro K
      exact preservesColimit_of_reflects_of_preserves N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
  refine ⟨h1, ?_⟩
  rw [h1, GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements]
  rfl

end GlobalTheory.EtC.FilteredElements
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def pbfMap (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (n i : ℤ)
    (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) : Ht q (pullback V (PGL.pr N)) n i :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def PBF (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Prop :=
  ∀ n i : ℤ, Function.Bijective (pbfMap q V n i)

theorem projectiveBundleFormula_of_unitOnEtalePoints (h : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V) : D1 :=
  fun q _ _ _ V hq n i => h q V hq n i

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopology
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem quadExt_topology : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ), FiniteDimensional F E ∧ IsTopologicalRing E ∧ ContinuousInv₀ E ∧ T2Space E ∧ Continuous c ∧ Continuous (Algebra.norm F : E → F) ∧ Continuous (Algebra.trace F E) ∧ ∀ (α ν : Type) [Fintype α] [Fintype ν], IsModuleTopology F (Matrix α ν E) ∧ Good (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE
  obtain ⟨b, -, -⟩ := hE.basis
  haveI hfd : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing F E
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have htr : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)
  have hN : ∀ z : E, Algebra.norm F z = (2 : F)⁻¹ * Algebra.trace F E (z * c z) := by
    intro z
    rw [← hE.algebraMap_norm z, Algebra.trace_algebraMap, Module.finrank_eq_card_basis b, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hNc : Continuous (Algebra.norm F : E → F) := by
    have : (Algebra.norm F : E → F) = fun z => (2 : F)⁻¹ * Algebra.trace F E (z * c z) := funext hN
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_id.mul hc))
  have hT2 : T2Space E := (_root_.GlobalTheory.KSp.good_of_finiteDimensional F E).t2
  have hinv : ∀ z : E, z⁻¹ = (Algebra.norm F z)⁻¹ • c z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [Algebra.smul_def, mul_assoc, mul_comm (c z) z, ← hE.algebraMap_norm z, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hI : ContinuousInv₀ E := by
    refine ⟨fun z hz => ?_⟩
    have : (Inv.inv : E → E) = fun z => (Algebra.norm F z)⁻¹ • c z := funext hinv
    rw [this]
    have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
    exact ((continuousAt_inv₀ hn).comp hNc.continuousAt).smul hc.continuousAt
  refine ⟨hfd, inferInstance, hI, hT2, hc, hNc, htr, fun α ν _ _ => ?_⟩
  haveI hM : IsModuleTopology F (Matrix α ν E) := inferInstanceAs (IsModuleTopology F (α → ν → E))
  exact ⟨hM, _root_.GlobalTheory.KSp.good_of_finiteDimensional F (Matrix α ν E)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompatStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_operators_heisenberg_compat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  first | exact @GlobalTheory.KSp.heisFun_parFun | exact GlobalTheory.KSp.heisFun_parFun | (intros; apply GlobalTheory.KSp.heisFun_parFun <;> assumption)
end

