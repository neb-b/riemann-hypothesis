module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTate
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCoindIntertwinerOfDoubleCoset
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

theorem exists_ne_zero_intertwiningMap_coind_of_doubleCoset :
    ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V') (x : G) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : P) (p' : P'), (p' : G) * x = x * (p : G) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∃ Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ'), Φ ≠ 0 := by
  intro G _ _ P P' V V' _ _ _ _ σ σ' x T hT h
  classical
  haveI : Fintype P' := Fintype.ofFinite _
  let L : Representation.coindV P.subtype σ →ₗ[ℂ] Representation.coindV P'.subtype σ' :=
    { toFun := fun f => ⟨fun y => ∑ p' : P', σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y))), by
        intro q y
        beta_reduce
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft q)
          (fun p' : P' => σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * (P'.subtype q * y)))))]
        refine Finset.sum_congr rfl fun p' _ => ?_
        simp [mul_assoc]⟩
      map_add' := fun f g => by
        ext y
        simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by
        ext y
        simp [Finset.smul_sum] }
  have hL : ∀ f y, (L f).1 y = ∑ p' : P', σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y))) :=
    fun _ _ => rfl
  refine ⟨⟨L, fun g => ?_⟩, fun h0 => ?_⟩
  · ext f y
    change (L (Representation.coind P.subtype σ g f)).1 y = (L f).1 (y * g)
    rw [hL, hL]
    refine Finset.sum_congr rfl fun p' _ => ?_
    change σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y * g))) = _
    rw [mul_assoc _ y g]
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hT (LinearMap.ext hc)
    let δ : Representation.coindV P.subtype σ :=
      ⟨fun y => if hy : y ∈ P then σ ⟨y, hy⟩ v else 0, by
        intro q y
        by_cases hy : y ∈ P
        · have hqy : P.subtype q * y ∈ P := P.mul_mem q.2 hy
          simp only [dif_pos hy, dif_pos hqy]
          rw [← Module.End.mul_apply, ← map_mul]
          rfl
        · have hqy : P.subtype q * y ∉ P := fun hh => hy ((P.mul_mem_cancel_left q.2).1 hh)
          simp only [dif_neg hy, dif_neg hqy, map_zero]⟩
    have hL0 : L = 0 := congrArg Representation.IntertwiningMap.toLinearMap h0
    have h1 : (L δ).1 x = 0 := by rw [hL0]; rfl
    have h2 : ∀ p' : P', σ' p' (T (δ.1 (x⁻¹ * (p' : G)⁻¹ * x))) =
        if x⁻¹ * (p' : G)⁻¹ * x ∈ P then T v else 0 := by
      intro p'
      by_cases hp : x⁻¹ * (p' : G)⁻¹ * x ∈ P
      · have hδ : δ.1 (x⁻¹ * (p' : G)⁻¹ * x) = σ ⟨_, hp⟩ v := dif_pos hp
        have := LinearMap.congr_fun (h ⟨_, hp⟩ p'⁻¹ (by simp [mul_assoc])) v
        simp only [LinearMap.comp_apply] at this
        rw [hδ, if_pos hp, ← this, ← Module.End.mul_apply, ← map_mul]
        simp
      · have hδ : δ.1 (x⁻¹ * (p' : G)⁻¹ * x) = 0 := dif_neg hp
        rw [hδ, if_neg hp]
        simp
    rw [hL, Finset.sum_congr rfl fun p' _ => h2 p', ← Finset.sum_filter, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have : (1 : P') ∈ Finset.univ.filter fun p' : P' => x⁻¹ * (p' : G)⁻¹ * x ∈ P := by
        simp [P.one_mem]
      exact (Finset.card_pos.2 ⟨_, this⟩).ne' (Nat.cast_eq_zero.1 h1)
    · exact hv h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIntertwiningOfCommutingIsotypicFacto
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicFactors

open Representation Module

section One

variable {H W V : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

theorem finiteDimensional_of_isotypic [FiniteDimensional ℂ V] [Nontrivial V]
    (τ : Representation ℂ H V) (ρ : Representation ℂ H W) (hρ : ρ.IsIrreducible)
    (h : IsIsotypicOf τ ρ) : FiniteDimensional ℂ W := by
  have : ∃ g : IntertwiningMap ρ τ, g ≠ 0 := by
    by_contra hc
    push Not at hc
    have : (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) = ⊥ := by
      refine iSup_eq_bot.2 fun f => ?_
      rw [hc f]
      exact LinearMap.range_eq_bot.2 rfl
    exact bot_ne_top (this.symm.trans h)
  obtain ⟨g, hg⟩ := this
  have hi := (IsIrreducible.injective_or_eq_zero g).resolve_right hg
  exact FiniteDimensional.of_injective g.toLinearMap hi

theorem classSum_scalar [Fintype H] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W)
    (hρ : ρ.IsIrreducible) (h : H) : ∃ s : ℂ, ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w := by
  have hT : ∀ g v, (∑ k, ρ (k * h * k⁻¹)) (ρ g v) = ρ g ((∑ k, ρ (k * h * k⁻¹)) v) := by
    intro g v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
    ((∑ k, ρ (k * h * k⁻¹)).intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun f : IntertwiningMap ρ ρ => f v) hc
  simpa using this.symm

theorem classSum_of_isotypic [Fintype H] (τ : Representation ℂ H V) (ρ : Representation ℂ H W)
    (hi : IsIsotypicOf τ ρ) (h : H) (s : ℂ) (hs : ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w) :
    (∑ k, τ (k * h * k⁻¹)) = s • (1 : Module.End ℂ V) := by
  have : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (∑ k, τ (k * h * k⁻¹)) (s • (1 : Module.End ℂ V)) := by
    rw [← (show _ = ⊤ from hi)]
    refine iSup_le fun f => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_eqLocus]
    have e := congrArg f.toLinearMap (hs w)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum, map_smul] at e
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply, ← e]
    exact Finset.sum_congr rfl fun k _ => (f.isIntertwining _ _ _ w).symm
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem card_mul_character {M : Type} [Group M] [Fintype H] (τ : Representation ℂ M V) (f : H →* M)
    (h : H) (s : ℂ) (hs : (∑ k, τ (f (k * h * k⁻¹))) = s • (1 : Module.End ℂ V)) (a : M)
    (ha : ∀ k, Commute (f k) a) :
    (Fintype.card H : ℂ) * τ.character (f h * a) = s * τ.character a := by
  have e := congrArg (fun T => LinearMap.trace ℂ V (T * τ a)) hs
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul] at e
  have e2 : ∀ k, LinearMap.trace ℂ V (τ (f (k * h * k⁻¹)) * τ a) = τ.character (f h * a) := by
    intro k
    rw [← map_mul, ← char_conj τ (f h * a) (f k)]
    have : f (k * h * k⁻¹) * a = f k * (f h * a) * (f k)⁻¹ := by
      rw [map_mul, map_mul, mul_assoc, (ha k⁻¹).eq, map_inv]
      simp only [mul_assoc]
    rw [this]
    rfl
  simp only [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e
  exact e

end One

theorem exists_ne_zero {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    [Nontrivial W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ g, (finrank ℂ W : ℂ) * ρ.character g = (finrank ℂ V : ℂ) * σ.character g) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h4 : (finrank ℂ W : ℂ) * finrank ℂ (IntertwiningMap ρ ρ)
      = (finrank ℂ V : ℂ) * finrank ℂ (IntertwiningMap ρ σ) := by
    rw [← h1, ← h2, mul_left_comm, mul_left_comm (finrank ℂ V : ℂ),
      Finset.mul_sum _ _ (finrank ℂ V : ℂ), Finset.mul_sum _ _ (finrank ℂ W : ℂ)]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, ← mul_assoc, h]
  have : Nontrivial (IntertwiningMap ρ ρ) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨IntertwiningMap.id ρ, 0, fun e => hv (congrArg (fun f : IntertwiningMap ρ ρ => f v) e)⟩⟩
  have h5 : finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ)
      = finrank ℂ V * finrank ℂ (IntertwiningMap ρ σ) := by exact_mod_cast h4
  have h3 : 0 < finrank ℂ (IntertwiningMap ρ σ) := by
    have : 0 < finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ) :=
      Nat.mul_pos Module.finrank_pos Module.finrank_pos
    rw [h5] at this
    exact Nat.pos_of_mul_pos_left this
  have := Module.nontrivial_of_finrank_pos h3
  exact exists_ne 0

theorem exists_intertwining_ne_zero : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  intro M _ _ ι _ H _ _ f htop hcomm W _ _ ρ hρ V V' _ _ _ _ _ _ _ _ τ τ' hτ hτ'
  classical
  have := Fintype.ofFinite ι
  have hcomm' : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (f i x) (f j y) :=
    fun i j hij => hcomm i j hij
  refine exists_ne_zero τ τ' fun m => ?_
  obtain ⟨h, rfl⟩ : m ∈ (MonoidHom.noncommPiCoprod f hcomm').range := by
    rw [MonoidHom.noncommPiCoprod_range, htop]
    exact Subgroup.mem_top m
  have key : ∀ (S : Finset ι) (comm : (S : Set ι).Pairwise (Function.onFun Commute fun i => f i (h i))),
      (finrank ℂ V' : ℂ) * τ.character (S.noncommProd (fun i => f i (h i)) comm)
        = (finrank ℂ V : ℂ) * τ'.character (S.noncommProd (fun i => f i (h i)) comm) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro comm; simp [mul_comm]
    | insert c S hc ih =>
      intro comm
      have := Fintype.ofFinite (H c)
      have := finiteDimensional_of_isotypic _ _ (hρ c) (hτ c)
      obtain ⟨s, hs⟩ := classSum_scalar (ρ c) (hρ c) (h c)
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hc]
      have ha : ∀ comm k, Commute (f c k) (S.noncommProd (fun i => f i (h i)) comm) := fun comm k =>
        Finset.noncommProd_commute _ _ _ _ fun i hi => hcomm c i (fun e => hc (e ▸ hi)) _ _
      have hcard : (Fintype.card (H c) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      refine mul_left_cancel₀ hcard ?_
      rw [mul_left_comm, card_mul_character τ (f c) (h c) s (classSum_of_isotypic _ _ (hτ c) _ _ hs) _ (ha _),
        mul_left_comm (Fintype.card (H c) : ℂ),
        card_mul_character τ' (f c) (h c) s (classSum_of_isotypic _ _ (hτ' c) _ _ hs) _ (ha _),
        mul_left_comm, ih, mul_left_comm]
  exact key Finset.univ fun _ _ _ _ hij => hcomm' hij _ _

end GlobalTheory.IsotypicFactors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.Bruhat

theorem exists_perm_rep_blockTri : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  intro F _ r b b' hb hb' g
  have hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ := F) c := by
    intro c hc u hu
    rw [mem_blockTri]
    intro i j hij
    exact unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  have hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero
  let d : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F) := rfl
  have hd : d ∈ blockTri (κ := F) b := by
    rw [mem_blockTri]
    intro i j hij
    rw [hdv]
    exact Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
  have hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F) := by
    ext a c
    rw [hdv, Matrix.mul_diagonal, permGL_apply]
    by_cases e : a = m.1 c <;> simp [mono, e]
  refine ⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩
  rw [h, hm]
  simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FinGL.Bruhat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfBlockSizeBijection
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

theorem exists_perm_of_block_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  classical
  intro r b b' R h1 h2 h3
  have h1' : ∀ i : Fin r, ∃ c', c' ∈ Set.range b' ∧ R (b i) c' :=
    fun i => (h1 (b i) ⟨i, rfl⟩).exists
  choose f hf1 hf2 using h1'
  have hiff : ∀ i c c', c ∈ Set.range b → c' ∈ Set.range b' → R c c' → (f i = c' ↔ b i = c) := by
    intro i c c' hc hc' hR
    constructor
    · intro h
      exact (h2 c' hc').unique ⟨⟨i, rfl⟩, h ▸ hf2 i⟩ ⟨hc, hR⟩
    · intro h
      subst h
      exact (h1 (b i) hc).unique ⟨hf1 i, hf2 i⟩ ⟨hc', hR⟩
  have hcard : ∀ c' : ℕ, Fintype.card {i // f i = c'} = Fintype.card {i // b' i = c'} := by
    intro c'
    rw [Fintype.card_subtype, Fintype.card_subtype]
    by_cases hc' : c' ∈ Set.range b'
    · obtain ⟨c, hc, hR⟩ := (h2 c' hc').exists
      have h := h3 c hc c' hc' hR
      unfold block at h
      rw [← h]
      congr 1
      ext i
      simp [hiff i c c' hc hc' hR]
    · rw [Finset.filter_eq_empty_iff.2, Finset.filter_eq_empty_iff.2]
      · intro i _ h
        exact hc' ⟨i, h⟩
      · intro i _ h
        exact hc' (h ▸ hf1 i)
  let e : ∀ c' : ℕ, {i // f i = c'} ≃ {i // b' i = c'} := fun c' => Fintype.equivOfCardEq (hcard c')
  have hw : ∀ i, b' (Equiv.ofFiberEquiv e i) = f i := fun i => Equiv.ofFiberEquiv_map e i
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_, fun i j => ?_⟩
  · rw [hw]; exact hf2 i
  · rw [hw, hw]
    exact (hiff i (b j) (f j) ⟨j, rfl⟩ (hf1 j) (hf2 j)).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsApproxFirstJetsPositive
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem jets_approx_sections_of_positive : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ q : Y → V n → ℂ, (∀ P ∈ T, Differentiable ℂ (q P)) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + (G + k • H)) F ∧ ∀ P ∈ T, ‖F (A.pick P) P * Complex.exp (-(k * q P (A.chart (A.pick P) P))) - p P (A.chart (A.pick P) P)‖ ≤ ε ∧ ‖fderiv ℂ (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) (A.chart (A.pick P) P)‖ ≤ ε := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T
  obtain ⟨C⟩ := _root_.GlobalTheory.OTY.nonempty_cover n Y ι La A
  obtain ⟨q, c, Cq, r0, hc, hr0, hqT, hrest⟩ := _root_.GlobalTheory.OTY.peak_sections_finite n Y ι La A C H hH T
  refine ⟨q, fun P hP => (hqT P hP).1, ?_⟩
  intro G p hp ε hε
  obtain ⟨K', t0, hK', hk6⟩ := _root_.GlobalTheory.rough_hormander_compact n Y ι La A C
  obtain ⟨k1, hk1⟩ := _root_.GlobalTheory.OTY.CoverCurv.curv_cover n Y ι La A C H G hH t0
  obtain ⟨K, hK, hF0⟩ := hrest G p hp
  have hloc : ∀ P : Y, ∃ k0 : ℕ, P ∈ T → ∀ k ≥ k0, ∀ D : ι → Y → ℂ,
      A.IsSSec (A.kap + (G + k • H)) D →
      DifferentiableOn ℂ (D (A.pick P) ∘ (A.chart (A.pick P)).symm) (ball (A.chart (A.pick P) P) r0) →
      n0 A (G + k • H) D ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) →
      ‖D (A.pick P) ((A.chart (A.pick P)).symm (A.chart (A.pick P) P)) *
          Complex.exp (-(k * q P (A.chart (A.pick P) P)))‖ ≤ ε ∧
      ‖fderiv ℂ (fun v => D (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)))
          (A.chart (A.pick P) P)‖ ≤ ε := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k0, hk0⟩ := _root_.GlobalTheory.JetSmall.main n Y ι La A H G (A.pick P) (A.chart (A.pick P) P) r0 c Cq
        (K' * K) (q P) hr0 hc (hqT P hP).2.1 (hqT P hP).1 (hqT P hP).2.2 ε hε
      exact ⟨k0, fun _ => hk0⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose k0 hk0 using hloc
  refine ⟨max k1 (T.sup k0), fun k hk => ?_⟩
  have hk1' : k1 ≤ k := le_trans (le_max_left _ _) hk
  obtain ⟨F0, hF0s, hF0b, hF0n⟩ := hF0 k
  obtain ⟨F, hFs, hFn⟩ := hk6 (G + k • H) t0 le_rfl (hk1 k hk1') F0 hF0s
  refine ⟨F, hFs, fun P hP => ?_⟩
  have hkP : k0 P ≤ k := le_trans (le_trans (Finset.le_sup hP) (le_max_right _ _)) hk
  have hDs : A.IsSSec (A.kap + (G + k • H)) (F0 - F) := by
    refine ⟨fun j => ?_, fun a b y ha hb => ?_⟩
    · have hd : DifferentiableOn ℂ (F j ∘ (A.chart j).symm) (A.chart j).target :=
        (hFs.1 j).mono fun _ hv => ⟨hv, trivial⟩
      have hF' : ContDiffOn ℝ ∞ (F j ∘ (A.chart j).symm) (A.chart j).target := fun v hv =>
        (hyq_contDiffAt_of_holo (A.chart j).open_target hd hv).contDiffWithinAt
      exact (hF0s.1 j).sub hF'
    · simp only [Pi.sub_apply]
      rw [hF0s.2 a b y ha hb, hFs.2 a b y trivial ha hb]
      ring
  have hb : ball (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target :=
    ball_subset_closedBall.trans (hqT P hP).2.1
  have hDd : DifferentiableOn ℂ ((F0 - F) (A.pick P) ∘ (A.chart (A.pick P)).symm)
      (ball (A.chart (A.pick P) P) r0) := by
    have hg : DifferentiableOn ℂ (fun v => p P v * Complex.exp (k * q P v) -
        F (A.pick P) ((A.chart (A.pick P)).symm v)) (ball (A.chart (A.pick P) P) r0) := by
      refine DifferentiableOn.sub ?_ ?_
      · exact ((hp P).mul (((hqT P hP).1.const_mul _).cexp)).differentiableOn
      · exact (hFs.1 (A.pick P)).mono fun v hv => ⟨hb hv, trivial⟩
    refine hg.congr fun v hv => ?_
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [hF0b P hP v hv]
  have hDn : n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) := by
    calc n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal K' * n1 C (G + k • H) F0 := hFn
      _ ≤ ENNReal.ofReal K' * ENNReal.ofReal (K * Real.exp (-c * k)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hK', mul_assoc]
  obtain ⟨h1, h2⟩ := hk0 P hP k hkP (F0 - F) hDs hDd hDn
  have key : ∀ v ∈ ball (A.chart (A.pick P) P) r0,
      F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v =
        -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
    intro v hv
    have h0 := hF0b P hP v hv
    have hE : Complex.exp (k * q P v) * Complex.exp (-(k * q P v)) = 1 := by
      rw [← Complex.exp_add]; simp
    simp only [Pi.sub_apply]
    rw [h0]
    linear_combination p P v * hE
  have hPx : (A.chart (A.pick P)).symm (A.chart (A.pick P) P) = P :=
    (A.chart (A.pick P)).left_inv (A.mem_pick P)
  have hx : A.chart (A.pick P) P ∈ ball (A.chart (A.pick P) P) r0 := mem_ball_self hr0
  refine ⟨?_, ?_⟩
  · have h3 := key _ hx
    rw [hPx] at h3 h1
    rw [h3, norm_neg]
    exact h1
  · have hev : (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v)
        =ᶠ[𝓝 (A.chart (A.pick P) P)]
        fun v => -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with v hv using key v hv
    rw [hev.fderiv_eq, fderiv_fun_neg, norm_neg]
    exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationClosedChartsSubordinateToCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_affine_le_of_cover {X : Scheme.{0}} {N : Type} (𝒰 : N → X.Opens) (h𝒰 : ⨆ i, 𝒰 i = ⊤) (e : Sp ℂ ⟶ X) :
    ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ⊤ ≤ e ⁻¹ᵁ U := by
  have pt : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have h1 : e pt ∈ ⨆ i, 𝒰 i := by rw [h𝒰]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h1
  obtain ⟨U, hU, hx, hle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hi
  refine ⟨i, U, hU, hle, fun y _ ↦ ?_⟩
  obtain rfl : y = pt := Subsingleton.elim _ _
  exact hx

theorem exists_charts_subordinate : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k) := by
  intro I _ g Λ _ F B _ X s σ u hX N 𝒰 h𝒰
  let Q : Opens (Tot I g) → Prop := fun W ↦ ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U
  obtain ⟨r, hr, hx⟩ := _root_.GlobalTheory.AnPer.exists_real_isFor u hX (Charts.std F Q) fun k ↦ by
    obtain ⟨i, U, h1, -, h3⟩ := k.2.2
    exact ⟨U, h1, h3⟩
  refine ⟨Charts.std F Q, r, fun k ↦ k.2.2.choose, ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩, fun l k' ↦ ?_, hr,
    fun k ↦ ?_⟩
  · obtain ⟨i, U, hU, hle, hp'⟩ := exists_affine_le_of_cover 𝒰 h𝒰 (u.E p)
    exact ⟨⟨⟨_, (u.hol U 0).1⟩, fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ hq.2⟩, hp, hp'⟩
  · have hc : ContinuousOn (F.shift l) (k₁.1 : Set (Tot I g)) := (F.shift_analytic l k₁.2.1).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k₁.2.2
    refine ⟨⟨⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' k₂.1, hc.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩,
      fun q hq ↦ k₁.2.1 q hq.1, i, U, hU, hle, fun q hq ↦ hW q hq.1⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]; exact hq.1
  · have hc : ContinuousOn (F.shift (-l)) (F.tot : Set (Tot I g)) := (F.shift_analytic (-l) fun _ h ↦ h).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k'.2.2
    refine ⟨⟨⟨(F.tot : Set (Tot I g)) ∩ F.shift (-l) ⁻¹' k'.1, hc.isOpen_inter_preimage F.tot.isOpen k'.1.isOpen⟩,
      fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ ?_⟩, fun q hq ↦ ⟨k'.2.1 q hq, ?_⟩, fun q hq ↦ hq.2⟩
    · rw [← u.per (-l) q hq.1]
      exact hW _ hq.2
    · change F.shift (-l) (F.shift l q) ∈ k'.1
      rwa [← F.shift_add, neg_add_cancel, F.shift_zero]
  · obtain ⟨U, hU, hle, hW⟩ := k.2.2.choose_spec
    exact fun y hy ↦ hle (hx k U hU hW hy)

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTateStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (hodgeTate G t)) := by
  first | exact @GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | exact GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | (intros; apply GlobalTheory.QLogPeriod.hasPeriod_hodgeTate <;> assumption)
end

