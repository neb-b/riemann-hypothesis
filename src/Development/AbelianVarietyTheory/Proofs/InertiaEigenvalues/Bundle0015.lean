module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentModPrimeOfPowLeCard
section
open Polynomial

namespace GlobalTheory

theorem exists_linearIndependent_of_pow_le_card_zmod (l : ℕ) [Fact l.Prime] {Q ι : Type} [AddCommGroup Q] [Module (ZMod l) Q]
    (Z : Finset ι) (w : ι → Q) (hinj : Set.InjOn w Z) (h : ℕ) (hcard : l ^ h ≤ Z.card) :
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ LinearIndependent (ZMod l) (fun a => w (x a)) := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hs : (Z.image w).card = Z.card := Finset.card_image_of_injOn hinj
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod l) ((Z.image w : Finset Q) : Set Q)
  have hbfin : b.Finite := (Finset.finite_toSet _).subset hbs
  haveI : Fintype b := hbfin.fintype
  have hrange : ∀ y ∈ Z.image w, ∃ f : b → ZMod l, ∑ c, f c • (c : Q) = y := by
    intro y hy
    have hy' : y ∈ Submodule.span (ZMod l) b := by
      rw [hspan]; exact Submodule.subset_span (by exact_mod_cast hy)
    rw [← Subtype.range_coe (s := b)] at hy'
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod l)).1 hy'
  have hle : (Z.image w).card ≤ l ^ Fintype.card b := by
    have h3 : (Z.image w).card ≤ (Finset.univ.image (fun f : b → ZMod l => ∑ c, f c • (c : Q))).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨f, hf⟩ := hrange y hy
      exact Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩
    calc _ ≤ _ := h3
      _ ≤ (Finset.univ : Finset (b → ZMod l)).card := Finset.card_image_le
      _ = l ^ Fintype.card b := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
  have hhb : h ≤ Fintype.card b := by
    have : l ^ h ≤ l ^ Fintype.card b := hcard.trans (hs ▸ hle)
    exact (Nat.pow_le_pow_iff_right hl1).1 this
  let e : Fin h ↪ b := (Fin.castLEEmb hhb).trans (Fintype.equivFin b).symm.toEmbedding
  have hpre : ∀ c : b, ∃ i ∈ Z, w i = c := fun c => Finset.mem_image.1 (hbs c.2)
  choose g hgZ hgw using hpre
  refine ⟨fun a => g (e a), fun a => hgZ _, ?_⟩
  have hli' : LinearIndependent (ZMod l) (fun a => ((e a : b) : Q)) := hli.comp e e.injective
  convert hli' using 1
  funext a
  exact hgw (e a)

theorem ph_a_basis : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ)
    (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card →
    (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') →
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  intro l _ V ι _ K' h Z v hl hcard hdist
  have hQ : ∀ y : V ⧸ K', l • y = 0 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => rw [← QuotientAddGroup.mk_nsmul, hl z]; rfl
  letI : Module (ZMod l) (V ⧸ K') := AddCommGroup.zmodModule hQ
  have hinj : Set.InjOn (fun i => (v i : V ⧸ K')) Z := by
    intro i hi i' hi' he
    by_contra hne
    exact hdist i hi i' hi' hne ((QuotientAddGroup.eq_iff_sub_mem).1 he)
  obtain ⟨x, hxZ, hli⟩ := exists_linearIndependent_of_pow_le_card_zmod l Z (fun i => (v i : V ⧸ K')) hinj h hcard
  refine ⟨x, hxZ, ?_⟩
  intro n hn a
  have hm : QuotientAddGroup.mk' K' (∑ a, n a • v (x a)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 hn
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hm
  simp only [map_nsmul, QuotientAddGroup.mk'_apply] at hm
  have hsum : ∑ a, (n a : ZMod l) • ((v (x a) : V ⧸ K')) = 0 := by
    rw [← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
  have hz := Fintype.linearIndependent_iff.1 hli (fun a => (n a : ZMod l)) hsum a
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFactorOfIdempotentSubfield
section
namespace GlobalTheory

private theorem cur_decomposition_of_maximal_minor {K : Type} [Field K] {d r : ℕ} (e : Matrix (Fin d) (Fin d) K)
    (τ σ : Fin r → Fin d) (hA : (e.submatrix τ σ).det ≠ 0)
    (hmax : ∀ τ' σ' : Fin (r + 1) → Fin d, (e.submatrix τ' σ').det = 0) :
    e.submatrix id σ * (e.submatrix τ σ)⁻¹ * e.submatrix τ id = e := by
  ext i j
  set A := e.submatrix τ σ with hAdef
  let B : Matrix (Fin r) (Fin 1) K := Matrix.of fun k _ => e (τ k) j
  let C : Matrix (Fin 1) (Fin r) K := Matrix.of fun _ l => e i (σ l)
  let D : Matrix (Fin 1) (Fin 1) K := Matrix.of fun _ _ => e i j
  have hM : Matrix.fromBlocks A B C D =
      e.submatrix (Sum.elim τ fun _ => i) (Sum.elim σ fun _ => j) := by
    ext (a | a) (b | b) <;> rfl
  have h0 : (Matrix.fromBlocks A B C D).det = 0 := by
    rw [hM, ← Matrix.det_reindex_self finSumFinEquiv, Matrix.reindex_apply,
      Matrix.submatrix_submatrix]
    exact hmax _ _
  have : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv] at h0
  have h1 := (mul_eq_zero.mp h0).resolve_left hA
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  have h2 : (C * A⁻¹ * B) 0 0 = (e.submatrix id σ * A⁻¹ * e.submatrix τ id) i j := rfl
  rw [← h2, ← h1]
  rfl

private theorem inv_mul_submatrix_apply_eq_det_ratio {K : Type} [Field K] {d r : ℕ}
    (e : Matrix (Fin d) (Fin d) K) (τ σ : Fin r → Fin d) (k : Fin r) (j : Fin d) :
    ((e.submatrix τ σ)⁻¹ * e.submatrix τ id) k j =
      (e.submatrix τ σ).det⁻¹ * (e.submatrix τ (Function.update σ k j)).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (Matrix.mulVec (e.submatrix τ σ).adjugate fun l => e (τ l) j) k = _
  rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  congr 1
  ext a c
  by_cases h : c = k
  · subst h; simp
  · simp [h]

theorem exists_integral_factor_of_idempotent {K : Type} [Field K] (O : ValuationSubring K) (d : ℕ)
    (e : Matrix (Fin d) (Fin d) K) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) K) (S : Matrix (Fin d) (Fin r) K),
      (∀ i j, R i j ∈ O) ∧ (∀ i j, S i j ∈ O) ∧ R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  classical
  let P : ℕ → Prop := fun k => ∃ τ σ : Fin k → Fin d, (e.submatrix τ σ).det ≠ 0
  set r := Nat.findGreatest P d with hr
  have hPr : P r := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ⟨Fin.elim0, Fin.elim0, by simp⟩
  have hnot : ∀ τ σ : Fin (r + 1) → Fin d, (e.submatrix τ σ).det = 0 := by
    intro τ σ
    by_contra hne
    by_cases hle : r + 1 ≤ d
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hle ⟨τ, σ, hne⟩
    · obtain ⟨a, b, hab, hτ⟩ := Fintype.exists_ne_map_eq_of_card_lt τ (by simp; omega)
      exact hne (Matrix.det_zero_of_row_eq hab (by funext c; simp [hτ]))
  let v := O.valuation
  obtain ⟨τ0, σ0, h0⟩ := hPr
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin r → Fin d) × (Fin r → Fin d) => v (e.submatrix p.1 p.2).det)
    ⟨(τ0, σ0), Finset.mem_univ _⟩
  obtain ⟨τ, σ⟩ := p
  have hA : (e.submatrix τ σ).det ≠ 0 := by
    intro hz
    have hle := hp (τ0, σ0) (Finset.mem_univ _)
    simp only [hz, map_zero] at hle
    exact h0 ((Valuation.zero_iff _).mp (le_antisymm hle zero_le))
  have hv : v (e.submatrix τ σ).det ≠ 0 := (Valuation.ne_zero_iff _).mpr hA
  let S : Matrix (Fin d) (Fin r) K := Matrix.of fun i k => if i = σ k then 1 else 0
  have hS : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin d) K), M * S = M.submatrix id σ := by
    intro m _ M
    ext a k
    simp [S, Matrix.mul_apply]
  refine ⟨r, (e.submatrix τ σ)⁻¹ * e.submatrix τ id, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    rw [inv_mul_submatrix_apply_eq_det_ratio, ← O.valuation_le_one_iff, map_mul, map_inv₀]
    have hle := hp (τ, Function.update σ k j) (Finset.mem_univ _)
    calc (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ (Function.update σ k j)).det
        ≤ (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ σ).det := mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hv
  · intro i k
    simp only [S, Matrix.of_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_assoc, hS]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
  · rw [Matrix.mul_assoc]
    congr 1
    ext a c
    change (e * e) (τ a) c = e (τ a) c
    rw [he]
  · rw [hS, ← Matrix.mul_assoc]
    exact cur_decomposition_of_maximal_minor e τ σ hA hnot

theorem exists_integral_factor_of_idempotent_subfield (C : Type) [NormedField C]
    [IsUltrametricDist C] (F : Subfield C) (d : ℕ) (e : Matrix (Fin d) (Fin d) C)
    (hF : ∀ i j, e i j ∈ F) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) C) (S : Matrix (Fin d) (Fin r) C),
      (∀ i j, R i j ∈ F ∧ ‖R i j‖ ≤ 1) ∧ (∀ i j, S i j ∈ F ∧ ‖S i j‖ ≤ 1) ∧
        R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  obtain ⟨e', rfl⟩ : ∃ e' : Matrix (Fin d) (Fin d) F, e'.map F.subtype = e :=
    ⟨Matrix.of fun i j => ⟨e i j, hF i j⟩, by ext; rfl⟩
  let O : ValuationSubring F :=
    { carrier := {x | ‖(x : C)‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_mul, norm_mul] at *
        calc ‖(a : C)‖ * ‖(b : C)‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha
      mem_or_inv_mem' := fun x => by
        rcases le_or_gt ‖(x : C)‖ 1 with h | h
        · exact Or.inl h
        · right
          change ‖((x⁻¹ : F) : C)‖ ≤ 1
          rw [Subfield.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ h.le }
  have hinj : Function.Injective (F.subtype : F → C) := Subtype.val_injective
  have he' : e' * e' = e' := Matrix.map_injective hinj (by
    change (e' * e').map F.subtype = e'.map F.subtype
    rw [Matrix.map_mul, he])
  obtain ⟨r, R, S, hR, hS, hRS, hRe, heSR⟩ := exists_integral_factor_of_idempotent O d e' he'
  refine ⟨r, R.map F.subtype, S.map F.subtype, fun i j => ⟨(R i j).2, hR i j⟩,
    fun i j => ⟨(S i j).2, hS i j⟩, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hRe]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, heSR]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntertwiningMapNeZeroOfIsotypicIrreducible
section
namespace GlobalTheory.IsoSep

open Representation

theorem main : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  intro H V W _ _ _ _ _ ρ σ hσ hsum hiso v hv
  haveI := hσ
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)

  have hatom : ∀ f : σ.IntertwiningMap ρ, f ≠ 0 → IsAtom f.range := by
    intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      apply hf
      ext w
      have hw : f w ∈ f.range := ⟨w, rfl⟩
      rw [h] at hw
      exact hw
    · intro U hU
      let U' : Subrepresentation σ := ⟨U.toSubmodule.comap f.toLinearMap, fun g w hw => by
        show f (σ g w) ∈ U.toSubmodule
        rw [f.isIntertwining]
        exact U.apply_mem_toSubmodule g hw⟩
      rcases eq_bot_or_eq_top U' with h | h
      · refine le_antisymm (fun x hx => ?_) bot_le
        obtain ⟨w, rfl⟩ := hU.le hx
        have hw : w ∈ U'.toSubmodule := hx
        rw [h] at hw
        have hw0 : w = 0 := (Submodule.mem_bot ℂ).1 hw
        show f w ∈ (⊥ : Submodule ℂ V)
        rw [hw0, map_zero]
        exact zero_mem _
      · exfalso
        refine hU.ne (le_antisymm hU.le ?_)
        rintro _ ⟨w, rfl⟩
        have hw : w ∈ U'.toSubmodule := by rw [h]; trivial
        exact hw

  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ρ.asModuleEquiv x ∈ (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) := by
      rw [hsum]; trivial
    have key := Submodule.iSup_induction _ (motive := fun y : V => ρ.asModuleEquiv.symm y ∈
      sSup {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule | IsSimpleModule (MonoidAlgebra ℂ H) m}) hx
      (fun f y hy => by
        by_cases hf : f = 0
        · subst hf
          obtain ⟨w, rfl⟩ := hy
          simp
        · refine le_sSup (a := e f.range) ?_ ?_
          · exact isSimpleModule_iff_isAtom.2 ((e.isAtom_iff _).2 (hatom f hf))
          · exact hy)
      (by simp) (fun a b ha hb => by simpa only [map_add] using add_mem ha hb)
    simpa using key

  let K : Submodule (MonoidAlgebra ℂ H) ρ.asModule := Submodule.span _ {ρ.asModuleEquiv.symm v}
  have hK : K ≠ ⊥ := by
    intro h
    apply hv
    have hm : ρ.asModuleEquiv.symm v ∈ K := Submodule.subset_span rfl
    rw [h, Submodule.mem_bot] at hm
    simpa using hm
  obtain ⟨N, hN, hNK⟩ := (eq_bot_or_exists_atom_le K).resolve_left hK
  obtain ⟨C, hC⟩ := exists_isCompl N
  let N' := e.symm N
  let C' := e.symm C
  have hC' : IsCompl N' C' := (e.isCompl_iff).2 (by
    simp only [N', C', OrderIso.apply_symm_apply]; exact hC)
  have hN' : IsAtom N' := (e.isAtom_iff N').1 (by simp only [N', OrderIso.apply_symm_apply]; exact hN)
  have hc : IsCompl N'.toSubmodule C'.toSubmodule := by
    constructor
    · rw [disjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.inf_eq_bot
    · rw [codisjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.sup_eq_top
  let P := Submodule.projectionOnto N'.toSubmodule C'.toSubmodule hc
  let τ := N'.toRepresentation
  let p : ρ.IntertwiningMap τ := ⟨P, fun g => LinearMap.ext fun x => by
    have hx : x ∈ N'.toSubmodule ⊔ C'.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : P (ρ g y) = ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩
    have h2 : P (ρ g z) = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨ρ g z, C'.apply_mem_toSubmodule g hz⟩
    have h3 : P y = ⟨y, hy⟩ := Submodule.projectionOnto_apply_left hc ⟨y, hy⟩
    have h4 : P z = 0 := Submodule.projectionOnto_apply_right hc ⟨z, hz⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, map_add (f := _), h1, h2, h3, h4, add_zero, map_zero]
    rfl⟩
  have hpv : p v ≠ 0 := by
    intro h0
    have hvC : v ∈ C'.toSubmodule := (Submodule.projectionOnto_apply_eq_zero_iff hc).1 h0
    have hKC : K ≤ C := by
      refine Submodule.span_le.2 ?_
      rintro _ rfl
      exact hvC
    have hNC : N ≤ N ⊓ C := le_inf le_rfl (hNK.trans hKC)
    rw [hC.inf_eq_bot] at hNC
    exact hN.1 (le_bot_iff.1 hNC)

  have hN'0 : N'.toSubmodule ≠ ⊥ := fun h => hN'.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'0
  have hτ : τ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · have hm : (⟨x0, hx0⟩ : N'.toSubmodule) ∈ (⊤ : Subrepresentation τ).toSubmodule := trivial
      rw [← h] at hm
      have : (⟨x0, hx0⟩ : N'.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 hm
      exact hx00 (congrArg Subtype.val this)
    · let U'' : Subrepresentation ρ := ⟨U.toSubmodule.map N'.toSubmodule.subtype, fun g x hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨τ g y, U.apply_mem_toSubmodule g hy, rfl⟩⟩
      have hle : U'' ≤ N' := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      rcases hN'.le_iff.1 hle with h | h
      · left
        refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun y hy => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := ⟨y, hy, rfl⟩
        rw [h] at hm
        have h0 : (y : V) = 0 := (Submodule.mem_bot ℂ).1 hm
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext h0)
      · right
        refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun y _ => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := by rw [h]; exact y.2
        obtain ⟨z, hz, hzy⟩ := hm
        have : z = y := Subtype.ext hzy
        rw [← this]
        exact hz
  let f' : τ.IntertwiningMap ρ := ⟨N'.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩
  have hf' : f' ≠ 0 := by
    intro h
    have := congrArg (fun q : τ.IntertwiningMap ρ => q ⟨x0, hx0⟩) h
    exact hx00 this
  obtain ⟨eqv⟩ := hiso _ τ hτ f' hf'
  refine ⟨eqv.symm.toIntertwiningMap.comp p, fun h => hpv ?_⟩
  have := congrArg eqv h
  simpa using this

end GlobalTheory.IsoSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantRightInverseField
section
namespace GlobalTheory.InvariantRightInverse

theorem exists_rightInverse_subfield {L : Type} [Field L] (K : Subfield L) {N b : Type}
    [Fintype N] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L)
    (h : κ * Y = 1) (hκ : ∀ i k, κ i k ∈ K) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ k j, Λ k j ∈ K := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (fun x y hxy => Subtype.ext hxy))
  have hπ' : ∀ x : K, π (x : L) = x := fun x => LinearMap.congr_fun hπ x
  refine ⟨Matrix.of fun k j => (π (Y k j) : L), ?_, fun k j => (π (Y k j)).2⟩
  ext i j
  have h1 : ∑ k, κ i k * Y k j = (1 : Matrix b b L) i j := by
    rw [← h, Matrix.mul_apply]
  have h2 : ∀ k, κ i k * (π (Y k j) : L) = (π (κ i k * Y k j) : L) := by
    intro k
    have := π.map_smul (⟨κ i k, hκ i k⟩ : K) (Y k j)
    have e : (⟨κ i k, hκ i k⟩ : K) • Y k j = κ i k * Y k j := rfl
    rw [e] at this
    rw [this]
    rfl
  have h3 : (1 : Matrix b b L) i j ∈ K := by
    rw [Matrix.one_apply]
    split_ifs
    · exact K.one_mem
    · exact K.zero_mem
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  calc ∑ k, κ i k * (π (Y k j) : L) = ∑ k, (π (κ i k * Y k j) : L) :=
        Finset.sum_congr rfl (fun k _ => h2 k)
    _ = ((∑ k, π (κ i k * Y k j) : K) : L) := by push_cast; rfl
    _ = (π (∑ k, κ i k * Y k j) : L) := by rw [map_sum]
    _ = (1 : Matrix b b L) i j := by
        rw [h1]
        exact congrArg Subtype.val (hπ' ⟨_, h3⟩)

theorem exists_invariant_rightInverse_field {L : Type} [Field L] (G : Type)
    (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq b]
    (κ : Matrix b N L) (Y : Matrix N b L) (h : κ * Y = 1)
    (hκ : ∀ g : G, Matrix.map κ (⇑(act g) : L → L) = κ) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g : G, Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  have hK : ∀ x : L, x ∈ (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) ↔
      ∀ g, act g x = x := by
    intro x
    rw [Subfield.mem_iInf]
    exact Iff.rfl
  obtain ⟨Λ, h1, h2⟩ := exists_rightInverse_subfield
    (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) κ Y h
    (fun i k => (hK _).2 (fun g => congrFun (congrFun (hκ g) i) k))
  refine ⟨Λ, h1, fun g => ?_⟩
  ext k j
  exact (hK _).1 (h2 k j) g

theorem exists_invariant_rightInverse :
    ∀ (L : Type) [inst : CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [inst_1 : Fintype N] [DecidableEq N] [Fintype b] [inst_4 : DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = (1 : Matrix b b L) → (∀ (g : G), Matrix.map κ (⇑(act g) : L → L) = κ) → ∃ (Λ : Matrix N b L), κ * Λ = (1 : Matrix b b L) ∧ ∀ (g : G), Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  intro L _ hL G act N b _ _ _ _ κ Y h hκ
  letI : Field L := hL.toField
  exact exists_invariant_rightInverse_field G act N b κ Y h hκ

end GlobalTheory.InvariantRightInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsComplOfSaturated
section
namespace GlobalTheory.SaturatedComplement

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (h : ∀ (a : O) (x : M), a ≠ (0 : O) → a • x ∈ N → x ∈ N) :
    ∃ C : Submodule O M, IsCompl N C := by
  have htf : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact h a x ha hq
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsec : ∀ q, N.mkQ (s q) = q := fun q => by
    simpa using LinearMap.congr_fun hs q
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxN ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply, hsec, sub_self]
    have := Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))
    simpa using this

end GlobalTheory.SaturatedComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitFamilyOfFiniteCoefficients
section
open scoped BigOperators

namespace GlobalTheory

theorem exists_limit_family_of_finite_coefficients (σ I R : Type) [Finite σ] [Finite I] [Finite R]
    (F : ℕ → I → (σ →₀ ℕ) → R) :
    ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧
      ∀ x m, m.degree ≤ N → F M x m = G x m := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩

  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → R, MapClusterPt G Filter.atTop F :=
    exists_clusterPt_of_compactSpace _
  refine ⟨G, fun N M₀ => ?_⟩

  have hnhds : ∀ᶠ H in nhds G, ∀ x, ∀ m ∈ {m : σ →₀ ℕ | m.degree ≤ N}, H x m = G x m := by
    refine Filter.eventually_all.2 fun x => ?_
    refine ((Finsupp.finite_of_degree_le N).eventually_all).2 fun m _ => ?_
    have hc : Continuous fun H : I → (σ →₀ ℕ) → R => H x m :=
      (continuous_apply m).comp (continuous_apply x)
    exact hc.continuousAt.eventually (isOpen_discrete {G x m} |>.mem_nhds rfl)
  obtain ⟨M, hM, hFM⟩ := Filter.frequently_atTop.1 (hG.frequently hnhds) M₀
  exact ⟨M, hM, fun x m hm => hFM x m hm⟩

end GlobalTheory
end

