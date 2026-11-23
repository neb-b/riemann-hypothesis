module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.Letters

theorem exists_emb_of_fixed {F E L : Type} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : Function.Bijective σ)
    (hfix : ∀ x, σ x = x → ∃ c : F, algebraMap F E c = x) (e : E →ₐ[F] L) :
    ∃ emb : ZMod (Module.finrank F E) → (E →ₐ[F] L),
      Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp σ = emb i := by
  classical
  let g : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hσ
  have hbot : IntermediateField.fixedField (Subgroup.zpowers g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.2 (hfix x (hx g (Subgroup.mem_zpowers g)))
  have hord : orderOf g = Module.finrank F E := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers g)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.symm
  haveI : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩
  let emb : ZMod (Module.finrank F E) → (E →ₐ[F] L) := fun i =>
    e.comp (g⁻¹ ^ i.val : E ≃ₐ[F] E).toAlgHom
  have hord' : orderOf g⁻¹ = Module.finrank F E := by rw [orderOf_inv, hord]
  have hinj : Function.Injective emb := by
    intro i j h
    have h1 : (g⁻¹ ^ i.val : E ≃ₐ[F] E) = g⁻¹ ^ j.val :=
      AlgEquiv.ext fun x => e.injective (DFunLike.congr_fun h x)
    rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at h1
    exact h1
  refine ⟨emb, ?_, fun i => ?_⟩
  · refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_zmod]
    exact card_algHom_le_finrank F E L
  · have h1 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) = g⁻¹ ^ (i.val + 1) := by
      rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff]
      simp
    have h2 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) * g = g⁻¹ ^ i.val := by
      rw [h1, pow_succ, inv_mul_cancel_right]
    exact AlgHom.ext fun x => congrArg e (DFunLike.congr_fun h2 x)

variable {l : ℕ} [Fact l.Prime]

theorem sigma_fixed (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) (hx : (P.PD K).σ x = x) :
    ∃ c : ℚ_[l], algebraMap ℚ_[l] ↥(K0 K) c = x := by
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact zero_mem _
  obtain ⟨c, hc⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x) (by rw [(P.PD K).φ_K₀, hx]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem)
  refine ⟨c, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hc]

end GlobalTheory.HWL.Letters

namespace GlobalTheory.HWL

theorem exists_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∃ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp (P.PD K).σ = emb i := by
  intro l _ P K s LL h
  haveI := (P.PD K).finK₀
  have hle : K0 K ≤ LL.1 := fun x hx =>
    h.2.2.2 (Ks K s).val ⟨x, (le_sup_left : K0 K ≤ Ks K s) hx⟩
  exact Letters.exists_emb_of_fixed _ (P.PD K).σ_bij (Letters.sigma_fixed P K)
    (IntermediateField.inclusion hle)

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGamGamKTorsion
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.PadicUnitSub

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_max_norm {ι : Type*} [Nonempty ι] (f : ι → ℤ_[l]) :
    ∃ i, ∀ j, ‖f j‖ ≤ ‖f i‖ := by
  classical
  by_cases h0 : ∀ j, f j = 0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, fun j => by rw [h0 j, h0 i]⟩
  · push_neg at h0
    have hex : ∃ n, ∃ j, f j ≠ 0 ∧ (f j).valuation = n := by
      obtain ⟨j, hj⟩ := h0
      exact ⟨_, j, hj, rfl⟩
    obtain ⟨i, hi, hiv⟩ := Nat.find_spec hex
    refine ⟨i, fun j => ?_⟩
    by_cases hj : f j = 0
    · rw [hj, norm_zero]; exact norm_nonneg _
    · have hle : Nat.find hex ≤ (f j).valuation := Nat.find_min' hex ⟨j, hj, rfl⟩
      rw [PadicInt.norm_eq_zpow_neg_valuation hj, PadicInt.norm_eq_zpow_neg_valuation hi, hiv]
      apply zpow_le_zpow_right₀ (by exact_mod_cast hl.out.one_lt.le)
      omega

theorem eq_one_of_pow_eq_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) (k : ℕ) (hk : 0 < k) (h : x ^ k = 1) : x = 1 := by
  have e := GlobalTheory.Cyc.norm_pow_nat_sub_one k hk.ne' x hx h2
  rw [h, sub_self, norm_zero] at e
  have hk' : ‖(k : ℤ_[l])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact_mod_cast hk.ne'
  rcases mul_eq_zero.1 e.symm with h' | h'
  · exact sub_eq_zero.1 (norm_eq_zero.1 h')
  · exact absurd h' hk'

theorem eq_of_torsion (u v : ℤ_[l]ˣ) (hu : IsOfFinOrder u) (hv : IsOfFinOrder v)
    (hx : ‖(u : ℤ_[l]) - v‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖(u : ℤ_[l]) - v‖ < (l : ℝ)⁻¹) : u = v := by
  have hw : IsOfFinOrder (u * v⁻¹) := hu.mul hv.inv
  have hnorm : ‖((u * v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = ‖(u : ℤ_[l]) - v‖ := by
    have e : ((u * v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((u : ℤ_[l]) - v) * ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [sub_mul, Units.mul_inv, Units.val_mul]
    rw [e, norm_mul, PadicInt.norm_units, mul_one]
  have h1 := eq_one_of_pow_eq_one _ (by rw [hnorm]; exact hx) (fun h => by rw [hnorm]; exact h2 h)
    (orderOf (u * v⁻¹)) hw.orderOf_pos
    (by rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one])
  have : u * v⁻¹ = 1 := Units.ext (h1.trans Units.val_one.symm)
  exact mul_inv_eq_one.1 this

theorem norm_le_of_toZModPow_eq (n : ℕ) (a b : ℤ_[l])
    (h : PadicInt.toZModPow n a = PadicInt.toZModPow n b) : ‖a - b‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h,
    sub_self]

theorem finite_torsion : {u : ℤ_[l]ˣ | IsOfFinOrder u}.Finite := by
  have : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  refine Set.Finite.of_finite_image
    (f := fun u : ℤ_[l]ˣ => PadicInt.toZModPow 2 (u : ℤ_[l])) (Set.toFinite _) ?_
  intro u hu v hv huv
  have hle := norm_le_of_toZModPow_eq 2 (u : ℤ_[l]) v huv
  have hlt : (l : ℝ) ^ (-((2 : ℕ) : ℤ)) < (l : ℝ)⁻¹ := by
    have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ h1 (by norm_num)
  exact eq_of_torsion u v hu hv (hle.trans hlt.le) (fun _ => hle.trans_lt hlt)

theorem norm_le_inv_of_lt_one (x : ℤ_[l]) (h : ‖x‖ < 1) : ‖x‖ ≤ (l : ℝ)⁻¹ := by
  have := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one x 0).1 (by simpa using h)
  simpa using this

theorem norm_lt_one_iff_toZMod (x : ℤ_[l]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma norm_natCast_padicInt_eq_one_of_not_dvd (n : ℕ) (h : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (n : ℤ)).1 (by rw [Int.cast_natCast]; exact hlt)
  exact_mod_cast this

theorem exists_teich (g : ℤ_[l]ˣ) :
    ∃ w : ℤ_[l]ˣ, IsOfFinOrder w ∧ ‖(w : ℤ_[l]) - g‖ < 1 := by
  have hl2 := hl.out.two_le
  set F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1 with hF
  have hder : ‖F.derivative.aeval (g : ℤ_[l])‖ = 1 := by
    have hn : ¬ l ∣ (l - 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Algebra.algebraMap_self, RingHom.id_apply, norm_mul, norm_pow, PadicInt.norm_units, one_pow,
      mul_one]
    exact_mod_cast norm_natCast_padicInt_eq_one_of_not_dvd (l - 1) hn
  have hval : ‖F.aeval (g : ℤ_[l])‖ < 1 := by
    have hg0 : PadicInt.toZMod (g : ℤ_[l]) ≠ 0 := (g.isUnit.map PadicInt.toZMod).ne_zero
    rw [norm_lt_one_iff_toZMod]
    simp only [hF, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_one, map_sub, map_pow,
      map_one]
    rw [ZMod.pow_card_sub_one_eq_one hg0, sub_self]
  obtain ⟨z, hz, hzg, -, -⟩ := hensels_lemma (F := F) (a := (g : ℤ_[l]))
    (by rw [hder, one_pow]; exact hval)
  rw [hder] at hzg
  have hz' : z ^ (l - 1) = 1 := by
    simpa [hF, sub_eq_zero] using hz
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz' (by omega)
  refine ⟨hu.unit, isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, by omega, Units.ext ?_⟩, ?_⟩
  · rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz', Units.val_one]
  · rw [IsUnit.unit_spec]; exact hzg

private lemma padicInt_norm_natCast_eq_one_of_not_dvd (n : ℕ) (h : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (n : ℤ)).1 (by rw [Int.cast_natCast]; exact hlt)
  exact_mod_cast this

theorem exists_gam_gamK_torsion :
    ∀ (l : ℕ) [Fact l.Prime] (s : ℕ) (Γ : Subgroup ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → u ∈ Γ) → ∃ (gam gamK : ↥Γ) (D : Finset ↥Γ), ‖((gam : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ (∀ g, g ∈ D ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1) ∧ (∀ g : ↥Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖ ≤ ‖((gamK : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖) ∧ ((∀ g : ↥Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖ ≤ ‖((gam : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖) → gamK = gam) ∧ (s = 1 → l ≠ 2 → gamK = gam) := by
  intro l _ s Γ hs hs2 hΓ
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hls : ‖((l : ℤ_[l]) ^ s)‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, inv_pow]
  have hlt1 : ‖((l : ℤ_[l]) ^ s)‖ < 1 := by
    rw [hls]; exact zpow_lt_one_of_neg₀ hl1 (by omega)
  have hunit : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
    rw [PadicInt.isUnit_iff, GlobalTheory.Cyc.padicInt_norm_add_eq_of_lt (by rwa [norm_one]), norm_one]
  have hg0 : (hunit.unit : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s := hunit.unit_spec
  have hg0Γ : hunit.unit ∈ Γ := hΓ _ (by rw [hg0, add_sub_cancel_left])

  have hTfin : ((CommGroup.torsion Γ : Subgroup Γ) : Set Γ).Finite := by
    refine (finite_torsion.preimage Subtype.val_injective.injOn).subset ?_
    intro g hg
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion g).1 hg)
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← Subgroup.coe_pow, hgk, Subgroup.coe_one]⟩
  have hD : ∀ g, g ∈ hTfin.toFinset ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1 := by
    intro g
    rw [Set.Finite.mem_toFinset, SetLike.mem_coe, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hDcard : hTfin.toFinset.card = Nat.card (CommGroup.torsion Γ) := by
    rw [← Nat.card_eq_card_finite_toFinset hTfin]; rfl
  have hDpow : ∀ g ∈ CommGroup.torsion Γ, g ^ hTfin.toFinset.card = 1 := by
    intro g hg
    have h1 := congrArg Subtype.val
      (pow_card_eq_one' (G := CommGroup.torsion Γ) (x := ⟨g, hg⟩))
    rw [hDcard]
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hNpos : 0 < hTfin.toFinset.card :=
    Finset.card_pos.2 ⟨1, (hD 1).2 ⟨1, one_pos, one_pow _⟩⟩
  obtain ⟨gmax, hgmax⟩ :=
    exists_max_norm (l := l) (fun g : Γ => ((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1)
  obtain ⟨gamK, hK1, hK2⟩ : ∃ gamK : Γ,
      (∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖((gamK : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖) ∧
      ((∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖(((⟨hunit.unit, hg0Γ⟩ : Γ) : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖) →
        gamK = ⟨hunit.unit, hg0Γ⟩) := by
    by_cases hc : ∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖(((⟨hunit.unit, hg0Γ⟩ : Γ) : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖
    · exact ⟨⟨hunit.unit, hg0Γ⟩, hc, fun _ => rfl⟩
    · exact ⟨gmax, hgmax, fun h => absurd h hc⟩
  refine ⟨⟨hunit.unit, hg0Γ⟩, gamK, hTfin.toFinset, ?_, hD, hK1, hK2, ?_⟩
  · show ‖(hunit.unit : ℤ_[l]) - 1‖ = _
    rw [hg0, add_sub_cancel_left, hls]
  · intro hs1 hl2
    subst hs1
    apply hK2

    have hcard : hTfin.toFinset.card < l := by
      have hle : hTfin.toFinset.card ≤ (Finset.univ.erase (0 : ZMod l)).card := by
        refine Finset.card_le_card_of_injOn (fun g : Γ => PadicInt.toZMod ((g : ℤ_[l]ˣ) : ℤ_[l]))
          ?_ ?_
        · intro g _
          simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
            Set.mem_singleton_iff, true_and, Finset.mem_erase, Finset.mem_univ, and_true]
          exact ((g : ℤ_[l]ˣ).isUnit.map PadicInt.toZMod).ne_zero
        · intro g hg h hh hgh
          have hgD := (hD g).1 hg
          have hhD := (hD h).1 hh
          obtain ⟨a, ha, hga⟩ := hgD
          obtain ⟨b, hb, hhb⟩ := hhD
          have hlt : ‖((g : ℤ_[l]ˣ) : ℤ_[l]) - ((h : ℤ_[l]ˣ) : ℤ_[l])‖ < 1 := by
            rw [norm_lt_one_iff_toZMod, map_sub, sub_eq_zero]; exact hgh
          apply Subtype.ext
          refine eq_of_torsion _ _ (isOfFinOrder_iff_pow_eq_one.2 ⟨a, ha, ?_⟩)
            (isOfFinOrder_iff_pow_eq_one.2 ⟨b, hb, ?_⟩) (norm_le_inv_of_lt_one _ hlt)
            (fun h2 => absurd h2 hl2)
          · rw [← Subgroup.coe_pow, hga, Subgroup.coe_one]
          · rw [← Subgroup.coe_pow, hhb, Subgroup.coe_one]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at hle
      have := hlp.two_le
      omega
    have hN : ‖((hTfin.toFinset.card : ℕ) : ℤ_[l])‖ = 1 :=
      padicInt_norm_natCast_eq_one_of_not_dvd _ (Nat.not_dvd_of_pos_of_lt hNpos hcard)
    have hgam1 : ‖(hunit.unit : ℤ_[l]) - 1‖ = (l : ℝ)⁻¹ := by
      rw [hg0, add_sub_cancel_left, pow_one, PadicInt.norm_p]
    have hgam : ‖(hunit.unit : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ = (l : ℝ)⁻¹ := by
      rw [GlobalTheory.Cyc.norm_pow_nat_sub_one _ hNpos.ne' _ hgam1.le (fun h2 => absurd h2 hl2), hgam1, hN,
        mul_one]
    intro g
    show _ ≤ ‖(hunit.unit : ℤ_[l]) ^ hTfin.toFinset.card - 1‖
    rw [hgam]
    obtain ⟨w, hw, hwg⟩ := exists_teich (g : ℤ_[l]ˣ)

    have hwΓ : w ∈ Γ := by
      have hmul : w * (g : ℤ_[l]ˣ)⁻¹ ∈ Γ := by
        apply hΓ
        rw [pow_one, ← PadicInt.norm_lt_one_iff_dvd]
        have e : ((w * (g : ℤ_[l]ˣ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
            ((w : ℤ_[l]) - ((g : ℤ_[l]ˣ) : ℤ_[l])) * (((g : ℤ_[l]ˣ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
          rw [sub_mul, Units.mul_inv, Units.val_mul]
        rw [e, norm_mul, PadicInt.norm_units, mul_one]
        exact hwg
      have := Γ.mul_mem hmul g.2
      rwa [inv_mul_cancel_right] at this
    have hwT : (⟨w, hwΓ⟩ : Γ) ∈ CommGroup.torsion Γ := by
      obtain ⟨k, hk, hwk⟩ := isOfFinOrder_iff_pow_eq_one.1 hw
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hwk)⟩
    have hwN : (w : ℤ_[l]) ^ hTfin.toFinset.card = 1 := by
      have h1 := congrArg (fun x : Γ => ((x : ℤ_[l]ˣ) : ℤ_[l])) (hDpow _ hwT)
      simpa using h1
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ((g : ℤ_[l]ˣ) : ℤ_[l]) (w : ℤ_[l]) hTfin.toFinset.card
    apply norm_le_inv_of_lt_one
    rw [← hwN, hc, norm_mul, norm_sub_rev]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one c)) hwg

end GlobalTheory.PadicUnitSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSortedNormalizedOrthBasisComplexPAdic
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PMonE.OrthBasis

private lemma exists_orthogonal_translate (l : ℕ) [Fact l.Prime] (W : Submodule ℚ_[l] ℂ_[l])
    [FiniteDimensional ℚ_[l] W] (x : ℂ_[l]) (hx : x ∉ W) :
    ∃ y : ℂ_[l], y - x ∈ W ∧ y ≠ 0 ∧ ∀ w ∈ W, ‖y‖ ≤ ‖y + w‖ ∧ ‖w‖ ≤ ‖y + w‖ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℚ_[l] W
  obtain ⟨w₀, hw₀K, hmin⟩ := (isCompact_closedBall (0 : W) ‖x‖).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
    (Continuous.continuousOn (f := fun w : W => ‖x - (w : ℂ_[l])‖) (by fun_prop))
  have h0 : ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x‖ := by
    simpa using hmin (Metric.mem_closedBall_self (norm_nonneg x) : (0 : W) ∈ _)
  have hglob : ∀ w : W, ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x - (w : ℂ_[l])‖ := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : W) ‖x‖
    · exact hmin hw
    · have hlt : ‖x‖ < ‖(w : ℂ_[l])‖ := by simpa using hw
      have h1 : ‖x - (w : ℂ_[l])‖ = ‖(w : ℂ_[l])‖ := by
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hlt.ne),
          norm_neg, max_eq_right hlt.le]
      rw [h1]; exact h0.trans hlt.le
  refine ⟨x - w₀, by simpa using W.neg_mem w₀.2, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · intro h
    exact hx (by rw [sub_eq_zero.1 h]; exact w₀.2)
  · have := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    simpa [sub_sub_eq_add_sub, sub_add_eq_add_sub, add_sub_assoc] using this
  · have h1 := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    have h2 : w = (x - w₀ + w) + -(x - w₀) := by abel
    calc ‖w‖ = ‖(x - w₀ + w) + -(x - w₀)‖ := by rw [← h2]
      _ ≤ max ‖x - w₀ + w‖ ‖-(x - w₀)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖x - w₀ + w‖ := by
        rw [norm_neg]
        refine max_le le_rfl ?_
        have : x - (↑(⟨w₀ - w, W.sub_mem w₀.2 hw⟩ : W) : ℂ_[l]) = x - w₀ + w := by simp; abel
        rw [← this]; exact h1

private lemma exists_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] :
    ∀ (n : ℕ) (μ : Fin n → ℂ_[l]), LinearIndependent ℚ_[l] μ →
      ∃ u : Fin n → ℂ_[l], (∀ i, u i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧ (∀ i, u i ≠ 0) ∧
        ∀ (c : Fin n → ℚ_[l]) (j : Fin n),
          ‖c j‖ * ‖u j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * u i‖ := by
  intro n
  induction n with
  | zero => intro μ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ j => j.elim0⟩
  | succ n ih =>
    intro μ hμ
    rw [← Fin.snoc_init_self μ, linearIndependent_finSnoc] at hμ
    obtain ⟨hμ₀, hx⟩ := hμ
    obtain ⟨u₀, hu₀S, hu₀, horth⟩ := ih _ hμ₀
    set W := Submodule.span ℚ_[l] (Set.range (Fin.init μ))
    haveI : FiniteDimensional ℚ_[l] W :=
      FiniteDimensional.span_of_finite ℚ_[l] (Set.finite_range _)
    obtain ⟨y, hyx, hy0, hy⟩ := exists_orthogonal_translate l W _ hx
    have hWS : W ≤ Submodule.span ℚ_[l] (Set.range μ) := by
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩
    have hxS : μ (Fin.last n) ∈ Submodule.span ℚ_[l] (Set.range μ) :=
      Submodule.subset_span ⟨_, rfl⟩
    refine ⟨Fin.snoc (α := fun _ => ℂ_[l]) u₀ y, fun i => ?_, fun i => ?_, fun c j => ?_⟩
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simp only [Fin.snoc_last]
        have : y = μ (Fin.last n) + (y - μ (Fin.last n)) := by abel
        rw [this]; exact Submodule.add_mem _ hxS (hWS hyx)
      · simp only [Fin.snoc_castSucc]; exact hWS (hu₀S k)
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa using hy0
      · simpa using hu₀ k
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      set w := ∑ i : Fin n, algebraMap ℚ_[l] ℂ_[l] (c i.castSucc) * u₀ i
      have hw : w ∈ W := Submodule.sum_mem _ fun i _ => by
        rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hu₀S i)
      have key : ‖c (Fin.last n)‖ * ‖y‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ ∧
          ‖w‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ := by
        by_cases hc : c (Fin.last n) = 0
        · simp [hc]
        · set a := algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))
          have hna : ‖a‖ = ‖c (Fin.last n)‖ := norm_algebraMap' ℂ_[l] _
          have ha : a ≠ 0 := by
            intro h; apply hc; rw [← norm_eq_zero, ← hna, h, norm_zero]
          have hw' : a⁻¹ * w ∈ W := by
            rw [show a⁻¹ = algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))⁻¹ by simp [a],
              ← Algebra.smul_def]
            exact Submodule.smul_mem _ _ hw
          obtain ⟨h1, h2⟩ := hy _ hw'
          have e : w + a * y = a * (y + a⁻¹ * w) := by field_simp; ring
          rw [e, norm_mul, hna]
          refine ⟨mul_le_mul_of_nonneg_left h1 (norm_nonneg _), ?_⟩
          have : ‖w‖ = ‖c (Fin.last n)‖ * ‖a⁻¹ * w‖ := by
            rw [norm_mul, norm_inv, hna, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
              one_mul]
          rw [this]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using key.1
      · simp only [Fin.snoc_castSucc]
        exact (horth (fun i => c i.castSucc) k).trans key.2

private lemma exists_rescale_norm_mem_Ioc (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (hx : x ≠ 0) :
    ∃ t : ℚ_[l], t ≠ 0 ∧ (l : ℝ)⁻¹ < ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ∧
      ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ≤ 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := zero_lt_one.trans hl
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.2 hx) hl
  have hN : ‖algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ (n + 1)) * x‖ = ‖x‖ / (l : ℝ) ^ (n + 1) := by
    rw [norm_mul, norm_algebraMap', norm_zpow, Padic.norm_p, inv_zpow, div_eq_inv_mul]
  refine ⟨(l : ℚ_[l]) ^ (n + 1), zpow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero),
    ?_, ?_⟩
  · rw [hN, lt_div_iff₀ (zpow_pos hlpos _), zpow_add_one₀ hlpos.ne', mul_comm _ (l : ℝ), ← mul_assoc,
      inv_mul_cancel₀ hlpos.ne', one_mul]
    exact h1
  · rw [hN, div_le_one (zpow_pos hlpos _)]
    exact h2

private lemma exists_sorted_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l])
    (hμ : LinearIndependent ℚ_[l] μ) :
    ∃ v : Fin h → ℂ_[l], (∀ i, v i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧
      (∀ i, v i ≠ 0 ∧ ‖v i‖ ≤ 1) ∧ (∀ i, (l : ℝ)⁻¹ < ‖v i‖) ∧ Antitone (fun i => ‖v i‖) ∧
      ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
        ‖c j‖ * ‖v j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * v i‖ := by
  obtain ⟨u, huS, hu0, horth⟩ := exists_orthogonal_family_in_span l h μ hμ
  choose t ht0 htlo hthi using fun i => exists_rescale_norm_mem_Ioc l (u i) (hu0 i)
  set w : Fin h → ℂ_[l] := fun i => algebraMap ℚ_[l] ℂ_[l] (t i) * u i with hw_def
  have hworth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
      ‖c j‖ * ‖w j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * w i‖ := by
    intro c j
    have := horth (fun i => c i * t i) j
    simp only [hw_def, map_mul, mul_assoc, norm_mul, norm_algebraMap'] at this ⊢
    exact this
  set σ := Tuple.sort (fun i => -‖w i‖)
  refine ⟨fun i => w (σ i), fun i => ?_, fun i => ⟨?_, hthi _⟩, fun i => htlo _, ?_, fun c j => ?_⟩
  · simp only [hw_def]
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (huS _)
  · simp only [hw_def]
    intro h0
    have := congrArg norm h0
    rw [norm_zero] at this
    exact (lt_irrefl (0 : ℝ)) ((inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)).trans
      (this ▸ htlo (σ i)))
  · intro a b hab
    exact neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖w i‖) hab)
  · have := hworth (fun k => c (σ.symm k)) (σ j)
    rw [← Equiv.sum_comp σ] at this
    simpa using this

theorem _root_.GlobalTheory.PMonE.OrthBasis.exists_orthBasis : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), (∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0) → ∃ (P : Matrix (Fin h) (Fin h) ℚ_[l]) (μ' : Fin h → ℂ_[l]), P.det ≠ 0 ∧ (∀ i, μ' i = ∑ j, algebraMap ℚ_[l] ℂ_[l] (P i j) * μ j) ∧ (∀ i, μ' i ≠ 0 ∧ ‖μ' i‖ ≤ 1) ∧ Antitone (fun i => ‖μ' i‖) ∧ (∀ i j, ‖μ' i‖ < l * ‖μ' j‖) ∧ ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ' j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ' i‖ := by
  intro l _ h μ hind
  classical
  have hμ : LinearIndependent ℚ_[l] μ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := hind g (by simpa [Algebra.smul_def] using hg)
    simp [this]
  obtain ⟨v, hvS, hv1, hvlo, hanti, horth⟩ := exists_sorted_orthogonal_family_in_span l h μ hμ
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (hvS i)
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨Matrix.of P, v, ?_, fun i => ?_, hv1, hanti, fun i j => ?_, horth⟩
  · intro hdet
    obtain ⟨w, hw0, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    have hcol : ∀ j, ∑ i, w i * P i j = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct] using congrFun hwP j
    have hsum : ∑ i, algebraMap ℚ_[l] ℂ_[l] (w i) * v i = 0 := by
      simp_rw [← Algebra.smul_def, ← hP, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hcol, zero_smul, Finset.sum_const_zero]
    apply hw0
    funext j
    have h1 := horth w j
    rw [hsum, norm_zero] at h1
    have h2 : 0 < ‖v j‖ := norm_pos_iff.2 (hv1 j).1
    have h3 : ‖w j‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w j)]) (norm_nonneg _)
    simpa using h3
  · rw [← hP i]
    simp [Algebra.smul_def]
  · calc ‖v i‖ ≤ 1 := (hv1 i).2
      _ = (l : ℝ) * (l : ℝ)⁻¹ := (mul_inv_cancel₀ hlpos.ne').symm
      _ < (l : ℝ) * ‖v j‖ := mul_lt_mul_of_pos_left (hvlo j) hlpos

end GlobalTheory.PMonE.OrthBasis
end

