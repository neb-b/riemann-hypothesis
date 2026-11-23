module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

@[expose] public section

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

namespace ColAsm

open Formalism.WachCohomologyFacts.PLenBound

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem len_two_step (A B P : Submodule O M) (hBA : B ≤ A) :
    Module.length O (↥A ⧸ P.comap A.subtype) =
      Module.length O (↥A ⧸ (B ⊔ P).comap A.subtype) + Module.length O (↥B ⧸ P.comap B.subtype) := by
  have hle : P.comap B.subtype ≤ (P.comap A.subtype).comap (Submodule.inclusion hBA) := by
    intro x hx
    simpa using hx
  let f := Submodule.mapQ (P.comap B.subtype) (P.comap A.subtype) (Submodule.inclusion hBA) hle
  have hPB : P.comap A.subtype ≤ (B ⊔ P).comap A.subtype := Submodule.comap_mono le_sup_right
  let g := Submodule.factor hPB
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  have hg : Function.Surjective g := Submodule.factor_surjective hPB
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro ha
      have h0 : (Submodule.Quotient.mk a : ↥A ⧸ (B ⊔ P).comap A.subtype) = 0 := ha
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at h0
      obtain ⟨b, hb, p, hp, hbp⟩ := Submodule.mem_sup.1 h0
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      rw [← hbp]
      simpa using P.neg_mem hp
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      show (Submodule.Quotient.mk (Submodule.inclusion hBA x) : ↥A ⧸ (B ⊔ P).comap A.subtype) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
      exact Submodule.mem_sup_left x.2
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem len_chain (P : Submodule O M) (k : ℕ) (F : ℕ → Submodule O M) (hF0 : F 0 = ⊤)
    (hF : ∀ i < k, F (i + 1) ≤ F i) :
    Module.length O (M ⧸ P) ≤
      (∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype)) +
        Module.length O (↥(F k) ⧸ P.comap (F k).subtype) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have e : (P.comap (F 0).subtype).map
        (((LinearEquiv.ofEq _ _ hF0).trans Submodule.topEquiv : ↥(F 0) ≃ₗ[O] M) : ↥(F 0) →ₗ[O] M) = P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨⟨x, by rw [hF0]; trivial⟩, by simpa using hx, rfl⟩
    exact le_of_eq ((Submodule.Quotient.equiv _ P _ e).length_eq).symm
  | succ k ih =>
    have ih' := ih (fun i hi => hF i (by omega))
    rw [len_two_step (F k) (F (k + 1)) P (hF k (by omega))] at ih'
    rw [Finset.sum_range_succ, add_assoc]
    exact ih'

theorem len_bound (a : O) (g e : ℕ) (Z Bc I : Submodule O M) (s : Finset M)
    (hcard : s.card ≤ g) (hZ : Submodule.span O (s : Set M) ⊔ Bc = Z) (hBc : Bc ≤ I)
    (hI : ∀ p ∈ Z, a ^ e • p ∈ I) :
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => hZ ▸ Submodule.mem_sup_left (Submodule.subset_span hx)
  let v : s → (↥Z ⧸ I.comap Z.subtype) := fun x => Submodule.Quotient.mk ⟨x.1, hsZ x.1 x.2⟩
  have hkill : ∀ i, (a ^ e) • v i = 0 := by
    intro i
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hI i.1 (hsZ i.1 i.2)
  have hspan : Submodule.span O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    let T : Submodule O M :=
      ((Submodule.span O (Set.range v)).comap (I.comap Z.subtype).mkQ).map Z.subtype
    have hT : Z ≤ T := by
      rw [← hZ]
      refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        intro y hy
        exact ⟨⟨y, hsZ y hy⟩, Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩, rfl⟩
      · intro b hb
        have hbZ : b ∈ Z := hZ ▸ Submodule.mem_sup_right hb
        refine ⟨⟨b, hbZ⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using hBc hb)]
        exact Submodule.zero_mem _
    obtain ⟨z', hz', hzz⟩ := hT hz
    have hz'' : z' = ⟨z, hz⟩ := Subtype.ext hzz
    subst hz''
    exact hz'
  have h1 := length_le_of_span v (a ^ e) hspan hkill
  have h2 := length_quot_pow_le a e
  rw [Fintype.card_coe] at h1
  calc _ ≤ _ := h1
    _ ≤ (s.card : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by gcongr
    _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by
        gcongr
    _ = _ := (mul_assoc _ _ _).symm

theorem sub_gen [IsDomain O] [IsPrincipalIdealRing O] [Module.Free O M] [Module.Finite O M]
    (a : O) (e : ℕ) (F P : Submodule O M) (hF : ∀ x ∈ F, a ^ e • x ∈ P) :
    Module.length O (↥F ⧸ P.comap F.subtype) ≤
      ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  obtain ⟨n, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  let s : Finset M := Finset.univ.image (fun i => (bF i : M))
  have hcard : s.card ≤ Module.finrank O M := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
      _ = Module.finrank O F := (Module.finrank_eq_card_basis bF).trans (by simp) |>.symm
      _ ≤ Module.finrank O M := Submodule.finrank_le F
  have hspan : Submodule.span O (s : Set M) ⊔ ⊥ = F := by
    rw [sup_bot_eq]
    have hs : (s : Set M) = F.subtype '' Set.range bF := by
      ext x; simp [s]
    rw [hs, Submodule.span_image, bF.span_eq, Submodule.map_top, Submodule.range_subtype]
  have h := len_bound a (Module.finrank O M) e F ⊥ P s hcard hspan bot_le hF
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

end ColAsm

open ColAsm in
theorem column_assembly_bound : ColAssembly := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen m e e' L hF0 hF hgen hG hN hk
  have hchain := len_chain P k F hF0 hF
  have hlast := sub_gen ℓ e (F k) P hk
  have hterm : ∀ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
      (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs with hig
    · obtain ⟨⟨s, hs, hsF, hFs⟩, hl⟩ := hG i hig
      have hZ : Submodule.span O (s : Set M) ⊔ F (i + 1) = F i :=
        le_antisymm (sup_le (Submodule.span_le.2 hsF) (hF i hi)) hFs
      have h1 := len_bound ℓ m e' (F i) (F (i + 1)) (F (i + 1) ⊔ P) s hs hZ le_sup_left hl
      calc _ ≤ (m : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := h1
        _ = ((m * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by push_cast; ring
    · exact hN i hi hig
  have hcount : ∑ i ∈ Finset.range k, (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) =
      ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hgen]
    have hsd : (Finset.range k).filter (fun i => i ∉ gen) = Finset.range k \ gen := by
      ext x
      simp [Finset.mem_sdiff]
    rw [hsd, Finset.card_sdiff, Finset.inter_eq_left.2 hgen, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
      ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    calc _ ≤ ∑ i ∈ Finset.range k, (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) *
          Module.length O (O ⧸ Ideal.span {ℓ}) := Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.sum_mul, hcount]
  calc Module.length O (M ⧸ P) ≤ _ := hchain
    _ ≤ ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) +
        ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := add_le_add hsum hlast
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

section Chain

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem chain_len_add (X Y Z : Submodule O M) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) =
      Module.length O (↥Y ⧸ X.comap Y.subtype) + Module.length O (↥Z ⧸ Y.comap Z.subtype) := by
  have hle : X.comap Y.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hYZ) :=
    fun x hx => hx
  have hle2 : X.comap Z.subtype ≤ (Y.comap Z.subtype).comap LinearMap.id := fun x hx => hXY hx
  let f := Submodule.mapQ (X.comap Y.subtype) (X.comap Z.subtype) (Submodule.inclusion hYZ) hle
  let g := Submodule.mapQ (X.comap Z.subtype) (Y.comap Z.subtype) LinearMap.id hle2
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hq
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, by rw [Submodule.mapQ_apply, LinearMap.id_apply]⟩
  have hfg : Function.Exact f g := by
    intro q
    constructor
    · intro hz
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hz
      have hz' : (z : M) ∈ Y := hz
      exact ⟨Submodule.Quotient.mk ⟨z, hz'⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact y.2
  exact Module.length_eq_add_of_exact f g hf hg hfg

theorem chain_len_le_of_le_sup (A X Z : Submodule O M) (hAZ : A ≤ Z) (hZ : Z ≤ A ⊔ X) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) ≤ Module.length O (↥A ⧸ X.comap A.subtype) := by
  have hle : X.comap A.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hAZ) :=
    fun x hx => hx
  apply Module.length_le_of_surjective (Submodule.mapQ _ _ (Submodule.inclusion hAZ) hle)
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1 (hZ z.2)
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - (z : M)) ∈ X
  rw [← hax, show a - (a + x) = -x by abel]
  exact X.neg_mem hx

theorem chain_len_le_top (A P : Submodule O M) (hA : ⊤ ≤ A ⊔ P) :
    Module.length O (M ⧸ P) ≤ Module.length O (↥A ⧸ P.comap A.subtype) := by
  apply Module.length_le_of_surjective (Submodule.mapQ (P.comap A.subtype) P A.subtype le_rfl)
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ :=
    Submodule.mem_sup.1 (hA (Submodule.mem_top : m ∈ (⊤ : Submodule O M)))
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - m) ∈ P
  rw [← hax, show a - (a + x) = -x by abel]
  exact P.neg_mem hx

end Chain

private lemma comap_subtype_inf_of_le {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (A B C : Submodule O M) (h : A ≤ C) : (B ⊓ C).comap A.subtype = B.comap A.subtype := by
  ext x
  simp [h x.2]

theorem column_chain_bound : ColChain := by
  unfold ColChain
  intro O _ M _ _ P k F h0 hF
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    exact chain_len_le_top (F 0) P (by rw [h0]; exact le_sup_left)
  | succ k ih =>
    have hk : F (k + 1) ≤ F k := hF k (Nat.lt_succ_self k)
    have ih' := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have e1 := chain_len_add (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k) (F k)
      (inf_le_inf_right _ le_sup_right) inf_le_right
    rw [comap_subtype_inf_of_le (F k) P (F k) le_rfl, comap_subtype_inf_of_le (F k) (F (k + 1) ⊔ P) (F k) le_rfl] at e1
    have e2 := chain_len_le_of_le_sup (F (k + 1)) (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k)
      (le_inf le_sup_left hk) (le_of_eq (sup_inf_assoc_of_le P hk))
    rw [comap_subtype_inf_of_le (F (k + 1)) P (F k) hk] at e2
    rw [Finset.sum_range_succ, add_assoc]
    refine le_trans ih' (add_le_add le_rfl ?_)
    rw [e1, add_comm]
    exact add_le_add le_rfl e2

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma lam_ge_one (ℓ H : ℕ) (hℓ : 2 ≤ ℓ) : 1 ≤ lam ℓ H := by
  unfold lam
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have h2 : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg h1 h2
    linarith

private lemma hcoef_le (x : ℝ) (hx : 11 ≤ x) :
    8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)) ≤ 32 / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd0 : (0 : ℝ) < x - 1 := by linarith
  have ht : (0 : ℝ) ≤ x - 11 := by linarith
  have ha : 8 * (2 * x - 1) / (x - 1) ^ 3 ≤ (41 / 2) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 3, pow_nonneg ht 2]
  have hb : 8 / (x - 1) ^ 2 ≤ 10 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hc : 1 / (x * (x - 1)) ≤ (11 / 10) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hx2 : (0 : ℝ) ≤ 1 / x ^ 2 := by positivity
  have e1 : (41 / 2) / x ^ 2 + 10 / x ^ 2 + (11 / 10) / x ^ 2 = (316 / 10) * (1 / x ^ 2) := by ring
  have e2 : 32 / x ^ 2 = 32 * (1 / x ^ 2) := by ring
  linarith

theorem expBound_statement : ExpBound := by
  intro ℓ hℓ h η S b a s₁ E e₂ hbh ha hs1 hE he2
  have hx : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hd0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) < ℓ := by linarith
  have hL := lam_ge_one ℓ (h + η) (by omega)
  have hc := hcoef_le (ℓ : ℝ) hx
  have hsig : sig ℓ h η = (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) + 1 := by
    unfold sig
    push_cast
    ring
  have hfl : ((h / (ℓ - 1) : ℕ) : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (m := h) (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h1
  rw [hsig]
  unfold sig₂ at he2 ⊢
  unfold aR at ha
  set L := lam ℓ (h + η) with hLdef
  set H : ℝ := ((h + η : ℕ) : ℝ) with hHdef
  have hhH : (h : ℝ) ≤ H := by
    rw [hHdef]
    push_cast
    linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hbH : (b : ℝ) ≤ H := le_trans (by exact_mod_cast hbh) hhH
  have hH0 : 0 ≤ H := by positivity
  have hfl2 : ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤ H / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [sq, ← div_div]
    apply div_le_div_of_nonneg_right _ hd0.le
    exact hfl.trans (div_le_div_of_nonneg_right hhH hd0.le)
  have hA : (a : ℝ) / ((ℓ : ℝ) - 1) ≤
      (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) :=
    div_le_div_of_nonneg_right ha hd0.le
  have hB : (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) ≤ H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hbH (by positivity)
  have hHc := mul_le_mul_of_nonneg_left hc hH0
  have e3 : H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) =
      H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3) := by
    rw [div_div, ← pow_succ, mul_div_assoc]
  have hv : 1 / ((ℓ : ℝ) - 1) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    linarith
  have hLv : L / ((ℓ : ℝ) - 1) ≤ L / 10 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hd
  have hSv : (S : ℝ) / ((ℓ : ℝ) - 1) ≤ S / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
  have hηv : 0 ≤ (η : ℝ) / ((ℓ : ℝ) - 1) := by positivity
  have k1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) =
      2 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) =
      3 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by
    ring
  have k3 : (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) =
      H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) + 4 * (1 / ((ℓ : ℝ) - 1)) +
        L / ((ℓ : ℝ) - 1) := by
    ring
  have k4 : (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) =
      ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) - 1) + (η : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k5 : H * (8 * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3 + 8 / ((ℓ : ℝ) - 1) ^ 2 +
      1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) =
      8 * (H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)) + 8 * (H / ((ℓ : ℝ) - 1) ^ 2) +
        H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
    ring
  have k6 : 2 * H / ((ℓ : ℝ) - 1) ^ 2 = 2 * (H / ((ℓ : ℝ) - 1) ^ 2) := by ring
  have k7 : 32 * H / (ℓ : ℝ) ^ 2 = H * (32 / (ℓ : ℝ) ^ 2) := by ring
  have k8 : 10 * (η : ℝ) / ((ℓ : ℝ) - 1) = 10 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by ring
  rw [k1] at hs1
  rw [k2] at hE
  rw [k3] at hA
  rw [k5] at hHc
  rw [k6] at he2
  rw [k4, k6, k7, k8]
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound
section
namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma hCoef_num (x : ℝ) (hx : 11 ≤ x) : 0 ≤ 7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32 := by

  have hy : 0 ≤ x - 11 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]

theorem h_coefficient_bound : HCoef := by
  intro x hx
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt h0
  have hx1 : x - 1 ≠ 0 := ne_of_gt h1
  have key := hCoef_num x hx
  have e : 32 / x ^ 2 - (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))
      = (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) := by
    field_simp
    ring
  have hd : 0 ≤ (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) :=
    div_nonneg key (by positivity)
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

theorem second_exponent_bound : MaxZeroExponentInequality := by
  intro ℓ hℓ b b' S h'' E s₂ L c' hE hs hL hc
  have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hl1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hS : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hcast : (((b + S + 1 : ℕ) : ℝ)) = (b : ℝ) + (S : ℝ) + 1 := by push_cast; ring

  have e2 : (b : ℝ) / ((ℓ : ℝ) - 1) = (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + (b : ℝ) / (ℓ : ℝ) := by
    field_simp
    ring
  have e1 : ((b : ℝ) + (S : ℝ) + 1) / ((ℓ : ℝ) - 1)
      = (b : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := by ring

  have e3 : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) ≤ (S : ℝ) + 1 := by
    have hq : 0 ≤ ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by linarith) hl1.le
    have hm : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) = (S : ℝ) + 1 := by
      field_simp
    nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have h4 : 0 ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := div_nonneg hb (mul_pos hl0 hl1).le
  rw [hcast]
  apply max_le
  · linarith
  · rw [e1, e2]
    linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

