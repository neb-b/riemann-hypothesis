module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0014
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousUnitriangularSection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatIffMemLocP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeOfHermitianTermTypesCauchySchwarz
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypesCS

theorem count_le (r a : ℕ) (H : ℝ) (ha : 1 ≤ a) (hH : (2 : ℝ) ^ a ≤ H) :
    ((a + a * (r * a) : ℕ) : ℝ) ≤ H ^ (r + 2) := by
  have hnat : a + a * (r * a) ≤ 2 ^ (a * (r + 2)) := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : r * a < 2 ^ (r * a) := Nat.lt_two_pow_self
    calc a + a * (r * a) = a * (1 + r * a) := by ring
      _ ≤ 2 ^ a * 2 ^ (r * a) := Nat.mul_le_mul h1.le (by omega)
      _ = 2 ^ (a + r * a) := (pow_add 2 a (r * a)).symm
      _ ≤ 2 ^ (a * (r + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc ((a + a * (r * a) : ℕ) : ℝ) ≤ ((2 ^ (a * (r + 2)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((2 : ℝ) ^ a) ^ (r + 2) := by push_cast; rw [pow_mul]
    _ ≤ H ^ (r + 2) := by gcongr

theorem ampSq_le_of_types : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk B hB1 hB2
  have hk1 : 1 ≤ k := by omega
  have hq2 : 2 ≤ S.q := GlobalTheory.HL.LevelFamilies.two_le_resQ S.ϖ S.ϖ_irr
  by_cases hex : ∃ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ
  swap
  ·
    simp only [not_exists] at hex
    have h0 := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (∅ : Finset ℕ)
      (fun _ _ _ => False) (fun d Λ => ¬ S.BBzero d Λ)
      (fun d Λ ht => absurd ht (hex d Λ)) (fun d Λ ht => absurd ht (hex d Λ))
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul] at h0
    exact h0.trans zero_le
  obtain ⟨d₀, Λ₀, ht₀⟩ := hex
  obtain ⟨ha0, -, -, hqa, hHp1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
  obtain ⟨A, hAa⟩ : ∃ A : ℕ, (A : ℤ) = S.a := ⟨_, Int.toNat_of_nonneg ha0⟩

  let s : Finset (ℕ ⊕ (ℕ × ℕ × ℕ)) :=
    (Finset.Icc 1 A).disjSum
      ((Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A).filter fun t => t.2.2 < t.1)
  let P : ℕ ⊕ (ℕ × ℕ × ℕ) → S.Datum → Submodule L.O S.V → Prop := fun x =>
    Sum.elim (fun i d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = S.q ^ i)
      (fun t => S.InFF (S.q ^ t.1) t.2.1 (S.q ^ t.1 - S.q ^ t.2.2)) x
  have hinj : ∀ m n : ℕ, S.q ^ m = S.q ^ n → m = n := fun m n h =>
    Nat.pow_right_injective hq2 h
  have hcover : ∀ d Λ, S.IsTerm d Λ → ((¬ S.BBzero d Λ) ↔ ∃ x ∈ s, P x d Λ) := by
    intro d Λ ht
    obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, hBB, -⟩ :=
      GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ ht
    constructor
    · intro hnz
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact absurd (hBB.mpr (by rw [hbe, h, pow_zero])) hnz
        · exact h
      by_cases hT : S.TypeBe d Λ
      · obtain ⟨i₁, J, i', h1, h1a, hJ1, hJr, hi', hF⟩ :=
          GlobalTheory.HL.LevelFamilies.exists_family L r k S d Λ ht hT
        refine ⟨Sum.inr (i₁, J, i'), ?_, hF⟩
        simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range]
        omega
      · refine ⟨Sum.inl i, ?_, hnz, hT, hbe⟩
        simp only [s, Finset.inl_mem_disjSum, Finset.mem_Icc]
        omega
    · rintro ⟨x, -, hx⟩
      rcases x with i | ⟨i, J, i'⟩
      · exact hx.1
      · exact hx.1.1
  have hdisj : ∀ d Λ, S.IsTerm d Λ → ∀ x ∈ s, ∀ y ∈ s, P x d Λ → P y d Λ → x = y := by
    intro d Λ _ x hx y hy hPx hPy
    rcases x with i | ⟨i, J, i'⟩ <;> rcases y with j | ⟨j, J', j'⟩ <;>
      dsimp only [P, Sum.elim_inl, Sum.elim_inr] at hPx hPy
    · exact congrArg Sum.inl (hinj _ _ (hPx.2.2.symm.trans hPy.2.2))
    · exact absurd hPy.1 hPx.2.1
    · exact absurd hPx.1 hPy.2.1
    · obtain ⟨-, hb, hle, ⟨y₀, hy₀, hlev⟩, hn⟩ := hPx
      obtain ⟨-, hb', hle', ⟨y₁, hy₁, hlev'⟩, hn'⟩ := hPy
      have hij : i = j := hinj _ _ (hb.symm.trans hb')
      subst hij
      have hJJ : J = J' := le_antisymm (hlev ▸ hle' y₀ hy₀) (hlev' ▸ hle y₁ hy₁)
      subst hJJ
      simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hx hy
      have hlt1 : S.q ^ i' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hx.2.le
      have hlt2 : S.q ^ j' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hy.2.le
      have hpow : S.q ^ i' = S.q ^ j' := by
        generalize S.q ^ i' = u at hn hlt1
        generalize S.q ^ j' = v at hn' hlt2
        generalize S.q ^ i = w at hn hn' hlt1 hlt2
        omega
      rw [hinj _ _ hpow]
  have hmain := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 s P (fun d Λ => ¬ S.BBzero d Λ)
    hcover hdisj
  have hsumB : ∑ x ∈ s, S.ampSq (P x) ≤ s.card * B := by
    have hle : ∀ x ∈ s, S.ampSq (P x) ≤ B := by
      intro x _
      rcases x with i | ⟨i, J, i'⟩
      · exact hB1 _
      · exact hB2 _ _ _
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s (fun x => S.ampSq (P x)) B hle
  have hcard : s.card ≤ A + A * (r * A) := by
    simp only [s, Finset.card_disjSum, Nat.card_Icc, Nat.add_sub_cancel]
    have h := Finset.card_filter_le (Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A)
      (fun t => t.2.2 < t.1)
    simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, Finset.card_range] at h
    omega
  have hHp0 : 0 ≤ S.Hp := le_trans zero_le_one hHp1
  have hreal : ((s.card : ℕ) : ℝ) ≤ S.Hp ^ (r + 2) := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · have : s.card = 0 := by rw [hA] at hcard; simpa using hcard
      rw [this, Nat.cast_zero]
      positivity
    · have h2A : (2 : ℝ) ^ A ≤ S.Hp :=
        calc (2 : ℝ) ^ A ≤ (S.q : ℝ) ^ A := by gcongr; exact_mod_cast hq2
          _ = (S.q : ℝ) ^ S.a := by rw [← hAa, zpow_natCast]
          _ ≤ S.Hp := hqa
      calc ((s.card : ℕ) : ℝ) ≤ ((A + A * (r * A) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ S.Hp ^ (r + 2) := count_le r A S.Hp hA h2A
  have hN : ((s.card : ℝ≥0∞) * s.card) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_mul', sq]
    exact mul_le_mul hreal hreal (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hreal)
  calc (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ s.card * ∑ x ∈ s, S.ampSq (P x) := hmain
    _ ≤ s.card * (s.card * B) := by gcongr
    _ = (s.card * s.card) * B := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by gcongr

end GlobalTheory.HL.TypesCS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesQuotientProdDegreeOnePrimes
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.SublatCount

section Abstract

variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]

def Ker (I : Ideal O) (N : Type) [AddCommGroup N] [Module O N] : Set (Submodule O N) :=
  {L | ∃ f : N →ₗ[O] O ⧸ I, Function.Surjective f ∧ LinearMap.ker f = L}

theorem encard_eq_of_bijOn {α β : Type} {s : Set α} {t : Set β} {f : α → β} (h : Set.BijOn f s t) :
    s.encard = t.encard := by
  rw [← h.image_eq, h.injOn.encard_image]

theorem mem_ker_iff (I : Ideal O) (L : Submodule O N) :
    L ∈ Ker I N ↔ Nonempty ((N ⧸ L) ≃ₗ[O] (O ⧸ I)) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f.quotKerEquivOfSurjective hf⟩
  · rintro ⟨e⟩
    refine ⟨e.toLinearMap ∘ₗ L.mkQ, e.surjective.comp L.mkQ_surjective, ?_⟩
    rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem smul_quot {I : Ideal O} {c : O} (hc : c ∈ I) (y : O ⧸ I) : c • y = 0 := by
  have : algebraMap O (O ⧸ I) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [Algebra.smul_def, this, zero_mul]

theorem smul_mem {I : Ideal O} {L : Submodule O N} (h : L ∈ Ker I N) {c : O} (hc : c ∈ I)
    (x : N) : c • x ∈ L := by
  obtain ⟨f, -, rfl⟩ := h
  rw [LinearMap.mem_ker, map_smul, smul_quot hc]

noncomputable def crt (I J : Ideal O) (h : IsCoprime I J) :
    (O ⧸ I * J) ≃ₗ[O] (O ⧸ I) × (O ⧸ J) :=
  { Ideal.quotientMulEquivQuotientProd I J h with
    map_smul' := fun c x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem encard_mul (I J : Ideal O) (h : IsCoprime I J) :
    (Ker (I * J) N).encard = (Ker I N).encard * (Ker J N).encard := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have key : ∀ {I J : Ideal O} {a b : O}, a ∈ I → b ∈ J → a + b = 1 →
      ∀ {L₁ L₂ L₁' L₂' : Submodule O N}, L₂ ∈ Ker J N → L₁' ∈ Ker I N →
      L₁ ⊓ L₂ = L₁' ⊓ L₂' → L₁ ≤ L₁' := by
    intro I J a b ha hb hab L₁ L₂ L₁' L₂' h2 h1' he x hx
    have h3 : b • x ∈ L₁ ⊓ L₂ := ⟨L₁.smul_mem b hx, smul_mem h2 hb x⟩
    rw [he] at h3
    have := L₁'.add_mem (smul_mem h1' ha x) h3.1
    rwa [← add_smul, hab, one_smul] at this
  rw [← Set.encard_prod]
  symm
  refine encard_eq_of_bijOn (f := fun p => p.1 ⊓ p.2) ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _⟩ ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩
    refine ⟨(crt I J h).symm.toLinearMap ∘ₗ f.prod g, (crt I J h).symm.surjective.comp ?_, ?_⟩
    · rintro ⟨x, y⟩
      obtain ⟨u, rfl⟩ := hf x
      obtain ⟨v, rfl⟩ := hg y
      refine ⟨b • u + a • v, Prod.ext ?_ ?_⟩
      · change f (b • u + a • v) = f u
        rw [map_add (f := _), map_smul, map_smul, smul_quot ha, ← smul_quot ha (f u), ← add_smul,
          add_comm, hab, one_smul]
      · change g (b • u + a • v) = g v
        rw [map_add (f := _), map_smul, map_smul, smul_quot hb, ← smul_quot hb (g v), ← add_smul,
          add_comm, hab, one_smul]
    · rw [LinearEquiv.ker_comp, LinearMap.ker_prod]
  · rintro ⟨L₁, L₂⟩ ⟨h1, h2⟩ ⟨L₁', L₂'⟩ ⟨h1', h2'⟩ he
    have he : L₁ ⊓ L₂ = L₁' ⊓ L₂' := he
    have he' : L₂ ⊓ L₁ = L₂' ⊓ L₁' := by rw [inf_comm, he, inf_comm]
    have hba : b + a = 1 := by rw [add_comm, hab]
    exact Prod.ext (le_antisymm (key ha hb hab h2 h1' he) (key ha hb hab h2' h1 he.symm))
      (le_antisymm (key hb ha hba h1 h2' he') (key hb ha hba h1' h2 he'.symm))
  · rintro _ ⟨f, hf, rfl⟩
    let g := (crt I J h).toLinearMap ∘ₗ f
    have hg : Function.Surjective g := (crt I J h).surjective.comp hf
    refine ⟨(LinearMap.ker (LinearMap.fst O _ _ ∘ₗ g), LinearMap.ker (LinearMap.snd O _ _ ∘ₗ g)),
      ⟨⟨_, Prod.fst_surjective.comp hg, rfl⟩, ⟨_, Prod.snd_surjective.comp hg, rfl⟩⟩, ?_⟩
    change LinearMap.ker _ ⊓ LinearMap.ker _ = _
    rw [← LinearMap.ker_prod, ← LinearEquiv.ker_comp (crt I J h) f]
    rfl

theorem encard_top : (Ker (⊤ : Ideal O) N).encard = 1 := by
  rw [Set.encard_eq_one]
  refine ⟨⊤, Set.eq_singleton_iff_unique_mem.2 ⟨⟨0, fun y => ⟨0, Subsingleton.elim _ _⟩, by simp⟩, ?_⟩⟩
  intro L hL
  rw [eq_top_iff]
  intro x _
  simpa using smul_mem hL (c := 1) trivial x

theorem encard_max [IsDomain O] [Module.Finite O N] [Module.Projective O N] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    (Ker P N).encard =
      ((∑ i ∈ Finset.range (Module.finrank O N), Nat.card (O ⧸ P) ^ i : ℕ) : ℕ∞) := by
  have : Nontrivial (O ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have he : Ker P N = {L : Submodule O N | ∃ f : N →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = L} := by
    ext L
    refine exists_congr fun f => and_congr_left fun _ => ⟨fun hf h0 => ?_, fun hf y => ?_⟩
    · obtain ⟨v, hv⟩ := hf 1
      rw [h0] at hv
      exact zero_ne_one hv
    · obtain ⟨v, hv⟩ := GlobalTheory.SW.Hyper.surj_of_ne P f hf
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨c • v, by rw [map_smul, hv, Algebra.smul_def, mul_one]; rfl⟩
  obtain ⟨hf, hc⟩ := GlobalTheory.SW.Hyper.count (M := N) P
  rw [he, ← hf.cast_ncard_eq]
  congr 1
  have h1 : 1 < Nat.card (O ⧸ P) := Finite.one_lt_card
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card (O ⧸ P) - 1) (by omega) ?_
  rw [hc, geom_sum_mul_of_one_le h1.le]

theorem encard_prod [IsDomain O] [Module.Finite O N] [Module.Projective O N] (T : ℕ) (hT : T ≠ 0)
    (s : Finset (Ideal O)) (hs : ∀ P ∈ s, P.IsMaximal ∧ Nat.card (O ⧸ P) = T) :
    (Ker (∏ P ∈ s, P) N).encard =
      (((∑ i ∈ Finset.range (Module.finrank O N), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.one_eq_top, encard_top]; simp
  | insert P s hP ih =>
    obtain ⟨hm, hc⟩ := hs P (Finset.mem_insert_self _ _)
    have : Finite (O ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hT)
    have hco : IsCoprime P (∏ Q ∈ s, Q) := IsCoprime.prod_right fun Q hQ =>
      Ideal.isCoprime_iff_sup_eq.2 (hm.coprime_of_ne (hs Q (Finset.mem_insert_of_mem hQ)).1
        fun h => hP (h ▸ hQ))
    rw [Finset.prod_insert hP, encard_mul _ _ hco, ih fun Q hQ => hs Q (Finset.mem_insert_of_mem hQ),
      encard_max, hc, Finset.card_insert_of_notMem hP, pow_succ', Nat.cast_mul]

end Abstract

theorem finrank_lattice {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsFullLattice K M) : Module.finrank (𝓞 K) M = Module.finrank K V := by
  letI := hM
  have hr : Module.rank (𝓞 K) V = Module.rank K V :=
    (IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl).symm
  have : Module.rank (𝓞 K) M = Module.rank K V := by
    apply le_antisymm
    · rw [← hr]; exact Submodule.rank_le M
    · obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
      rw [Submodule.IsFullLattice.span_eq_top (A := K) (M := M)] at hspan
      have h1 : Module.rank K V = Cardinal.mk s := by
        rw [← rank_top, ← hspan, rank_span_set hli]
      have h2 : LinearIndependent (𝓞 K) (fun x : s => (⟨x.1, hsM x.2⟩ : M)) := by
        apply LinearIndependent.of_comp M.subtype
        exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hli
      rw [h1]
      exact h2.cardinal_le_rank
  simp only [Module.finrank, this]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsFullLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ M hM T s hT hs
  letI := hM
  letI : Module.Finite (𝓞 K) M := Submodule.IsLattice.finite K M
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  rw [← finrank_lattice M hM, ← encard_prod (N := M) T hT.ne_zero s fun P hP =>
    ⟨(hs P hP).1, by rw [← (hs P hP).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]⟩]
  refine encard_eq_of_bijOn (f := fun L => L.comap M.subtype) ⟨?_, ?_, ?_⟩
  · intro L hL
    exact (mem_ker_iff _ _).2 hL.2
  · intro L hL L' hL' h
    have := congrArg (Submodule.map M.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hL.1,
      inf_eq_right.2 hL'.1] at this
  · intro L hL
    have h : (L.map M.subtype).comap M.subtype = L := Submodule.comap_map_eq_of_injective M.injective_subtype L
    refine ⟨L.map M.subtype, ⟨Submodule.map_subtype_le _ _, ?_⟩, h⟩
    rw [h]
    exact (mem_ker_iff _ _).1 hL

end GlobalTheory.SublatCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberMulRegulatorLeSqrtDiscrRpow
section
open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem log_pow_div_factorial_le_rpow_of_one_le {u s : ℝ} (hu : 1 ≤ u) (hs : 1 ≤ s) (r : ℕ) :
    Real.log u ^ r / (r.factorial : ℝ) ≤ u ^ s := by
  have h := Real.pow_div_factorial_le_exp (Real.log u) (Real.log_nonneg hu) r
  rw [Real.exp_log (by linarith)] at h
  refine h.trans ?_
  calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
    _ ≤ u ^ s := Real.rpow_le_rpow_of_exponent_le hu hs

theorem classNumber_mul_regulator_le_sqrt_discr_rpow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s →
      (classNumber K : ℝ) * Units.regulator K ≤
        Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ hK s hs
  classical
  set Y : ℝ := Real.sqrt |(discr K : ℝ)| with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊Y⌋₊).subset fun I hI => ?_
    exact Nat.le_floor hI.2
  set T := hfin.toFinset with hT
  have hmem : ∀ I, I ∈ T ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y := fun I => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  let cls : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun I =>
    if h : I ∈ nonZeroDivisors (Ideal (𝓞 K)) then ClassGroup.mk0 ⟨I, h⟩ else 1
  let g : Ideal (𝓞 K) → ℝ := fun I =>
    Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)
  have h1 : ∀ C : ClassGroup (𝓞 K),
      Units.regulator K ≤ ∑ I ∈ T.filter (fun I => cls I = C), g I := by
    intro C
    refine _root_.GlobalTheory.RegulatorClassBound.regulator_le_sum_class K hK C _ fun I => ?_
    rw [Finset.mem_filter, hmem]
    constructor
    · rintro ⟨⟨h0, hle⟩, hc⟩
      have hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero h0
      refine ⟨hI, ?_, hle⟩
      simpa only [cls, dif_pos hI] using hc
    · rintro ⟨hI, hc, hle⟩
      refine ⟨⟨nonZeroDivisors.ne_zero hI, hle⟩, ?_⟩
      simpa only [cls, dif_pos hI] using hc
  have h2 : ∀ I ∈ T, g I ≤ Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := by
    intro I hI
    obtain ⟨h0, hle⟩ := (hmem I).1 hI
    have hN : (0 : ℝ) < Ideal.absNorm I := by
      have : Ideal.absNorm I ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hu : 1 ≤ Y / Ideal.absNorm I := (one_le_div hN).2 hle
    refine (log_pow_div_factorial_le_rpow_of_one_le hu hs.le _).trans (le_of_eq ?_)
    rw [Real.div_rpow hY0 hN.le, Real.rpow_neg hN.le, div_eq_mul_inv]
  calc (classNumber K : ℝ) * Units.regulator K
      = ∑ _C : ClassGroup (𝓞 K), Units.regulator K := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, classNumber]
    _ ≤ ∑ C : ClassGroup (𝓞 K), ∑ I ∈ T.filter (fun I => cls I = C), g I :=
        Finset.sum_le_sum fun C _ => h1 C
    _ = ∑ I ∈ T, g I := Finset.sum_fiberwise T cls g
    _ ≤ ∑ I ∈ T, Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := Finset.sum_le_sum h2
    _ = Y ^ s * ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) := (Finset.mul_sum _ _ _).symm
    _ ≤ Y ^ s * (s / (s - 1)) ^ Module.finrank ℚ K :=
        mul_le_mul_of_nonneg_left
          (_root_.GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le K s hs T fun I hI => ((hmem I).1 hI).1) (Real.rpow_nonneg hY0 s)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesOfIndexLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem sublattice_count : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ M hM i hi
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.IsTorsionFree (𝓞 K) M := inferInstance
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
    have h1 : Module.rank (𝓞 K) M ≤ Module.rank K V := by
      rw [IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
      exact Submodule.rank_le M
    exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K V)
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (Module.finrank K V) i hi hr
  have hinj : Set.InjOn (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i} := by
    intro N hN N' hN' e
    have := congrArg (Submodule.map M.subtype) e
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hN.1, inf_eq_right.mpr hN'.1] using this
  have hmaps : Set.MapsTo (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}
      {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i} := by
    intro N hN
    exact hN.2
  have h2 := Set.encard_le_encard_of_injOn hmaps hinj
  rw [← hfin.cast_ncard_eq] at h2
  calc _ ≤ (((({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast h2
    _ = ENNReal.ofReal ({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℝ) := by
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

end GlobalTheory.Mass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousUnitriangularSectionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitriangular_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Continuous t ∧ (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) := by
  first | exact @GlobalTheory.UnitriSection.unitri_section | exact GlobalTheory.UnitriSection.unitri_section | (intros; apply GlobalTheory.UnitriSection.unitri_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruenceStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_unitriangular_of_local_congruence : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  first | exact @GlobalTheory.HL.LocCongApprox.loc_cong_approx | exact GlobalTheory.HL.LocCongApprox.loc_cong_approx | (intros; apply GlobalTheory.HL.LocCongApprox.loc_cong_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroupStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gluing_homomorphism_defect_group : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ, S.TauRel d Λ w y) ∧ (∀ w y y', S.TauRel d Λ w y → (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ)) ∧ (∀ c ∈ L.O, ∀ w₁ w₂ y₁ y₂, S.TauRel d Λ w₁ y₁ → S.TauRel d Λ w₂ y₂ → S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂)) ∧ (∀ w ∈ S.W0, w ∈ Λ ↔ (w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0)) ∧ S.Ihat d Λ ≤ S.sat Λ ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by
  first | exact @GlobalTheory.HL.Gluing.main | exact GlobalTheory.HL.Gluing.main | (intros; apply GlobalTheory.HL.Gluing.main <;> assumption)
end

