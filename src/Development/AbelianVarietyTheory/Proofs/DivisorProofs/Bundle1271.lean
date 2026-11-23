module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorConstantTermSum
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.HeckeCT

open Formalism.UG Formalism.UG.P GlobalTheory.LFun

section Tri

variable {R T : Type} [CommRing R] [CommRing T] {r s N : ℕ} (h : r + s = N)

def Tri (g : GL (Fin N) R) (m : GL (Fin r) R × GL (Fin s) R) : Prop :=
  ∃ X, g.val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val X 0 m.2.val

theorem blk_sub (m : GL (Fin r) R × GL (Fin s) R) :
    (blk h m).val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val 0 0 m.2.val := by
  change (Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks m.1.val 0 0 m.2.val)).submatrix _ _ = _
  simp

theorem tri_blk (m : GL (Fin r) R × GL (Fin s) R) : Tri h (blk h m) m := ⟨0, blk_sub h m⟩

variable {h}

theorem Tri.mul {g g' : GL (Fin N) R} {m m' : GL (Fin r) R × GL (Fin s) R} (a : Tri h g m) (b : Tri h g' m') :
    Tri h (g * g') (m * m') := by
  obtain ⟨X, a⟩ := a
  obtain ⟨Y, b⟩ := b
  refine ⟨m.1.val * Y + X * m'.2.val, ?_⟩
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (blkE h), a, b, Matrix.fromBlocks_multiply]
  simp

end Tri

theorem blk_mem {L : Type} [Field L] {O : Subring L} {r s N : ℕ} (h : r + s = N) {m : GL (Fin r) L × GL (Fin s) L}
    (h1 : m.1 ∈ GLint (Fin r) O) (h2 : m.2 ∈ GLint (Fin s) O) : blk h m ∈ GLint (Fin N) O := by
  have key : ∀ m : GL (Fin r) L × GL (Fin s) L, m.1 ∈ GLint (Fin r) O → m.2 ∈ GLint (Fin s) O →
      ∀ a b, (blk h m).val a b ∈ O := fun m h1 h2 a b => by
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    have := congrFun (congrFun (blk_sub h m) a) b
    rw [Matrix.submatrix_apply] at this
    rw [this]
    rcases a with a | a <;> rcases b with b | b
    exacts [satake_glint_entry O h1 a b, O.zero_mem, O.zero_mem, satake_glint_entry O h2 a b]
  refine satake_mem_glint O _ (key m h1 h2) ?_
  rw [← map_inv]
  exact key _ (inv_mem h1) (inv_mem h2)

theorem sum_fun {α A B C Q : Type} [Fintype α] [Fintype A] [Fintype B] [Fintype C] [Fintype Q] [DecidableEq α]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (e : A ⊕ B ⊕ C ≃ α) (G : (A → Q) → (B → Q) → ℂ) :
    ∑ c : α → Q, G (fun a => c (e (.inl a))) (fun b => c (e (.inr (.inl b)))) =
      (Fintype.card Q : ℂ) ^ Fintype.card C * ∑ a, ∑ b, G a b := by
  let f : (A → Q) × (B → Q) × (C → Q) ≃ (α → Q) :=
    (((Equiv.sumArrowEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))).symm).trans (e.arrowCongr (Equiv.refl Q))
  rw [← f.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [f]

section Pairs

variable {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
  (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)

def pairMap : satakePairs S₁ ⊕ satakePairs S₂ ⊕ (S₁ × (S₂ᶜ : Finset (Fin s))) → satakePairs S
  | .inl p => ⟨(blkE h (.inl p.1.1), blkE h (.inl p.1.2)), (h1 _).2 p.2.1, fun e => p.2.2.1 ((h1 _).1 e), p.2.2.2⟩
  | .inr (.inl p) => ⟨(blkE h (.inr p.1.1), blkE h (.inr p.1.2)), (h2 _).2 p.2.1, fun e => p.2.2.1 ((h2 _).1 e),
      Nat.add_lt_add_left p.2.2.2 r⟩
  | .inr (.inr p) => ⟨(blkE h (.inl p.1.1), blkE h (.inr p.2.1)), (h1 _).2 p.1.2,
      fun e => Finset.mem_compl.1 p.2.2 ((h2 _).1 e), Nat.lt_add_right _ p.1.1.2⟩

theorem pairMap_bijective : Function.Bijective (pairMap h h1 h2) := by
  constructor
  · rintro (p | p | p) (p' | p' | p') e <;> simp [pairMap] at e ⊢
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Prod.ext e.1 e.2
  · rintro ⟨⟨a, b⟩, x, y, z⟩
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    rcases a with a | a <;> rcases b with b | b
    · exact ⟨.inl ⟨(a, b), (h1 _).1 x, fun e => y ((h1 _).2 e), z⟩, rfl⟩
    · exact ⟨.inr (.inr (⟨a, (h1 _).1 x⟩, ⟨b, Finset.mem_compl.2 fun e => y ((h2 _).2 e)⟩)), rfl⟩
    · exact absurd (Nat.lt_add_right a b.2) (not_lt.2 (le_of_lt z))
    · exact ⟨.inr (.inl ⟨(a, b), (h2 _).1 x, fun e => y ((h2 _).2 e), Nat.lt_of_add_lt_add_left z⟩), rfl⟩

theorem tri_satakeGL {L : Type} [Field L] (O : Subring L) {π : L} (hπ : π ≠ 0) (c : satakePairs S → O) :
    Tri h (satakeGL O hπ S c) (satakeGL O hπ S₁ fun p => c (pairMap h h1 h2 (.inl p)),
      satakeGL O hπ S₂ fun p => c (pairMap h h1 h2 (.inr (.inl p)))) := by
  refine ⟨Matrix.of fun a b => (satakeGL O hπ S c).val (blkE h (.inl a)) (blkE h (.inr b)), ?_⟩
  ext (a | a) (b | b)
  · have : blkE h (.inl a) < blkE h (.inl b) ↔ a < b := Iff.rfl
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, satakeGL_apply, satakeN, h1, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    rfl
  · rfl
  · exact satakeGL_lower O hπ S c _ _ (Nat.lt_add_right a b.2)
  · have : blkE h (.inr a) < blkE h (.inr b) ↔ a < b := Nat.add_lt_add_iff_left
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, satakeGL_apply, satakeN, h2, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq]
    rfl

end Pairs

section Local

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E}
  (hu : IsUnifV E v ϖ)

abbrev Res : Type := satakeRes (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩

abbrev rep {n : ℕ} (S : Finset (Fin n)) (c : satakePairs S → Res hu) : GL (Fin n) (v.adicCompletion E) :=
  satakeGL (Ov E v) (satake_unif_ne_zero v hu) S fun p => satakeSec (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩ (c p)

variable [Fintype (Res hu)]

theorem finsum_Tj {n j : ℕ} (hj : j ≤ n) (F : GL (Fin n) (v.adicCompletion E) → ℂ)
    (hF : ∀ g, ∀ k ∈ KGL v (n := n), F (g * k) = F g) :
    ∑ᶠ c : GL (Fin n) (v.adicCompletion E) ⧸ KGL v (n := n), Tj ℂ n (Ov E v) ϖ j c.out * F c.out =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∑ c : satakePairs S → Res hu, F (rep hu S c) := by
  classical
  have hϖ := mem_Ov_of_isUnifV hu
  have hr := satake_range_eq v hϖ hu Final.TjCosets hj
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion E)) : GL (Fin n) (v.adicCompletion E) ⧸ KGL v (n := n)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj v hϖ hu h),
      Finset.sum_subtype (Finset.univ.powersetCard j) (p := fun S : Finset (Fin n) => S.card = j)
        (fun S => by simp [Finset.mem_powersetCard]), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KGL v (n := n)) (satakeB v hϖ hu ⟨S, c⟩)
    rw [hκ, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right v (satakeB_mem v hϖ hu ⟨S, c⟩) κ.2),
      Pi.one_apply, one_mul, hF _ _ κ.2]
    rfl
  · intro x hx
    have hT : Tj ℂ n (Ov E v) ϖ j x.out ≠ 0 := left_ne_zero_of_mul hx
    rw [satake_Tj_ne_zero_iff] at hT
    obtain ⟨i, rfl⟩ := (Set.ext_iff.1 hr x).2 hT
    simp

theorem sum_rep {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
    (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)
    (F : GL (Fin N) (v.adicCompletion E) → ℂ) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ c : satakePairs S → Res hu, F (rep hu S c) = (qV E v : ℂ) ^ (S₁.card * (s - S₂.card)) *
      ∑ c₁ : satakePairs S₁ → Res hu, ∑ c₂ : satakePairs S₂ → Res hu, F (blk h (rep hu S₁ c₁, rep hu S₂ c₂)) := by
  have := sum_fun (Equiv.ofBijective _ (pairMap_bijective h h1 h2))
    fun (c₁ : satakePairs S₁ → Res hu) (c₂ : satakePairs S₂ → Res hu) => F (blk h (rep hu S₁ c₁, rep hu S₂ c₂))
  rw [← Nat.card_eq_fintype_card, satake_card_res v _ hu, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin] at this
  rw [← this]
  exact Finset.sum_congr rfl fun c _ => hF _ _ (tri_satakeGL h h1 h2 _ _ _)


omit [Fintype (Res hu)] in
include hu in
theorem finsum_Tj_levi {r s N j : ℕ} (h : r + s = N) (hj : j ≤ N) (F : GL (Fin N) (v.adicCompletion E) → ℂ)
    (hK : ∀ g, ∀ k ∈ KGL v (n := N), F (g * k) = F g) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ᶠ c : GL (Fin N) (v.adicCompletion E) ⧸ KGL v (n := N), Tj ℂ N (Ov E v) ϖ j c.out * F c.out =
      ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
        (qV E v : ℂ) ^ (i.1 * (s - i.2)) * ∑ᶠ c₁ : GL (Fin r) (v.adicCompletion E) ⧸ KGL v (n := r),
          ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v (n := s),
            Tj ℂ r (Ov E v) ϖ i.1 c₁.out * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (c₁.out, c₂.out)) := by
  classical
  have := satake_res_finite v (mem_Ov_of_isUnifV hu) hu
  let _ : Fintype (Res hu) := Fintype.ofFinite _
  let J : Finset (Fin r) × Finset (Fin s) ≃ Finset (Fin N) :=
    Finset.sumEquiv.symm.toEquiv.trans (blkE h).finsetCongr
  have hJ : ∀ T, J T = (T.1.disjSum T.2).map (blkE h).toEmbedding := fun _ => rfl
  rw [finsum_Tj hu hj F hK,
    ← Finset.sum_equiv J (s := Finset.univ.filter fun T => T.1.card + T.2.card = j)
      (f := fun T => ∑ c : satakePairs (J T) → Res hu, F (rep hu (J T) c))
      (fun T => by simp [hJ, Finset.mem_powersetCard]) (fun _ _ => rfl),
    ← Finset.sum_fiberwise_of_maps_to (g := fun T : Finset (Fin r) × Finset (Fin s) => (T.1.card, T.2.card))
      (t := (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j)) (fun T hT => by
        have a1 := Finset.card_le_univ T.1
        have a2 := Finset.card_le_univ T.2
        simp only [Fintype.card_fin] at a1 a2
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hT ⊢
        omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hi
  have e1 : ∀ g : GL (Fin r) (v.adicCompletion E), ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v (n := s),
      Tj ℂ r (Ov E v) ϖ i.1 g * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (g, c₂.out)) =
      Tj ℂ r (Ov E v) ϖ i.1 g * ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c)) := fun g => by
    rw [← finsum_Tj hu hi.1.2 (fun x => F (blk h (g, x))) fun x k hk => ?_, mul_finsum]
    · simp only [mul_assoc]
    · rw [← hK (blk h (g, x)) _ (blk_mem h (m := (1, k)) (one_mem _) hk), ← map_mul]
      simp
  simp only [e1]
  rw [finsum_Tj hu hi.1.1 (fun g => ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c))) fun x k hk =>
      Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => by
        rw [← hK (blk h (x, _)) _ (blk_mem h (m := (k, 1)) hk (one_mem _)), ← map_mul]
        simp]
  rw [Finset.sum_congr (s₂ := Finset.univ.powersetCard i.1 ×ˢ Finset.univ.powersetCard i.2) ?_ fun _ _ => rfl,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun S₁ hS₁ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [sum_rep hu h (S₁ := S₁) (S₂ := S₂) (fun a => by simp [hJ]) (fun a => by simp [hJ]) F hF,
      (Finset.mem_powersetCard.1 hS₁).2, (Finset.mem_powersetCard.1 hS₂).2]
  · ext T
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ, Prod.ext_iff]
    omega

end Local

section Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

end Global

end GlobalTheory.ResW.HeckeCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramDetEqNormSqBasisDetMul
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.GramChange

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

theorem form_sum_right (nm : HermFam F V) (σ : F →+* ℂ) {ι : Type} (s : Finset ι) (f : ι → V) (x : V) :
    nm.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, nm.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := nm.add_right σ x 0 0
    simp only [add_zero] at h
    linear_combination -h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, nm.add_right, ih]

theorem form_sum_left (nm : HermFam F V) (σ : F →+* ℂ) {ι : Type} (s : Finset ι) (f : ι → V) (y : V) :
    nm.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, nm.form σ (f i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← nm.conj_symm σ y, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => nm.conj_symm σ y (f i)

theorem form_smul_left (nm : HermFam F V) (σ : F →+* ℂ) (a : F) (x y : V) :
    nm.form σ (a • x) y = starRingEnd ℂ (σ a) * nm.form σ x y := by
  rw [← nm.conj_symm σ y, nm.smul_right, map_mul, nm.conj_symm]

theorem gram_eq {d : ℕ} (nm : HermFam F V) (σ : F →+* ℂ) (b : Module.Basis (Fin d) F V) (v : Fin d → V) :
    nm.gram σ v = Matrix.conjTranspose ((b.toMatrix v).map σ) * nm.gram σ ⇑b * (b.toMatrix v).map σ := by
  have hv : ∀ j, v j = ∑ i, b.toMatrix v i j • b i := fun j => by
    simp [Module.Basis.toMatrix_apply, b.sum_repr]
  ext a c
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply]
  rw [hv a, hv c, form_sum_left]
  simp_rw [form_smul_left, form_sum_right, nm.smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def]
  ring

theorem gram_det (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V)
    (σ : F →+* ℂ) (d : ℕ) (b : Module.Basis (Fin d) F V) (v : Fin d → V) :
    (nm.gram σ v).det = ((Complex.normSq (σ (b.det v)) : ℝ) : ℂ) * (nm.gram σ ⇑b).det := by
  have hd : ((b.toMatrix v).map σ).det = σ (b.det v) := by
    rw [Module.Basis.det_apply, RingHom.map_det]
    rfl
  rw [gram_eq nm σ b v, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hd,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end GlobalTheory.GramChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSystemSlopeBoundOfDeterminantSlopeInequ
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShortNum

theorem claimS_to_hsClaimS : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ →
    h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  intro T D n Λ β Λ₀ ΛD ΛT δ h h' d deg hD hT hn hΛ hβ hδ hh hC
  obtain ⟨hz0, hz1, hineq⟩ := hC
  unfold Formalism.NormVectorIdentities.Items.HSClaimS Formalism.NormVectorIdentities.Items.hsZ Formalism.NormVectorIdentities.Items.hsR Formalism.NormVectorIdentities.Items.hsLogRho Formalism.NormVectorIdentities.Items.hsG
  set z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d with hz
  refine ⟨hz0, hz1, ?_⟩
  set ρ : ℝ := Real.log Λ + 26 * Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) with hρ
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hT2 : (2 : ℝ) ≤ T := by
    have : 2 ≤ T := by omega
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hβpos : 0 < β := by linarith
  have h1 : Real.log (Real.exp ρ * T) = ρ + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp]
  have h2 : Real.log (2 * Real.exp ρ * Real.sqrt β) = Real.log 2 + ρ + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr hβpos).ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt hβpos.le]
  have hX : (2 : ℝ) ≤ 2 + |h| + Real.log Λ := by have := abs_nonneg h; linarith
  have hprod : 2 * n ≤ n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ) := by
    have a1 : n ≤ n * (D : ℝ) := by nlinarith
    have a2 : n ≤ n * (D : ℝ) * 1 * δ := by nlinarith
    nlinarith
  have hlog2n : Real.log 2 + Real.log n ≤ Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hprod
  have hl2 := Real.log_two_gt_d9
  have hcst : HSShort.cst n Λ = Real.log n + Real.log Λ + (Real.log n + 1) / 2 := by
    unfold HSShort.cst; rw [Real.log_mul (by linarith) (by linarith)]
  have hc : HSShort.cst n Λ ≤ ρ := by rw [hcst, hρ]; linarith
  have hc0 : 0 ≤ HSShort.cst n Λ := by rw [hcst]; positivity
  rw [h1, h2]
  clear h1 h2 hprod hlog2n hcst hX
  generalize HSShort.cst n Λ = c at *
  clear_value ρ z
  generalize (T : ℝ) = t at *
  generalize (D : ℝ) = e at *
  generalize Real.log t = lt at *
  generalize Real.log n = ln at *
  generalize Real.log β = lb at *
  have hA : t * h - 3 * (e + 1) * |h| - Real.log Λ₀ - 26 * e ^ 2 * (ρ + lt)
        - (t + e + 1) * lb - (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2)
      ≤ t * h' - e * (e + 1) * c - Real.log Λ₀ - t / 2 * lb := by
    have e1 : t * h - t * ((ln + 1) / 2) ≤ t * h' := by
      have := mul_le_mul_of_nonneg_left hh hTpos.le
      linarith
    have e2 : e * (e + 1) * c ≤ 26 * e ^ 2 * (ρ + lt) := by
      have : e * (e + 1) ≤ 2 * e ^ 2 := by nlinarith
      have hD2 : 0 ≤ e ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right this hc0, mul_nonneg hD2 hlogT, mul_le_mul_of_nonneg_left hc hD2,
        mul_nonneg hD2 hc0]
    have e3 : t / 2 * lb ≤ (t + e + 1) * lb := mul_le_mul_of_nonneg_right (by linarith) hlogβ
    have e4 : t * ((ln + 1) / 2) ≤ (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2) := by
      have hg : (ln + 1) / 2 ≤ (e + 1) * (ln + 1) / 2 + 1 + 2 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e) (by linarith : (0 : ℝ) ≤ ln + 1)]
      have hT' : t ≤ t + e ^ 2 := by linarith [sq_nonneg e]
      calc t * ((ln + 1) / 2) ≤ t * ((e + 1) * (ln + 1) / 2 + 1 + 2) :=
            mul_le_mul_of_nonneg_left hg hTpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hT' (by positivity)
    have e5 : 0 ≤ 3 * (e + 1) * |h| := by positivity
    linarith
  have hB : t * c + t / 2 * lb + Real.log ΛD + Real.log ΛT
      ≤ t * (Real.log 2 + ρ + lb / 2) + Real.log ΛD + Real.log ΛT := by
    have : t * c ≤ t * (Real.log 2 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hTpos.le
    linarith
  have hz1' : 0 ≤ 1 - z := by linarith
  have m1 := mul_le_mul_of_nonneg_left hA hz1'
  have m2 := mul_le_mul_of_nonneg_left hB hz0
  linarith

end GlobalTheory.HSShortNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_corrC : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (corrC ρ G₀ G₁) (offHyp S U) := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK
  obtain ⟨C, hC0, hCb⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  set c' : ℝ := |c| + C + C * (|c| + C) with hc'
  have hposition : ∀ v ∈ offHyp S U, v ∈ K → ∀ j : Fin n, ∀ i a b p q,
      ‖intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j i a b p q‖ *
        (poinWt S v a * poinWt S v b) ≤ c' := by
    intro v hv hvK j i a b p q
    obtain ⟨-, hdb, hcn, hcv⟩ := hCb v hvK
    have hw01 := (_root_.GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos S v (hsmall v hv.1)).1
    have hwa := hw01 a
    have hwb := hw01 b
    have hab : poinWt S v a * poinWt S v b ≤ 1 := mul_le_one₀ hwa.2 hwb.1 hwb.2
    have hab0 : 0 ≤ poinWt S v a * poinWt S v b := mul_nonneg hwa.1 hwb.1
    have hca : 0 ≤ |c| := abs_nonneg c
    have hCc : 0 ≤ C * (|c| + C) := mul_nonneg hC0 (add_nonneg hca hC0)
    unfold intersection_update_fsHerm_neg_one
    split_ifs with h1 h2
    · have := hcurv v hv a b p q
      simp only [curvAt]
      linarith [le_abs_self c]
    · simp only [cutForm, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul]
      have e1 := hconn v hv a p q
      have e2 := hcn a p q
      have e3 := hdb b
      have hxy := norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
      have hD0 := norm_nonneg (dbar (fun x => (ρ x : ℂ)) v (coordVec b))
      have hN0 := norm_nonneg (conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q)
      have hwab : poinWt S v a * poinWt S v b ≤ poinWt S v a := mul_le_of_le_one_right hwa.1 hwb.2
      have hY : ‖conn G₀ v (coordVec a) p q‖ * poinWt S v a ≤ C :=
        (mul_le_mul e2 hwa.2 hwa.1 hC0).trans (by rw [mul_one])
      have hS : (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖) * poinWt S v a ≤ |c| + C := by
        calc _ ≤ (‖conn G₁ v (coordVec a) p q‖ + ‖conn G₀ v (coordVec a) p q‖) * poinWt S v a :=
              mul_le_mul_of_nonneg_right hxy hwa.1
          _ ≤ |c| + C := by rw [add_mul]; linarith [le_abs_self c]
      calc _ ≤ ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              ‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a :=
            mul_le_mul_of_nonneg_left hwab (mul_nonneg hD0 hN0)
        _ = ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a) := by ring
        _ ≤ C * (|c| + C) := mul_le_mul e3 hS (mul_nonneg hN0 hwa.1) hC0
        _ ≤ c' := by linarith
    · have := hcv a b p q
      simp only [curvAt]
      have : ‖curv G₀ v (coordVec a) (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ C :=
        (mul_le_mul this hab hab0 hC0).trans (by rw [mul_one])
      linarith
  refine GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (corrC ρ G₀ G₁)
    ((n : ℝ) * ((Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n)) hU hK hKU hsmall ?_ ?_ ?_
  · intro v hv
    have hvU := hv.1
    have hρv : ContDiffAt ℝ 1 ρ v :=
      (hρ.contDiffAt (hU.mem_nhds hvU)).of_le (WithTop.coe_le_coe.2 le_top)
    exact (_root_.GlobalTheory.GoodTop.continuousAt_corrC hρv ((hG₀ v hvU).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₀ v hvU).2
      ((hG₁ v hv).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₁ v hv).2).continuousWithinAt
  · intro v hv hvK
    apply GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero
    have : U \ K ∈ 𝓝 v := (hU.sdiff hK.isClosed).mem_nhds ⟨hv.1, hvK⟩
    filter_upwards [this] with x hx
    exact hρK x hx.1 hx.2
  · intro v hv hvK
    have hwpos : ∀ a, 0 < poinWt S v a := (_root_.GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
    calc ‖corrC ρ G₀ G₁ v‖
        ≤ ∑ j : Fin n, ‖mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n *
            ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
          Finset.sum_le_sum fun j _ => _root_.GlobalTheory.GoodTop.norm_mixTop_le_of_weighted _ _ c' hwpos (hposition v hv hvK j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.GoodTop
end

