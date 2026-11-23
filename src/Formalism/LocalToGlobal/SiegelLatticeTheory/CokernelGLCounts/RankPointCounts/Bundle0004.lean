module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardMulConjEqLeOfFractionalIdeal
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

theorem card_mul_conj_eq_le_of_fractionalIdeal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E) (hJ : J ≠ 0) (hm : m ≠ 0)
    (S : Finset E) (hS : ∀ x ∈ S, x ∈ J ∧ x * IsCMField.complexConj E x = m) :
    (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
      2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, a = (J.den : 𝓞 E) := ⟨_, rfl⟩
  have hcoe : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = (y : E) := fun _ => rfl
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := by
    rw [ha]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors J.den.2
  have hmem : ∀ x ∈ S, ∃ y ∈ J.num, algebraMap (𝓞 E) E y = algebraMap (𝓞 E) E a * x := by
    intro x hx
    have h1 : J.den • x ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J.num := by
      rw [← J.den_mul_self_eq_num]
      exact Submodule.smul_mem_pointwise_smul x _ _ (hS x hx).1
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.1 h1
    refine ⟨y, hy, ?_⟩
    rw [ha]
    simpa [Algebra.smul_def, Submonoid.smul_def] using hy'
  choose! g hgI hg using hmem
  have hginj : Set.InjOn g S := by
    intro x hx y hy hxy
    have h := (hg x hx).symm.trans ((congrArg (algebraMap (𝓞 E) E) hxy).trans (hg y hy))
    exact mul_left_cancel₀ ha0 h
  have hTcard : (S.image g).card = S.card := Finset.card_image_of_injOn hginj
  have hgm : ∀ x ∈ S, algebraMap (𝓞 E) E (g x * cO E (g x)) =
      algebraMap (𝓞 E) E a * IsCMField.complexConj E (algebraMap (𝓞 E) E a) * m := by
    intro x hx
    rw [map_mul, hcoe (cO E (g x)), cO_coe, ← hcoe, hg x hx, map_mul, ← (hS x hx).2]
    ring
  have hT : ∀ y ∈ S.image g, y ∈ J.num ∧ y * cO E y = g x0 * cO E (g x0) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨hgI x hx, ?_⟩
    apply IsFractionRing.injective (𝓞 E) E
    rw [hgm x hx, hgm x0 hx0]
  have hnum : J.num ≠ ⊥ := by
    intro h
    apply hJ
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  have hc0 : IsCMField.complexConj E (algebraMap (𝓞 E) E a) ≠ 0 :=
    (map_ne_zero_iff _ (IsCMField.complexConj E).injective).2 ha0
  have hm'0 : g x0 * cO E (g x0) ≠ 0 := by
    intro h
    have h2 := hgm x0 hx0
    rw [h, map_zero] at h2
    exact (mul_ne_zero (mul_ne_zero ha0 hc0) hm) h2.symm
  have key := count_int J.num hnum (g x0 * cO E (g x0)) hm'0 (S.image g) hT
  have key' : ((((S.image g).card * Ideal.absNorm J.num ^ 2 : ℕ)) : ℝ) ≤
      ((2 * Module.finrank ℚ E ^ 2 * (Algebra.norm ℤ (g x0 * cO E (g x0))).natAbs : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast [Nat.cast_natAbs, Int.cast_abs] at key'
  rw [hTcard] at key'
  have hconj : ∀ y : E, Algebra.norm ℚ (IsCMField.complexConj E y) = Algebra.norm ℚ y := by
    intro y
    exact Algebra.norm_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y
  have hNaQ : ((Algebra.norm ℤ a : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 E) E a) :=
    Algebra.coe_norm_int a
  have hNa0 : ((Algebra.norm ℤ a : ℤ) : ℝ) ≠ 0 := by
    have h : Algebra.norm ℚ (algebraMap (𝓞 E) E a) ≠ 0 := Algebra.norm_ne_zero_iff.2 ha0
    rw [← hNaQ] at h
    exact_mod_cast h
  have hNm' : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ) =
      ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 * ((Algebra.norm ℚ m : ℚ) : ℝ) := by
    have h : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℚ) =
        Algebra.norm ℚ (algebraMap (𝓞 E) E a) ^ 2 * Algebra.norm ℚ m := by
      rw [Algebra.coe_norm_int, ← hcoe, hgm x0 hx0, map_mul (Algebra.norm ℚ), map_mul (Algebra.norm ℚ),
        hconj]
      ring
    have h3 : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ) =
        (((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℚ) : ℝ) := by norm_cast
    rw [h3, h, ← hNaQ]
    push_cast
    ring
  have hJn : ((FractionalIdeal.absNorm J : ℚ) : ℝ) =
      ((Ideal.absNorm J.num : ℕ) : ℝ) / |((Algebra.norm ℤ a : ℤ) : ℝ)| := by
    rw [FractionalIdeal.absNorm_eq, ha]
    push_cast
    rfl
  have hpos : (0 : ℝ) < ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hNa0))
  rw [hJn, div_pow, sq_abs, mul_div_assoc', div_le_iff₀ hpos]
  calc (S.card : ℝ) * ((Ideal.absNorm J.num : ℕ) : ℝ) ^ 2
      ≤ 2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ)| := key'
    _ = 2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| *
        ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 := by
      rw [hNm', abs_mul, abs_of_nonneg (sq_nonneg _)]
      ring

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CosetFd
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem coset_fd {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (L Λ : AddSubgroup V)
    (hle : Λ ≤ L) (hfin : (Λ.addSubgroupOf L).FiniteIndex) (FL : Set V) (hFL : MeasurableSet FL)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) :
    ∃ G : Set V, MeasurableSet G ∧ ∀ v, ∃! a : Λ, (a : V) + v ∈ G := by
  set Λ' := Λ.addSubgroupOf L
  have : Finite (L ⧸ Λ') := Λ'.finite_quotient_of_finiteIndex
  have : Fintype (L ⧸ Λ') := Fintype.ofFinite _
  let rep : L ⧸ Λ' → L := fun q => q.out
  let G : Set V := ⋃ q : L ⧸ Λ', (fun y => ((rep q : L) : V) + y) ⁻¹' FL
  refine ⟨G, MeasurableSet.iUnion fun q => measurable_const_add _ hFL, fun v => ?_⟩
  obtain ⟨l, hl, hlu⟩ := hdL v
  set q : L ⧸ Λ' := (l : L ⧸ Λ')
  have hdiff : -(rep q) + l ∈ Λ' := by
    have : ((rep q : L) : L ⧸ Λ') = q := QuotientAddGroup.out_eq' q
    rw [← QuotientAddGroup.eq]; exact this
  have hΛ : ((-(rep q) + l : L) : V) ∈ Λ := by
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff; exact hdiff
  refine ⟨⟨_, hΛ⟩, Set.mem_iUnion.2 ⟨q, ?_⟩, ?_⟩
  · show ((rep q : L) : V) + (((-(rep q) + l : L) : V) + v) ∈ FL
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← add_assoc, add_neg_cancel_left]; exact hl
  · rintro ⟨a, ha⟩ haG
    obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 haG
    have hq'' : ((rep q' : L) : V) + (a + v) ∈ FL := hq'
    have hmem : ((rep q' : V) + a) ∈ L := L.add_mem (rep q').2 (hle ha)
    have h1 : (⟨(rep q' : V) + a, hmem⟩ : L) = l := hlu _ (by show (rep q' : V) + a + v ∈ FL; rw [add_assoc]; exact hq'')

    have hqq : q' = q := by
      have e : (rep q' : L) + ⟨a, hle ha⟩ = l := by
        apply Subtype.ext; simpa using congrArg Subtype.val h1
      have hmk : ((l : L) : L ⧸ Λ') = ((rep q' : L) : L ⧸ Λ') := by
        rw [← e, QuotientAddGroup.eq]
        simp only [neg_add_rev, neg_add_cancel_right]
        rw [AddSubgroup.mem_addSubgroupOf]
        simpa using Λ.neg_mem ha
      rw [show ((rep q' : L) : L ⧸ Λ') = q' from QuotientAddGroup.out_eq' q'] at hmk
      exact hmk.symm
    apply Subtype.ext
    show a = ((-(rep q) + l : L) : V)
    have := congrArg Subtype.val h1
    simp only at this
    rw [← hqq]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← this]
    abel

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfA
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := by simpa using H.h_smul_left a x y

theorem hL_apply (x y : V) : hL H y x = H.h x y := rfl

def GramInv {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, (∀ i j, N i j ∈ M.L.O) ∧ N * H.gram v = 1

variable {H}

theorem h_right_zero {ι : Type} {v : ι → V} {w : V} (hw : ∀ i, H.h w (v i) = 0) {y : V}
    (hy : y ∈ Submodule.span E (Set.range v)) : H.h w y = 0 := by
  have hspan : Submodule.span E (Set.range v) ≤ LinearMap.ker (hL H w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hL_apply, H.h_herm, hw i, map_zero]
  have hy' : H.h y w = 0 := by
    have h1 := hspan hy
    rwa [LinearMap.mem_ker, hL_apply] at h1
  rw [H.h_herm, hy', map_zero]

private theorem h_fintype_sum_smul_left {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) (y : V) :
    H.h (∑ j, c j • v j) y = ∑ j, c j * H.h (v j) y := by
  have h1 := map_sum (hL H y) (fun j => c j • v j) Finset.univ
  simp only [map_smul, smul_eq_mul, hL_apply] at h1
  exact h1

private theorem h_sum_smul_eq_gram_mulVec {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) (i : ι) :
    H.h (∑ j, c j • v j) (v i) = (H.gram v *ᵥ c) i := by
  rw [h_fintype_sum_smul_left]
  show ∑ j, c j * H.h (v j) (v i) = ∑ j, H.h (v j) (v i) * c j
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_zero_of_orth {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hz
  have hc : H.gram v *ᵥ c = 0 := by
    funext i
    rw [← h_sum_smul_eq_gram_mulVec v c i]
    exact h0 i
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← hNG, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  subst hc0
  simp

private theorem h_sub_left' (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := by
  have h1 := (hL H z).map_sub x y
  rw [hL_apply, hL_apply, hL_apply] at h1
  exact h1

theorem decomp {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) {x : V} (hx : x ∈ Λ) :
    ∃ c : ι → E, (∀ j, c j ∈ M.L.O) ∧ ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hNO, hNG⟩ := hN
  have hGN : H.gram v * N = 1 := by
    first
      | exact mul_eq_one_comm.1 hNG
      | (rw [← Matrix.inv_eq_left_inv hNG]
         exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hNG))
  refine ⟨N *ᵥ fun k => H.h x (v k), fun j => ?_, fun i => ?_⟩
  · show ∑ k, N j k * H.h x (v k) ∈ M.L.O
    exact sum_mem fun k _ => mul_mem (hNO j k) (hI x hx (v k) (hv k))
  · rw [h_sub_left', h_sum_smul_eq_gram_mulVec v _ i, Matrix.mulVec_mulVec, hGN, Matrix.one_mulVec]
    exact sub_self _

theorem comb_mem_span {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    ∑ j, c j • v j ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem comb_mem_lat {ι : Type} [Fintype ι] {v : ι → V} {Λ : Submodule M.L.O V} (hv : ∀ i, v i ∈ Λ) {c : ι → E}
    (hc : ∀ j, c j ∈ M.L.O) : ∑ j, c j • v j ∈ Λ :=
  Submodule.sum_mem _ fun j _ => Λ.smul_mem (⟨c j, hc j⟩ : M.L.O) (hv j)

theorem le_of_Lset {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {f : Fin (r + 1) → V} (hX : H.X f ≤ Submodule.span E (Set.range v)) {Λ₁ Λ₂ : Submodule M.L.O V}
    (hI1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, H.h x y ∈ M.L.O) (hI2 : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, H.h x y ∈ M.L.O)
    (hv1 : ∀ i, v i ∈ Λ₁) (hv2 : ∀ i, v i ∈ Λ₂) (hL : H.Lset Λ₁ f ⊆ H.Lset Λ₂ f) : Λ₁ ≤ Λ₂ := by
  intro x hx
  obtain ⟨c, hcO, hc⟩ := decomp hN hI1 hv1 hx
  have hs2 : ∑ j, c j • v j ∈ Λ₂ := comb_mem_lat hv2 hcO
  have hperp : x - ∑ j, c j • v j ∈ H.perp (H.X f) := by
    show ∀ z ∈ H.X f, H.h (x - ∑ j, c j • v j) z = 0
    intro z hz
    exact h_right_zero hc (hX hz)
  have hx0 : x - ∑ j, c j • v j ∈ Λ₁ := Λ₁.sub_mem hx (comb_mem_lat hv1 hcO)
  have hmem : H.mkW f ⟨x - ∑ j, c j • v j, hperp⟩ ∈ H.Lset Λ₁ f :=
    ⟨⟨x - ∑ j, c j • v j, hperp⟩, hx0, rfl⟩
  obtain ⟨y, hyΛ, hyeq⟩ := hL hmem
  obtain ⟨d, hdO, hd⟩ := decomp hN hI2 hv2 hyΛ
  have ht2 : ∑ j, d j • v j ∈ Λ₂ := comb_mem_lat hv2 hdO
  have hdiff : (y : V) - (x - ∑ j, c j • v j) ∈ H.X f := by
    have hk := LinearMap.sub_mem_ker_iff.2 hyeq
    rw [Formalism.MainNotions.S.Loc.HermSp.mkW, Submodule.ker_mkQ, Submodule.mem_comap] at hk
    simpa using hk
  have hzero : (x - ∑ j, c j • v j) - ((y : V) - ∑ j, d j • v j) = 0 := by
    apply eq_zero_of_orth hN
    · have h1 : (y : V) - (x - ∑ j, c j • v j) ∈ Submodule.span E (Set.range v) := hX hdiff
      have h2 : ∑ j, d j • v j ∈ Submodule.span E (Set.range v) := comb_mem_span v d
      have h3 : (x - ∑ j, c j • v j) - ((y : V) - ∑ j, d j • v j) =
          ∑ j, d j • v j - ((y : V) - (x - ∑ j, c j • v j)) := by abel
      rw [h3]
      exact Submodule.sub_mem _ h2 h1
    · intro i
      rw [h_sub_left', hc i, hd i, sub_zero]
  have hx0' : x - ∑ j, c j • v j ∈ Λ₂ := by
    rw [sub_eq_zero.1 hzero]
    exact Λ₂.sub_mem hyΛ ht2
  have h4 := Λ₂.add_mem hx0' hs2
  rwa [sub_add_cancel] at h4

theorem lat_eq_of_Lset {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {f : Fin (r + 1) → V} (hX : H.X f ≤ Submodule.span E (Set.range v)) {Λ₁ Λ₂ : Submodule M.L.O V}
    (h1 : H.IsSelfDual Λ₁) (h2 : H.IsSelfDual Λ₂) (hv1 : ∀ i, v i ∈ Λ₁) (hv2 : ∀ i, v i ∈ Λ₂)
    (hL : H.Lset Λ₁ f = H.Lset Λ₂ f) : Λ₁ = Λ₂ := by
  have hI1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, H.h x y ∈ M.L.O := fun x hx => (h1.2.2 x).1 hx
  have hI2 : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, H.h x y ∈ M.L.O := fun x hx => (h2.2.2 x).1 hx
  exact le_antisymm (le_of_Lset hN hX hI1 hI2 hv1 hv2 hL.subset)
    (le_of_Lset hN hX hI2 hI1 hv2 hv1 hL.symm.subset)

theorem f_mem_MMfam {r : ℕ} (t : Term V M r) (a : Fin (r + 1)) : t.f a ∈ Set.range (H.MMfam t) := by
  refine ⟨Sum.inl a, ?_⟩
  unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
  first
    | (generalize M.split = s
       cases s <;> rfl)
    | (rcases hs : M.split with _ | g <;> simp [hs])

theorem X_le_MMfam {r : ℕ} (t : Term V M r) : H.X t.f ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  unfold Formalism.MainNotions.S.Loc.HermSp.X
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact f_mem_MMfam (H := H) t a.castSucc

end Formalism.MainNotions.S.Loc.HermSp.CohU
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem perp_anti {S T : Submodule E V} (h : S ≤ T) : H.perp T ≤ H.perp S :=
  fun _ hv x hx => hv x (h hx)

theorem X_le_Xp {r : ℕ} (f : Fin (r + 1) → V) : H.X f ≤ H.Xp f :=
  Submodule.span_mono (Set.range_subset_iff.mpr fun a => ⟨a.castSucc, rfl⟩)

theorem mem_perp_isotropicSpan_of_mem_framePerp {r : ℕ} {f f' : Fin (r + 1) → V} {w : V} (hw : w ∈ H.W0 f f') :
    w ∈ H.perp (H.X f) :=
  perp_anti H ((X_le_Xp H f).trans le_sup_left) hw

theorem mem_perp_isotropicSpan_of_mem_framePerp' {r : ℕ} {f f' : Fin (r + 1) → V} {w : V} (hw : w ∈ H.W0 f f') :
    w ∈ H.perp (H.X f') :=
  perp_anti H ((X_le_Xp H f').trans le_sup_right) hw

theorem sub_mem_X_of_mkW_eq {r : ℕ} {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))}
    (h : H.mkW f x = H.mkW f y) : (x : V) - y ∈ H.X f := by
  have h' := (Submodule.Quotient.eq _).mp h
  simpa using h'

end Basic

section Stmt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def Lemma0L (M : Model F E) (r : ℕ) : Prop :=
  M.split = none → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f'))

theorem lemma0L_holds (M : Model F E) (r : ℕ) : Lemma0L M r := by
  intro hsplit V _ _ H t hgen w hw
  classical
  have hprim := hgen.2
  simp only [HermSp.MMfam, hsplit] at hprim
  obtain ⟨hmem, hli, hspan⟩ := hprim
  constructor
  · intro hwL
    exact ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩⟩
  · rintro ⟨⟨x, hxL, hxw⟩, ⟨x', hx'L, hx'w⟩⟩
    have hp : (x : V) - w ∈ Submodule.span E (Set.range fun a : Fin r => t.f a.castSucc) :=
      sub_mem_X_of_mkW_eq H (y := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) hxw
    have hq : (x' : V) - w ∈ Submodule.span E (Set.range fun a : Fin r => t.f' a.castSucc) :=
      sub_mem_X_of_mkW_eq H (y := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩) hx'w
    obtain ⟨cp, hcp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
    obtain ⟨cq, hcq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
    have hdiff : (x : V) - x' ∈ t.abelian₂ := t.abelian₂.sub_mem hxL hx'L
    have hdiffE : (x : V) - x' ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
      have e : (x : V) - x' = ((x : V) - w) - ((x' : V) - w) := by abel
      rw [e]
      refine Submodule.sub_mem _ ?_ ?_
      · exact (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a.castSucc, rfl⟩)) hp
      · exact (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a.castSucc, rfl⟩)) hq
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan _ hdiff hdiffE)
    have hinjl : Function.Injective (fun a : Fin r => (Sum.inl a.castSucc : Fin (r + 1) ⊕ Fin (r + 1))) :=
      Sum.inl_injective.comp (Fin.castSucc_injective r)
    have hinjr : Function.Injective (fun a : Fin r => (Sum.inr a.castSucc : Fin (r + 1) ⊕ Fin (r + 1))) :=
      Sum.inr_injective.comp (Fin.castSucc_injective r)
    set e1 : (Fin (r + 1) ⊕ Fin (r + 1)) →₀ E :=
      cp.mapDomain (fun a => Sum.inl a.castSucc) - cq.mapDomain (fun a => Sum.inr a.castSucc) with he1
    set e2 : (Fin (r + 1) ⊕ Fin (r + 1)) →₀ E := l.mapRange (fun a : M.L.O => (a : E)) rfl with he2
    have h1 : Finsupp.linearCombination E (Sum.elim t.f t.f') e1 = (x : V) - x' := by
      rw [he1, map_sub, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain,
        Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      have e : (x : V) - x' = ((x : V) - w) - ((x' : V) - w) := by abel
      rw [e, ← hcp, ← hcq]
      rfl
    have h2 : Finsupp.linearCombination E (Sum.elim t.f t.f') e2 = (x : V) - x' := by
      rw [← hl, he2, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      rfl
    have he : e1 = e2 := hli (h1.trans h2.symm)
    have hcoef : ∀ a : Fin r, cp a = (l (Sum.inl a.castSucc) : E) := by
      intro a
      have h := congrArg (fun e => e (Sum.inl a.castSucc)) he
      simp only [he1, he2, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at h
      rw [Finsupp.mapDomain_apply_of_injective hinjl, Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨b, hb⟩
        simp at hb), sub_zero] at h
      exact h
    have hpL : (x : V) - w ∈ t.abelian₂ := by
      rw [← hcp]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [hcoef a]
      exact t.abelian₂.smul_mem (l (Sum.inl a.castSucc)) (hmem (Sum.inl a.castSucc))
    have e : w = (x : V) - ((x : V) - w) := by abel
    rw [e]
    exact t.abelian₂.sub_mem hxL hpL

end Stmt

end Formalism.L2.SG.LsDatumA
end
end

