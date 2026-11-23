module

public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
section
open Finset

noncomputable section

namespace Formalism.REAL

private theorem epow_zero_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin n) : epow E 0 a b = if a = b then 1 else 0 := by
  first | rfl | simp [epow]

private theorem epow_succ_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (k : ℕ) (a b : Fin n) : epow E (k + 1) a b = ∑ c, epow E k a c * E c b := by
  first | rfl | simp [epow]

theorem HWDiag_cov {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) :
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0) := by
  intro k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow]
    have lhs : E c d * (if a = b then (1:A) else 0) - (if a = b then (1:A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [lhs]
    by_cases h : d = a ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have h1 : (if d = a then (if c = b then (1:A) else 0) else 0) = 0 := by
        split_ifs with h2 h3 <;> simp_all
      have h2 : (if b = c then (if a = d then (1:A) else 0) else 0) = 0 := by
        split_ifs with h2 h3 <;> simp_all
      rw [h1, h2, sub_zero]
  | succ k ih =>
    intro a b c d
    have key : ∀ e, E c d * (epow E k a e * E e b) - (epow E k a e * E e b) * E c d
        = (E c d * epow E k a e - epow E k a e * E c d) * E e b
          + epow E k a e * (E c d * E e b - E e b * E c d) := by
      intro e; noncomm_ring
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun e _ => key e)]
    simp only [ih, hE c d]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
        mul_ite] <;> abel

private theorem module_end_mul_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f g : Module.End ℂ V) (v : V) : (f * g) v = f (g v) := rfl

theorem HWDiag_covApply {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (k : ℕ) (a b c d : Fin n) (v : V) :
    epow E k a b (E c d v) = E c d (epow E k a b v) -
      ((if d = a then epow E k c b v else 0) - (if b = c then epow E k a d v else 0)) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) (HWDiag_cov E hE k a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h' : epow E k a b (E c d v) = E c d (epow E k a b v) -
      (E c d (epow E k a b v) - epow E k a b (E c d v)) := by abel
  rw [h', h]
  split_ifs <;> simp

private theorem module_end_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (s : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  first
  | exact LinearMap.sum_apply s f v
  | simp
  | (classical
     induction s using Finset.induction_on with
     | empty => simp
     | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, LinearMap.add_apply, ih])

theorem HWDiag_upper {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a b : Fin n), a < b → epow E k a b v = 0 := by
  have hv' : (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0 := hv
  intro k
  induction k with
  | zero =>
    intro a b hab
    simp [epow_zero_apply, hab.ne]
  | succ k ih =>
    intro a b hab
    rw [epow_succ_apply, module_end_finset_sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [module_end_mul_apply]
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · rw [hv'.2 c b hcb, map_zero]
    · rw [hcb, hv'.1 b, map_smul, ih a b hab, smul_zero]
    · rw [HWDiag_covApply E hE k a c c b v, ih a c (hab.trans hcb), map_zero,
        ih a b hab]
      simp [hab.ne']

private theorem card_filter_fin_lt_eq {n : ℕ} (a : Fin n) :
    (univ.filter fun b : Fin n => a < b).card = n - 1 - (a : ℕ) := by
  first
  | (rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext; simp]
     exact Fin.card_Ioi a)
  | (have hmap : (univ.filter fun b : Fin n => a < b).map Fin.valEmbedding =
        Finset.Ico ((a : ℕ) + 1) n := by
       ext x
       simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
         Fin.valEmbedding_apply, Finset.mem_Ico]
       constructor
       · rintro ⟨b, hb, rfl⟩
         exact ⟨Nat.succ_le_of_lt hb, b.isLt⟩
       · rintro ⟨h1, h2⟩
         exact ⟨⟨x, h2⟩, Fin.lt_def.mpr (by simpa using h1), rfl⟩
     rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]
     omega)

private theorem cast_nat_sub_one_sub_fin_eq_complex {n : ℕ} (a : Fin n) :
    ((n - 1 - (a : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (a : ℂ) := by
  have ha := a.isLt
  have hN : n - 1 - (a : ℕ) + (a : ℕ) + 1 = n := by omega
  have hc : ((n - 1 - (a : ℕ) : ℕ) : ℂ) + (a : ℂ) + 1 = (n : ℂ) := by
    first
    | exact_mod_cast hN
    | (have h' := congrArg (Nat.cast : ℕ → ℂ) hN
       push_cast at h'
       exact h')
  linear_combination hc

theorem generatorPowDiagRecursion_holds : HWDiag := by
  unfold HWDiag
  intro V _i1 _i2 n E ν v hE hv k a
  have hv' : (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0 := hv
  have hterm : ∀ c : Fin n, epow E k a c (E c a v) =
      (if c = a then ν a • epow E k a a v else 0) +
        (if a < c then epow E k a a v - epow E k c c v else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hca
    · rw [hv'.2 c a hca, map_zero]
      simp [hca.ne, not_lt.mpr hca.le]
    · rw [hca, hv'.1 a, map_smul]
      simp
    · rw [HWDiag_covApply E hE k a c c a v,
        HWDiag_upper E ν v hE hv k a c hca, map_zero]
      simp [hca.ne', hca]
  have h1 : (∑ c : Fin n, if c = a then ν a • epow E k a a v else 0) =
      ν a • epow E k a a v := by
    simp
  have h2 : (∑ c : Fin n, if a < c then epow E k a a v - epow E k c c v else 0) =
      ∑ c ∈ univ.filter (fun b => a < b), (epow E k a a v - epow E k c c v) := by
    rw [Finset.sum_filter]
  have hsmul : (n - 1 - (a : ℕ)) • epow E k a a v =
      ((n : ℂ) - 1 - (a : ℂ)) • epow E k a a v := by
    rw [← cast_nat_sub_one_sub_fin_eq_complex a]
    first
    | exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
    | exact nsmul_eq_smul_cast ℂ _ _
    | simp
  rw [epow_succ_apply, module_end_finset_sum_apply]
  simp only [module_end_mul_apply, hterm]
  rw [Finset.sum_add_distrib, h1, h2, Finset.sum_sub_distrib, Finset.sum_const,
    card_filter_fin_lt_eq, hsmul]
  simp only [lsh, add_smul]
  abel

theorem HWDiag_Amat_upper {n : ℕ} (l : Fin n → ℂ) : (Amat l).IsUpperTriangular := by
  intro i j hij
  have h : j < i := hij
  simp [Amat, h.ne', not_lt.mpr h.le]

theorem HWDiag_charpoly {n : ℕ} (l : Fin n → ℂ) :
    (Amat l).charpoly = ∏ s : Fin n, (Polynomial.X - Polynomial.C (l s)) := by
  have hU := HWDiag_Amat_upper l
  first
  | (rw [Matrix.charpoly_of_upperTriangular _ hU]
     simp [Amat])
  | (rw [Matrix.charpoly, Matrix.det_of_upperTriangular]
     · refine Finset.prod_congr rfl fun s _ => ?_
       simp [Matrix.charmatrix_apply_eq, Amat]
     · intro i j hij
       have h : j < i := hij
       first
       | simp [Matrix.charmatrix_apply_ne _ _ _ h.ne', Amat, h.ne', not_lt.mpr h.le]
       | simp [Matrix.charmatrix_apply, Amat, h.ne', not_lt.mpr h.le])

private theorem sum_Amat_smul_eq_smul_sub_sum_gt {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (l : Fin n → ℂ) (y : Fin n → V) (a : Fin n) :
    ∑ c, Amat l a c • y c = l a • y a - ∑ c ∈ univ.filter (fun b => a < b), y c := by
  have hterm : ∀ c, Amat l a c • y c =
      (if c = a then l a • y c else 0) - (if a < c then y c else 0) := by
    intro c
    simp only [Amat, Matrix.of_apply]
    rcases lt_trichotomy c a with hca | hca | hca
    · simp [hca.ne, hca.ne', not_lt.mpr hca.le]
    · subst hca
      simp
    · simp [hca.ne, hca.ne', hca]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_sub_distrib, Finset.sum_filter]
  simp

theorem diagChar_of (h : HWDiag) : DiagChar := by
  unfold HWDiag at h
  unfold DiagChar
  intro V _i1 _i2 n E ν v hE hv a
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ, M = Amat (lsh ν) := ⟨_, rfl⟩
  have hrec : ∀ (k : ℕ) (b : Fin n),
      epow E (k + 1) b b v = ∑ c, M b c • epow E k c c v := by
    intro k b
    first
    | rw [h V n E ν v hE hv k b, hM, sum_Amat_smul_eq_smul_sub_sum_gt]
    | (rw [h V n E ν v hE hv k b, hM]; simp only [sum_Amat_smul_eq_smul_sub_sum_gt])
  have hpow : ∀ (k : ℕ) (b : Fin n), epow E k b b v = ∑ c, (M ^ k) b c • v := by
    intro k
    induction k with
    | zero =>
      intro b
      simp [epow_zero_apply, Matrix.one_apply]
    | succ k ih =>
      intro b
      rw [hrec, pow_succ']
      simp only [ih, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm
  have hchar : (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))) = M.charpoly := by
    rw [hM, HWDiag_charpoly]
  have hdeg : M.charpoly.natDegree < n + 1 := by
    have hd := Matrix.charpoly_natDegree_eq_dim M
    rw [Fintype.card_fin] at hd
    omega
  have hzero : Polynomial.aeval M M.charpoly = 0 := Matrix.aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range' hdeg] at hzero
  have hentry : ∀ c : Fin n, ∑ i ∈ range (n + 1), M.charpoly.coeff i * (M ^ i) a c = 0 := by
    intro c
    have hac := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N a c) hzero
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hac
  rw [hchar]
  simp only [hpow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hentry, zero_smul, Finset.sum_const_zero]

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
section
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section KT2Gen
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem mem_compactSpan (x : V) : x ∈ kSpan ε F x := by
  exact Submodule.mem_sInf.2 fun S hS => hS.1

theorem compactSpan_le {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) :
    kSpan ε F x ≤ S := sInf_le ⟨hx, hS⟩

theorem isCompactInvariant_compactSpan (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  rw [kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem isWeightVector_apply (hrel : KRel ε F) {ν : Fin n → ℝ} {v : V}
    (hv : IsWeight F ν v) (a b : Fin n) (hab : ε a = ε b) :
    IsWeight F (ν + root a b) (F a b v) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T v) (hrel c c a b rfl hab)
  have e1 : (if c = a then F c b else 0) v = (if c = a then (1 : ℂ) else 0) • F a b v := by
    split_ifs with h1
    · subst h1
      simp
    · simp
  have e2 : (if b = c then F a c else 0) v = (if c = b then (1 : ℂ) else 0) • F a b v := by
    by_cases h2 : c = b
    · subst h2
      simp
    · simp [h2, Ne.symm h2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul, e1, e2] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← sub_smul, ← add_smul]
  congr 1
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

end KT2Gen

theorem eigenvalue_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {F : Fin n → Fin n → Module.End ℂ V} (hunit : KUnit ε F)
    {v : V} (hv : v ≠ 0) (a : Fin n) {c : ℂ} (hc : F a a v = c • v) : ((c.re : ℝ) : ℂ) = c := by
  have h := hunit a a rfl v v
  rw [hc, inner_smul_left, inner_smul_right] at h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv
  exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hvv h)

theorem kHiUniq_of (hl : KLow) (_hw : KWtOrth) (ho : KOrth) : KHiUniq := by
  intro V _ _ n ε F μ ν x y hrel hunit hx hyx hy
  by_cases hμν : ν = μ
  · right
    refine ⟨hμν, ?_⟩
    obtain ⟨hspan, huniq⟩ := hl V n ε F μ x hrel hx
    exact huniq y (hspan ▸ hyx) (hμν ▸ hy.1)
  · left
    have h0 := ho V n ε F μ ν x y hrel hunit hx hy (Ne.symm hμν) y hyx y (mem_compactSpan y)
    exact inner_self_eq_zero.1 h0

theorem kIrr_of (he : KHiExist) (hu : KHiUniq) : KIrr := by
  intro V _ _ n ε F μ x hfd hrel hunit hx S hS hSst
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  haveI := hfd
  have hfdS : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hS
  obtain ⟨y, hyS, hy0, ν, hy⟩ := he V n ε F S hfdS hrel hunit hSst h0
  rcases hu V n ε F μ ν x y hrel hunit hx (hS hyS) hy with h | ⟨-, c, hc⟩
  · exact absurd h hy0
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hy0 hc
    have hxS : x ∈ S := by
      have h1 : c⁻¹ • y ∈ S := S.smul_mem _ hyS
      rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
    exact le_antisymm hS (compactSpan_le hxS hSst)

theorem weighted_sum_rootVector_shift {n : ℕ} (ν : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, -((i : ℕ) : ℝ) * (ν + root a b) i) =
      (∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  simp only [root, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem highestWeightExists_holds : KHiExist := by
  intro V _ _ n ε F S hfd hrel hunit hst hne
  haveI := hfd
  have hcomm : ∀ a b : Fin n, F a a * F b b = F b b * F a a := by
    intro a b
    have h := hrel a a b b rfl rfl
    by_cases hab : a = b
    · subst hab
      rfl
    · simpa [hab, Ne.symm hab, sub_eq_zero] using h
  have main : ∀ s : Finset (Fin n), ∃ W : Submodule ℂ V, W ≤ S ∧ W ≠ ⊥ ∧
      (∀ a, ∀ w ∈ W, F a a w ∈ W) ∧ ∃ lam : Fin n → ℂ, ∀ a ∈ s, ∀ w ∈ W, F a a w = lam a • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨S, le_rfl, hne, fun a w hw => hst a a rfl w hw, 0, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨W, hWS, hW0, hWst, lam, hlam⟩ := ih
      haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F a a).restrict (hWst a))
      obtain ⟨⟨v, hvW⟩, hv⟩ := hc.exists_hasEigenvector
      have hker : ∀ y, y ∈ LinearMap.ker (F a a - c • 1) ↔ F a a y = c • y := by
        intro y
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero]
      have hvker : F a a v = c • v := by
        have h1 := congrArg Subtype.val hv.apply_eq_smul
        simpa using h1
      refine ⟨W ⊓ LinearMap.ker (F a a - c • 1), inf_le_left.trans hWS, ?_, ?_, Function.update lam a c, ?_⟩
      · intro h
        have hvmem : v ∈ W ⊓ LinearMap.ker (F a a - c • 1) := ⟨hvW, (hker v).2 hvker⟩
        rw [h] at hvmem
        exact hv.2 (Subtype.ext (by simpa using (Submodule.mem_bot ℂ).1 hvmem))
      · intro b w hw
        refine ⟨hWst b w hw.1, (hker _).2 ?_⟩
        have h1 : F a a w = c • w := (hker w).1 hw.2
        have h2 := congrArg (fun T : Module.End ℂ V => T w) (hcomm a b)
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb w hw
        rcases Finset.mem_insert.1 hb with rfl | hb'
        · rw [Function.update_self]
          exact (hker w).1 hw.2
        · rw [Function.update_of_ne (by rintro rfl; exact ha hb')]
          exact hlam b hb' w hw.1
  obtain ⟨W, hWS, hW0, -, lam, hlam⟩ := main Finset.univ
  obtain ⟨v0, hv0W, hv00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hw0 : IsWeight F (fun a => (lam a).re) v0 := fun a => by
    rw [eigenvalue_real hunit hv00 a (hlam a (Finset.mem_univ a) v0 hv0W)]
    exact hlam a (Finset.mem_univ a) v0 hv0W
  have hstab : ∀ a, ∀ y ∈ S, F a a y ∈ S := fun a => hst a a rfl
  have hfinW : {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v}.Finite := by
    refine (Set.Finite.pi (t := fun a => {r : ℝ | Module.End.HasEigenvalue ((F a a).restrict (hstab a)) (r : ℂ)})
      (fun a => ?_)).subset ?_
    · exact (Module.End.finite_hasEigenvalue _).preimage (fun _ _ _ _ h => Complex.ofReal_injective h)
    · rintro ν ⟨v, hvS, hv0, hvw⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
      intro a
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvS⟩)
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        apply Subtype.ext
        simp [hvw a]
      · intro h
        apply hv0
        simpa using congrArg Subtype.val h
  obtain ⟨ν, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := Set.exists_max_image _
    (fun ν : Fin n → ℝ => ∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) hfinW ⟨_, v0, hWS hv0W, hv00, hw0⟩
  refine ⟨v, hvS, hv0, ν, hvw, fun a b hab hεab => ?_⟩
  by_contra hne'
  have hmem : ν + root a b ∈ {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v} :=
    ⟨F a b v, hst a b hεab v hvS, hne', isWeightVector_apply hrel hvw a b hεab⟩
  have h1 := hmax _ hmem
  rw [weighted_sum_rootVector_shift] at h1
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end Formalism.REAL
end
end

