module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsFreeResolutionShortExact
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem exists_free_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  intro k G _ _ A
  let e : Rep.free k G A ⟶ A := Rep.freeLift k G A (fun x => x)
  have he : Epi e := (Rep.epi_iff_surjective e).2 fun x =>
    ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by
      simp [e, Representation.freeLift_single_single]⟩
  exact ⟨A, kernel e, kernel.ι e, e, kernel.condition e,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e) inferInstance he⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_free_resolution_short_exact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.exists_free_shortExact
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsGLMovingUnimodularPairToLastBasis
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

noncomputable section

namespace GlobalTheory.UnimodTransvect

variable {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m]

theorem vecMulVec_zero' (a : m → R) : vecMulVec a (0 : m → R) = 0 := by
  ext i j
  simp [vecMulVec]

def tv (a b : m → R) (h : b ⬝ᵥ a = 0) : GL m R where
  val := 1 + vecMulVec a b
  inv := 1 - vecMulVec a b
  val_inv := by
    rw [mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero']; abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero']; abel

theorem tv_mulVec (a b : m → R) (h : b ⬝ᵥ a = 0) (v : m → R) :
    ((tv a b h : GL m R) : Matrix m m R) *ᵥ v = v + (b ⬝ᵥ v) • a := by
  change (1 + vecMulVec a b) *ᵥ v = _
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_tv_inv (a b : m → R) (h : b ⬝ᵥ a = 0) (f : m → R) :
    f ᵥ* (((tv a b h)⁻¹ : GL m R) : Matrix m m R) = f - (f ⬝ᵥ a) • b := by
  change f ᵥ* (1 - vecMulVec a b) = _
  rw [vecMul_sub, vecMul_one, vecMul_vecMulVec]

theorem reach_trans {v w u : m → R} (h1 : ∃ g : GL m R, (g : Matrix m m R) *ᵥ v = w)
    (h2 : ∃ g : GL m R, (g : Matrix m m R) *ᵥ w = u) : ∃ g : GL m R, (g : Matrix m m R) *ᵥ v = u := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨g2 * g1, ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2]

variable {n : ℕ}

theorem reach_of_last_one (u : Fin (n + 1) → R) (hu : u (Fin.last n) = 1) :
    ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ u = Pi.single (Fin.last n) 1 := by
  refine ⟨tv (Pi.single (Fin.last n) 1 - u) (Pi.single (Fin.last n) 1) ?_, ?_⟩
  · rw [single_dotProduct, Pi.sub_apply, Pi.single_eq_same, hu]
    ring
  · rw [tv_mulVec, single_dotProduct, hu, one_mul, one_smul]
    abel

theorem reach_last_one (w : Fin (n + 1) → R) (c : Fin n → R)
    (hc : ∑ i, c i * w i.castSucc = 1) :
    ∃ g : GL (Fin (n + 1)) R, ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ w) (Fin.last n) = 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (n + 1) → R, c' = Fin.snoc c 0 := ⟨_, rfl⟩
  have hcl : c' (Fin.last n) = 0 := by simp [hc']
  have hcw : c' ⬝ᵥ w = 1 := by
    rw [dotProduct, Fin.sum_univ_castSucc, hcl, zero_mul, add_zero]
    simpa [hc'] using hc
  refine ⟨tv (Pi.single (Fin.last n) 1) ((1 - w (Fin.last n)) • c') ?_, ?_⟩
  · rw [dotProduct_single, Pi.smul_apply, hcl, smul_zero, zero_mul]
  · rw [tv_mulVec, smul_dotProduct, hcw, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    simp only [smul_eq_mul]
    ring

theorem reach_first_unimod {s : ℕ} (hS : StableRangeLe R s) (hn : s ≤ n) (v f : Fin (n + 1) → R)
    (hfv : f ⬝ᵥ v = 1) :
    ∃ g : GL (Fin (n + 1)) R, ∃ c : Fin n → R, ∑ i, c i * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v) i.castSucc = 1 := by
  have hU : Unimodular R v := by
    unfold Unimodular
    rw [Ideal.eq_top_iff_one, ← hfv, Ideal.mem_span_range_iff_exists_fun]
    exact ⟨f, rfl⟩
  obtain ⟨t, ht⟩ := hS n hn v hU
  unfold Unimodular at ht
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => v i.castSucc + t i * v (Fin.last n)) := by
    rw [ht]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → R, a = Fin.snoc t 0 := ⟨_, rfl⟩
  have hal : a (Fin.last n) = 0 := by simp [ha]
  refine ⟨tv a (Pi.single (Fin.last n) 1) (by rw [single_dotProduct, hal, mul_zero]), c, ?_⟩
  refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
  rw [tv_mulVec, single_dotProduct, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [ha, Fin.snoc_castSucc]
  ring

theorem main : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v f : Fin (n + 1) → R, f ⬝ᵥ v = 1 → ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v = Pi.single (Fin.last n) 1 ∧ f ᵥ* ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Pi.single (Fin.last n) 1 := by
  intro R _ s hS n hn v f hfv
  obtain ⟨g1, c, hc⟩ := reach_first_unimod hS hn v f hfv
  obtain ⟨g2, hg2⟩ := reach_last_one _ c hc
  obtain ⟨g3, hg3⟩ := reach_of_last_one _ hg2
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin (n + 1)) R, g = g3 * g2 * g1 := ⟨_, rfl⟩
  have hgv : (g : Matrix _ _ R) *ᵥ v = Pi.single (Fin.last n) 1 := by
    rw [hg, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact hg3
  obtain ⟨f', hf'⟩ : ∃ f' : Fin (n + 1) → R, f' = f ᵥ* ((g⁻¹ : GL _ R) : Matrix _ _ R) := ⟨_, rfl⟩
  have hfl : f' (Fin.last n) = 1 := by
    have : f' ⬝ᵥ ((g : Matrix _ _ R) *ᵥ v) = 1 := by
      rw [hf', ← dotProduct_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec, hfv]
    rwa [hgv, dotProduct_single, mul_one] at this
  have hb : (f' - Pi.single (Fin.last n) 1) ⬝ᵥ Pi.single (Fin.last n) (1 : R) = 0 := by
    rw [dotProduct_single, Pi.sub_apply, hfl, Pi.single_eq_same]
    ring
  refine ⟨tv (Pi.single (Fin.last n) 1) (f' - Pi.single (Fin.last n) 1) hb * g, ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hgv, tv_mulVec, hb, zero_smul, add_zero]
  · rw [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul, ← hf', vecMul_tv_inv, dotProduct_single,
      hfl, mul_one, one_smul]
    abel

end GlobalTheory.UnimodTransvect

end

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_GL_moving_unimodular_pair_to_last_basis : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v f : Fin (n + 1) → R, f ⬝ᵥ v = 1 → ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v = Pi.single (Fin.last n) 1 ∧ f ᵥ* ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Pi.single (Fin.last n) 1 := by
  first
  | exact @GlobalTheory.UnimodTransvect.main
  | exact @GlobalTheory.UnimodTransvect.reach_first_unimod
  | exact @GlobalTheory.UnimodTransvect.reach_last_one
  | exact @GlobalTheory.UnimodTransvect.reach_of_last_one
  | exact @GlobalTheory.UnimodTransvect.reach_trans
  | exact @GlobalTheory.UnimodTransvect.vecMul_tv_inv
  | exact @GlobalTheory.UnimodTransvect.tv_mulVec
  | exact @GlobalTheory.UnimodTransvect.vecMulVec_zero'
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSplitSeqLinkInOrthogonalEqLinkIn
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.RowLink

variable {R : Type} [CommRing R] {N : ℕ}

def Orth (y z : (Fin N → R) × (Fin N → R)) : Prop := y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0

theorem mem_splitSeq_iff (l : List ((Fin N → R) × (Fin N → R))) :
    l ∈ splitSeq R N ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise Orth := by
  simp only [splitSeq, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, List.pairwise_iff_get.mpr fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
      simpa using h i i
    · simpa [Fin.ne_of_lt hij] using h i j
    · simpa [(Fin.ne_of_lt hij).symm] using h j i
  · rintro ⟨h1, h2⟩ i j
    have hp := List.pairwise_iff_get.mp h2
    rcases lt_trichotomy i j with hij | rfl | hij
    · simpa [Fin.ne_of_lt hij] using (hp i j hij).1
    · simpa using h1 _ (List.get_mem l i)
    · simpa [(Fin.ne_of_lt hij).symm] using (hp j i hij).2

theorem append_mem_splitSeq_iff (l₁ l₂ : List ((Fin N → R) × (Fin N → R))) :
    l₁ ++ l₂ ∈ splitSeq R N ↔
      l₁ ∈ splitSeq R N ∧ l₂ ∈ splitSeq R N ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, Orth a b := by
  rw [mem_splitSeq_iff, mem_splitSeq_iff, mem_splitSeq_iff, List.pairwise_append]
  constructor
  · rintro ⟨h1, p1, p2, p3⟩
    exact ⟨⟨fun y hy => h1 y (List.mem_append.mpr (Or.inl hy)), p1⟩,
      ⟨fun y hy => h1 y (List.mem_append.mpr (Or.inr hy)), p2⟩, p3⟩
  · rintro ⟨⟨h1, p1⟩, ⟨h2, p2⟩, p3⟩
    exact ⟨fun y hy => (List.mem_append.mp hy).elim (h1 y) (h2 y), p1, p2, p3⟩

def corr (γ : List ((Fin N → R) × (Fin N → R))) (v : Fin N → R) : Fin N → R :=
  v - ∑ i : Fin γ.length, ((γ.get i).2 ⬝ᵥ v) • (γ.get i).1

theorem dot_corr_of_orth (γ : List ((Fin N → R) × (Fin N → R))) (u v : Fin N → R)
    (hu : ∀ z ∈ γ, u ⬝ᵥ z.1 = 0) : u ⬝ᵥ corr γ v = u ⬝ᵥ v := by
  unfold corr
  rw [dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero, sub_zero]
  intro i _
  rw [dotProduct_smul, hu _ (List.get_mem γ i), smul_zero]

theorem form_dot_corr (γ : List ((Fin N → R) × (Fin N → R))) (hγ : γ ∈ splitSeq R N)
    (z : (Fin N → R) × (Fin N → R)) (hz : z ∈ γ) (v : Fin N → R) : z.2 ⬝ᵥ corr γ v = 0 := by
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hz
  have h : ∀ i j : Fin γ.length, (γ.get i).2 ⬝ᵥ (γ.get j).1 = if i = j then 1 else 0 := hγ
  unfold corr
  rw [dotProduct_sub, dotProduct_sum]
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin γ.length)),
      (γ.get k).2 ⬝ᵥ (((γ.get i).2 ⬝ᵥ v) • (γ.get i).1) =
        if k = i then (γ.get i).2 ⬝ᵥ v else 0 := by
    intro i _
    rw [dotProduct_smul, h k i, smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq Finset.univ k, if_pos (Finset.mem_univ _),
    sub_self]

end GlobalTheory.SeqCx.RowLink

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn : ∀ (R : Type) [CommRing R] (N : ℕ) (γ σ : List ((Fin N → R) × (Fin N → R))), γ ∈ splitSeq R N → σ ∈ splitSeq R N → (∀ y ∈ σ, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0) → ∃ ρ ∈ splitSeq R N, ρ.length = γ.length + σ.length ∧ linkIn {x | x ∈ splitSeq R N ∧ ∀ y ∈ x, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0} {y | ∀ z ∈ γ, z.2 ⬝ᵥ y.1 = 0} σ = linkIn (splitSeq R N) Set.univ ρ := by
  intro R _ N γ σ hγ hσ hσγ
  obtain ⟨σ', hσ'eq⟩ : ∃ s, s = σ.map (fun y => (GlobalTheory.SeqCx.RowLink.corr γ y.1, y.2)) := ⟨_, rfl⟩
  have hc : ∀ y ∈ σ, ∀ v, y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ v = y.2 ⬝ᵥ v :=
    fun y hy v => GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ y.2 v (hσγ y hy)
  have hσ's : σ' ∈ splitSeq R N := by
    rw [GlobalTheory.SeqCx.RowLink.mem_splitSeq_iff] at hσ ⊢
    rw [hσ'eq]
    refine ⟨?_, ?_⟩
    · intro y' hy'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
      show y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ y.1 = 1
      rw [hc y hy]
      exact hσ.1 y hy
    · rw [List.pairwise_map]
      refine hσ.2.imp_of_mem ?_
      intro a b ha hb hab
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at hab ⊢
      exact ⟨(hc a ha b.1).trans hab.1, (hc b hb a.1).trans hab.2⟩
  have horth : ∀ a ∈ γ, ∀ b ∈ σ', GlobalTheory.SeqCx.RowLink.Orth a b := by
    intro a ha b hb
    rw [hσ'eq] at hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    simp only [GlobalTheory.SeqCx.RowLink.Orth]
    exact ⟨GlobalTheory.SeqCx.RowLink.form_dot_corr γ hγ a ha y.1, hσγ y hy a ha⟩
  have hρ : γ ++ σ' ∈ splitSeq R N :=
    (GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff γ σ').mpr ⟨hγ, hσ's, horth⟩
  refine ⟨γ ++ σ', hρ, by rw [List.length_append, hσ'eq, List.length_map], ?_⟩
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_univ, implies_true, true_and, List.append_assoc,
    GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff, List.mem_append]
  constructor
  · rintro ⟨hS, ⟨-, hw, hσw⟩, hz⟩
    refine ⟨hγ, ⟨hσ's, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      rw [hσ'eq] at ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      have h1 := hσw y hy b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 y.1 (hz b (Or.inr hb))).trans h1.2⟩
    · intro a ha b hb
      rcases hb with hb | hb
      · exact horth a ha b hb
      · simp only [GlobalTheory.SeqCx.RowLink.Orth]
        exact ⟨hS b hb a ha, hz b (Or.inr hb) a ha⟩
  · rintro ⟨-, ⟨-, hw, hσ'w⟩, hγx⟩
    refine ⟨fun x hx z hz => And.left (hγx z hz x (Or.inr hx)), ⟨hσ, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      have hbγ : ∀ z ∈ γ, b.2 ⬝ᵥ z.1 = 0 := fun z hz => And.right (hγx z hz b (Or.inr hb))
      have h1 := hσ'w (GlobalTheory.SeqCx.RowLink.corr γ a.1, a.2)
        (by rw [hσ'eq]; exact List.mem_map.mpr ⟨a, ha, rfl⟩) b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 a.1 hbγ).symm.trans h1.2⟩
    · intro y hy z hz
      rcases hy with hy | hy
      · exact hσγ y hy z hz
      · exact And.right (hγx z hz y (Or.inr hy))

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSyzygyFactorization
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.TruncFirstCycles

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  intro k G _ _ C d hdd hsurj hex
  have hz0 : ∀ x : C 2, (d 0).hom ((d 1).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 0)
    simpa [Rep.hom_comp] using h
  have hz1 : ∀ x : C 3, (d 1).hom ((d 2).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 1)
    simpa [Rep.hom_comp] using h
  let K := (d 0).hom.ker
  let ι : Rep.of K.toRepresentation ⟶ C 1 :=
    Rep.ofHom (σ := (C 1).ρ) ⟨K.toSubmodule.subtype, fun g => by ext; rfl⟩
  let bl : C 2 →ₗ[k] K.toSubmodule :=
    (d 1).hom.toLinearMap.codRestrict K.toSubmodule (fun x => hz0 x)
  let b : C 2 ⟶ Rep.of K.toRepresentation :=
    Rep.ofHom (ρ := (C 2).ρ) ⟨bl, fun g => by
      ext x
      exact Rep.hom_comm_apply (d 1) g x⟩
  have hιd : ι ≫ d 0 = 0 := by
    apply Rep.hom_ext
    ext x
    exact x.2
  refine ⟨Rep.of K.toRepresentation, ι, hιd, b, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
          (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
        mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
        epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  · apply Rep.hom_ext
    ext x
    rfl
  · intro z
    obtain ⟨y, hy⟩ := (hex z.1).1 z.2
    exact ⟨y, Subtype.ext hy⟩
  · apply Rep.hom_ext
    ext x
    exact hz1 x
  · intro h2 y
    rw [← h2 y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end GlobalTheory.HomStab.TruncFirstCycles

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_syzygy_factorization : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  first
  | exact @GlobalTheory.HomStab.TruncFirstCycles.main
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyLongExactMapsNaturalOfRes
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

private theorem groupHomology_chainsMap_comp_comm_of_compat (k G H : Type) [CommRing k] [Group G] [Group H]
    (φ : H →* G) (A B : Rep k H) (C D : Rep k G)
    (f : A ⟶ B) (g : C ⟶ D) (u : A ⟶ Rep.res φ C) (v : B ⟶ Rep.res φ D)
    (h : ∀ a, v.hom (f.hom a) = g.hom (u.hom a)) :
    groupHomology.chainsMap (MonoidHom.id H) f ≫ groupHomology.chainsMap φ v =
      groupHomology.chainsMap φ u ≫ groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp [groupHomology.chainsMap_f_single, h]

theorem groupHomology_δ_natural_changeGroup : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)) (hX : X.ShortExact) (hY : Y.ShortExact) (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, groupHomology.δ hX (n + 1) n rfl ≫ groupHomology.map φ u₁ n = groupHomology.map φ u₃ (n + 1) ≫ groupHomology.δ hY (n + 1) n rfl ∧ hMap X.f n ≫ groupHomology.map φ u₂ n = groupHomology.map φ u₁ n ≫ hMap Y.f n ∧ hMap X.g n ≫ groupHomology.map φ u₃ n = groupHomology.map φ u₂ n ≫ hMap Y.g n := by
  intro k G H _ _ _ φ X Y hX hY u₁ u₂ u₃ h₁ h₂ n
  have c₁ := groupHomology_chainsMap_comp_comm_of_compat k G H φ _ _ _ _ X.f Y.f u₁ u₂ h₁
  have c₂ := groupHomology_chainsMap_comp_comm_of_compat k G H φ _ _ _ _ X.g Y.g u₂ u₃ h₂
  have d₁ := congrArg (fun f => HomologicalComplex.homologyMap f n) c₁
  have d₂ := congrArg (fun f => HomologicalComplex.homologyMap f n) c₂
  simp only [HomologicalComplex.homologyMap_comp] at d₁ d₂
  refine ⟨?_, d₁, d₂⟩
  let Φ : X.map (groupHomology.chainsFunctor k H) ⟶ Y.map (groupHomology.chainsFunctor k G) :=
    { τ₁ := groupHomology.chainsMap φ u₁
      τ₂ := groupHomology.chainsMap φ u₂
      τ₃ := groupHomology.chainsMap φ u₃
      comm₁₂ := c₁.symm
      comm₂₃ := c₂.symm }
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (groupHomology.map_chainsFunctor_shortExact hX) (groupHomology.map_chainsFunctor_shortExact hY)
    (n + 1) n rfl

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.groupHomology_longExact_maps_natural_of_res : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)) (hX : X.ShortExact) (hY : Y.ShortExact) (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, groupHomology.δ hX (n + 1) n rfl ≫ groupHomology.map φ u₁ n = groupHomology.map φ u₃ (n + 1) ≫ groupHomology.δ hY (n + 1) n rfl ∧ hMap X.f n ≫ groupHomology.map φ u₂ n = groupHomology.map φ u₁ n ≫ hMap Y.f n ∧ hMap X.g n ≫ groupHomology.map φ u₃ n = groupHomology.map φ u₂ n ≫ hMap Y.g n := by
  first
  | exact @GlobalTheory.HomStab.groupHomology_δ_natural_changeGroup
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HMapSumZsmulAdd
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem chainsMap_id_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (f + g) =
      groupHomology.chainsMap (MonoidHom.id G) f + groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp only [groupHomology.chainsMap_f_single, HomologicalComplex.add_f_apply]
  simp [groupHomology.chainsMap_f_single]
  rw [← Finsupp.single_add]
  rfl

theorem hMap_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) (n : ℕ) :
    hMap (f + g) n = hMap f n + hMap g n := by
  unfold hMap groupHomology.map
  rw [chainsMap_id_add, HomologicalComplex.homologyMap_add]

noncomputable def hMapHom {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    (A ⟶ B) →+ (groupHomology A n ⟶ groupHomology B n) :=
  AddMonoidHom.mk' (fun f => hMap f n) fun f g => hMap_add f g n

theorem hMap_additive : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  intro k G _ _ A B n
  refine ⟨fun f g => hMap_add f g n, ?_, ?_, ?_⟩
  · exact map_zero (hMapHom A B n)
  · intro m f
    exact map_zsmul (hMapHom A B n) m f
  · intro ι T f
    exact map_sum (hMapHom A B n) f T

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.hMap_sum_zsmul_add : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  first
  | exact @GlobalTheory.HomStab.hMap_additive
  | exact @GlobalTheory.HomStab.hMap_add
  | exact @GlobalTheory.HomStab.chainsMap_id_add
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStaircaseStepSurjective
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem homStab_step : ∀ (k G : Type) [CommRing k] [Group G] (C₃ C₂ Z₁ C₁ Z₀ : Rep k G) (a : C₃ ⟶ C₂)
    (b : C₂ ⟶ Z₁) (ι : Z₁ ⟶ C₁) (e : C₁ ⟶ Z₀) (h : ι ≫ e = 0), (ShortComplex.mk ι e h).ShortExact →
    a ≫ b = 0 → ∀ q : ℕ, Function.Surjective (hMap b q).hom →
    Function.Exact (hMap a q).hom (hMap (b ≫ ι) q).hom → Function.Surjective (hMap e (q + 1)).hom := by
  intro k G _ _ C₃ C₂ Z₁ C₁ Z₀ a b ι e h hX hab q hb hex
  have hcomp : ∀ {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ),
      hMap (f ≫ g) n = hMap f n ≫ hMap g n :=
    fun f g n => (groupHomology.functor k G n).map_comp f g
  have hzero : hMap (0 : C₃ ⟶ Z₁) q = 0 := (groupHomology.functor k G q).map_zero _ _
  have hinj : Function.Injective (hMap ι q).hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := hb z
    have hy : (hMap (b ≫ ι) q).hom y = 0 := by
      rw [hcomp]
      simpa using hz
    obtain ⟨x, rfl⟩ := (hex y).1 hy
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomp, hab, hzero]
    rfl
  intro w
  have h3 := groupHomology.mapShortComplex₃_exact hX (i := q + 1) (j := q) rfl
  have hδ : (groupHomology.δ hX (q + 1) q rfl).hom w = 0 := by
    apply hinj
    rw [map_zero]
    exact (groupHomology.mapShortComplex₁ hX (i := q + 1) (j := q) rfl).moduleCat_zero_apply w
  exact (ShortComplex.moduleCat_exact_iff _).1 h3 w hδ

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
end

