module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
section
noncomputable section
namespace GlobalTheory.GLGen
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

theorem single_neg' (x y : Fin n) (a : R) : single x y (-a) = -single x y a := by
  ext p q; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp

theorem diag_transv_diag (a b : Fin n → R) (hab : ∀ k, a k * b k = 1) {i j : Fin n} (hij : i ≠ j) (c : R) :
    diagonal a * transvection i j c * diagonal b = transvection i j (a i * c * b j) := by
  have h1 : diagonal a * diagonal b = (1 : Matrix (Fin n) (Fin n) R) := by
    rw [diagonal_mul_diagonal]; simp [hab]
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  congr 1
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h <;> simp_all

theorem w_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-((u⁻¹ : Rˣ) : R)) * transvection i j (u : R) =
      1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1 := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, z1, z2, z3, z4]
  simp only [mul_neg, neg_mul, Units.mul_inv, Units.inv_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, single_neg', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]
  abel

theorem ww_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    (1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) *
      (1 + single i j ((-1 : Rˣ) : R) + single j i (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) =
      diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1) := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, z1, z2, z3, z4]
  clear z1 z2 z3 z4
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hji : j ≠ i := Ne.symm hij
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi; simp [hij, hji]
    · by_cases hpj : p = j
      · subst hpj; simp [hij, hji]
      · simp [hpi, hpj, Ne.symm hpi, Ne.symm hpj]
  · by_cases hpi : p = i <;> by_cases hqi : q = i <;> by_cases hpj : p = j <;> by_cases hqj : q = j <;>
      simp_all [eq_comm]

def diagU (u : Fin n → Rˣ) : GL (Fin n) R :=
  ⟨diagonal (fun k => (u k : R)), diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem diagU_val (u : Fin n → Rˣ) : ((diagU u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (u k : R)) := rfl

theorem diagU_inv_val (u : Fin n → Rˣ) :
    (((diagU u)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)) := rfl

theorem diagU_mul (u v : Fin n → Rˣ) : diagU (u * v) = diagU u * diagU v := by
  ext : 1
  simp only [Units.val_mul, diagU_val, diagonal_mul_diagonal, Pi.mul_apply]

theorem diagU_one : diagU (1 : Fin n → Rˣ) = 1 := by
  ext : 1
  simp [diagU_val]

def transvGL {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]⟩

def transvSet (R : Type) [CommRing R] (n : ℕ) : Set (GL (Fin n) R) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin n) (Fin n) R) = transvection i j c}

def elem (R : Type) [CommRing R] (n : ℕ) : Subgroup (GL (Fin n) R) := Subgroup.closure (transvSet R n)

theorem transvGL_mem {i j : Fin n} (hij : i ≠ j) (c : R) : transvGL hij c ∈ elem R n :=
  Subgroup.subset_closure ⟨i, j, c, hij, rfl⟩

theorem conj_mem (u : Fin n → Rˣ) {e : GL (Fin n) R} (he : e ∈ elem R n) :
    diagU u * e * (diagU u)⁻¹ ∈ elem R n := by
  have hle : elem R n ≤ (elem R n).comap (MulAut.conj (diagU u)).toMonoidHom := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨i, j, (u i : R) * c * ((u j)⁻¹ : Rˣ), hij, ?_⟩
    rw [Units.val_mul, Units.val_mul, hg, diagU_val, diagU_inv_val]
    exact diag_transv_diag _ _ (fun k => Units.mul_inv (u k)) hij c
  simpa using hle he

theorem whitehead_mem {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) ∈ elem R n := by
  have e : diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) =
      transvGL hij (u : R) * transvGL hij.symm (-((u⁻¹ : Rˣ) : R)) * transvGL hij (u : R) *
      (transvGL hij ((-1 : Rˣ) : R) * transvGL hij.symm (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) *
        transvGL hij ((-1 : Rˣ) : R)) := by
    ext : 1
    simp only [Units.val_mul, transvGL, diagU_val]
    rw [w_eq hij u, w_eq hij (-1), ww_eq hij u]
    congr 1
    funext k
    split_ifs <;> rfl
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) <;> exact transvGL_mem _ _

theorem diagU_inv (u : Fin n → Rˣ) : diagU u⁻¹ = (diagU u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagU_mul, inv_mul_cancel, diagU_one])

def diagHomU : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun := diagU
  map_one' := diagU_one
  map_mul' := diagU_mul

theorem pair_mem_elem (i j : Fin n) (a : Rˣ) :
    diagU (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) ∈ elem R n := by
  by_cases hij : i = j
  · subst hij
    have : (Pi.mulSingle i a * Pi.mulSingle i a⁻¹ : Fin n → Rˣ) = 1 := by
      rw [← Pi.mulSingle_mul]; simp
    rw [this, diagU_one]
    exact one_mem _
  · have hji : j ≠ i := fun h => hij h.symm
    have : (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) =
        fun k => if k = i then a else if k = j then a⁻¹ else 1 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    rw [this]
    exact whitehead_mem hij a

theorem diag_mem_of_prod (u : Fin n → Rˣ) (hu : ∏ k, u k = 1) : diagU u ∈ elem R n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : diagU u = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
    exact one_mem _
  · let j : Fin n := ⟨0, hpos⟩
    have key : u = ∏ k, (Pi.mulSingle k (u k) * Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ) := by
      rw [Finset.prod_mul_distrib, Finset.univ_prod_mulSingle]
      have : (∏ k, (Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)) = 1 := by
        have h := map_prod (MonoidHom.mulSingle (fun _ : Fin n => Rˣ) j) (fun k => (u k)⁻¹)
          Finset.univ
        rw [Finset.prod_inv_distrib, hu, inv_one, map_one] at h
        exact h.symm
      rw [this, mul_one]
    have : u ∈ (elem R n).comap (diagHomU (R := R) (n := n)) := by
      rw [key]
      exact Subgroup.prod_mem _ (fun k _ => pair_mem_elem k j (u k))
    exact this

theorem det_eq_one_of_mem {e : GL (Fin n) R} (he : e ∈ elem R n) : GeneralLinearGroup.det e = 1 := by
  have hle : elem R n ≤ (GeneralLinearGroup.det : GL (Fin n) R →* Rˣ).ker := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ hij]
    rfl
  exact hle he

theorem mem_of_det_eq_one : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) →
    ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R),
      u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  intro R _ hsr n H hH a ha
  have hEH : elem R n ≤ H := Subgroup.closure_le _ |>.2 (by
    rintro g ⟨i, j, c, hij, hg⟩; exact hH i j hij c g hg)
  have hSR : PI.VolSemiDirect.W.Cj.HasStableRangeOne R := fun a b x y h =>
    hsr a b ⟨x, y, by rw [← h]; ring⟩
  have hmem := PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag R hSR n a
  have key : ∀ g ∈ Subgroup.closure ({g : GL (Fin n) R | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin n → R, (g : Matrix (Fin n) (Fin n) R) = Matrix.diagonal d}),
      ∃ u : Fin n → Rˣ, g * diagU u ∈ elem R n := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨i, j, c, hij, hg⟩ | ⟨d, hd⟩
      · exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.subset_closure ⟨i, j, c, hij, hg⟩⟩
      · have hu : ∀ k, IsUnit (d k) := fun k => by
          have h : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          have h' := congrFun (congrFun h k) k
          rw [hd, Matrix.mul_diagonal, one_apply_eq] at h'
          exact ⟨⟨d k, _, by rw [mul_comm]; exact h', h'⟩, rfl⟩
        refine ⟨fun k => (hu k).unit⁻¹, ?_⟩
        have e : g * diagU (fun k => (hu k).unit⁻¹) = 1 := by
          ext : 1
          rw [Units.val_mul, hd, diagU_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
          congr 1
          funext k
          exact (hu k).mul_val_inv
        rw [e]; exact Subgroup.one_mem _
    | one => exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨v * u, ?_⟩
      have h := Subgroup.mul_mem _ hu (conj_mem u⁻¹ hv)
      rw [diagU_inv, inv_inv] at h
      convert h using 1
      rw [diagU_mul]
      group
    | inv x _ hx =>
      obtain ⟨u, hu⟩ := hx
      refine ⟨u⁻¹, ?_⟩
      have h := conj_mem u (Subgroup.inv_mem _ hu)
      rw [diagU_inv]
      convert h using 1
      group
  obtain ⟨u, hu⟩ := key a hmem
  have h1 := det_eq_one_of_mem hu
  rw [map_mul, ha, one_mul] at h1
  have hprod : ∏ k, u k = 1 := by
    have h2 := congrArg Units.val h1
    rw [GeneralLinearGroup.val_det_apply, diagU_val, det_diagonal] at h2
    ext
    rw [Units.coe_prod]
    simpa using h2
  have hd := diag_mem_of_prod u hprod
  have e : a = (a * diagU u) * (diagU u)⁻¹ := by group
  rw [e]
  exact hEH (Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hd))

end GlobalTheory.GLGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmField
section
noncomputable section

namespace GlobalTheory.StableRange

open IsDedekindDomain NumberField

theorem exists_inv_mod_maximal {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (b : S) :
    ∃ y : S, ∀ m : Ideal S, m.IsMaximal → b ∈ m ∨ 1 - b * y ∈ m := by
  let I : Ideal S := (Ideal.jacobson (⊥ : Ideal B)).map (algebraMap B S)
  have hI : ∀ m : Ideal S, m.IsMaximal → I ≤ m := by
    intro m hm
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap B S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) m
    exact sInf_le ⟨bot_le, this⟩
  have hp : ∀ p : Ideal S, p.IsPrime → I ≤ p → p.IsMaximal := by
    intro p hp hIp
    rw [Ideal.map_le_iff_le_comap] at hIp
    have hq : (p.comap (algebraMap B S)).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (p.comap (algebraMap B S)).IsMaximal := by
      rw [Ideal.isMaximal_iff]
      refine ⟨(Ideal.ne_top_iff_one _).1 hq.ne_top, fun J x hJ hx hxJ => ?_⟩
      obtain ⟨y, hy⟩ := hB x
      have h1 : x * (1 - x * y) ∈ p.comap (algebraMap B S) :=
        hIp (Ideal.mem_jacobson_bot.2 hy)
      have h2 := (hq.mem_or_mem h1).resolve_left hx
      have := J.add_mem (hJ h2) (J.mul_mem_right y hxJ)
      simpa using this
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) p hmax
  let M : Submonoid S :=
    { carrier := {s | ∃ (n : ℕ) (y : S), s = b ^ n * (1 - b * y)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, y, rfl⟩ ⟨k, w, rfl⟩
        exact ⟨n + k, y + w - b * y * w, by ring⟩ }
  by_cases hd : Disjoint (I : Set S) (M : Set S)
  · exfalso
    obtain ⟨p, hpp, hIp, hdis⟩ := Ideal.exists_le_prime_disjoint I M hd
    have hm := hp p hpp hIp
    have hb : b ∉ p := fun h => Set.disjoint_left.1 hdis h ⟨1, 0, by simp⟩
    obtain ⟨y, i, hi, hy⟩ := hm.exists_inv hb
    refine Set.disjoint_left.1 hdis hi ⟨0, y, ?_⟩
    rw [← hy]; ring
  · obtain ⟨s, hsI, n, y, rfl⟩ := Set.not_disjoint_iff.1 hd
    refine ⟨y, fun m hm => ?_⟩
    rcases hm.isPrime.mem_or_mem (hI m hm hsI) with h | h
    · exact Or.inl (hm.isPrime.mem_of_pow_mem n h)
    · exact Or.inr h

theorem stable_of_isIntegral {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (a b : S)
    (h : IsCoprime a b) : ∃ t : S, IsUnit (a + t * b) := by
  obtain ⟨y, hy⟩ := exists_inv_mod_maximal hB b
  obtain ⟨u, w, huw⟩ := h
  refine ⟨y * (1 - a), ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := a + y * (1 - a) * b) hn
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hy m hm with hb | hb
  · have e : (1 : S) = u * (a + y * (1 - a) * b) + (w - u * (y * (1 - a))) * b := by
      linear_combination -huw
    rw [e]
    exact m.add_mem (m.mul_mem_left _ hmem) (m.mul_mem_left _ hb)
  · have e : (1 : S) = (a + y * (1 - a) * b) + (1 - a) * (1 - b * y) := by ring
    rw [e]
    exact m.add_mem hmem (m.mul_mem_left _ hb)

theorem stable_of_subrings {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R]
    (hA : ∀ s : Finset A, ∃ B : Subring A, (s : Set A) ⊆ B ∧
      ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1))
    (a b : R) (h : IsCoprime a b) : ∃ t : R, IsUnit (a + t * b) := by
  classical
  obtain ⟨u, w, huw⟩ := h
  choose p hpm hp using fun r : R => (Algebra.IsIntegral.isIntegral (R := A) r)
  obtain ⟨B, hs, hB⟩ := hA ((p a).coeffs ∪ (p b).coeffs ∪ (p u).coeffs ∪ (p w).coeffs)
  have key : ∀ r : R, ((p r).coeffs : Set A) ⊆ B → IsIntegral B r := by
    intro r hr
    refine ⟨(p r).toSubring B hr, (Polynomial.monic_toSubring _ _ hr).2 (hpm r), ?_⟩
    have e : algebraMap B R = (algebraMap A R).comp B.subtype := rfl
    rw [e, ← Polynomial.eval₂_map, Polynomial.map_toSubring]
    exact hp r
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  obtain ⟨t, ht⟩ := stable_of_isIntegral (S := integralClosure B R) hB ⟨a, key a h1⟩ ⟨b, key b h2⟩
    ⟨⟨u, key u h3⟩, ⟨w, key w h4⟩, Subtype.ext huw⟩
  exact ⟨t, ht.map (integralClosure B R).val⟩

variable (K : Type*) [Field K] [NumberField K]

def intOutside (T : Set (HeightOneSpectrum (𝓞 K))) : Subring (AdeleRing (𝓞 K) K) where
  carrier := {x | ∀ v ∉ T, x.2 v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v hv := mul_mem (ha v hv) (hb v hv)
  one_mem' v _ := one_mem (v.adicCompletionIntegers K)
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

def mkAdele {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (f : ∀ w : InfinitePlace K, w.Completion) (g : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hg : ∀ v ∉ T, g v ∈ v.adicCompletionIntegers K) : intOutside K T :=
  ⟨(f, ⟨g, hT.subset fun v hv => by
    by_contra h
    exact hv (hg v h)⟩), hg⟩

theorem isUnit_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (x : intOutside K T)
    (h1 : ∀ w, x.1.1 w ≠ 0) (h2 : ∀ v, x.1.2 v ≠ 0) (h3 : ∀ v ∉ T, Valued.v (x.1.2 v) = 1) :
    IsUnit x := by
  refine IsUnit.of_mul_eq_one (mkAdele K hT (fun w => (x.1.1 w)⁻¹) (fun v => (x.1.2 v)⁻¹)
    fun v hv => ?_) ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h3 v hv, inv_one]
  · refine Subtype.ext (Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_))
    · exact mul_inv_cancel₀ (h1 w)
    · exact mul_inv_cancel₀ (h2 v)

theorem mul_one_sub_mul_inv {L : Type*} [Field L] (x : L) : x * (1 - x * x⁻¹) = 0 := by
  by_cases h : x = 0
  · simp [h]
  · simp [h]

open Classical in
theorem regular_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (x : intOutside K T) :
    ∃ y : intOutside K T, ∀ z : intOutside K T, IsUnit (x * (1 - x * y) * z + 1) := by
  refine ⟨mkAdele K hT (fun w => (x.1.1 w)⁻¹)
    (fun v => if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0) fun v hv => ?_, fun z => ?_⟩
  · split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h.resolve_left hv, inv_one]
    · exact zero_mem _
  · have hv : ∀ v, Valued.v (x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1) = 1 := by
      intro v
      split_ifs with h
      · rw [mul_one_sub_mul_inv]; simp
      · obtain ⟨hT', h1⟩ := not_or.1 h
        have hx : Valued.v (x.1.2 v) ≤ 1 := x.2 v hT'
        have hz : Valued.v (z.1.2 v) ≤ 1 := z.2 v hT'
        rw [mul_zero, sub_zero, mul_one, add_comm]
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        exact (mul_le_of_le_one_right' hz).trans_lt (lt_of_le_of_ne hx h1)
    refine isUnit_intOutside K hT _ (fun w => ?_) (fun v => ?_) (fun v _ => hv v)
    · change x.1.1 w * (1 - x.1.1 w * (x.1.1 w)⁻¹) * z.1.1 w + 1 ≠ 0
      rw [mul_one_sub_mul_inv]; simp
    · intro h0
      have h1 := hv v
      have h2 : x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1 = 0 := h0
      rw [h2] at h1
      simp at h1

theorem stable_adele {R : Type*} [CommRing R] [Algebra (AdeleRing (𝓞 K) K) R]
    [Algebra.IsIntegral (AdeleRing (𝓞 K) K) R] (a b : R) (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  refine stable_of_subrings (A := AdeleRing (𝓞 K) K) (fun s => ?_) a b h
  have hT : (⋃ x ∈ (s : Set (AdeleRing (𝓞 K) K)),
      {v : HeightOneSpectrum (𝓞 K) | x.2 v ∉ v.adicCompletionIntegers K}).Finite :=
    s.finite_toSet.biUnion fun x _ => x.2.2
  refine ⟨intOutside K _, fun x hx v hv => ?_, regular_intOutside K hT⟩
  by_contra h
  exact hv (Set.mem_biUnion hx h)

end GlobalTheory.StableRange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.StableRange.adeles_stableRange_one :
    ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) :=
  fun D a b h => GlobalTheory.StableRange.stable_adele D.host.F a b h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitone
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

theorem OffAnti.idOff_le (D : D7) {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : idOff D P ≤ idOff D Q := by
  unfold idOff
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, h w.1 w.2⟩ le_rfl

theorem OffAnti.congGrp_le {D : D7} (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V g) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V g)) := by
    ext i j
    simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

theorem grpOff_anti : ∀ (D : D7) (S : HSp D) (P Q : Pl D → Prop), (∀ v, Q v → P v) → grpOff S P ≤ grpOff S Q :=
  fun D S _ _ h => OffAnti.congGrp_le S (OffAnti.idOff_le D h)

end GlobalTheory.FinPl
end

