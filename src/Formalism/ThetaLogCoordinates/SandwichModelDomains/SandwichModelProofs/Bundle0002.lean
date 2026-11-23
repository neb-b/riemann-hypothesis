module

public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Ascent
section
open MvPolynomial

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem asc_map_weyl (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  set φ : ℤ →+* O := Int.castRingHom O with hφ
  have hrow : ∀ (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) ℤ),
      rowGen O a b (map φ g) = Polynomial.map (map φ) (rowGen ℤ a b g) := by
    intro a b g
    have key : ((rowGen O a b).toRingHom.comp (map φ) :
          MvPolynomial (Fin r × Fin n) ℤ →+* Polynomial (MvPolynomial (Fin r × Fin n) O)) =
        (Polynomial.mapRingHom (map φ)).comp (rowGen ℤ a b).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [← RingHom.comp_apply, eq_intCast, ← RingHom.comp_apply, eq_intCast]
      · intro v
        simp only [RingHom.comp_apply]
        (simp [rowGen]) <;> (try split_ifs) <;> (try simp)
    exact RingHom.congr_fun key g
  have hdiv : ∀ (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (rowDiv ℤ a b k g) = rowDiv O a b k (map φ g) := by
    intro a b k g
    unfold rowDiv
    rw [hrow, Polynomial.coeff_map]
  have hword : ∀ (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (applyWord ℤ w g) = applyWord O w (map φ g) := by
    intro w g
    induction w with
    | nil => rfl
    | cons x w ih =>
      show map φ (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g)) =
        rowDiv O x.1 x.2.1 x.2.2 (applyWord O w (map φ g))
      rw [hdiv, ih]
  have hhw : map φ (hw ℤ hn ν) = hw O hn ν := by
    unfold hw
    rw [map_prod]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_pow]
    congr 1
    unfold lpMinor
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    try dsimp only
    rw [hword, hhw]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_zsmul]
    first
      | exact zsmul_mem hx c
      | exact Submodule.smul_of_tower_mem _ c hx

theorem ascent_domain_holds : AscentDomain := by
  intro p r n hn ν e h O _ _ hO x hx
  rw [standardMonomialSpanDomain O r n ν] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hy
    have hZ : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := by
      rw [← hsh]; exact bidetMem ℤ r n K sz hsz I
    obtain ⟨c, hc, hm⟩ := h _ hZ
    have h2 := asc_map_weyl O hn ν _ hm
    have e2 : map (Int.castRingHom O) ((c * (p : ℤ) ^ e) • bideterminant ℤ sz hsz I) =
        ((c : ℤ) : O) • (((p : O) ^ e) • bideterminant O sz hsz I) := by
      rw [smul_eq_C_mul, map_mul, map_C, ldlat_map_bidet, smul_smul, smul_eq_C_mul]
      simp
    rw [e2] at h2
    obtain ⟨u, hu⟩ := hO c hc
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h2
    rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at h3
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

end Formalism.InvariantFactorPaths.INST
end

-- bundled from Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Descent
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem dsc_denominator (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ g ∈ dualWeyl ℤ r n ν, N • g ∈ weyl ℤ r n hn ν := by
  obtain ⟨b, ⟨_, hspan, _⟩, _⟩ := sSBasis ℤ r n ν
  have : Fintype (ssIdx r n ν) := (sSIdxFinite r n ν).fintype
  have hb : ∀ i, b i ∈ dualWeyl ℤ r n ν := fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc0 hc using fun i => weylRational r n hn ν hν (b i) (hb i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i, fun g hg => ?_⟩
  rw [← hspan] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i), mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hc i)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem dsc_split (p : ℕ) [hp : Fact p.Prime] (N : ℤ) (hN : N ≠ 0) :
    ∃ (k : ℕ) (c : ℤ), N = (p : ℤ) ^ k * c ∧ ¬ (p : ℤ) ∣ c := by
  have hfin : FiniteMultiplicity (p : ℤ) N :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.out.ne_one, hN⟩
  obtain ⟨c, h1, h2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, h1, h2⟩

theorem dsc_approx (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (k : ℕ)
    (y : MvPolynomial (Fin r × Fin n) ℤ_[p]) (hy : y ∈ weyl ℤ_[p] r n hn ν) :
    ∃ d ∈ weyl ℤ r n hn ν, ∃ z : MvPolynomial (Fin r × Fin n) ℤ_[p],
      y = map (Int.castRingHom ℤ_[p]) d + ((p : ℤ_[p]) ^ k) • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, 0, ?_⟩
    simp only [smul_zero, add_zero]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, z1, rfl⟩ := hx
    obtain ⟨d2, hd2, z2, rfl⟩ := hy
    refine ⟨d1 + d2, Submodule.add_mem _ hd1 hd2, z1 + z2, ?_⟩
    rw [map_add (f := _), smul_add]; abel
  | smul a x _ hx =>
    obtain ⟨d, hd, z, rfl⟩ := hx
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ k * a' := by
      rw [← ha']; ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • d, Submodule.smul_mem _ _ hd,
      a' • map (Int.castRingHom ℤ_[p]) d + a • z, ?_⟩
    have hm : map (Int.castRingHom ℤ_[p]) (((PadicInt.appr a k : ℕ) : ℤ) • d) =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]; simp
    have h1 : a • map (Int.castRingHom ℤ_[p]) d =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d +
          ((p : ℤ_[p]) ^ k * a') • map (Int.castRingHom ℤ_[p]) d := by
      rw [← add_smul, ← ha]
    rw [hm, smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a, h1, add_assoc]

theorem dsc_divide (p : ℕ) [Fact p.Prime] {σ : Type*} (k : ℕ) (g : MvPolynomial σ ℤ)
    (z : MvPolynomial σ ℤ_[p]) (h : map (Int.castRingHom ℤ_[p]) g = ((p : ℤ_[p]) ^ k) • z) :
    ∃ g1 : MvPolynomial σ ℤ, g = ((p : ℤ) ^ k) • g1 := by
  have hd : C ((p : ℤ) ^ k) ∣ g := by
    rw [C_dvd_iff_dvd_coeff]
    intro m
    rw [← PadicInt.pow_p_dvd_int_iff]
    have := congrArg (AddMonoidAlgebra.coeff · m) h
    rw [coeff_map, coeff_smul] at this
    exact ⟨AddMonoidAlgebra.coeff z m, by simpa using this⟩
  obtain ⟨g1, rfl⟩ := hd
  exact ⟨g1, by rw [smul_eq_C_mul]⟩

theorem descent_over_integers : DescentZ := by
  intro p _ r n hn ν hν e hyp f hf
  obtain ⟨N, hN0, hN⟩ := dsc_denominator r n hn ν hν
  obtain ⟨k, c, hNc, hc⟩ := dsc_split p N hN0
  have hmf : map (Int.castRingHom ℤ_[p]) f ∈ dualWeyl ℤ_[p] r n ν :=
    dualWeylMap ℤ ℤ_[p] (Int.castRingHom ℤ_[p]) r n ν f hf
  obtain ⟨d, hd, z, hz⟩ := dsc_approx p r n hn ν k _ (hyp _ hmf)
  have hmap : map (Int.castRingHom ℤ_[p]) (((p : ℤ) ^ e) • f - d) = ((p : ℤ_[p]) ^ k) • z := by
    rw [map_sub, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    have : (Int.castRingHom ℤ_[p]) ((p : ℤ) ^ e) = (p : ℤ_[p]) ^ e := by simp
    rw [this, hz]; abel
  obtain ⟨g1, hg1⟩ := dsc_divide p k _ z hmap
  have hg0 : ((p : ℤ) ^ e) • f - d ∈ dualWeyl ℤ r n ν :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (weylLeDual ℤ r n hn ν hν hd)
  have hpk : ((p : ℤ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hg1m : g1 ∈ dualWeyl ℤ r n ν := dualWeylSat ℤ r n ν _ g1 hpk (hg1 ▸ hg0)
  refine ⟨c, hc, ?_⟩
  have key : (c * (p : ℤ) ^ e) • f = c • d + N • g1 := by
    rw [hNc, mul_comm ((p : ℤ) ^ k) c, mul_smul, mul_smul, ← hg1, smul_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hd) (hN g1 hg1m)

end Formalism.InvariantFactorPaths.INST
end
end

-- bundled from Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Spread
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

lemma spr_rowDeg_bidet (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin r) :
    rowDeg m a = ∑ k : Fin K, ∑ q : Fin (sz k), (Pi.single (I k q) 1 : Fin r → ℕ) a := by
  have h := ldbasis_bidet_rowHom R sz hsz I (mem_support_iff.mp hm)
  rw [← ldrow_weight_rowW, h]
  simp only [Finset.sum_apply]

lemma spr_count_le {r s : ℕ} (I : Fin s → Fin r) (hI : Function.Injective I) (a : Fin r) :
    ∑ q : Fin s, (Pi.single (I q) 1 : Fin r → ℕ) a ≤ if 0 < s then 1 else 0 := by
  classical
  have h1 : ∑ q : Fin s, (Pi.single (I q) 1 : Fin r → ℕ) a
      = (Finset.univ.filter fun q : Fin s => I q = a).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : I q = a
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [h1]
  by_cases hs : 0 < s
  · rw [if_pos hs, Finset.card_le_one]
    intro x hx y hy
    exact hI ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · have hs0 : s = 0 := by omega
    subst hs0
    simp

lemma spr_one_le_count {n s : ℕ} (I : Fin s → Fin n) (hI : Function.Injective I) (hs : s = n) (a : Fin n) :
    1 ≤ ∑ q : Fin s, (Pi.single (I q) 1 : Fin n → ℕ) a := by
  classical
  subst hs
  obtain ⟨q, rfl⟩ := (Finite.injective_iff_surjective.mp hI) a
  calc 1 = (Pi.single (I q) 1 : Fin s → ℕ) (I q) := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun q' : Fin s => (Pi.single (I q') 1 : Fin s → ℕ) (I q))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

lemma spr_bidet_le (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (hI : ∀ k, Function.Injective (I k)) (l : ℕ)
    (hl : ∀ t : Fin n, shapeDeg sz t ≤ l)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin r) : rowDeg m a ≤ l := by
  classical
  rw [spr_rowDeg_bidet R sz hsz I m hm a]
  refine (Finset.sum_le_sum fun k _ => spr_count_le (I k) (hI k) a).trans ?_
  rw [← Finset.card_filter]
  by_cases hn : 0 < n
  · exact hl ⟨0, hn⟩
  · have : (Finset.univ.filter fun k : Fin K => 0 < sz k) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun k _ => ?_
      have := hsz k
      omega
    rw [this]
    simp

lemma spr_le_bidet (R : Type*) [CommRing R] {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, Function.Injective (I k)) (lo : ℕ)
    (hlo : ∀ t : Fin n, lo ≤ shapeDeg sz t)
    (m : Fin n × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin n) : lo ≤ rowDeg m a := by
  classical
  rw [spr_rowDeg_bidet R sz hsz I m hm a]
  have hn : n - 1 < n := by have := a.isLt; omega
  refine (hlo ⟨n - 1, hn⟩).trans ?_
  unfold shapeDeg
  rw [Finset.card_filter]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : n - 1 < sz k
  · rw [if_pos hk]
    exact spr_one_le_count (I k) (hI k) (by have := hsz k; omega) a
  · rw [if_neg hk]
    exact Nat.zero_le _

lemma spr_support_induction (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ)
    (P : (Fin r × Fin n →₀ ℕ) → Prop)
    (hP : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r),
      shapeDeg sz = ν → (∀ i, StrictMono (I i)) → ∀ m ∈ (bideterminant R sz hsz I).support, P m)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : ∀ m ∈ f.support, P m := by
  classical
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R r n ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨_, _, K, sz, hsz, I, hsh, hmono, hbi⟩ := hb i
    rw [hbi]
    exact hP K sz hsz I hsh hmono
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

lemma spr_upper (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ) (hl : ∀ t, ν t ≤ l)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin r) : rowDeg m a ≤ l := by
  refine spr_support_induction R r n ν (fun m => rowDeg m a ≤ l) ?_ f hf m hm
  intro K sz hsz I hsh hmono m hm
  exact spr_bidet_le R sz hsz I (fun k => (hmono k).injective) l (by rw [hsh]; exact hl) m hm a

lemma spr_lower (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ν : Fin n → ℕ) (lo : ℕ) (hlo : ∀ t, lo ≤ ν t)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n ν) (m : Fin n × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin n) : lo ≤ rowDeg m a := by
  refine spr_support_induction R n n ν (fun m => lo ≤ rowDeg m a) ?_ f hf m hm
  intro K sz hsz I hsh hmono m hm
  exact spr_le_bidet R sz hsz I (fun k => (hmono k).injective) lo (by rw [hsh]; exact hlo) m hm a

theorem spread_top_holds : SpreadTop := by
  intro R _ _ r n ν l hl f hf g _ m hm m' _ a
  exact (spr_upper R r n ν l hl f hf m hm a).trans (Nat.le_add_left _ _)

theorem spread_square_holds : SpreadSquare := by
  intro R _ _ n ν l hl f hf g hg m hm m' hm' a
  have : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨s, hs⟩ := Finite.exists_max ν
  obtain ⟨t, ht⟩ := Finite.exists_min ν
  have h1 := spr_upper R n n ν (ν s) hs f hf m hm a
  have h2 := spr_lower R n ν (ν t) ht g hg m' hm' a
  have h3 := hl s t
  omega

end Formalism.InvariantFactorPaths.INST
end
end

