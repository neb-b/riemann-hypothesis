module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MapSpan
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mem_ev_iff_apply_eq_zero_off_diagonal_blocks {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ)
    (Z : Matrix (Fin n) (Fin n) R) :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
  constructor
  · intro h i j hij
    exact (Submodule.mem_bot A).1 ((h i j).2 hij)
  · intro h i j
    exact ⟨fun _ => Submodule.mem_top, fun hij => by rw [h i j hij]; exact Submodule.zero_mem _⟩

theorem UpperTheory.V.Pa.Det.detFr :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∃ D : DetFr (FractionRing x.A) F.G₀ n, D.a = x.a ∧ D.G' = F.G' ∧ (∀ g, D.r g = x.ρX (FractionRing x.A) g) ∧ D.σ = F.conj ∧ ∀ g : F.G₀, D.χF g = algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A (F.ε g : ℤ_[l])) := by
  intro l _ F n x hl hg
  obtain ⟨g₀, hg₀⟩ := hg
  have hev : ∀ g : F.G₀, (mat x.ρ g).map (algebraMap x.A (FractionRing x.A)) ∈
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    intro g
    rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
    intro i j hij
    have h0 := (mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 (x.blk g) i j hij
    rw [Matrix.map_apply, h0, map_zero]
  have hmap : ∀ M ∈ Submodule.span x.A ((mat x.ρ) '' (F.G' : Set F.G₀)),
      M.map (algebraMap x.A (FractionRing x.A)) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      exact Submodule.subset_span ⟨g, hg, rfl⟩
    | zero =>
      have h0 : (0 : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A (FractionRing x.A)) = 0 := by
        ext i j
        simp
      rw [h0]
      exact Submodule.zero_mem _
    | add M N _ _ hM hN =>
      have h0 : (M + N).map (algebraMap x.A (FractionRing x.A)) =
          M.map (algebraMap x.A (FractionRing x.A)) + N.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.add_mem _ hM hN
    | smul c M _ hM =>
      have h0 : (c • M).map (algebraMap x.A (FractionRing x.A)) =
          algebraMap x.A (FractionRing x.A) c • M.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.smul_mem _ _ hM
  have hsingle : ∀ i j : Fin n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) →
      Matrix.single i j (1 : FractionRing x.A) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro i j hij
    have hZ : Matrix.single i j (1 : x.A) ∈ Ev x.A x.A n x.a := by
      rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
      intro k m hkm
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hkm hij
    obtain ⟨s, hs⟩ := x.span _ hZ
    have key := hmap _ hs
    have h1 : ((PowerSeries.X : x.A) ^ s • Matrix.single i j (1 : x.A)).map
        (algebraMap x.A (FractionRing x.A)) =
        algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) • Matrix.single i j (1 : FractionRing x.A) := by
      ext k m
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1] at key
    have hne : algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) ≠ 0 := by
      intro h
      apply pow_ne_zero s (PowerSeries.X_ne_zero (R := x.K))
      apply IsFractionRing.injective x.A (FractionRing x.A)
      rw [h, map_zero]
    have h2 := Submodule.smul_mem _ (algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s))⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  have hspan : Submodule.span (FractionRing x.A)
      ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) =
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, -, rfl⟩
      exact hev g
    · intro Z hZ
      rw [Matrix.matrix_eq_sum_single Z]
      refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
      by_cases hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
      · have h3 : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : FractionRing x.A) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [h3]
        exact Submodule.smul_mem _ _ (hsingle i j hij)
      · rw [(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 hZ i j hij, Matrix.single_zero]
        exact Submodule.zero_mem _
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra h
    have hm : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    have h4 : ((2 : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_ofNat, ← hm, map_ofNat]
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h4
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h5)
  have hc : ∀ g : F.G₀, F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    intro g
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε (g : F.Γ)
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_inv_cancel_right]
  refine ⟨DetFr.mk ?_ x.a x.a_pos x.a_le F.G' ?_ (F.eps x.A (FractionRing x.A)) ?_ g₀ ?_
    ((algebraMap x.A (FractionRing x.A)).mapMatrix.toMonoidHom.comp (mat x.ρ)) hspan hev F.conj ?_ ?_
    (fun g => Units.map (algebraMap x.A (FractionRing x.A)).toMonoidHom
      ((F.eps ℤ_[l] x.A g) ^ (1 - (n : ℤ)))) ?_, rfl, rfl, fun g => rfl, rfl, fun g => rfl⟩
  · have h6 := (h2.map ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))).ne_zero
    rw [RingHom.comp_apply, map_ofNat, map_ofNat] at h6
    exact h6
  · intro g h
    rw [GFrame.G', MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, mul_comm]
  · intro g hg
    rw [GFrame.G', MonoidHom.mem_ker] at hg
    show Units.map _ ((F.ε.comp F.η.ker.subtype) g) = 1
    rw [hg, map_one]
  · intro h
    apply hg₀
    have h7 := congrArg Units.val h
    change algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l])) = 1 at h7
    have h8 : ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
        RingHom.ker ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A)) := by
      rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, h7, map_one, sub_self]
    have h9 := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) h8
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h9
    exact h9
  · intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (g : F.Γ)
    calc F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * (g : F.Γ) * (F.c * F.c)⁻¹ := by group
      _ = (g : F.Γ) := by rw [F.c_sq]; group
  · intro g
    show Units.map _ ((F.ε.comp F.η.ker.subtype) (F.conj g)) = Units.map _ ((F.ε.comp F.η.ker.subtype) g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ (hc g)
  · intro g
    show ((mat x.ρ g).map (algebraMap x.A (FractionRing x.A)))ᵀ *
        (mat x.ρ (F.conj g)).map (algebraMap x.A (FractionRing x.A)) =
        (algebraMap x.A (FractionRing x.A) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) • 1
    have h0 := x.form g
    rw [Units.val_one, Matrix.mul_one] at h0
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h0]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.OmDense
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

open Polynomial

private noncomputable def dsc {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R :=
  resultant M.charpoly (derivative M.charpoly) n n

private theorem dsc_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    dsc (M.map φ) = φ (dsc M) := by
  unfold dsc
  rw [Matrix.charpoly_map, derivative_map, resultant_map_map]

private theorem dsc_ne_iff {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    dsc M ≠ 0 ↔ M.charpoly.Separable := by
  have hm : M.charpoly.Monic := Matrix.charpoly_monic M
  have hd : M.charpoly.natDegree = n := by simp [Matrix.charpoly_natDegree_eq_dim]
  have hle : (derivative M.charpoly).natDegree ≤ n :=
    (natDegree_derivative_le _).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hc : M.charpoly.coeff n = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have h1 : dsc M = resultant M.charpoly (derivative M.charpoly) := by
    unfold dsc
    have := resultant_add_right_deg M.charpoly (derivative M.charpoly) n (derivative M.charpoly).natDegree k le_rfl
    rw [← hk, hc, one_pow, one_mul] at this
    rw [this, hd]
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hm]
  rfl

private theorem sep_iff {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    (M.charpoly.map (algebraMap A (FractionRing A))).Separable ↔ dsc M ≠ 0 := by
  rw [← Matrix.charpoly_map, ← dsc_ne_iff, dsc_map]
  exact (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A)))

private theorem sep_open {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) :
    IsOpen {σ : F.G₀ | ((mat x.ρ σ).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable} := by
  simp only [sep_iff]
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hN : ∃ N : ℕ, dsc (mat x.ρ s) ∉ maximalIdeal x.A ^ N := by
    by_contra hc
    push Not at hc
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal x.A) (maximalIdeal.isMaximal _).ne_top
    have h2 : dsc (mat x.ρ s) ∈ ⨅ N : ℕ, maximalIdeal x.A ^ N := Submodule.mem_iInf _ |>.2 hc
    rw [this] at h2
    exact hs (by simpa using h2)
  obtain ⟨N, hN⟩ := hN
  have hev : ∀ᶠ g in nhds s, ∀ i j, Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ g i j)
      = Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ s i j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact (x.cont i j N).eventually_eq s
  filter_upwards [hev] with g hg h0
  apply hN
  have hM : (mat x.ρ g).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N))
      = (mat x.ρ s).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N)) := by
    ext i j; exact hg i j
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← dsc_map, ← hM, dsc_map, h0, map_zero]

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.omDense :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n h : ℕ} (x : Fin h → NP F n), (∀ i, (x i).N3) → (F.G' : Set F.G₀) ⊆ closure {σ : F.G₀ | σ ∈ F.G' ∧ ∀ i, ((mat (x i).ρ σ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable} := by
  intro l _ F n h x hx σ hσ
  rw [mem_closure_iff]
  intro U hU hσU
  have key : ∀ S : Finset (Fin h), ∃ τ ∈ U ∩ (F.G' : Set F.G₀), ∀ i ∈ S,
      ((mat (x i).ρ τ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨σ, ⟨hσU, hσ⟩, by simp⟩
    | insert a S ha ih =>
      obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := ih
      have ho : IsOpen (U ∩ ⋂ i ∈ S, {σ : F.G₀ | ((mat (x i).ρ σ).charpoly.map
          (algebraMap (x i).A (FractionRing (x i).A))).Separable}) :=
        hU.inter (isOpen_biInter_finset fun i _ => UpperTheory.V.Pa.Det.sep_open (x i))
      obtain ⟨τ', ⟨⟨g1, g2⟩, g3⟩, g4⟩ := hx a _ ho ⟨τ, ⟨h1, Set.mem_iInter₂.2 h3⟩, h2⟩
      refine ⟨τ', ⟨g1, g3⟩, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact g4
      · exact Set.mem_iInter₂.1 g2 i hi
  obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := key Finset.univ
  exact ⟨τ, h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PadicHomUnique
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_unique {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (hl : (l : R) = 0)
    (f g : ℤ_[l] →+* R) : f = g := by
  ext z
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 z)
  have hz : z = y * (l : ℤ_[l]) + (z.appr 1 : ℤ_[l]) := by
    rw [pow_one] at hy; rw [hy]; ring
  rw [hz]
  simp [hl]

private theorem adic_push {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R')
    [IsLocalHom f] {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact map_nonunit f y hy
  exact (ha N).comp (Ideal.quotientMap _ f hle)

private theorem span_push {K K' : Type} [Field K] [Field K'] {n a : ℕ} (j : PowerSeries K →+* PowerSeries K')
    (hj : Function.Injective j) (S : Set (Matrix (Fin n) (Fin n) (PowerSeries K)))
    (h : ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) S) :
    ∀ Z ∈ Ev (PowerSeries K') (PowerSeries K') n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K') ^ s • Z ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
  have hmap : ∀ M ∈ Submodule.span (PowerSeries K) S,
      M.map j ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM => exact Submodule.subset_span ⟨M, hM, rfl⟩
    | zero => simp
    | add M N _ _ h1 h2 => rw [Matrix.map_add _ (map_add j)]; exact add_mem h1 h2
    | smul c M _ h1 =>
      have : (c • M).map j = j c • M.map j := by ext1 p q; simp
      rw [this]; exact Submodule.smul_mem _ _ h1
  have hX : j PowerSeries.X ≠ 0 := fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hX (PowerSeries.X_irreducible (R := K'))
  obtain ⟨u, hu⟩ := hm.dvd
  intro Z hZ
  have key : ∀ p q : Fin n, ∃ s : ℕ, (PowerSeries.X : PowerSeries K') ^ s • Matrix.single p q (Z p q) ∈
      Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro p q
    by_cases hpq : ((p : ℕ) < a) ↔ ((q : ℕ) < a)
    · have hE : Matrix.single p q (1 : PowerSeries K) ∈ Ev (PowerSeries K) (PowerSeries K) n a := by
        intro p' q'
        refine ⟨fun _ => trivial, fun e => ?_⟩
        rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact e hpq
      obtain ⟨s, hs⟩ := h _ hE
      refine ⟨m * s, ?_⟩
      have : (PowerSeries.X : PowerSeries K') ^ (m * s) • Matrix.single p q (Z p q) =
          (u ^ s * Z p q) • ((PowerSeries.X : PowerSeries K) ^ s • Matrix.single p q (1 : PowerSeries K)).map j := by
        ext1 p' q'
        rw [pow_mul, hu]
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs
        · simp only [mul_one, map_pow]; ring
        · simp
      rw [this]
      exact Submodule.smul_mem _ _ (hmap _ hs)
    · have : Z p q = 0 := (Submodule.mem_bot _).1 ((hZ p q).2 hpq)
      exact ⟨0, by simp [this]⟩
  choose s hs using key
  refine ⟨∑ p, ∑ q, s p q, ?_⟩
  rw [Matrix.matrix_eq_sum_single Z, Finset.smul_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hle : s p q ≤ ∑ p, ∑ q, s p q :=
    le_trans (Finset.single_le_sum (f := fun q => s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
      (Finset.single_le_sum (f := fun p => ∑ q, s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
  rw [hd, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ (hs p q)

private theorem pushCh_inj {H A B : Type} [Group H] [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) {χ χ' : H →* Aˣ} (h : pushCh f χ = pushCh f χ') : χ = χ' := by
  ext g
  exact hf (congrArg Units.val (DFunLike.congr_fun h g))

private noncomputable def pushNP {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (K' : Type) [Field K'] [Finite K']
    [Algebra ℤ_[l] K'] (j : x.A →+* PowerSeries K') (hj : Function.Injective j) [IsLocalHom j]
    (he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries K')) : NP F n where
  K := K'
  ρ := pushRep j x.ρ
  cont p q := adic_push j (x.cont p q)
  form g := by
    have h := congrArg (fun M => M.map j) (x.form g)
    have h1 : mat (pushRep j x.ρ) g = (mat x.ρ g).map j := rfl
    have h2 : mat (pushRep j x.ρ) (F.conj g) = (mat x.ρ (F.conj g)).map j := rfl
    have h3 : ((F.eps ℤ_[l] (PowerSeries K') g ^ (1 - (n : ℤ)) : (PowerSeries K')ˣ) : PowerSeries K') =
        j ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) := by
      rw [← he]
      exact (congrArg Units.val (map_zpow (Units.map (j : x.A →* PowerSeries K')) _ _)).symm
    rw [h1, h2, h3]
    simp only [Units.val_one, mul_one, Matrix.map_mul] at h ⊢
    rw [← Matrix.transpose_map, h]
    ext1 p q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  a := x.a
  a_pos := x.a_pos
  a_le := x.a_le
  blk g p q := ⟨fun _ => trivial, fun e => by
    have : mat x.ρ g p q = 0 := (x.blk g p q).2 e
    show j (mat x.ρ g p q) = 0
    rw [this, map_zero]⟩
  span Z hZ := by
    have := span_push j hj _ x.span Z hZ
    rwa [Set.image_image] at this
  ine u g hg := by
    show GeneralLinearGroup.map j (x.ρ g) = 1
    rw [x.ine u g hg, map_one]
  ψ v i := pushCh j (x.ψ v i)
  ψ_mu v i g hg := by
    show Units.map _ (x.ψ v i g) = 1
    rw [x.ψ_mu v i g hg, map_one]
  w v := GeneralLinearGroup.map j (x.w v)
  ty := x.ty
  w_blk v p q e := by
    show j (x.w v p q) = 0
    rw [x.w_blk v p q e, map_zero]
  tri v g := by
    have e : (GeneralLinearGroup.map j (x.w v))⁻¹ * pushRep j x.ρ (F.φ v g) * GeneralLinearGroup.map j (x.w v) =
        GeneralLinearGroup.map j ((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p q) = 0
      rw [(x.tri v g).1 p q hpq, map_zero]
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p p) = j _
      rw [(x.tri v g).2 p]
  N1 v := by
    refine ⟨fun p q hpq e => (x.N1 v).1 p q hpq (pushCh_inj hj e), fun p q hpq e => (x.N1 v).2 p q hpq (pushCh_inj hj ?_)⟩
    rw [e, ← he]
    ext g
    simp

theorem UpperTheory.V.Pa.Det.extEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (A' : Type) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [IsEqDVR l A'] (j₀ : x.A →+* A'), Function.Injective j₀ → IsLocalHom j₀ → j₀.Finite → ∃ (x' : NP F n) (j : x.A →+* x'.A) (e : x'.A ≃+* A'), x.Ext2 x' j ∧ (∀ a, e (j a) = j₀ a) ∧ Nat.card x'.K = Nat.card (ResidueField A') := by
  intro l _ F n x A' _ _ _ hA j₀ hinj hloc hfin
  haveI := hA.complete
  haveI := hA.finite
  haveI := hA.char
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A'
  obtain ⟨e, -, -⟩ := UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr A' l t ht
  letI : Algebra ℤ_[l] (ResidueField A') := ((residue A').comp (j₀.comp (algebraMap ℤ_[l] x.A))).toAlgebra
  let j : x.A →+* PowerSeries (ResidueField A') := (e.symm : A' →+* _).comp j₀
  have hj : Function.Injective j := e.symm.injective.comp hinj
  haveI hl : IsLocalHom j := ⟨fun a ha => hloc.1 a (by simpa using ha.map e)⟩
  have hjf : j.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.symm.surjective) hfin
  have h0 : (l : PowerSeries (ResidueField A')) = 0 := e.injective (by simp)
  have he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries (ResidueField A')) := by
    have := padic_hom_unique h0 (j.comp ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])))
      ((algebraMap ℤ_[l] _).comp (algebraMap ℤ_[l] ℤ_[l]))
    unfold GFrame.eps
    rw [← this]
    rfl
  exact ⟨pushNP x (ResidueField A') j hj he, j, e, ⟨⟨hj, hl, hjf, rfl, rfl, fun _ _ => rfl⟩, fun _ => rfl, rfl⟩,
    fun a => e.apply_symm_apply _, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.phiSub :
    ∀ (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G),
      IsOpen (H : Set G) → PhiCond (Γ := G) l → PhiCond (Γ := H) l := by
  intro l G _ _ _ H hH hG
  unfold PhiCond at *
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hG (K.map H.subtype) hK'
  let e := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
  have he : ∀ y : K.map H.subtype, (((e.symm y : K) : H) : G) = (y : G) := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have hc : Continuous fun y : K.map H.subtype => (e.symm y : K) := by
    apply continuous_induced_rng.2
    apply continuous_induced_rng.2
    exact continuous_subtype_val.congr fun y => (he y).symm
  refine Finite.of_injective
    (β := {ψ : K.map H.subtype →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, by
      show IsOpen ((fun y => (e.symm y : K)) ⁻¹' (φ.1.ker : Set K))
      exact φ.2.preimage hc⟩) ?_
  intro φ ψ h
  apply Subtype.ext
  ext k
  have h' := congrArg (fun χ : {ψ : K.map H.subtype →* Multiplicative (ZMod l) //
    IsOpen (ψ.ker : Set (K.map H.subtype))} => χ.1 (e k)) h
  simpa using h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SolBase
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.solBase :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ} (e : ι → F) (r : ι → Matrix (Fin n) (Fin n) F), (∀ X : Matrix (Fin n) (Fin n) F, (∀ i, e i • (r i * X) = X * r i) → X = 0) → ∀ X : Matrix (Fin n) (Fin n) F', (∀ i, f (e i) • ((r i).map f * X) = X * (r i).map f) → X = 0 := by
  intro F F' ι _ _ f n e r h X hX
  letI : Algebra F F' := f.toAlgebra
  have hs : ∀ (x : F) (y : F'), f x * y = x • y := fun x y => (Algebra.smul_def x y).symm
  let b := Module.Basis.ofVectorSpace F F'
  have key : ∀ k, (Matrix.of fun a c => b.repr (X a c) k) = 0 := by
    intro k
    apply h
    intro i
    ext a c
    have hac := congrArg (fun M => b.repr (M a c) k) (hX i)
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply] at hac ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hs, mul_comm (X _ _) (f _), ← Finset.smul_sum, map_sum, map_smul, Finsupp.smul_apply,
      smul_eq_mul] at hac
    change e i * (Finsupp.applyAddHom k : (_ →₀ F) →+ F) (∑ x, r i a x • b.repr (X x c)) =
      (Finsupp.applyAddHom k : (_ →₀ F) →+ F) (∑ x, r i x c • b.repr (X a x)) at hac
    simp only [map_sum, Finsupp.applyAddHom_apply, Finsupp.smul_apply, smul_eq_mul] at hac
    simpa only [mul_comm] using hac
  ext a c
  have hk : b.repr (X a c) = 0 := by
    ext k
    exact congrFun (congrFun (key k) a) c
  simpa using hk
end

