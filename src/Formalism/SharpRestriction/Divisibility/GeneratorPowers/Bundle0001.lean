module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsBasisOfSaturated
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.SatLin

theorem exists_basis_of_saturated {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {d r : ℕ}
    (u : Fin r → (Fin d → R)) (hu : LinearIndependent R u)
    (hs : ∀ (v : Fin d → R) (a : R), a ≠ 0 → a • v ∈ Submodule.span R (Set.range u) →
      v ∈ Submodule.span R (Set.range u)) :
    ∃ (w : Fin d → Fin d → R) (emb : Fin r ↪ Fin d), (∀ i, w (emb i) = u i) ∧
      ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j := by
  classical
  set S := Submodule.span R (Set.range u) with hS
  haveI : NoZeroSMulDivisors R ((Fin d → R) ⧸ S) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective S q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      exact hs v a ha h
  haveI : Module.Free R ((Fin d → R) ⧸ S) := Module.free_of_finite_type_torsion_free'
  let bQ := Module.Free.chooseBasis R ((Fin d → R) ⧸ S)
  choose s' hs' using fun j => Submodule.Quotient.mk_surjective S (bQ j)
  let w' := Sum.elim u s'
  have hmk : ∀ i, Submodule.Quotient.mk (p := S) (u i) = 0 := fun i =>
    (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent R w' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    have hr : ∀ j, g (Sum.inr j) = 0 := by
      have h1 := congrArg S.mkQ hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w', Sum.elim_inl, Sum.elim_inr, map_add (f := _), map_sum, map_smul, map_zero, Submodule.mkQ_apply,
        hmk, hs', smul_zero, Finset.sum_const_zero, zero_add] at h1
      exact Fintype.linearIndependent_iff.1 bQ.linearIndependent _ h1
    have hl : ∀ i, g (Sum.inl i) = 0 := by
      simp only [hr, zero_smul, Finset.sum_const_zero, add_zero, w', Sum.elim_inl] at hg
      exact Fintype.linearIndependent_iff.1 hu _ hg
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range w') := by
    intro v _
    have hv := bQ.sum_repr (Submodule.Quotient.mk (p := S) v)
    have ht : (∑ j, bQ.repr (Submodule.Quotient.mk (p := S) v) j • s' j) ∈ Submodule.span R (Set.range w') :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
    have hvt : v - ∑ j, bQ.repr (Submodule.Quotient.mk (p := S) v) j • s' j ∈ S := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hs']
      rw [hv, sub_self]
    have hSle : S ≤ Submodule.span R (Set.range w') :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    have h := Submodule.add_mem _ (hSle hvt) ht
    rwa [sub_add_cancel] at h
  let B := Module.Basis.mk hli hsp
  have hcard : Fintype.card (Fin r ⊕ Module.Free.ChooseBasisIndex R ((Fin d → R) ⧸ S)) = d := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  let b := B.reindex e
  refine ⟨fun k => b k, ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩, fun i => ?_, fun v => ?_⟩
  · simp [b, B, Module.Basis.reindex_apply, Module.Basis.mk_apply, w']
  · refine ⟨fun k => b.repr v k, fun j => ?_, fun a ha => ?_⟩
    · have h := congrFun (b.sum_repr v) j
      simpa [Finset.sum_apply, smul_eq_mul] using h
    · have hv : ∑ k, a k • b k = v := funext fun j => by simpa [Finset.sum_apply, smul_eq_mul] using ha j
      funext k
      rw [← hv]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]

end Formalism.L2.Pj.SatLin
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

open NumberField Matrix

section Core

variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]

theorem hom_basis {R' : Type} [Ring R'] (f : 𝓞 E →+* R') (b : Module.Basis κ ℤ (𝓞 E)) (x : 𝓞 E) :
    f x = ∑ k, ((b.repr x k : ℤ) : R') * f (b k) := by
  conv_lhs => rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul]

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]

theorem decomp_of_inv (ρ : 𝓞 E →+* Module.End R M) (χ : ι → (𝓞 E →+* R)) (b : Module.Basis κ ℤ (𝓞 E))
    (Cm : κ → ι → R) (hAC : ∀ σ τ, ∑ i, χ σ (b i) * Cm i τ = if σ = τ then 1 else 0)
    (hCA : ∀ i j, ∑ τ, Cm i τ * χ τ (b j) = if i = j then 1 else 0) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by
  classical
  set Q : ι → M → M := fun σ m => ∑ i, Cm i σ • ρ (b i) m with hQ
  have hcoef : ∀ (a : 𝓞 E) (i : κ), ∑ τ, χ τ a * Cm i τ = ((b.repr a i : ℤ) : R) := by
    intro a i
    have h1 : ∀ τ, χ τ a = ∑ k, ((b.repr a k : ℤ) : R) * χ τ (b k) := fun τ => hom_basis (χ τ) b a
    have hCA' : ∀ k, ∑ τ, χ τ (b k) * Cm i τ = if i = k then 1 else 0 := by
      intro k
      rw [← hCA i k]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    simp_rw [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hCA']
    simp
  have F3 : ∀ (a : 𝓞 E) (m : M), ρ a m = ∑ τ, χ τ a • Q τ m := by
    intro a m
    simp only [hQ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcoef]
    conv_lhs => rw [hom_basis ρ b a]
    simp [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  have eig : ∀ σ (a : 𝓞 E) (m : M), ρ a (Q σ m) = χ σ a • Q σ m := by
    intro σ a m
    have h1 : ρ a (Q σ m) = ∑ i, Cm i σ • ρ (a * b i) m := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hQ, map_sum, map_smul, map_mul, Module.End.mul_apply]
    rw [h1]
    simp_rw [F3 _ m, map_mul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have h2 : ∀ τ, ∑ i, Cm i σ * (χ τ a * χ τ (b i)) = χ τ a * (if τ = σ then 1 else 0) := by
      intro τ
      rw [← hAC τ σ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h2]
    simp
  have hsum1 : ∀ m : M, ∑ σ, Q σ m = m := by
    intro m
    have := F3 1 m
    simp at this
    exact this.symm
  have hlin : ∀ σ (f : ι → M), Q σ (∑ σ', f σ') = ∑ σ', Q σ (f σ') := by
    intro σ f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hQ, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  refine ⟨fun m => ⟨fun σ => Q σ m, fun σ a => eig σ a m, hsum1 m⟩, ?_⟩
  intro mσ hmσ hsum σ
  have hQe : ∀ τ σ', Q τ (mσ σ') = if σ' = τ then mσ σ' else 0 := by
    intro τ σ'
    simp only [hQ, hmσ, smul_smul]
    rw [← Finset.sum_smul]
    rw [show ∑ i, Cm i τ * χ σ' (b i) = if σ' = τ then 1 else 0 from by
      rw [← hAC σ' τ]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    split_ifs <;> simp
  have h0 : Q σ (∑ σ', mσ σ') = 0 := by
    rw [hsum]
    simp [hQ]
  rw [hlin] at h0
  simpa [hQe] using h0

end Core

section NT

variable (E : Type) [Field E] [NumberField E]

theorem isUnit_of_not_dvd {V : Type} [CommRing V] [IsLocalRing V] (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (d : ℤ) (hd : ¬ (g : ℤ) ∣ d) : IsUnit (d : V) := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hd
  have h1 : (u : V) * (g : V) + (v : V) * (d : V) = 1 := by
    have := congrArg (Int.cast : ℤ → V) huv
    push_cast at this
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hgV
  · exact isUnit_of_mul_isUnit_right h

end NT

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PairEvaluation
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

abbrev Io (S σ : Type) [CommRing S] : Ideal (MvPolynomial σ S) := idealOfVars σ S

def xs (S : Type) [CommRing S] {n : ℕ} (d : ℕ) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => X (k, i)

def lin {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => ∑ l, C (A i l) * X (k, l)

def ev2 {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) : MvPolynomial τ S :=
  aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h

lemma eval_pair_one {τ : Type} (u v : Fin d → MvPolynomial τ S) : ev2 (1 : MvPolynomial (Fin 2 × Fin d) S) u v = 1 := by
  simp [ev2]

lemma eval_pair_sub {τ : Type} (h h' : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) :
    ev2 (h - h') u v = ev2 h u v - ev2 h' u v := by
  simp [ev2]

section Sub

variable {σ τ : Type}

lemma aeval_mem_pow (g : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (k : ℕ) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ k) : aeval g p ∈ Io S τ ^ k := by
  have h1 : Io S σ ≤ (Io S τ).comap (aeval g) := by
    show Ideal.span (Set.range X) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hg i
  exact (Ideal.le_comap_pow (f := aeval g) k) (Ideal.pow_right_mono h1 k hp)

lemma sub_C_mem (p : MvPolynomial σ S) : p - C (AddMonoidAlgebra.coeff p 0) ∈ Io S σ := by
  have h := (mem_pow_idealOfVars_iff' (σ := σ) (R := S) 1 (p - C (AddMonoidAlgebra.coeff p 0))).2 (fun x hx => by
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst hx0
    simp)
  simpa using h

lemma aeval_sub_aeval_mem (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (p : MvPolynomial σ S) : aeval g p - aeval g' p ∈ Io S τ := by
  have h0 : p - C (AddMonoidAlgebra.coeff p 0) ∈ Io S σ ^ 1 := by simpa using sub_C_mem p
  have h1 := aeval_mem_pow g hg 1 h0
  have h2 := aeval_mem_pow g' hg' 1 h0
  have h3 := sub_mem (by simpa using h1) (by simpa using h2)
  simpa [map_sub, aeval_C] using h3

lemma aeval_sub_mem_sq (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) {p : MvPolynomial σ S} (hp : p ∈ Io S σ) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  have hp' : p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ S)) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using hgg i
  | zero => simp
  | add x y _ _ hx hy =>
    have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
      simp only [map_add (f := _)]; ring
    rw [e]; exact add_mem hx hy
  | smul r x hxm hx =>
    have e : aeval g (r • x) - aeval g' (r • x) =
        (aeval g r - aeval g' r) * aeval g x + aeval g' r * (aeval g x - aeval g' x) := by
      simp only [smul_eq_mul, map_mul]; ring
    rw [e]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    have hx1 : x ∈ Io S σ ^ 1 := by simpa using hxm
    exact Ideal.mul_mem_mul (aeval_sub_aeval_mem g g' hg hg' r) (by simpa using aeval_mem_pow g hg 1 hx1)

lemma aeval_sub_mem_pow (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) : ∀ (k : ℕ) (p : MvPolynomial σ S), p ∈ Io S σ ^ k →
    aeval g p - aeval g' p ∈ Io S τ ^ (k + 1)
  | 0, p, _ => by simpa using aeval_sub_aeval_mem g g' hg hg' p
  | k + 1, p, hp => by
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun p => aeval g p - aeval g' p ∈ Io S τ ^ (k + 1 + 1)) hp ?_ ?_
    · intro a ha b hb
      change aeval g (a * b) - aeval g' (a * b) ∈ Io S τ ^ (k + 1 + 1)
      have e : aeval g (a * b) - aeval g' (a * b) =
          (aeval g a - aeval g' a) * aeval g b + aeval g' a * (aeval g b - aeval g' b) := by
        simp only [map_mul]; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [pow_succ]
        have hb1 : b ∈ Io S σ ^ 1 := by simpa using hb
        exact Ideal.mul_mem_mul (aeval_sub_mem_pow g g' hg hg' hgg k a ha)
          (by simpa using aeval_mem_pow g hg 1 hb1)
      · have e2 : Io S τ ^ (k + 1 + 1) = Io S τ ^ k * Io S τ ^ 2 := by rw [← pow_add]
        rw [e2]
        exact Ideal.mul_mem_mul (aeval_mem_pow g' hg' k ha) (aeval_sub_mem_sq g g' hg hg' hgg hb)
    · intro x y hx hy
      change aeval g (x + y) - aeval g' (x + y) ∈ Io S τ ^ (k + 1 + 1)
      have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
        simp only [map_add (f := _)]; ring
      rw [e]; exact add_mem hx hy

lemma eq_zero_of_isHomogeneous {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j)
    (hm : h ∈ Io S σ ^ (j + 1)) : h = 0 := by
  ext e
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hne
  have h1 := (mem_pow_idealOfVars_iff (j + 1) h).1 hm e (mem_support_iff.2 hne)
  have h2 : e.degree = j := by
    have := hh hne
    rw [Finsupp.degree_eq_weight_one]
    exact this
  omega

lemma sub_homogeneousComponent_mem {W : MvPolynomial σ S} {j : ℕ} (hW : W ∈ Io S σ ^ j) :
    W - homogeneousComponent j W ∈ Io S σ ^ (j + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hW ⊢
  intro x hx
  rw [coeff_sub, coeff_homogeneousComponent]
  split_ifs with h
  · simp
  · have : x.degree < j := by omega
    simp [hW x this]

end Sub

lemma eval_pair_homogeneous {τ : Type} {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j)
    (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (ev2 h u v).IsHomogeneous j := by
  have := hh.aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) (n := 1)
    (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
  rw [one_mul] at this
  exact this

lemma xs_hom {n : ℕ} (k : Fin n) (i : Fin d) : (xs S d k i).IsHomogeneous 1 := isHomogeneous_X S _

lemma lin_hom {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : (lin A k i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X S _).C_mul _

lemma xs_mem {n : ℕ} (k : Fin n) (i : Fin d) : xs S d k i ∈ Io S (Fin n × Fin d) :=
  Ideal.subset_span ⟨_, rfl⟩

lemma lin_mem {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : lin A k i ∈ Io S (Fin n × Fin d) :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

section Main

variable [Algebra ℚ S]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

def WhitenStatement : Prop :=
  ∀ (d : ℕ) (L : Matrix (Fin d) (Fin d) ℝ), L.PosDef →
    ∃ R : Matrix (Fin d) (Fin d) ℝ, IsUnit R.det ∧ L = Rᵀ * R

def HalfTraceStatement : Prop :=
  ∀ (d : ℕ) (L G K R : Matrix (Fin d) (Fin d) ℝ), L = Rᵀ * R → IsUnit R.det → G.PosSemidef →
    Kᵀ * G = -(G * K) → K * L = -(L * Kᵀ) → IsUnit K.det →
    ∀ x : Fin d → ℝ, x ⬝ᵥ (G *ᵥ x) ≤
      (1 / 2) * trace (L * G) * (((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ x))

def ShortDualStatement : Prop :=
  ∀ (d : ℕ) (L R : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ), 0 < d → L = Rᵀ * R → IsUnit R.det → 0 < μ →
    (∀ t : Fin d → ℤ, t ≠ 0 → μ ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ))) →
    ∀ δ : ℝ, 0 < δ → ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧
      ∀ j, ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ≤
        ((d : ℝ) / μ + δ) ^ 2

def FiniteShortStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℝ), G.PosDef → ∀ B : ℝ,
    {c : Fin d → ℤ | (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ B}.Finite

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

