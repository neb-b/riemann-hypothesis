module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Formalism.SatakeDualWeyl.Bundle0001

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
section
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem levelv_relIndex_ne_zero {G : Type*} [Group G] (H K : Subgroup G) {β : Type*} [Finite β]
    (f : G → β) (hf : ∀ a ∈ K, ∀ b ∈ K, f a = f b → a⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_surjective
      (fun y : Set.range (fun k : K => f k) =>
        (QuotientGroup.mk (Set.mem_range.mp y.2).choose : K ⧸ H.subgroupOf K)) ?_
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨f k, k, rfl⟩, ?_⟩
    beta_reduce
    have hc := (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose_spec
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hf _ (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose.2 _ k.2 hc
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

section Local

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev lvS (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

theorem levelv_tmul_mem (e : E) (he : e ∈ intOE E) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : e ⊗ₜ[F] x ∈ lvS F E v := by
  have h1 : e ⊗ₜ[F] (1 : v.adicCompletion F) ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_left _ ⟨⟨e, he⟩, rfl⟩
  have h2 : (1 : E) ⊗ₜ[F] x ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_right _ ⟨⟨x, hx⟩, rfl⟩
  simpa using mul_mem h1 h2

def levelvPsi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →+
      E ⊗[F] v.adicCompletion F :=
  AddMonoidHom.mk' (fun a => ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((a i : v.adicCompletionIntegers F) : v.adicCompletion F))
    (by intro a a'; simp [tmul_add, Finset.sum_add_distrib])

theorem levelv_tmul_mem_range (e : 𝓞 E) (x : v.adicCompletionIntegers F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] (x : v.adicCompletion F) ∈ (levelvPsi F E v).range := by
  classical
  let φ : 𝓞 E →+ E ⊗[F] v.adicCompletion F :=
    AddMonoidHom.mk' (fun y => algebraMap (𝓞 E) E y ⊗ₜ[F] (x : v.adicCompletion F))
      (by intro a b; simp [TensorProduct.add_tmul])
  have hb : ∀ i, φ (RingOfIntegers.basis E i) ∈ (levelvPsi F E v).range := by
    intro i
    refine AddMonoidHom.mem_range.mpr ⟨Pi.single i x, ?_⟩
    simp only [levelvPsi, AddMonoidHom.mk'_apply, φ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  show φ e ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (RingOfIntegers.basis E).sum_repr e, map_sum]
  exact sum_mem fun i _ => by rw [map_zsmul]; exact zsmul_mem (hb i) _

theorem levelv_mul_mem_range (y y' : E ⊗[F] v.adicCompletion F)
    (hy : y ∈ (levelvPsi F E v).range) (hy' : y' ∈ (levelvPsi F E v).range) :
    y * y' ∈ (levelvPsi F E v).range := by
  have hPsi : ∀ c, levelvPsi F E v c = ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((c i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun c => rfl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hy
  obtain ⟨a', rfl⟩ := AddMonoidHom.mem_range.mp hy'
  rw [hPsi, hPsi]
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  first
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E i * RingOfIntegers.basis E j) (a i * a' j)
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E j * RingOfIntegers.basis E i) (a j * a' i)

def levelvT (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) where
  carrier := (levelvPsi F E v).range
  mul_mem' := levelv_mul_mem_range v _ _
  one_mem' := by
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = algebraMap (𝓞 E) E 1 ⊗ₜ[F]
        ((1 : v.adicCompletionIntegers F) : v.adicCompletion F) := by rw [map_one]; rfl
    rw [h1]
    exact levelv_tmul_mem_range v 1 1
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

theorem levelv_S_le_range (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ lvS F E v) :
    y ∈ (levelvPsi F E v).range := by
  have hle : lvS F E v ≤ levelvT F E v := by
    apply Subring.closure_le.mpr
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩)
    · obtain ⟨e', rfl⟩ := RingHom.mem_range.mp he
      show algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : v.adicCompletion F) ∈ (levelvPsi F E v).range
      simpa using levelv_tmul_mem_range v e' 1
    · show (1 : E) ⊗ₜ[F] x ∈ (levelvPsi F E v).range
      have h := levelv_tmul_mem_range (E := E) v 1 ⟨x, hx⟩
      first
        | exact h
        | (rw [map_one] at h; exact h)
        | simpa using h
  exact hle hy

theorem levelv_denom (y : E ⊗[F] v.adicCompletion F) : ∃ N : ℕ, N ≠ 0 ∧ N • y ∈ lvS F E v := by
  classical
  have h1 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = (m • e) ⊗ₜ[F] x :=
    fun m e x => (map_nsmul ((TensorProduct.mk F E (v.adicCompletion F)).flip x) m e).symm
  have h2 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = e ⊗ₜ[F] (m • x) :=
    fun m e x => (map_nsmul (TensorProduct.mk F E (v.adicCompletion F) e) m x).symm
  have hE : ∀ e : E, ∃ M : ℕ, M ≠ 0 ∧ M • e ∈ intOE E := by
    intro e
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
    refine ⟨Ideal.absNorm (Ideal.span {s}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hs0
    · refine RingHom.mem_range.mpr ⟨t * a, ?_⟩
      have hs' : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 E) E), ← ht, map_mul, map_mul]
      field_simp <;> ring
  have hF : ∀ x : v.adicCompletion F, ∃ N : ℕ, N ≠ 0 ∧ N • x ∈ v.adicCompletionIntegers F := by
    intro x
    obtain ⟨b, hb, hbx⟩ :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    · have hcv : algebraMap (𝓞 F) (v.adicCompletion F) c ∈ v.adicCompletionIntegers F :=
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) c).2
      have key : Ideal.absNorm (Ideal.span {b}) • x = algebraMap (𝓞 F) (v.adicCompletion F) c *
          (x * algebraMap (𝓞 F) (v.adicCompletion F) b) := by
        rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 F) (v.adicCompletion F)), ← hc, map_mul]
        ring
      rw [key]
      exact mul_mem hcv hbx
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | tmul e x =>
    obtain ⟨M, hM0, hM⟩ := hE e
    obtain ⟨N, hN0, hN⟩ := hF x
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [mul_smul, h2, h1]
    exact levelv_tmul_mem v _ hM _ hN
  | add y z hy hz =>
    obtain ⟨M, hM0, hM⟩ := hy
    obtain ⟨N, hN0, hN⟩ := hz
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hM _
    · rw [mul_smul]
      exact nsmul_mem hN _

theorem levelv_denom_family {ι : Type*} [Fintype ι] (a : ι → E ⊗[F] v.adicCompletion F) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i, N • a i ∈ lvS F E v := by
  classical
  choose M hM0 hM using fun i => levelv_denom v (a i)
  refine ⟨∏ i, M i, Finset.prod_ne_zero_iff.mpr fun i _ => hM0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ M (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hM i) _

end Local

section Lattice

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

end Lattice

section GLact

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

end GLact


end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

section Gen

variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_coe_bc (f : R →+* A) (u : GL n R) :
    ((bc (n := n) f u : GL n A) : Matrix n n A) = (u : Matrix n n R).map f := by
  rfl

theorem levelvsplit_mem_range_iff (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by
  constructor
  · intro hg
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨fun i j => ⟨(u : Matrix n n R) i j, rfl⟩, fun i j => ⟨((u⁻¹ : GL n R) : Matrix n n R) i j, ?_⟩⟩
    rw [← map_inv (bc (n := n) f) u]
    rfl
  · rintro ⟨h1, h2⟩
    choose M hM using h1
    choose N hN using h2
    have hinj : Function.Injective (f.mapMatrix : Matrix n n R →+* Matrix n n A) := by
      intro X Y h
      ext i j
      have h' := congrArg (fun Z : Matrix n n A => Z i j) h
      exact hf h'
    have hMg : f.mapMatrix (Matrix.of M) = (g : Matrix n n A) := by
      ext i j
      exact hM i j
    have hNg : f.mapMatrix (Matrix.of N) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      exact hN i j
    have e1 : Matrix.of M * Matrix.of N = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.mul_inv])
    have e2 : Matrix.of N * Matrix.of M = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.inv_mul])
    exact MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, e1, e2⟩, Units.ext hMg⟩

end Gen

section Split

variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_unitary (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by
  have hh' : Formalism.UG.cT τ (h : Matrix n n B) * J' * (h : Matrix n n B) = J' := hh
  have key : (Formalism.UG.cT τ (h : Matrix n n B)).map ((RingHom.fst K K).comp φ.toRingHom) =
      ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ := by
    ext i j
    simp [Formalism.UG.cT, hτ, Formalism.UG.swapR]
  have h2 := congrArg (fun M : Matrix n n B => M.map ((RingHom.fst K K).comp φ.toRingHom)) hh'
  simp only [Matrix.map_mul] at h2
  rw [key] at h2
  exact h2

theorem levelvsplit_solve (A Ainv P1 P1i P2 : Matrix n n K) (hA : A * Ainv = 1)
    (hP : P1 * P1i = 1) (hrel : P2ᵀ * A * P1 = A) : P2 = (A * P1i * Ainv)ᵀ := by
  have h1 : P2ᵀ * A = A * P1i := by
    calc P2ᵀ * A = P2ᵀ * A * (P1 * P1i) := by rw [hP, Matrix.mul_one]
      _ = P2ᵀ * A * P1 * P1i := by simp only [Matrix.mul_assoc]
      _ = A * P1i := by rw [hrel]
  have h2 : P2ᵀ = A * P1i * Ainv := by
    calc P2ᵀ = P2ᵀ * (A * Ainv) := by rw [hA, Matrix.mul_one]
      _ = P2ᵀ * A * Ainv := by rw [Matrix.mul_assoc]
      _ = A * P1i * Ainv := by rw [h1]
  rw [← h2, Matrix.transpose_transpose]

end Split

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeRes
section
noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.UG.P

open Formalism.UG

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem satake_unif_ne_zero {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h0
  subst h0
  unfold IsUnifV at h
  first | simp at h | done

theorem satake_lt_one_le {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  cases x using WithZero.recZeroCoe with
  | zero => exact WithZero.zero_le _
  | coe a =>
    have h1 : a < 1 := by exact_mod_cast hx
    have h2 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      change Multiplicative.toAdd a ≤ -1
      have h3 : Multiplicative.toAdd a < 0 := h1
      omega
    exact WithZero.coe_le_coe.mpr h2

private theorem mem_Ov_iff' (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  unfold Ov
  first
    | exact Iff.rfl
    | exact mem_adicCompletionIntegers
    | simp [mem_adicCompletionIntegers]

theorem satake_unif_inv_not_mem {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ⁻¹ ∉ Ov F v := by
  unfold IsUnifV at h
  intro hm
  have hm' : Valued.v ϖ⁻¹ ≤ 1 := (mem_Ov_iff' v _).mp hm
  rw [map_inv₀, h] at hm'
  have h4 : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ : Multiplicative ℤ) ≤ 1 := by
    rw [← WithZero.coe_le_coe, WithZero.coe_inv]
    first | exact_mod_cast hm' | simpa using hm'
  have h5 : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹) ≤ Multiplicative.toAdd (1 : Multiplicative ℤ) := h4
  simp at h5

theorem satake_mem_span_iff {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ)
    (y : Ov F v) : y ∈ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)} ↔ Valued.v (y : v.adicCompletion F) < 1 := by
  have h0 := satake_unif_ne_zero v h
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : Valued.v ((z : Ov F v) : v.adicCompletion F) ≤ 1 := z.2
    show Valued.v ((z : v.adicCompletion F) * ϖ) < 1
    rw [Valuation.map_mul, h]
    calc Valued.v (z : v.adicCompletion F) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul, ← WithZero.coe_one, WithZero.coe_lt_coe]
          show (-1 : ℤ) < 0
          omega
  · intro hy
    have hle := satake_lt_one_le hy
    have hm : (y : v.adicCompletion F) * ϖ⁻¹ ∈ Ov F v := by
      show Valued.v ((y : v.adicCompletion F) * ϖ⁻¹) ≤ 1
      rw [Valuation.map_mul, Valuation.map_inv, h]
      calc Valued.v (y : v.adicCompletion F) * (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹
          ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
              (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹ :=
            by gcongr
        _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (y : v.adicCompletion F) * ϖ⁻¹ * ϖ = y
    field_simp

def satakeIota : 𝓞 F →+* Ov F v := algebraMap (𝓞 F) (v.adicCompletionIntegers F)

theorem satakeIota_coe (r : 𝓞 F) :
    ((satakeIota v r : Ov F v) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r := by first | rfl | simp [satakeIota] | (unfold satakeIota Ov; done)

theorem satake_card_res {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ) :
    Nat.card (Ov F v ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}) = qV F v := by
  set I := Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}
  let φ : 𝓞 F →+* Ov F v ⧸ I := (Ideal.Quotient.mk I).comp (satakeIota v)
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [satake_mem_span_iff v hϖ h]
    unfold satakeIota
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : Ov F v) ∈ I := htop ▸ Submodule.mem_top
    rw [satake_mem_span_iff v hϖ h] at h1
    simp at h1
  have : Nontrivial (Ov F v ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have hinj : Function.Injective ψ := RingHom.injective ψ
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    show φ r = _
    simp only [φ, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, satake_mem_span_iff v hϖ h]
    have e : ((satakeIota v r - x : Ov F v) : v.adicCompletion F) =
        -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, satakeIota_coe, neg_sub]
    rw [e, Valuation.map_neg]
    exact hr
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)]
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem satake_ordV_unif {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ordV F v ϖ = 1 := by
  unfold ordV IsUnifV at *
  have h0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, h]
  rw [WithZero.coe_injective e]
  simp

theorem satake_ordV_one : ordV F v 1 = 0 := by
  unfold ordV
  have h0 : Valued.v (1 : v.adicCompletion F) ≠ 0 := by simp
  rw [dite_eq_right h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [WithZero.coe_injective e]
  simp

theorem satake_two_le_qV : 2 ≤ qV F v := by
  unfold qV
  have h1 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h2 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

end Formalism.UG.P
end
end

