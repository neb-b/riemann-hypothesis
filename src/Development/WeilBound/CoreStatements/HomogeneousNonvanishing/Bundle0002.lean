module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CrtGood
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem crt_div {M : Type} [AddCommGroup M] (x : M) : ∀ n : ℕ, 0 < n →
    (∀ p k : ℕ, p.Prime → p ^ k ∣ n → ∃ e, x = p ^ k • e) → ∃ e, x = n • e := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => intro _ h; exact h p k hp dvd_rfl
  | zero => intro h; omega
  | one => intro _ _; exact ⟨x, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    obtain ⟨e, he⟩ := iha (by omega) fun p k hp hk => h p k hp (hk.mul_right b)
    obtain ⟨f, hf⟩ := ihb (by omega) fun p k hp hk => h p k hp (hk.mul_left a)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine ⟨u • f + v • e, ?_⟩
    have h1 : x = (u * a) • x + (v * b) • x := by rw [← add_smul, huv, one_smul]
    have h2 : (u * a) • x = (a * b) • (u • f) := by
      rw [hf, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    have h3 : (v * b) • x = (a * b) • (v • e) := by
      rw [he, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    rw [smul_add, ← h2, ← h3, ← h1]

theorem crt_le {p : ℕ} {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'} (f : ProIsoAt p O B B')
    (k j : ℕ) (x : L) : ∃ e, f.a (k + j) x = f.a k x + p ^ k • e := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := f.compat (k + j) x
    refine ⟨e + p ^ j • e', ?_⟩
    rw [← add_assoc, he', he, smul_add, smul_smul, ← pow_add, add_assoc]

theorem crt_good {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
    (f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B') : ∀ n : ℕ, ∃ a : L →ₗ[O] L', 0 < n →
      ∀ (p k : ℕ) (hp : p.Prime), p ^ k ∣ n → ∀ x, ∃ e, a x = (f p hp).a k x + p ^ k • e := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q m hq _ =>
    refine ⟨(f q hq).a m, fun _ p k hp hk x => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨(f q hq).a m x - (f p hp).a 0 x, by simp⟩
    · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1
        (hp.dvd_of_dvd_pow ((dvd_pow_self p hk0.ne').trans hk))
      subst hpq
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hk)
      exact crt_le _ k j x
  | zero => exact ⟨0, fun h => by omega⟩
  | one =>
    refine ⟨0, fun _ p k hp hk x => ?_⟩
    rw [Nat.dvd_one.1 hk]
    exact ⟨-(f p hp).a k x, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨A, hA⟩ := iha
    obtain ⟨C, hC⟩ := ihb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine ⟨(v * b) • A + (u * a) • C, fun _ p k hp hk x => ?_⟩
    have hor : p ^ k ∣ a ∨ p ^ k ∣ b := by
      by_cases hpa : p ∣ a
      · left
        have : Nat.Coprime (p ^ k) b := Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_left hpa hab)
        exact this.dvd_of_dvd_mul_right hk
      · right
        have : Nat.Coprime (p ^ k) a := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
        exact this.dvd_of_dvd_mul_left hk
    rcases hor with h | h
    · obtain ⟨e, he⟩ := hA (by omega) p k hp h x
      obtain ⟨c, hc⟩ := h
      refine ⟨e + (u * c) • (C x - A x), ?_⟩
      have h1 : v * b = 1 - u * a := by linarith
      have h2 : p ^ k • ((u * c) • (C x - A x)) = (u * a) • (C x - A x) := by
        rw [← natCast_zsmul, smul_smul]; congr 1; rw [hc]; push_cast; ring
      rw [smul_add, h2, ← add_assoc, ← he, h1]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]
      abel
    · obtain ⟨e, he⟩ := hC (by omega) p k hp h x
      obtain ⟨c, hc⟩ := h
      refine ⟨e + (v * c) • (A x - C x), ?_⟩
      have h1 : u * a = 1 - v * b := by linarith
      have h2 : p ^ k • ((v * c) • (A x - C x)) = (v * b) • (A x - C x) := by
        rw [← natCast_zsmul, smul_smul]; congr 1; rw [hc]; push_cast; ring
      rw [smul_add, h2, ← add_assoc, ← he, h1]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]
      abel

theorem tw_crt : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') := by
  intro O _ L L' _ _ _ _ B B' h
  let f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B' := fun p hp => (h p hp).some
  choose a ha using crt_good f
  refine ⟨⟨a, ?_, ?_, ?_, ?_⟩⟩
  · intro n hn x
    constructor
    · rintro ⟨y, hy⟩
      refine crt_div x n hn fun p k hp hk => ?_
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨c, hc⟩ := hk
      refine ((f p hp).inj k x).1 ⟨c • y - e, ?_⟩
      rw [smul_sub, smul_smul, ← hc, ← hy, he]; abel
    · rintro ⟨y, rfl⟩
      exact ⟨a n y, map_nsmul _ _ _⟩
  · intro n hn y
    obtain ⟨e, he⟩ := crt_div ((LinearMap.range (a n)).mkQ y) n hn fun p k hp hk => by
      obtain ⟨x, e, rfl⟩ := (f p hp).surj k y
      obtain ⟨e', he'⟩ := ha n hn p k hp hk x
      refine ⟨(LinearMap.range (a n)).mkQ (e - e'), ?_⟩
      rw [← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ⟨x, by rw [he', smul_sub]; abel⟩
    obtain ⟨e, rfl⟩ := Submodule.mkQ_surjective _ e
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at he
    obtain ⟨x, hx⟩ := he
    exact ⟨x, e, by rw [hx]; abel⟩
  · intro n hn x y
    obtain ⟨e, he⟩ := crt_div (B' (a n x) (a n y) - B x y) n hn fun p k hp hk => by
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨e', he'⟩ := ha n hn p k hp hk y
      obtain ⟨c, hc⟩ := (f p hp).isom k x y
      refine ⟨c + B' e (a n y) + B' ((f p hp).a k x) e', ?_⟩
      have h1 : B' (a n x) (a n y) = B' ((f p hp).a k x) (a n y) + p ^ k • B' e (a n y) := by
        rw [he, map_add (f := _), map_nsmul]; rfl
      have h2 : B' ((f p hp).a k x) (a n y) = B' ((f p hp).a k x) ((f p hp).a k y)
          + p ^ k • B' ((f p hp).a k x) e' := by
        rw [he', map_add (f := _), map_nsmul]
      rw [h1, h2]
      simp only [nsmul_eq_mul]
      push_cast
      linear_combination hc
    exact ⟨e, by rw [he, nsmul_eq_mul]⟩
  · intro n m hn hm x
    obtain ⟨e, he⟩ := crt_div (a (n * m) x - a n x) n hn fun p k hp hk => by
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨e', he'⟩ := ha (n * m) (Nat.mul_pos hn hm) p k hp (hk.mul_right m) x
      exact ⟨e' - e, by rw [he, he', smul_sub]; abel⟩
    exact ⟨e, by rw [← he]; abel⟩

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGStd
section
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem hermitian_form_standard_basis (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (hσ : ∀ r, σ (σ r) = r)
    (N : ℕ) (A g : Matrix (Fin N) (Fin N) R) (hg : IsUnit g.det) (h : (g.map σ).transpose * A * g = 1) :
    ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y,
      ∑ i, ∑ j, φ x i * A i j * σ (φ y j) = ∑ i, x i * σ (y i) := by
  have hM : IsUnit (g.map σ).det := by
    have e : σ g.det = (g.map σ).det := AlgHom.map_det σ g
    rw [← e]
    exact hg.map σ
  refine ⟨Matrix.toLinearEquiv' (g.map σ) (Matrix.invertibleOfIsUnitDet (g.map σ) hM), fun x y => ?_⟩
  have hs : (fun j => σ (Matrix.mulVec (g.map σ) y j)) = Matrix.mulVec g (fun k => σ (y k)) := by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
  have key : ∀ u w : Fin N → R, ∑ i, ∑ j, u i * A i j * w j = dotProduct u (Matrix.mulVec A w) := by
    intro u w
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hT : (A * g).transpose * g.map σ = 1 := by
    rw [← Matrix.transpose_transpose (g.map σ), ← Matrix.transpose_mul, ← Matrix.mul_assoc, h,
      Matrix.transpose_one]
  change ∑ i, ∑ j, Matrix.mulVec (g.map σ) x i * A i j * σ (Matrix.mulVec (g.map σ) y j) = _
  rw [key _ (fun j => σ (Matrix.mulVec (g.map σ) y j)), hs, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  simp [dotProduct]

theorem tw_g_std : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ), (∀ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin N) (Fin N) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1) → ∀ ψ ψ' : LinearMap.BilinForm Z (Fin N → R), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → (∀ x, ψ' x x = 0) → Function.Bijective ψ' → (∀ (a : R) x y, ψ' (a • x) y = ψ' x (σ a • y)) → ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y, ψ' (φ x) (φ y) = ψ x y := by
  intro Z R _ _ _ σ hσ lam hlam hbij N hstd ψ ψ' hψ0 hψb hψs hψ'0 hψ'b hψ's
  obtain ⟨A, hAh, hAu, hAψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ hψ0 hψb hψs
  obtain ⟨A', hA'h, hA'u, hA'ψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ' hψ'0 hψ'b hψ's
  obtain ⟨g, hg, hgA⟩ := hstd A hAh hAu
  obtain ⟨g', hg', hgA'⟩ := hstd A' hA'h hA'u
  obtain ⟨φ, hφ⟩ := hermitian_form_standard_basis Z R σ hσ N A g hg hgA
  obtain ⟨φ', hφ'⟩ := hermitian_form_standard_basis Z R σ hσ N A' g' hg' hgA'
  refine ⟨φ.symm.trans φ', fun x y => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hA'ψ, hφ', ← hφ, φ.apply_symm_apply,
    φ.apply_symm_apply, ← hAψ]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGTheta
section
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem anti_one {B : Type} [CommRing B] (σ : B ≃+* B) (I : Ideal B)
    (hspan : Ideal.span (Set.range fun x : B => x - σ x) = ⊤) (P : Ideal B) (hP : ¬ I ≤ P * I) :
    ∃ x ∈ I, x - σ x ∉ P * I := by
  by_contra hcon
  push_neg at hcon
  apply hP
  intro i hi
  have hJ : Ideal.span (Set.range fun x : B => x - σ x) ≤
      Submodule.comap (LinearMap.toSpanSingleton B B i) (P * I) := by
    rw [Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, smul_eq_mul]
    have h1 := hcon (b * i) (I.mul_mem_left b hi)
    have h2 := hcon i hi
    have e : (b - σ b) * i = (b * i - σ (b * i)) - σ b * (i - σ i) := by
      rw [map_mul]
      ring
    rw [e]
    exact sub_mem h1 (Ideal.mul_mem_left _ _ h2)
  rw [hspan] at hJ
  have h1 : (1 : B) ∈ Submodule.comap (LinearMap.toSpanSingleton B B i) (P * I) :=
    hJ Submodule.mem_top
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
  exact h1

theorem anti_avoid {B : Type} [CommRing B] (σ : B ≃+* B) (hσ : ∀ x, σ (σ x) = x) (I : Ideal B)
    (hI : ∀ x ∈ I, σ x ∈ I) (hspan : Ideal.span (Set.range fun x : B => x - σ x) = ⊤)
    (S : Finset (Ideal B)) (hS : ∀ P ∈ S, P.IsMaximal ∧ ¬ I ≤ P * I) :
    ∃ x ∈ I, ∀ P ∈ S, x - σ x ∉ P * I := by
  classical
  have hmap : ∀ P : Ideal B, P * I ≤ (P.comap σ * I).comap σ := by
    intro P
    rw [Ideal.mul_le]
    intro r hr s hs
    rw [Ideal.mem_comap, map_mul]
    refine Ideal.mul_mem_mul ?_ (hI s hs)
    rw [Ideal.mem_comap, hσ]
    exact hr
  have hneg : ∀ x : B, σ (x - σ x) = -(x - σ x) := by
    intro x
    rw [map_sub, hσ, neg_sub]
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨0, I.zero_mem, fun P hP => by simp at hP⟩
  intro P S hPS ih hS
  obtain ⟨x, hxI, hx⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
  obtain ⟨hPmax, hPI⟩ := hS P (Finset.mem_insert_self P S)
  by_cases hxP : x - σ x ∈ P * I
  swap
  · refine ⟨x, hxI, fun Q hQ => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact hxP
    · exact hx Q hQ
  by_cases hσP : P.comap σ ∈ S
  · exfalso
    apply hx _ hσP
    have h1 := Ideal.mem_comap.mp (hmap P hxP)
    rw [hneg] at h1
    exact neg_mem_iff.mp h1
  have hPc : (P.comap σ).IsPrime := Ideal.comap_isPrime σ P
  have hnot : ¬ ((S.inf fun Q => Q ⊓ Q.comap σ : Ideal B) : Set B) ⊆
      (P : Set B) ∪ (P.comap σ : Set B) := by
    rw [Ideal.subset_union]
    rintro (hle | hle)
    · obtain ⟨Q, hQ, hQle⟩ := (Ideal.IsPrime.inf_le' hPmax.isPrime).mp hle
      have hQmax := (hS Q (Finset.mem_insert_of_mem hQ)).1
      rcases hPmax.isPrime.inf_le.mp hQle with h | h
      · exact hPS (by rw [← hQmax.eq_of_le hPmax.ne_top h]; exact hQ)
      · apply hσP
        have hQle' : Q ≤ P.comap σ := fun q hq => by
          rw [Ideal.mem_comap]
          apply h
          rw [Ideal.mem_comap, hσ]
          exact hq
        rw [← hQmax.eq_of_le hPc.ne_top hQle']
        exact hQ
    · obtain ⟨Q, hQ, hQle⟩ := (Ideal.IsPrime.inf_le' hPc).mp hle
      have hQmax := (hS Q (Finset.mem_insert_of_mem hQ)).1
      rcases hPc.inf_le.mp hQle with h | h
      · exact hσP (by rw [← hQmax.eq_of_le hPc.ne_top h]; exact hQ)
      · apply hPS
        have hQle' : Q ≤ P := fun q hq => by
          have h2 := h (show σ q ∈ Q.comap σ by rw [Ideal.mem_comap, hσ]; exact hq)
          rw [Ideal.mem_comap, hσ] at h2
          exact h2
        rw [← hQmax.eq_of_le hPmax.ne_top hQle']
        exact hQ
  obtain ⟨a, haK, haP⟩ := Set.not_subset.mp hnot
  rw [Set.mem_union, not_or] at haP
  obtain ⟨haP1, haP2⟩ := haP
  have hσa : σ a ∉ P := fun h => haP2 (Ideal.mem_comap.mpr h)
  have haQ : ∀ Q ∈ S, a ∈ Q := by
    intro Q hQ
    have h := Finset.inf_le (f := fun Q : Ideal B => Q ⊓ Q.comap σ) hQ haK
    exact (Submodule.mem_inf.mp h).1
  have hc : σ (a * σ a) = a * σ a := by
    rw [map_mul, hσ, mul_comm]
  have hcP : a * σ a ∉ P := fun h => (hPmax.isPrime.mem_or_mem h).elim haP1 hσa
  obtain ⟨y, hyI, hy⟩ := PositivityTheory.UnitarySelfGeneration.anti_one σ I hspan P hPI
  have hyD : y - σ y ∈ I := I.sub_mem hyI (hI y hyI)
  refine ⟨x + a * σ a * y, I.add_mem hxI (I.mul_mem_left _ hyI), fun Q hQ => ?_⟩
  have hD : x + a * σ a * y - σ (x + a * σ a * y) = (x - σ x) + a * σ a * (y - σ y) := by
    rw [map_add (f := _), map_mul, hc]
    ring
  rw [hD]
  rcases Finset.mem_insert.mp hQ with rfl | hQ
  · intro hmem
    apply hy
    rw [Submodule.add_mem_iff_right _ hxP] at hmem
    obtain ⟨d, e, he, hde⟩ := hPmax.exists_inv hcP
    have hyz : y - σ y = d * (a * σ a * (y - σ y)) + e * (y - σ y) := by
      calc y - σ y = (d * (a * σ a) + e) * (y - σ y) := by rw [hde, one_mul]
        _ = d * (a * σ a * (y - σ y)) + e * (y - σ y) := by ring
    rw [hyz]
    exact add_mem (Ideal.mul_mem_left _ d hmem) (Ideal.mul_mem_mul he hyD)
  · intro hmem
    apply hx Q hQ
    have hcQ : a * σ a * (y - σ y) ∈ Q * I :=
      Ideal.mul_mem_mul (Ideal.mul_mem_right _ Q (haQ Q hQ)) hyD
    exact (Submodule.add_mem_iff_left _ hcQ).mp hmem

theorem anti_ded {B : Type} [CommRing B] [IsDedekindDomain B] (σ : B ≃+* B) (hσ : ∀ x, σ (σ x) = x)
    (I : Ideal B) (hI0 : I ≠ ⊥)
    (hI : ∀ x ∈ I, σ x ∈ I) (hspan : Ideal.span (Set.range fun x : B => x - σ x) = ⊤)
    (p : B) (hp : p ≠ 0) : ∃ x ∈ I, ∀ P : Ideal B, P.IsMaximal → p ∈ P → x - σ x ∉ P * I := by
  classical
  have hspan0 : Ideal.span {p} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp
  have hI0' : I ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    exact hI0
  have hT : ∀ P ∈ (Ideal.finite_factors hspan0).toFinset.image
      (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal), P.IsMaximal ∧ ¬ I ≤ P * I := by
    intro P hP
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨v.isMaximal, fun hle => ?_⟩
    have heq : v.asIdeal * I = ⊤ * I := by
      rw [Ideal.top_mul]
      exact le_antisymm (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs) hle
    exact v.isMaximal.ne_top (mul_right_cancel₀ hI0' heq)
  obtain ⟨x, hxI, hx⟩ :=
    PositivityTheory.UnitarySelfGeneration.anti_avoid σ hσ I hI hspan _ hT
  refine ⟨x, hxI, fun P hPmax hpP => hx P ?_⟩
  have hPbot : P ≠ ⊥ := fun h => hp (by rw [h] at hpP; exact Ideal.mem_bot.mp hpP)
  refine Finset.mem_image.mpr ⟨⟨P, hPmax.isPrime, hPbot⟩, ?_, rfl⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  exact hpP

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) (a : 𝓞 E) : bar (bar a) = a := by
  apply RingOfIntegers.ext
  rw [hbar, hbar, IsCMField.complexConj_apply_apply]

theorem tw_g_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : ℕ, p.Prime → ∃ θ : 𝓞 E, IsCoprime (θ - bar θ) (p : 𝓞 E) := by
  intro E _ _ _ bar hbar hunr p hp
  have hspan := PositivityTheory.UnitarySelfGeneration.tw_g_diff E bar hbar hunr
  have hinv : ∀ a, bar (bar a) = a := PositivityTheory.UnitarySelfGeneration.bar_bar bar hbar
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨x, -, hx⟩ := PositivityTheory.UnitarySelfGeneration.anti_ded bar hinv ⊤
    top_ne_bot (fun _ _ => Submodule.mem_top) hspan (p : 𝓞 E) hp0
  refine ⟨x, ?_⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  apply hx P hPmax (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  rw [Ideal.mul_top]
  exact hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

end PositivityTheory.UnitarySelfGeneration
end

