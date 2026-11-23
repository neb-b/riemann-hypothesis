module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictIndepPowOfRegularPair
section
namespace GlobalTheory.BSP.StrictIndep

variable {S A : Type} [CommRing S] [CommRing A]

theorem span_sup_span_eq_pair (x y : S) :
    Ideal.span {x} ⊔ Ideal.span {y} = Ideal.span ({x, y} : Set S) := by
  rw [← Ideal.span_union, Set.singleton_union]

theorem map_span_pair (s : S →+* A) (x y : S) :
    (Ideal.span {x} ⊔ Ideal.span {y}).map s = Ideal.span ({s x, s y} : Set A) := by
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    span_sup_span_eq_pair]

theorem sum_decomp (s : S →+* A) {ι : Type} (b : ι → A) (T : Finset ι) (u v : ι → S) (P Q : S) :
    ∑ i ∈ T, s (u i * P + v i * Q) * b i
      = s P * ∑ i ∈ T, s (u i) * b i + s Q * ∑ i ∈ T, s (v i) * b i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add (f := _), map_mul]
  ring

theorem indep_finset (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q})
    (T : Finset ι) (c : ι → S) (h : ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p, s q} : Set A)) :
    ∀ i ∈ T, c i ∈ Ideal.span ({p, q} : Set S) := by
  classical
  intro i hi
  have key := h3 (Finsupp.onFinset T (fun j => if j ∈ T then c j else 0)
    (by intro j hj; by_contra hn; simp [hn] at hj)) (by
      rw [map_span_pair, Finsupp.onFinset_sum _ (by intro j; simp)]
      convert h using 1
      exact Finset.sum_congr rfl (fun j hj => by simp [hj])) i
  rw [span_sup_span_eq_pair] at key
  simpa [hi] using key

theorem dvd_of_dvd_pow_mul (s : S →+* A) (p q : S)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x) :
    ∀ (n : ℕ) (x : A), s p ∣ s q ^ n * x → s p ∣ x := by
  intro n
  induction n with
  | zero => intro x h; simpa using h
  | succ n ih =>
    intro x h
    apply h2
    apply ih
    rw [pow_succ, mul_assoc] at h
    exact h

theorem pow_dvd_of_dvd_pow_mul (s : S →+* A) (p q : S)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x) (n : ℕ) :
    ∀ (m : ℕ) (x : A), s q ^ n ∣ s p ^ m * x → s q ^ n ∣ x := by
  have base : ∀ x : A, s q ^ n ∣ s p * x → s q ^ n ∣ x := by
    rintro x ⟨y, hy⟩
    obtain ⟨t, ht⟩ := dvd_of_dvd_pow_mul s p q h2 n y ⟨x, by rw [← hy]⟩
    refine ⟨t, ?_⟩
    have h0 : s p * (x - s q ^ n * t) = 0 := by
      rw [mul_sub, hy, ht]; ring
    exact sub_eq_zero.1 (h1 _ h0)
  intro m
  induction m with
  | zero => intro x h; simpa using h
  | succ m ih =>
    intro x h
    apply base
    apply ih
    rw [pow_succ, mul_assoc] at h
    exact h

theorem step_one (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) :
    ∀ (n : ℕ) (T : Finset ι) (c : ι → S),
      ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p, s q ^ n} : Set A) →
      ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S) := by
  intro n
  induction n with
  | zero =>
    intro T c _ i _
    exact Ideal.mem_span_pair.2 ⟨0, c i, by simp⟩
  | succ n ih =>
    intro T c h
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
    have hT : ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S) :=
      ih T c (Ideal.mem_span_pair.2 ⟨x, y * s q, by rw [← hxy]; ring⟩)
    have hex : ∀ i, ∃ u v : S, i ∈ T → u * p + v * q ^ n = c i := by
      intro i
      by_cases hi : i ∈ T
      · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hT i hi)
        exact ⟨u, v, fun _ => huv⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose u v huv using hex
    have hsum : ∑ i ∈ T, s (c i) * b i
        = s p * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i := by
      rw [← map_pow, ← sum_decomp]
      exact Finset.sum_congr rfl fun i hi => by rw [huv i hi]
    set U := ∑ i ∈ T, s (u i) * b i
    set V := ∑ i ∈ T, s (v i) * b i
    have hd : s p ∣ s q ^ n * (V - y * s q) :=
      ⟨x - U, by linear_combination -hxy - hsum⟩
    obtain ⟨t, ht⟩ := dvd_of_dvd_pow_mul s p q h2 n _ hd
    have hV : V ∈ Ideal.span ({s p, s q} : Set A) :=
      Ideal.mem_span_pair.2 ⟨t, y, by linear_combination -ht⟩
    intro i hi
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (indep_finset s p q b h3 T v hV i hi)
    refine Ideal.mem_span_pair.2 ⟨u i + α * q ^ n, β, ?_⟩
    rw [← huv i hi, ← hαβ]
    ring

theorem step_three (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) (n : ℕ) :
    ∀ (m : ℕ) (T : Finset ι) (c : ι → S),
      ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p ^ m, s q ^ n} : Set A) →
      ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S) := by
  intro m
  induction m with
  | zero =>
    intro T c _ i _
    exact Ideal.mem_span_pair.2 ⟨c i, 0, by simp⟩
  | succ m ih =>
    intro T c h
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
    have hT : ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S) :=
      ih T c (Ideal.mem_span_pair.2 ⟨x * s p, y, by rw [← hxy]; ring⟩)
    have hex : ∀ i, ∃ u v : S, i ∈ T → u * p ^ m + v * q ^ n = c i := by
      intro i
      by_cases hi : i ∈ T
      · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hT i hi)
        exact ⟨u, v, fun _ => huv⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose u v huv using hex
    have hsum : ∑ i ∈ T, s (c i) * b i
        = s p ^ m * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i := by
      rw [← map_pow, ← map_pow, ← sum_decomp]
      exact Finset.sum_congr rfl fun i hi => by rw [huv i hi]
    set U := ∑ i ∈ T, s (u i) * b i
    set V := ∑ i ∈ T, s (v i) * b i
    have hd : s q ^ n ∣ s p ^ m * (U - x * s p) :=
      ⟨y - V, by linear_combination -hxy - hsum⟩
    obtain ⟨w, hw⟩ := pow_dvd_of_dvd_pow_mul s p q h1 h2 n m _ hd
    have hU : U ∈ Ideal.span ({s p, s q ^ n} : Set A) :=
      Ideal.mem_span_pair.2 ⟨x, w, by linear_combination -hw⟩
    intro i hi
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (step_one s p q b h1 h2 h3 n T u hU i hi)
    refine Ideal.mem_span_pair.2 ⟨α, β * p ^ m + v i, ?_⟩
    rw [← huv i hi, ← hαβ]
    ring

end GlobalTheory.BSP.StrictIndep

namespace GlobalTheory.BSP


open GlobalTheory.BSP.StrictIndep in
theorem strict_indep_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (p q : S)
    (ι : Type) (b : ι → A), (∀ x : A, s p * x = 0 → x = 0) →
    (∀ x : A, s p ∣ s q * x → s p ∣ x) →
    (∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) →
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈
      ((Ideal.span {p} ⊔ Ideal.span {q}) ^ m).map s →
      ∀ i, a i ∈ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n := by
  intro S A _ _ s p q ι b h1 h2 h3 n
  refine ⟨n + n, fun a ha i => ?_⟩
  have hle : (Ideal.span {p} ⊔ Ideal.span {q}) ^ (n + n) ≤ Ideal.span {p ^ n} ⊔ Ideal.span {q ^ n} := by
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
  have ha' : a.sum (fun i y => s y * b i) ∈ Ideal.span ({s p ^ n, s q ^ n} : Set A) := by
    have := Ideal.map_mono (f := s) hle ha
    rwa [map_span_pair, map_pow, map_pow] at this
  by_cases hi : i ∈ a.support
  · have hc := step_three s p q b h1 h2 h3 n n a.support (fun j => a j) ha' i hi
    rw [← span_sup_span_eq_pair, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow] at hc
    have hle2 : Ideal.span {p} ^ n ⊔ Ideal.span {q} ^ n ≤ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n :=
      sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)
    exact hle2 hc
  · rw [Finsupp.notMem_support_iff.1 hi]
    exact Ideal.zero_mem _

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycle
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.TameRel

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]


omit [IsTopologicalGroup Γ] in
theorem hom_trivial {l : ℕ} (hU : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → U.index.Coprime l)
    {C : Type} [Group C] (f : Γ →* C) (hf : IsOpen (f.ker : Set Γ)) (n : ℕ) (hC : ∀ x : C, x ^ l ^ n = 1) (j : Γ) :
    f j = 1 := by
  have h1 : f j ^ f.ker.index = 1 := by
    rw [← map_pow]
    exact f.ker.pow_index_mem j
  have h2 := (hU _ inferInstance hf).pow_right n
  have h3 := pow_gcd_eq_one.2 ⟨h1, hC (f j)⟩
  rwa [h2, pow_one] at h3


omit [IsTopologicalGroup Γ] in
theorem vanish_of_additive {l : ℕ} {J : Subgroup Γ}
    (hU : ∀ U : Subgroup J, U.Normal → IsOpen (U : Set J) → U.index.Coprime l)
    (K : Type) [Field K] [CharP K l] {W : Type} [AddCommGroup W] [Module K W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ J, ∀ h ∈ J, w (g * h) = w g + w h) : ∀ j ∈ J, w j = 0 := by
  intro j hj
  let f : J →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hf : IsOpen (f.ker : Set J) := (hw {0}).preimage continuous_subtype_val
  refine hom_trivial hU f hf 1 (fun x => ?_) ⟨j, hj⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, pow_one, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, toAdd_one]


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem additive_zpow {D : Subgroup Γ} {W : Type} [AddCommGroup W] (w : Γ → W)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (k : ℤ) : w (γ ^ k) = k • w γ := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  exact congrArg Multiplicative.toAdd (map_zpow f ⟨γ, hγ⟩ k)

theorem vanish_closure {D J : Subgroup Γ} (hJ : J ≤ D) {W : Type} [AddCommGroup W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (h0 : w γ = 0) (h1 : ∀ j ∈ J, w j = 0) :
    ∀ σ ∈ (Subgroup.zpowers γ ⊔ J).topologicalClosure, w σ = 0 := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hle : Subgroup.zpowers γ ⊔ J ≤ f.ker.map D.subtype := by
    refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨γ, hγ⟩, ?_, rfl⟩) fun j hj => ⟨⟨j, hJ hj⟩, ?_, rfl⟩
    · exact congrArg Multiplicative.ofAdd h0
    · exact congrArg Multiplicative.ofAdd (h1 j hj)
  have hsub : ((Subgroup.zpowers γ ⊔ J : Subgroup Γ) : Set Γ) ⊆ {x | w x = 0} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    exact congrArg Multiplicative.toAdd hy
  intro σ hσ
  exact closure_minimal hsub (hw.isClosed_fiber 0) hσ


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem second_pow {D : Subgroup Γ} {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] (z0 z1 : Γ → W)
    (lam : Γ → K) (hlam : ∀ g ∈ D, ∀ h ∈ D, lam (g * h) = lam g + lam h)
    (h1 : ∀ g ∈ D, ∀ h ∈ D, z1 (g * h) = z1 g + z1 h + lam g • z0 h) (h01 : z0 1 = 0) {γ : Γ} (hγ : γ ∈ D) (n : ℕ) :
    z1 (γ ^ n) = (n : K) • z1 γ + ((n.choose 2 : ℕ) : K) • lam γ • z0 γ := by
  induction n with
  | zero =>
    have := h1 1 D.one_mem 1 D.one_mem
    rw [mul_one, h01, smul_zero, add_zero] at this
    simpa using this
  | succ n ih =>
    have e : lam (γ ^ n) = (n : K) * lam γ := by
      have := additive_zpow lam hlam hγ n
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast] at this
    rw [pow_succ, h1 _ (D.pow_mem hγ n) _ hγ, ih, e, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast
    module

end Abstract

theorem cast_of_mod {K : Type} [Field K] {l M q : ℕ} [CharP K l] (hM : 1 ≤ M) (hq : q % (2 * l ^ M) = 1) :
    (q : K) = 1 ∧ ((q.choose 2 : ℕ) : K) = 0 := by
  have h := Nat.div_add_mod q (2 * l ^ M)
  rw [hq] at h
  generalize q / (2 * l ^ M) = t at h
  have hl : ((l ^ M : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero K l, zero_pow (by omega)]
  refine ⟨?_, ?_⟩
  · rw [← h, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hl]
    simp
  · have : q.choose 2 = q * (l ^ M * t) := by
      rw [Nat.choose_two_right]
      have : q - 1 = 2 * (l ^ M * t) := by rw [← h, Nat.add_sub_cancel, mul_assoc]
      rw [this, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this, Nat.cast_mul, Nat.cast_mul, hl]
    simp

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  intro hT F Ω _ _ _ _ _ l _ M A v hA hl hM hq d hd hsurj φ hφ
  obtain ⟨-, -, hU, -, ⟨γ0, hγ0⟩, hrel⟩ := hT F Ω l A v hA hl
  have hID : Ine (F := F) A ≤ Dec (F := F) A := fun σ hσ => hσ.1
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := F) A l
  have hJD := hJI.trans hID
  have hγD : γ0 ∈ Dec (F := F) A := hID hγ0.1
  have hφD : φ ∈ Dec (F := F) A := hφ.1
  have hdJ : ∀ j ∈ GlobalTheory.TameQuot.ineKer F A l, d j = 1 := fun j hj => by
    refine hom_trivial hU (d.comp (GlobalTheory.TameQuot.ineKer F A l).subtype) (hd.preimage continuous_subtype_val) M
      (fun x => ?_) ⟨j, hj⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, d γ0 ^ k = Multiplicative.ofAdd 1 := by
    obtain ⟨σ, hσ, hσd⟩ := hsurj (Multiplicative.ofAdd 1)
    have ho : IsOpen (((Subgroup.zpowers (d γ0)).comap d : Subgroup (G F Ω)) : Set (G F Ω)) :=
      Subgroup.isOpen_mono (H₁ := d.ker) (fun x hx => by
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact Subgroup.one_mem _) hd
    have hle : (Subgroup.zpowers γ0 ⊔ GlobalTheory.TameQuot.ineKer F A l).topologicalClosure ≤
        (Subgroup.zpowers (d γ0)).comap d := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ fun j hj => ?_) (Subgroup.isClosed_of_isOpen _ ho)
      · exact Subgroup.zpowers_le.2 (Subgroup.mem_zpowers _)
      · rw [Subgroup.mem_comap, hdJ j hj]; exact Subgroup.one_mem _
    obtain ⟨k, hk⟩ := hle (hγ0.2 hσ)
    exact ⟨k, hk.trans hσd⟩
  refine ⟨γ0 ^ k, Subgroup.zpow_mem _ hγ0.1 k, by rw [map_zpow, hk], ?_⟩
  intro K _ _ W _ _ z0 hz0 hadd0
  have hkK : (k : K) ≠ 0 := by
    intro h0
    have h1 : (k : ZMod (l ^ M)) * (d γ0).toAdd = 1 := by
      have := congrArg Multiplicative.toAdd hk
      rwa [toAdd_zpow, zsmul_eq_mul] at this
    have h2 := congrArg (ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) K) h1
    rw [map_mul, map_intCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  have hz0J := vanish_of_additive hU K z0 hz0 fun g hg h hh => hadd0 g (hJD hg) h (hJD hh)
  have e0 : z0 (γ0 ^ k) = (k : K) • z0 γ0 := by rw [additive_zpow z0 hadd0 hγD, Int.cast_smul_eq_zsmul]
  refine ⟨fun h σ hσ => ?_, fun lam z1 hlam hz1 haddl hadd1 => ?_⟩
  · rw [e0] at h
    exact vanish_closure hJD z0 hz0 hadd0 hγD ((smul_eq_zero.1 h).resolve_left hkK) hz0J σ (hγ0.2 hσ)
  · have hlJ := vanish_of_additive hU K lam hlam fun g hg h hh => haddl g (hJD hg) h (hJD hh)
    have hz1J := vanish_of_additive hU K z1 hz1 fun g hg h hh => by
      rw [hadd1 g (hJD hg) h (hJD hh), hz0J h hh, smul_zero, add_zero]
    have el : lam (γ0 ^ k) = (k : K) * lam γ0 := by rw [additive_zpow lam haddl hγD, zsmul_eq_mul]
    obtain ⟨hq1, hq2⟩ := cast_of_mod (K := K) hM hq
    have hj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) ∈ GlobalTheory.TameQuot.ineKer F A l :=
      (hrel ⟨φ, hφD⟩ ⟨γ0, hγD⟩ hφ hγ0).2.1
    generalize hjj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) = j at hj
    have hmul : φ * γ0 = γ0 ^ normV v * j * φ := by rw [← hjj]; group
    have hp : γ0 ^ normV v ∈ Dec (F := F) A := Subgroup.pow_mem _ hγD _
    have a1 := hadd1 φ hφD γ0 hγD
    have a2 : z1 (γ0 ^ normV v) = z1 γ0 := by
      rw [second_pow z0 z1 lam haddl hadd1 (hz0J 1 (Subgroup.one_mem _)) hγD, hq1, hq2, one_smul, zero_smul, add_zero]
    have a3 : lam (γ0 ^ normV v) = lam γ0 := by
      have := additive_zpow lam haddl hγD (normV v)
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast, hq1, one_mul] at this
    rw [hmul, hadd1 _ (Subgroup.mul_mem _ hp (hJD hj)) φ hφD, hadd1 _ hp j (hJD hj), haddl _ hp j (hJD hj), a2, a3,
      hz0J j hj, hz1J j hj, hlJ j hj, smul_zero, add_zero, add_zero, add_zero, add_comm (z1 φ), add_right_inj] at a1
    rw [el, e0, mul_smul, a1, smul_comm]

end GlobalTheory.TameRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootPowIdealsTendstoZeroWeakTop
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakClosed.SmallW

theorem glue
  (tilt : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), ¬ IsUnit (AI.εroot s - 1) ∧ ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ (AI.εroot s - 1) ^ m)
  (nbhd : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ → (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) → letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l, (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U)
  (witt : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p] (x : WittVector p R) (N m : ℕ), ∃ k : ℕ, ∀ (z : WittVector p R) (n : ℕ), n < N → (x ^ k * z).coeff n ∈ Ideal.span {x.coeff 0 ^ m}) :
  ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U := by
  intro l _ P AI s
  intro U hU

  obtain ⟨hnu, hdiv⟩ := tilt AI s

  obtain ⟨N, m, hN⟩ := nbhd (AI.εroot s - 1) hnu hdiv U hU

  obtain ⟨k, hk⟩ := witt (WittVector.teichmuller l (AI.εroot s) - 1) N m
  refine ⟨k, fun z => hN _ fun n hn => ?_⟩
  have h0 : (WittVector.teichmuller l (AI.εroot s) - 1 : WittVector l (OCb l)).coeff 0 =
      AI.εroot s - 1 := by
    have h := WittVector.add_coeff_zero
      (WittVector.teichmuller l (AI.εroot s) - 1 : WittVector l (OCb l)) 1
    rw [sub_add_cancel, WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h
    exact eq_sub_of_add_eq h.symm
  simpa [h0] using hk z n hn

theorem main : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U :=
  glue _root_.GlobalTheory.WeakClosed.TiltUnif.main GlobalTheory.T.weakly_small_of_not_isUnit_of_dvd_pow _root_.GlobalTheory.WittHighPow.high_pow_coeff_mem_span_pow

end GlobalTheory.WeakClosed.SmallW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOfCompatibleRoots
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem tilt_of_compatible_roots : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ → OC l),
    (∀ n, s (n + 1) ^ l = s n) → ∃ y : OCb l, ∀ n, GlobalTheory.MemLoc.rootT y n = s n := by
  intro l _ s hs
  exact (GlobalTheory.MemLoc.tilt_facts l).1 s hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTer
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_indep_of_first_terms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  intro l _ h d r y hh hr0 hr1 hy hdet c hc
  have h1 : 1 ≤ h := by omega
  refine _root_.GlobalTheory.indep_over_Ql_of_indep_mod_l l d (Fin 2) (fun a i => abelian₂ h i (y a)) (fun i => gam l h i r) ?_ ?_ c ?_
  · intro a i
    exact (_root_.GlobalTheory.PSer.Lam_main l h i r (y a) h1 hr1 (hy a)).2.2.1
  · intro n hn
    apply hdet n
    have hls := fun j => _root_.GlobalTheory.PSer.lamsum l h j d r (fun a => y a 0) n h1 hr0 hr1 (fun a => hy a 0)
    have hρ0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hρ1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (pow_pos (Fact.out : l.Prime).pos h).ne'
    refine _root_.GlobalTheory.PSer.norm_sh_le_of_lam_le l h (r ^ l ^ h) (∑ a, n a • y a 0) hh hρ0 hρ1 (lt_of_le_of_lt (hls 0).1 hr1) ?_
    intro j hj
    have hG := _root_.GlobalTheory.gam_laws l h j r h1 hr0 hr1
    rw [hG.2.2.2.2.1]
    have hnn : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_nonneg (norm_nonneg _) hG.2.2.1
    have hA := (hls j).2
    have hB : ‖∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a))‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hnn fun a _ => ?_
      rw [norm_mul]
      have hb := (_root_.GlobalTheory.PSer.Lam_main l h j r (y a) h1 hr1 (hy a)).2.1
      rw [norm_sub_rev] at hb
      calc ‖(n a : ℂ_[l])‖ * ‖lam h j (y a 0) - abelian₂ h j (y a)‖ ≤ 1 * (‖(l : ℂ_[l])‖ * gam l h j r) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) hb (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hC : ‖∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := hn ⟨j, hj⟩
    have heq : lam h j (∑ a, n a • y a 0) = (lam h j (∑ a, n a • y a 0) - ∑ a, (n a : ℂ_[l]) * lam h j (y a 0)) + (∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a)) + ∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB hC)
  · intro i
    exact hc i.1 i.2

end GlobalTheory.PSer
end

