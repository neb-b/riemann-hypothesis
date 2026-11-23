module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousLiftCompatible
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem homogeneous_lift_compatible : ∀ (l : ℕ) [Fact l.Prime] (w : ℕ) (p : (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n))), (∀ n, (p n).IsHomogeneous w) → (∀ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (p (n + 1)) = p n) → ∃ q : MvPolynomial (Fin 2) ℤ_[l], q.IsHomogeneous w ∧ (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q = p n) ∧ ∀ q' : MvPolynomial (Fin 2) ℤ_[l], (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q' = p n) → q' = q := by
  intro l _ w p hhom hcomp
  have hc1 : ∀ (m : Fin 2 →₀ ℕ) (n : ℕ),
      ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) ((p (n + 1)).coeff m) = (p n).coeff m := by
    intro m n
    rw [← hcomp n, MvPolynomial.coeff_map]
  have hc : ∀ (m : Fin 2 →₀ ℕ) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁)) ((p k₂).coeff m) = (p k₁).coeff m := by
    intro m k₁ k₂ hk
    induction k₂, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [← ih, ← hc1 m k]
      show _ = ((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)))) _
      rw [ZMod.castHom_comp]

  let f : ∀ k, MvPolynomial (Fin 2 →₀ ℕ) ℤ →+* ZMod (l ^ k) := fun k =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun m => (p k).coeff m)
  have hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply MvPolynomial.ringHom_ext
    · intro r; simp [f]
    · intro m
      simp only [f, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hc m k₁ k₂ hk
  let g := PadicInt.lift hf
  let c : (Fin 2 →₀ ℕ) → ℤ_[l] := fun m => g (MvPolynomial.X m)
  have hcn : ∀ m n, PadicInt.toZModPow n (c m) = (p n).coeff m := by
    intro m n
    have := congrArg (fun φ => φ (MvPolynomial.X m)) (PadicInt.lift_spec hf n)
    simpa [c, g, f] using this
  have hdeg : ∀ m, c m ≠ 0 → m.degree = w := by
    intro m hm
    by_contra hne
    apply hm
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, map_zero]
    by_contra h0
    apply hne
    rw [Finsupp.degree_eq_weight_one]
    exact hhom n h0
  have hfin : (Function.support c).Finite :=
    (Finsupp.finite_of_degree_le w).subset fun m hm => le_of_eq (hdeg m hm)
  let q : MvPolynomial (Fin 2) ℤ_[l] := ∑ m ∈ hfin.toFinset, MvPolynomial.monomial m (c m)
  have hq : ∀ m, q.coeff m = c m := by
    intro m
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h.symm
  refine ⟨q, ?_, ?_, ?_⟩
  · intro m hm
    rw [hq] at hm
    have h := hdeg m hm
    rw [Finsupp.degree_eq_weight_one] at h
    exact h
  · intro n
    ext m
    rw [MvPolynomial.coeff_map, hq, hcn]
  · intro q' hq'
    apply MvPolynomial.ext
    intro m
    rw [hq]
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, ← hq' n, MvPolynomial.coeff_map]

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def BtN (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], ∃ χ : SL(2, ℤ) → ZMod (l ^ n), H3.Kum X l n (b u) χ ∧ ∃ M : ℕ, 0 < M ∧
    ∀ δ : Gam N l, (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (c δ) = χ δ

def BtZ (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ n : ℕ, BtN X N l n b (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (c δ))

def Z1 (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (Gam N l → MvPolynomial (Fin 2) ℤ_[l]) where
  carrier := {c | (∀ γ, (c γ).IsHomogeneous w) ∧
    ∀ γ δ : Gam N l, c (γ * δ) = slP ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ}
  add_mem' := by
    rintro c c' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => (h1 γ).add (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add (f := _)]; abel
  zero_mem' := ⟨fun γ => MvPolynomial.isHomogeneous_zero _ _ _, fun γ δ => by simp⟩
  smul_mem' := by
    rintro r c ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · simpa [MvPolynomial.smul_eq_C_mul] using (MvPolynomial.isHomogeneous_C _ r).mul (h1 γ)
    · simp only [Pi.smul_apply, h2, map_smul, smul_add]

theorem hs_codiscrete_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem btZ_zero (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : BtZ X N l 0 0 := by
  intro n u
  refine ⟨0, ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, ?_, ?_⟩, 1, one_pos, fun δ _ => by simp⟩
  · simp [Tower.cls]
  · apply H3.isRoot_one
    haveI := hs_codiscrete_neBot
    exact one_ne_zero
  · intro δ _ z _; simp

end GlobalTheory.KZ.BettiB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctions
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.PolAct

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def homF (A : Submodule R M) (w : ℕ) : Submodule R ((Fin 2 → R) → M) where
  carrier := {b | ∃ c : Fin (w + 1) → M, (∀ i, c i ∈ A) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}
  zero_mem' := ⟨0, fun _ => A.zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c + d, fun i => A.add_mem (hc i) (hd i), fun u => by
      simp [ha, hb, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro r b ⟨c, hc, hb⟩
    exact ⟨r • c, fun i => A.smul_mem r (hc i), fun u => by
      simp only [Pi.smul_apply, hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma const_mem_homF_zero {A : Submodule R M} {x : M} (hx : x ∈ A) :
    (fun _ : Fin 2 → R => x) ∈ _root_.GlobalTheory.KZ.PolAct.homF A 0 :=
  ⟨fun _ => x, fun _ => hx, fun u => by simp⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_zero_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 0 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨Fin.cons 0 c, fun i => ?_, fun u => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [A.zero_mem]
    · simp [hc]
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, zero_add, Fin.val_succ,
      Nat.add_sub_add_right, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_one_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 1 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨fun j => if h : (j : ℕ) < n + 1 then c ⟨j, h⟩ else 0, fun j => ?_, fun u => ?_⟩
  · dsimp only
    split_ifs
    · exact hc _
    · exact A.zero_mem
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_self_iff_false,
      dif_neg, not_false_eq_true, smul_zero, add_zero, Fin.eta, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : n + 1 - (i : ℕ) = n - (i : ℕ) + 1 := Nat.sub_add_comm (Nat.lt_succ_iff.mp i.isLt)
    rw [hi, pow_succ]
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    (fun u => (α * u 0 + β * u 1) • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  have h := (_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).add_mem
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem α
      (coord_zero_smul_mem_homF_succ hb))
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem β
      (coord_one_smul_mem_homF_succ hb))
  convert h using 1
  funext u
  simp [add_smul, mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_pow_smul_mem_homF_add {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    ∀ k : ℕ, (fun u => (α * u 0 + β * u 1) ^ k • b u) ∈
      _root_.GlobalTheory.KZ.PolAct.homF A (n + k) := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := linear_form_smul_mem_homF_succ ih α β
    show _ ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + k + 1)
    convert h using 1
    funext u
    rw [pow_succ, mul_comm]
    exact (smul_smul (α * u 0 + β * u 1)
      ((α * u 0 + β * u 1) ^ k) (b u)).symm


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
theorem _root_.GlobalTheory.KZ.PolAct.subst_mem {A : Submodule R M} {w : ℕ} (φ : M →ₗ[R] M)
    (hφ : ∀ a ∈ A, φ a ∈ A)
    (m : Matrix (Fin 2) (Fin 2) R) {b : (Fin 2 → R) → M}
    (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A w) :
    (fun u => φ (b (m *ᵥ u))) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
  obtain ⟨c, hc, hbu⟩ := hb
  have hterm : ∀ i : Fin (w + 1), (fun u : Fin 2 → R =>
      ((m 0 0 * u 0 + m 0 1 * u 1) ^ (i : ℕ) * (m 1 0 * u 0 + m 1 1 * u 1) ^ (w - (i : ℕ))) •
        φ (c i)) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
    intro i
    have h0 := const_mem_homF_zero (hφ _ (hc i))
    have h1 := linear_form_pow_smul_mem_homF_add h0 (m 1 0) (m 1 1) (w - i)
    have h2 := linear_form_pow_smul_mem_homF_add h1 (m 0 0) (m 0 1) i
    have hdeg : 0 + (w - (i : ℕ)) + i = w := by
      have := i.isLt
      omega
    rw [hdeg] at h2
    convert h2 using 1
    funext u
    rw [mul_smul]
  have hsum := Submodule.sum_mem (_root_.GlobalTheory.KZ.PolAct.homF A w)
    (t := Finset.univ) (fun i _ => hterm i)
  convert hsum using 1
  funext u
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hbu, map_sum, map_smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Finset.sum_apply]


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
theorem _root_.GlobalTheory.KZ.PolAct.act_mem_pol {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l w : ℕ) [Fact l.Prime]
    (m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ a ∈ X.A l, X.kmap l
      (X.sl (_root_.GlobalTheory.KZ.toGQ m)).toRingEquiv a ∈ X.A l) :
    ∀ b ∈ X.Pol l w,
      X.act l m b ∈
        X.Pol l w := by
  intro b hb
  exact _root_.GlobalTheory.KZ.PolAct.subst_mem (A := X.A l) (w := w) _ h _ hb

end GlobalTheory.KZ.PolAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentatives
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem exists_right_div_upperTriangular_prime_det (q : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ)
    (h1 : (q : ℤ) ∣ m 0 1 - m 0 0 * k) (h2 : (q : ℤ) ∣ m 1 1 - m 1 0 * k) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨!![m 0 0, a; m 1 0, c], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -ha | linear_combination ha | linear_combination -hc

theorem cosetPrimeDet : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q →
    (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨
    ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  intro q hq m hdet
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Matrix.det_fin_two] at hdet
  have hd : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
    have : ((m 0 0 * m 1 1 - m 0 1 * m 1 0 : ℤ) : ZMod q) = 0 := by
      rw [hdet]; simp
    push_cast at this
    exact this

  have dv : ∀ x : ℤ, (x : ZMod q) = 0 → (q : ℤ) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx

  have fin : ∀ t : ZMod q, ((m 0 1 : ℤ) : ZMod q) - (m 0 0 : ℤ) * t = 0 →
      ((m 1 1 : ℤ) : ZMod q) - (m 1 0 : ℤ) * t = 0 →
      ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
    intro t ht1 ht2
    refine ⟨t.val, ZMod.val_lt t, exists_right_div_upperTriangular_prime_det q m t.val (dv _ ?_) (dv _ ?_)⟩
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht1
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht2
  by_cases ha : ((m 0 0 : ℤ) : ZMod q) = 0
  · by_cases hc : ((m 1 0 : ℤ) : ZMod q) = 0
    ·
      left
      obtain ⟨x, hx⟩ := dv _ ha
      obtain ⟨y, hy⟩ := dv _ hc
      refine ⟨!![x, m 0 1; y, m 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination hx | linear_combination -hy
    · right
      have h01 : ((m 0 1 : ℤ) : ZMod q) = 0 := by
        have : ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
          linear_combination -hd + ((m 1 1 : ℤ) : ZMod q) * ha
        exact (mul_eq_zero.mp this).resolve_right hc
      have hinv := mul_inv_cancel₀ hc
      refine fin (((m 1 1 : ℤ) : ZMod q) * ((m 1 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
      · rw [ha, h01]; ring
      · linear_combination -((m 1 1 : ℤ) : ZMod q) * hinv
  · right
    have hinv := mul_inv_cancel₀ ha
    refine fin (((m 0 1 : ℤ) : ZMod q) * ((m 0 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
    · linear_combination -((m 0 1 : ℤ) : ZMod q) * hinv
    · linear_combination ((m 0 0 : ℤ) : ZMod q)⁻¹ * hd - ((m 1 1 : ℤ) : ZMod q) * hinv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixChosenDiamondMatrixGamma1Gamma0
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

private lemma exists_isDiam_of_coprime (N l d : ℕ) (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hNl d 1
  have hk1 : Nat.Coprime k N := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkN]
    exact hd
  have hk2 : Nat.Coprime k l := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkl]
    simp
  have hk : Nat.Coprime k (N * l) := Nat.Coprime.mul_right hk1 hk2
  have hg : Int.gcd (k : ℤ) ((N * l : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hk
  have hb := Int.gcd_eq_gcd_ab (k : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  have hdet : (!![Int.gcdA (k : ℤ) ((N * l : ℕ) : ℤ), -Int.gcdB (k : ℤ) ((N * l : ℕ) : ℤ);
      ((N * l : ℕ) : ℤ), (k : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  refine ⟨(⟨_, hdet⟩ : SL(2, ℤ)), Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · simp only [en]
    simp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hkN

theorem isDiam_sgD_of_prime : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N →
    IsDiam N l d (sgD N l d) := by
  intro N l d _ _ hNl hd
  exact Classical.epsilon_spec (exists_isDiam_of_coprime N l d hNl hd)

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduce
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_pow_reduce (l n v : ℕ) (hl : l ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) ^ l =
      Complex.exp (2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  rw [← Complex.exp_nat_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hv : (v : ℂ) = ((v % l ^ n : ℕ) : ℂ) + (l : ℂ) ^ n * ((v / l ^ n : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mod_add_div v (l ^ n)).symm
  have e : (l : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) =
      2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n) +
        ((v / l ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hv]; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ →
      Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  intro Ω _ _ ε X l _ n x χ ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl0⟩
  refine ⟨f, fun z => a z ^ l, fun z => b z ^ l, M, hM, ?_, ⟨ha.pow l, hb.pow l, ?_, ?_⟩, ?_⟩
  · have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x
    change x.val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n) (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x) = _
    rw [hx]
    rfl
  · intro h
    apply hb0
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at h ⊢
    exact h.mono fun z hz => (pow_eq_zero_iff hl0).1 hz
  · have e1 : ((fun z => b z ^ l : ℂ → ℂ) : Mero) = (b : Mero) ^ l := Filter.Germ.coe_pow b l
    have e2 : ((fun z => a z ^ l : ℂ → ℂ) : Mero) = (a : Mero) ^ l := Filter.Germ.coe_pow a l
    rw [e1, e2, ← pow_mul, ← pow_mul, ← pow_succ', hab]
  · intro δ hδ z hz
    have h1 := congrArg (fun t : ℂ => t ^ l) (hrel δ hδ z hz)
    simp only [mul_pow] at h1
    rw [exp_pow_reduce l n _ hl0] at h1
    have hv : (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)).val = (χ δ).val % l ^ n := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [hv]
    simpa only [mul_pow, mul_assoc] using h1

end GlobalTheory.KZ.H3
end

