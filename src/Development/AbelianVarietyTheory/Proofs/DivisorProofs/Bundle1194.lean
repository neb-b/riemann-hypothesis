module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.RelMove

section Generic

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

theorem triv_move (σ : S →+* Sᵐᵒᵖ) (b : S) (x Y : Sˣ) (t s : A)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t) :
    ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop =
      algebraMap A S (s * t) := by
  have h1 : (σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop
      = s • ((x : S) * ((((Y⁻¹ : Sˣ) : S) * Y) * b * ((σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop)) * (σ x).unop) := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, ← Algebra.smul_def, mul_smul_comm,
          smul_mul_assoc, mul_assoc]
    _ = algebraMap A S (s * t) := by
        rw [Units.inv_mul, h1, one_mul, mul_one, hx, map_mul, Algebra.smul_def]

end Generic

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_units (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul, Units.inv_mul]; simp [sh]

theorem key (y v : G.Cˣ) (β : G.C) (s : ℚ) :
    ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C s * (y * ((v : G.C) * β * sh G v) * sh G y) := by
  calc ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C)
      = s • ((y : G.C) * v * (((y⁻¹ : G.Cˣ) : G.C) * y) * β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) *
          sh G v * sh G y) := by
        simp only [Units.val_mul, sh_mul, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, sh_units, mul_one, mul_one, Algebra.smul_def]; simp only [mul_assoc]

theorem scal (y : G.Cˣ) (β : G.C) (s u : ℚ) :
    algebraMap ℚ G.C u * (algebraMap ℚ G.C s * (y * β * sh G y)) =
      algebraMap ℚ G.C s * (y * (algebraMap ℚ G.C u * β) * sh G y) := by
  simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm u s]

theorem cancel (y : G.Cˣ) (X Z : G.C) (s : ℚ) (hs : s ≠ 0)
    (h : algebraMap ℚ G.C s * (y * X * sh G y) = algebraMap ℚ G.C s * (y * Z * sh G y)) : X = Z := by
  have h' : (y : G.C) * X * sh G y = y * Z * sh G y := by
    have := congrArg (fun w => algebraMap ℚ G.C s⁻¹ * w) h
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul] using this
  have e : ∀ W : G.C, W = ((y⁻¹ : G.Cˣ) : G.C) * (y * W * sh G y) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
    intro W
    rw [mul_assoc, mul_assoc, sh_units, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e X, e Z, h']

def cj (y : G.Cˣ) : G.Cˣ × ℚˣ ≃* G.Cˣ × ℚˣ := (MulAut.conj y).prodCongr (MulEquiv.refl ℚˣ)

theorem cj_apply (y : G.Cˣ) (v : G.Cˣ × ℚˣ) : cj y v = (y * v.1 * y⁻¹, v.2) := rfl

theorem mem_of (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (v : G.Cˣ × ℚˣ) (hv : v ∈ P.cent) : cj y v ∈ Q.cent := by
  obtain ⟨h1, h2⟩ := hv
  change v.1 * P.γ = P.γ * v.1 at h1
  change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β at h2
  refine ⟨?_, ?_⟩
  · change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹)
    rw [hγ]
    calc y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) = y * (v.1 * P.γ) * y⁻¹ := by group
      _ = y * (P.γ * v.1) * y⁻¹ := by rw [h1]
      _ = _ := by group
  · change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β
    rw [hβ, key, h2, scal]

theorem mem_back (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (w : G.Cˣ × ℚˣ) (hw : w ∈ Q.cent) : (cj y).symm w ∈ P.cent := by
  obtain ⟨h1, h2⟩ := hw
  set v := (cj y).symm w with hv
  have hw' : w = cj y v := by rw [hv, MulEquiv.apply_symm_apply]
  rw [hw', cj_apply] at h1 h2
  change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹) at h1
  change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β at h2
  refine ⟨?_, ?_⟩
  · change v.1 * P.γ = P.γ * v.1
    rw [hγ] at h1
    have : y * (v.1 * P.γ) * y⁻¹ = y * (P.γ * v.1) * y⁻¹ := by
      calc y * (v.1 * P.γ) * y⁻¹ = y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) := by group
        _ = (y * P.γ * y⁻¹) * (y * v.1 * y⁻¹) := h1
        _ = _ := by group
    simpa using this
  · change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β
    rw [hβ, key, scal] at h2
    exact cancel y _ _ s hs h2

theorem cent_map (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) : P.cent.map (cj y).toMonoidHom = Q.cent := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mem_of P Q y s hβ hγ v hv
  · intro hw
    exact ⟨(cj y).symm w, mem_back P Q y s hs hβ hγ w hw, by simp⟩

theorem toAf_val (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (v : P.cent) :
    ((P.toAf x t hx v : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      (x * Units.map (inC G (AfP p)).toMonoidHom v.1.1 * x⁻¹, Units.map (algebraMap ℚ (AfP p)).toMonoidHom v.1.2) :=
  rfl

theorem toQr_val (P : Pair G) (r : ℕ) (z : Gr G r) (v : P.cent) :
    P.toQr r z v = z⁻¹ * inclG G r (locC G v.1) * z := by
  simp [Pair.toQr, carry, MulAut.conj_apply]

theorem locC_conj (y : G.Cˣ) (v : G.Cˣ × ℚˣ) :
    locC G (y * v.1 * y⁻¹, v.2) = locC G (y, 1) * locC G v * (locC G (y, 1))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem triv_rel (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    Triv G (AfP p) Q.β (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs) * t) := by
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (inC G (AfP p) y)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  unfold Triv
  rw [hβ, map_mul, map_mul, map_mul, e1, e2]
  have := triv_move (starT G.star (AfP p)) (inC G (AfP p) P.β) x (Units.map (inC G (AfP p)).toMonoidHom y)
    (t : AfP p) (algebraMap ℚ (AfP p) s) hx
  simpa [mul_assoc] using this

end GlobalTheory.LKMid.RelMove

namespace GlobalTheory.LKMid.Pair


open GlobalTheory.LKMid.RelMove in
theorem term_eq_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
    P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  intro p _ G P Q Kf f r K φ hr hf hφ hPQ
  obtain ⟨y, s, hs, hβ, hγ⟩ := hPQ
  have hc : Q.c = P.c := (GlobalTheory.T.related_pairs_same_polarization p G P Q ⟨y, s, hs, hβ, hγ⟩).2
  have hat : Q.atP = locC G (y, 1) * P.atP * (locC G (y, 1))⁻¹ := by
    have := locC_conj y (P.γ, P.c)
    simp only [Pair.atP, hγ, hc]
    exact this
  have hnrm : ∀ δ z, IsNrm G r P.atP δ z → IsNrm G r Q.atP δ (inclG G r (locC G (y, 1)) * z) := by
    intro δ z h
    unfold IsNrm at h ⊢
    rw [h, hat, map_mul, map_mul, map_inv]
    group
  by_cases hP : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2
  · obtain ⟨⟨δ, z⟩, hδ⟩ := hP
    obtain ⟨x, t, hx⟩ := P.trivAf
    have hx' := triv_rel P Q y s hs.ne' hβ x t hx
    rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f r K φ hr hf hφ x t hx δ z hδ,
      GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G Q Kf f r K φ hr hf hφ _ _ hx' δ _ (hnrm δ z hδ)]
    let e : P.cent ≃* Q.cent := ((cj y).subgroupMap P.cent).trans
      (MulEquiv.subgroupCongr (cent_map P Q y s hs.ne' hβ hγ))
    have he : ∀ v : P.cent, ((e v : Q.cent) : G.Cˣ × ℚˣ) = cj y v := fun v => rfl
    have hA : (Q.toAf _ _ hx').comp e.toMonoidHom = P.toAf x t hx := by
      ext v : 1
      apply Subtype.ext
      rw [MonoidHom.comp_apply, toAf_val, toAf_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      refine Prod.ext ?_ rfl
      simp only [map_mul, map_inv]
      group
    have hQr : (Q.toQr r (inclG G r (locC G (y, 1)) * z)).comp e.toMonoidHom = P.toQr r z := by
      ext v : 1
      rw [MonoidHom.comp_apply, toQr_val, toQr_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      rw [locC_conj, map_mul, map_mul, map_inv]
      group
    have hS : Q.self = e P.self := by
      apply Subtype.ext
      rw [he, cj_apply]
      exact Prod.ext hγ hc
    unfold termAt
    have hS' : Q.toAf _ _ hx' (e P.self) = P.toAf x t hx P.self := by rw [← hA]; rfl
    rw [hS, ← GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv e, hS', hA, hQr]
  · have hQ : ¬ ∃ dz : Gr G r × Gr G r, IsNrm G r Q.atP dz.1 dz.2 := by
      rintro ⟨⟨δ, z⟩, h⟩
      apply hP
      refine ⟨(δ, (inclG G r (locC G (y, 1)))⁻¹ * z), ?_⟩
      unfold IsNrm at h ⊢
      rw [h, hat, map_mul, map_mul, map_inv]
      group
    unfold term
    rw [dite_eq_right hP, dite_eq_right hQ]

end GlobalTheory.LKMid.Pair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem swap_rev_comm {n : ℕ} (a i : Fin n) :
    Equiv.swap a a.rev i.rev = (Equiv.swap a a.rev i).rev := by
  rcases eq_or_ne i a with rfl | h1
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases eq_or_ne i a.rev with rfl | h2
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => h2 (by rw [← h, Fin.rev_rev])
  · exact fun h => h1 (Fin.rev_injective h)

theorem conj_diag_apply {R : Type} [CommRing R] {n : ℕ} (s : Equiv.Perm (Fin n))
    (Y Yi T : Matrix (Fin n) (Fin n) R) (hinv : Yi * Y = 1)
    (hY : ∀ i j, i ≠ s j → Y i j = 0) (hYi : ∀ i j, j ≠ s i → Yi i j = 0)
    (hT : ∀ i j, i ≠ j → T i j = 0) (i j : Fin n) :
    (Yi * T * Y) i j = if i = j then T (s i) (s i) else 0 := by
  have e1 : (Yi * T * Y) i j = Yi i (s j) * T (s j) (s j) * Y (s j) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
      · intro p _ hp; rw [hT p (s j) hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r _ hr; rw [hY r j hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  split_ifs with hij
  · subst hij
    have e2 : (Yi * Y) i i = Yi i (s i) * Y (s i) i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
      · intro p _ hp; rw [hY p i hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hinv, Matrix.one_apply_eq] at e2
    calc Yi i (s i) * T (s i) (s i) * Y (s i) i = T (s i) (s i) * (Yi i (s i) * Y (s i) i) := by ring
      _ = T (s i) (s i) := by rw [← e2, mul_one]
  · rw [hYi i (s j) (fun h => hij (s.injective h).symm), zero_mul, zero_mul]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_inv (z : L) : ordL z⁻¹ = -ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ordL]
  have h1 := GlobalTheory.BorelUMod.v_eq_exp (inv_ne_zero hz)
  rw [map_inv₀, GlobalTheory.BorelUMod.v_eq_exp hz, ← WithZero.exp_neg, WithZero.exp_inj] at h1
  linarith

theorem ordL_map {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (z : L) : ordL (σ z) = ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : σ z ≠ 0 := (map_ne_zero σ).2 hz
  have h1 := hσ z
  rw [GlobalTheory.BorelUMod.v_eq_exp hz, GlobalTheory.BorelUMod.v_eq_exp hz', WithZero.exp_inj] at h1
  linarith

end GlobalTheory.WeylCell.U21TorusFactor

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw α φ hφ t ht w x
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by
    rw [simpleU, if_neg hk]
  set a : Fin n := lo k with ha
  have hkv : k.val = n / 2 - 1 := by have := k.2; omega
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with h | h
    · exact absurd h hn
    · exact Nat.odd_iff.1 h
  have hav : a.val = k.val := rfl
  have hrv : (a.rev).val = n - 1 - k.val := by rw [Fin.val_rev, hav]; omega

  set Y : Matrix (Fin n) (Fin n) L := (((y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYd
  set Yi : Matrix (Fin n) (Fin n) L := ((((y : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYid
  set T : Matrix (Fin n) (Fin n) L := (((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  have hinv : Yi * Y = 1 := by
    rw [hYid, hYd, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYw : ∀ i j, i ≠ Equiv.swap a a.rev j → Y i j = 0 := by
    intro i j h; rw [← hs] at h; exact hw i j h
  have hYi : ∀ i j, j ≠ Equiv.swap a a.rev i → Yi i j = 0 := by
    intro i j h
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (y : GU σ n).2 i j
    rw [hYid, hm]
    have : j.rev ≠ Equiv.swap a a.rev i.rev := by
      rw [swap_rev_comm]; exact fun h' => h (Fin.rev_injective h')
    exact (congrArg σ (hYw _ _ this)).trans (map_zero σ)
  set b : GU σ n := y⁻¹ * t * y with hbd
  have hb : ∀ i j, (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if i = j then T (Equiv.swap a a.rev i) (Equiv.swap a a.rev i) else 0 := by
    intro i j
    have : (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Yi * T * Y := by
      simp [hbd, hYid, hYd, hTd, Units.val_mul]
    rw [this]
    exact conj_diag_apply _ Y Yi T hinv hYw hYi ht i j
  have hB : IsBorelU b := by
    intro i j hij
    rw [hb, if_neg (ne_of_gt hij)]
  have hsph := hφ b (y⁻¹ * w * x) 1 hB (one_mem _)
  have hprod : y⁻¹ * t * w * x = b * (y⁻¹ * w * x) * 1 := by
    rw [hbd]; group

  have hTa : T a a ≠ 0 ∧ ordL (T a.rev a.rev) = -ordL (T a a) := by
    set Ti : Matrix (Fin n) (Fin n) L := ((((t : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTid
    have h1 : T * Ti = 1 := by
      rw [hTid, hTd, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (T * Ti) a a = T a a * Ti a a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · intro p _ hp; rw [ht a p (Ne.symm hp), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, Matrix.one_apply_eq] at h2
    have hne : T a a ≠ 0 := by intro h0; rw [h0, zero_mul] at h2; exact one_ne_zero h2
    have hTi : Ti a a = (T a a)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h2.symm
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (t : GU σ n).2 a a
    rw [← hTid, hTi] at hm
    refine ⟨hne, ?_⟩
    rw [← ordL_map hσv (T a.rev a.rev)]
    exact (congrArg ordL hm.symm).trans (ordL_inv _)

  have e : ∀ (β : Fin (n / 2) → ℂ) (g : GU σ n), chiDeltaU q β g =
      ∏ i : Fin (n / 2), β i ^ ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
        (q : ℂ) ^ (-(ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
    intro β g
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dite_eq_left (by have := i.2; omega)]
    rfl
  have hact : ∀ i, (actU k α i : ℂ) = if i = k then (α k : ℂ)⁻¹ else α i := by
    intro i
    unfold actU
    rw [dite_eq_right hk]
    by_cases hi : i = k
    · subst hi; simp [Function.update_self, Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne hi, hi]
  have key : chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
    rw [e, e, Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
    have hrest : ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (α i : ℂ) ^ ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) =
        ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := by simpa using hi
      have hfix : Equiv.swap a a.rev (lo i) = lo i := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; apply hik; ext; have := congrArg Fin.val h; simpa [ha] using this
        · intro h; have := congrArg Fin.val h; rw [hrv] at this
          have h3 : (lo i : Fin n).val = i.val := rfl
          have := i.2; omega
      rw [hb, if_pos rfl, hfix, hact, if_neg hik]
    rw [hrest, hb, if_pos rfl, ← ha, Equiv.swap_apply_left, hTa.2, hact, if_pos rfl]
    have hE : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 2 := by omega
    rw [hE]
    set o := ordL (T a a)
    set R := ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    have hqq : (q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o) = (q : ℂ) ^ (-o * 2) := by
      rw [← zpow_add₀ hq]; ring_nf
    have hα : (α k : ℂ) ^ (-o) = ((α k : ℂ)⁻¹) ^ o := by rw [zpow_neg, inv_zpow]
    calc (α k : ℂ) ^ (-o) * (q : ℂ) ^ (-(-o) * 2) * R * (q : ℂ) ^ (-4 * o)
        = (α k : ℂ) ^ (-o) * ((q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o)) * R := by ring
      _ = ((α k : ℂ)⁻¹) ^ o * (q : ℂ) ^ (-o * 2) * R := by rw [hqq, hα]
  rw [hprod, hsph]
  calc chiDeltaU q (fun i => (α i : ℂ)) b * φ (y⁻¹ * w * x) * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))
      = (chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))) * φ (y⁻¹ * w * x) := by ring
    _ = _ := by rw [key]

end GlobalTheory.WeylCell.U21TorusFactor
end
end

