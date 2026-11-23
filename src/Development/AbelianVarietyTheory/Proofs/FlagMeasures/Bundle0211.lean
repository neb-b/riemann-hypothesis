module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoords
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovTop

theorem upperIn_of_zero {r : ℕ} (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, ne_of_lt h]
  · simp [upperIn, upper, h, Matrix.one_apply]

private theorem uEmb_one' (k r : ℕ) : uEmb k r (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  unfold uEmb
  simp only [inv_one, Matrix.one_apply]
  split_ifs <;> simp_all [Fin.ext_iff]
  omega

theorem crd_of_zero {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (h : q.1 = 0) :
    crd k r j β q = pTop k r j q.2 := by
  rw [crd, h, upperIn_of_zero, uEmb_one', Matrix.mul_one]

private theorem mulVec_bvec_lemma_2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M *ᵥ bvec j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

private theorem eI_inj' {k r : ℕ} (a c : Fin r) : eI k r a = eI k r c ↔ a = c := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  · rintro rfl
    rfl

private theorem wI_ne_esI' {k r : ℕ} (l : Fin (k + 1)) (b : Fin r) : wI k r l ≠ esI k r b := by
  intro h
  have h0 := congrArg Fin.val h
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  omega

private theorem pTop_mulVec_eq_of_vanishing {k r j : ℕ} (q : PTop k r j) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ m : Fin (2 * r + k + 1), r ≤ m.val → w m = 0) : pTop k r j q *ᵥ w = w := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [pTop, pOf, pEl]
  · intro m _ hmi
    by_cases hm : r ≤ m.val
    · simp [hw m hm]
    · have hz : pTop k r j q i m = 0 := by
        unfold pTop pOf pEl
        rw [if_neg (Ne.symm hmi), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
      simp [hz]
  · simp

private theorem pTop_wI_esI_eq {k r j : ℕ} (q : PTop k r j) (b : Fin r) (hb : j ≤ b.val) (l : Fin (k + 1)) :
    pTop k r j q (wI k r l) (esI k r b) = q.1 ⟨b, hb⟩ l := by
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  unfold pTop pOf pEl
  rw [if_neg (wI_ne_esI' l b), dite_eq_right (by omega), dif_pos (by omega)]
  have e1 : (⟨2 * r + k - (esI k r b).val, by omega⟩ : Fin r) = b := by
    apply Fin.ext
    show 2 * r + k - (2 * r + k - b.val) = b.val
    omega
  have e2 : (⟨(wI k r l).val - r, by omega⟩ : Fin (k + 1)) = l := by
    apply Fin.ext
    show r + l.val - r = l.val
    omega
  have hb' : j ≤ 2 * r + k - (esI k r b).val := by omega
  simp only [e1, e2, dif_pos hb']

private theorem crd_mulVec_bvec_eI_eq_upperIn {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    (crd k r j β q *ᵥ bvec (eI k r b)) (eI k r a) = upperIn β q.1 a b := by
  have ha : (eI k r a).val = a.val := rfl
  have hb : (eI k r b).val = b.val := rfl
  have := a.isLt
  have := b.isLt
  rw [crd, ← Matrix.mulVec_mulVec, pTop_mulVec_eq_of_vanishing, mulVec_bvec_lemma_2]
  · unfold uEmb
    rw [dif_pos (by omega)]
    rfl
  · intro m hm
    rw [mulVec_bvec_lemma_2]
    unfold uEmb
    have hne : m ≠ eI k r b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), if_neg hne]

theorem coords_top : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq
  obtain ⟨hR, -, -, -, -, hE, hI, -, -⟩ := hF
  obtain ⟨hadd, hsmul, -, -⟩ := id hR
  have hv : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) :=
    fun a => (hE a).1
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hβ⟩ u hsu
    dsimp only at hab hβ hsu ⊢
    have hab' : a.val < b.val := hab
    have hcol : upperIn β q.1 a b = q.1 ⟨⟨(a, b), hab⟩, hβ⟩ := by
      simp [upperIn, upper, hab, hβ]
    have key := congrFun (hq (N.F.e b.castSucc)) (eI k r a)
    rw [hsu, hadd, RealMat.phi_sum hR, hv b, Matrix.mulVec_smul, Pi.smul_apply, crd_mulVec_bvec_eI_eq_upperIn, hcol] at key
    simp only [hsmul, hv, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply,
      eI_inj', hab.ne, if_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_add, Complex.ofReal_pow] at key
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    have hpow : (ρ : ℂ) ^ (r - a.val) = (ρ : ℂ) ^ (r - b.val) * (ρ : ℂ) ^ (b.val - a.val) := by
      rw [← pow_add]
      congr 1
      have := b.isLt
      omega
    push_cast
    apply mul_left_cancel₀ hne
    linear_combination key + σ (u a) * hpow
  · intro h0 a
    apply RealMat.phi_inj hR
    rw [← hq, crd_of_zero β q h0, hv a, Matrix.mulVec_smul, pTop_mulVec_eq_of_vanishing]
    intro m hm
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have := a.isLt
    omega
  · rintro h0 ⟨b, hb⟩ y hy
    dsimp only at hy ⊢
    funext l
    have hw : s (N.ist b) - N.ist b - y ∈ N.F.Xa r := (Submodule.mem_inf.mp hy).1
    have hz := RealMat.coord_of_mem_Xa hR (fun a => (hE a).1) hw (wI k r l)
      (by have : (wI k r l).val = r + l.val := rfl; omega)
    have key := congrFun (hq (N.ist b)) (wI k r l)
    have hsplit : s (N.ist b) = N.ist b + y + (s (N.ist b) - N.ist b - y) := by abel
    rw [hsplit, hadd, hadd, hI b hb, crd_of_zero β q h0, Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec_lemma_2,
      pTop_wI_esI_eq q.2 b hb l] at key
    simp only [Pi.add_apply, hz, add_zero, Pi.smul_apply, bvec, Pi.single_apply, wI_ne_esI' l b, if_false,
      smul_eq_mul, mul_zero, zero_add, Complex.ofReal_inv, Complex.ofReal_pow] at key
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    rw [← key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end GlobalTheory.DegVol.RefCovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealMatrixMemBesselUnipotentOfFrame
section
open Matrix

noncomputable section
open Formalism.HermitianLatticeCounting.S6 Formalism.QuantumDeterminants GlobalTheory.DegVol.RealMat

namespace GlobalTheory.DegVol.FrameUnip

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {k r : ℕ} {σ : K →+* ℂ} {Φ : V → Fin (2 * r + k + 1) → ℂ}

theorem phi_zero' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) : Φ 0 = 0 := by
  have := h.2.1 0 0
  simpa using this

theorem phi_sub' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (x y : V) : Φ (x - y) = Φ x - Φ y := by
  have := h.1 (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem phi_sum' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {α : Type} (s : Finset α) (f : α → V) :
    Φ (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phi_zero' h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.1, ih]

theorem span_ind' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (P : (Fin (2 * r + k + 1) → ℂ) → Prop) (h0 : ∀ x, P (Φ x))
    (ha : ∀ u v, P u → P v → P (u + v)) (hs : ∀ (c : ℂ) u, P u → P (c • u)) (u : Fin (2 * r + k + 1) → ℂ) : P u := by
  have hu : u ∈ Submodule.span ℂ (Set.range Φ) := by rw [h.2.2.2]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact h0 y
  | zero => rw [← phi_zero' h]; exact h0 0
  | add x y _ _ hx hy => exact ha _ _ hx hy
  | smul c x _ hx => exact hs _ _ hx

theorem mem_UH' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (e : ∀ x y, herm (Hpk k r) (m *ᵥ Φ x) (m *ᵥ Φ y) = herm (Hpk k r) (Φ x) (Φ y)) : m ∈ UH (Hpk k r) := by
  have h1 : ∀ u w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w := by
    intro u
    refine span_ind' h (fun u => ∀ w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w) (fun x => ?_)
      (fun u v hu hv w => by rw [mulVec_add, herm_add_left, herm_add_left, hu, hv])
      (fun c u hu w => by rw [mulVec_smul, herm_smul_left, herm_smul_left, hu]) u
    exact span_ind' h _ (e x) (fun u v hu hv => by rw [mulVec_add, GlobalTheory.DegVol.RealMat.herm_add_right, GlobalTheory.DegVol.RealMat.herm_add_right, hu, hv])
      (fun c u hu => by rw [mulVec_smul, herm_smul_right, herm_smul_right, hu])
  ext i j
  exact (herm_bvec _ i j).symm.trans (by rw [← herm_mulVec, h1, herm_bvec])

theorem coord_span (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {e : Fin r → V} {ρ : Fin r → ℂ}
    (he : ∀ a, Φ (e a) = ρ a • bvec (eI k r a)) {S : Set (Fin r)} (i : Fin (2 * r + k + 1))
    (hS : ∀ b ∈ S, b.val < i.val) {y : V} (hy : y ∈ Submodule.span K (e '' S)) : Φ y i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' := hS b hb
    have : i ≠ eI k r b := fun e => by
      have := congrArg Fin.val e
      simp only [eI] at this; omega
    simp [he, bvec, this]
  | zero => rw [phi_zero' h]; rfl
  | add x y _ _ hx hy => rw [h.1, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [h.2.1, Pi.smul_apply, hx, smul_zero]

theorem mem_Nset : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro K V _ _ _ _ H k r σ Φ h e f ρ ρ' hρ hρ' he hf hef m hm h2 h3 n hn
  refine ⟨mem_UH' h fun x y => by rw [hn, hn, h.2.2.1, h.2.2.1, hm], fun a i hi => ?_, fun i j hj hj' hi => ?_⟩
  · have := coord_span h he i (S := {b | b < a}) (fun b hb => lt_of_lt_of_le (Fin.lt_def.1 hb) hi) (h2 a)
    rw [phi_sub' h, ← hn, he, mulVec_smul, ← smul_sub, Pi.smul_apply, smul_eq_zero, or_iff_right (hρ a), Pi.sub_apply,
      sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this
  · let P : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u =>
      u - ∑ a : Fin r, herm (Hpk k r) u (Φ (e a)) • Φ (f a)
    have hP : ∀ u, (n *ᵥ P u - P u) i = 0 := by
      refine span_ind' h _ (fun x => ?_) (fun u v hu hv => ?_) (fun c u hu => ?_)
      · have ex : P (Φ x) = Φ (x - ∑ a : Fin r, H.B x (e a) • f a) := by
          simp only [P, phi_sub' h, phi_sum' h, h.2.1, h.2.2.1]
        rw [ex, hn, ← phi_sub' h]
        have hperp : ∀ b, H.B (e b) (x - ∑ a : Fin r, H.B x (e a) • f a) = 0 := fun b => by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sub, map_sum]
          simp [hef]
          rw [starRingEnd_apply, H.herm, sub_self]
        have := h3 _ hperp
        rw [← Set.image_univ] at this
        exact coord_span h he i (fun b _ => lt_of_lt_of_le b.2 hi) this
      · have ex : P (u + v) = P u + P v := by
          simp only [P, herm_add_left, add_smul, Finset.sum_add_distrib]; abel
        rw [ex, mulVec_add, add_sub_add_comm, Pi.add_apply, hu, hv, add_zero]
      · have ex : P (c • u) = c • P u := by
          simp only [P, herm_smul_left, smul_sub, Finset.smul_sum, smul_smul]
        rw [ex, mulVec_smul, ← smul_sub, Pi.smul_apply, hu, smul_zero]
    have ex : P (bvec j) = bvec j := by
      simp only [P]
      rw [Finset.sum_eq_zero, sub_zero]
      intro a _
      have hne : esI k r a ≠ j := fun e' => by
        have := congrArg Fin.val e'
        have := a.2
        simp only [esI] at *; omega
      rw [he, herm_smul_right, herm_eI]
      simp [bvec, hne]
    have := hP (bvec j)
    rw [ex, Pi.sub_apply, sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this

end GlobalTheory.DegVol.FrameUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationMemStandardMiddleSpace
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.MidLift

open GlobalTheory.DegVol.RealMat

variable {k r j : ℕ}

private lemma Hpk_esI_apply' (a : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) i = if i = eI k r a then 1 else 0 := by
  have ha := a.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_esI (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, Hpk_esI_apply']

theorem coord_eq_zero {g : Mat k r} (hg : g ∈ UH (Hpk k r))
    (hX : ∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, a.val < j → herm (Hpk k r) u (g⁻¹ *ᵥ bvec (eI k r a)) = 0)
    (b : Fin r) (hb : b.val < j) : u (eI k r b) = 0 := by
  have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hg

  have hinj : Function.Injective (Matrix.mulVecLin g⁻¹) := by
    intro x y hxy
    have h := congrArg (fun v => g *ᵥ v) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet] using h

  have hli : ∀ f : {a : Fin r // a.val < j} → Fin (2 * r + k + 1), Function.Injective f →
      LinearIndependent ℂ (fun a => bvec (f a)) := by
    intro f hf
    have h := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp f hf
    convert h using 1
    funext a
    simp [bvec, Function.comp]
  have hI1 : Function.Injective fun a : {a : Fin r // a.val < j} => eI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [eI, Fin.val_mk] at h'
    exact Subtype.ext (Fin.ext h')
  have hI2 : Function.Injective fun a : {a : Fin r // a.val < j} => esI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [esI, Fin.val_mk] at h'
    have := a.1.isLt
    have := a'.1.isLt
    exact Subtype.ext (Fin.ext (by omega))
  have hl1 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1)) := hli _ hI1
  have hl2 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hli _ hI2

  have hle : (XJ k r j).map (Matrix.mulVecLin g⁻¹) ≤ XstJ k r j := by
    unfold XJ
    rw [Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact (hX a.1 a.2).1
  have hrank : Module.finrank ℂ ((XJ k r j).map (Matrix.mulVecLin g⁻¹)) = Module.finrank ℂ (XstJ k r j) := by
    rw [← (Submodule.equivMapOfInjective _ hinj (XJ k r j)).finrank_eq]
    unfold XJ XstJ
    rw [finrank_span_eq_card hl1, finrank_span_eq_card hl2]
  have heq : (XJ k r j).map (Matrix.mulVecLin g⁻¹) = XstJ k r j :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : bvec (esI k r b) ∈ (XJ k r j).map (Matrix.mulVecLin g⁻¹) := by
    rw [heq]
    unfold XstJ
    exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hmem
  have hzero : ∀ x ∈ XJ k r j, herm (Hpk k r) u (g⁻¹ *ᵥ x) = 0 := by
    intro x hx
    unfold XJ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hu a.1 a.2
    | zero => simp [herm]
    | add x₁ x₂ _ _ h₁ h₂ => rw [Matrix.mulVec_add, GlobalTheory.DegVol.RealMat.herm_add_right, h₁, h₂, add_zero]
    | smul c y _ h => rw [Matrix.mulVec_smul, GlobalTheory.DegVol.RealMat.herm_smul_right, h, mul_zero]
  rw [← herm_esI u b, ← hxe, Matrix.mulVecLin_apply]
  exact hzero x hx

theorem inWb_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF w hw
  unfold IsFrameOf at hF
  obtain ⟨hR, -, -, -, ⟨c, hN⟩, he, hist, -, -⟩ := hF
  unfold IsReal at hR
  obtain ⟨-, -, hiso, -⟩ := hR
  unfold IsNormal0 at hN
  obtain ⟨hgG, -, -, -, -, hX, -, -⟩ := hN
  unfold GlobalTheory.DegCnt.NF.Wn at hw
  rw [GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw

  have hBe : ∀ a : Fin r, H.B w (N.F.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F.e a.castSucc) w, hw _ h1, star_zero]
  have hBe' : ∀ a : Fin r, H.B w (N.F'.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F'.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F'.e a.castSucc) w, hw _ h1, star_zero]
  have hBist : ∀ b : Fin r, N.j ≤ b.val → H.B w (N.ist b) = 0 := by
    intro b hb
    have h1 : N.ist b ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← H.herm (N.ist b) w, hw _ h1, star_zero]
  have hρ' : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (pow_pos hρ n).ne'

  have hes : ∀ a : Fin r, Φ w (esI k r a) = 0 := by
    intro a
    have h1 := hiso w (N.F.e a.castSucc)
    rw [(he a).1, GlobalTheory.DegVol.RealMat.herm_smul_right, GlobalTheory.DegVol.RealMat.herm_eI, hBe a, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 (hρ' _))

  have hhi : ∀ b : Fin r, N.j ≤ b.val → Φ w (eI k r b) = 0 := by
    intro b hb
    have h1 := hiso w (N.ist b)
    rw [hist b hb, GlobalTheory.DegVol.RealMat.herm_smul_right, herm_esI, hBist b hb, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (star_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_pos hρ _).ne')))

  have hlo : ∀ b : Fin r, b.val < N.j → Φ w (eI k r b) = 0 := by
    have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hgG
    intro b hb
    refine coord_eq_zero (j := N.j) hgG hX (fun a _ => ?_) b hb
    have h3 : Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • (g⁻¹ *ᵥ bvec (eI k r a)) := by
      rw [← Matrix.mulVec_smul, ← (he a).2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
    have h2 : g⁻¹ *ᵥ bvec (eI k r a) = (((ρ ^ (r - a.val) : ℝ) : ℂ))⁻¹ • Φ (N.F'.e a.castSucc) := by
      rw [h3, inv_smul_smul₀ (hρ' _)]
    rw [h2, GlobalTheory.DegVol.RealMat.herm_smul_right, hiso, hBe' a, map_zero, mul_zero]
  unfold inWb
  intro i hi
  rcases hi with hi | hi
  · have hb : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [← hb]
    by_cases hj : i.val < N.j
    · exact hlo ⟨i.val, hi⟩ hj
    · exact hhi ⟨i.val, hi⟩ (not_lt.1 hj)
  · have hlt : 2 * r + k - i.val < r := by
      have := i.isLt
      omega
    have hb : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by
      apply Fin.ext
      simp only [esI, Fin.val_mk]
      have := i.isLt
      omega
    rw [← hb]
    exact hes _

end GlobalTheory.DegVol.MidLift
end

