module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixPiIffForallEval
section
open Matrix

namespace GlobalTheory.BesselChar

theorem unip_pi_iff {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) (ι → S)) (K : Matrix (Fin ρ) (Fin n) (ι → S))
    (M : Matrix (Fin n) (Fin n) (ι → S)) :
    GlobalTheory.BesselChar.Unip E K M ↔ ∀ i, GlobalTheory.BesselChar.Unip (E.map (Pi.evalRingHom (fun _ => S) i))
      (K.map (Pi.evalRingHom (fun _ => S) i)) (M.map (Pi.evalRingHom (fun _ => S) i)) := by
  constructor
  · rintro ⟨⟨T, hT, e⟩, h2⟩ i
    set φ := Pi.evalRingHom (fun _ => S) i
    refine ⟨⟨T.map φ, fun j l hjl => by simp [Matrix.map_apply, hT j l hjl], ?_⟩, fun y hy => ?_⟩
    · have := congrArg (fun X => X.map φ) e
      simpa only [Matrix.map_mul, Matrix.map_add _ (map_add φ)] using this
    · let y' : Fin n → ι → S := fun k => Pi.single i (y k)
      have hy' : K *ᵥ y' = 0 := by
        funext j i'
        by_cases hi : i' = i
        · subst hi
          have h1 := congr_fun (mulVec_map φ K y') j
          have h0 : (fun k => φ (y' k)) = y := by
            funext k; simp [φ, y']
          rw [h0, hy] at h1
          simpa [φ] using h1.symm
        · show (∑ k, K j k * y' k) i' = 0
          rw [Finset.sum_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          simp [y', Pi.single_apply, hi]
      obtain ⟨a, ha⟩ := h2 y' hy'
      refine ⟨fun l => φ (a l), ?_⟩
      have h0 : (fun k => φ (y' k)) = y := by
        funext k; simp [φ, y']
      have h1 := mulVec_map φ M y'
      have h3 := mulVec_map φ E a
      rw [h0] at h1
      rw [h1, h3, ha]
      funext k
      simp only [Pi.add_apply, map_add (f := _)]
      rw [show φ (y' k) = y k from congr_fun h0 k]
  · intro h
    choose hc hv using h
    choose T hT e using hc
    refine ⟨⟨Matrix.of fun j l i => T i j l, fun j l hjl => by funext i; exact hT i j l hjl, ?_⟩, fun y hy => ?_⟩
    · ext k l i
      have h1 := congr_fun (congr_fun (e i) k) l
      have hT' : (Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i) = T i := by
        ext j l; rfl
      have h2 : ((M * E).map (Pi.evalRingHom (fun _ => S) i)) k l
          = ((E + E * Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i)) k l := by
        rw [Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hT']
        exact h1
      simpa using h2
    · have hyi : ∀ i, K.map (Pi.evalRingHom (fun _ => S) i) *ᵥ (fun k => y k i) = 0 := by
        intro i
        have := mulVec_map (Pi.evalRingHom (fun _ => S) i) K y
        refine this.trans ?_
        rw [hy]; rfl
      choose a ha using fun i => hv i _ (hyi i)
      refine ⟨fun l i => a i l, ?_⟩
      funext k i
      have h1 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) M y) k
      have h3 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) E (fun l i => a i l)) k
      have h4 := congr_fun (ha i) k
      simp only [Pi.evalRingHom_apply] at h1 h3
      show (M *ᵥ y) k i = y k i + (E *ᵥ fun l i => a i l) k i
      rw [← h1, ← h3, h4]
      rfl

end GlobalTheory.BesselChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentRealPlaceIffFrameUnipotentRadical
section
open Matrix NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealUnipFrame

variable {n ρ : ℕ}

theorem mem_span_image_iff (g : Fin ρ → Fin n → ℂ) (S : Set (Fin ρ)) (w : Fin n → ℂ) :
    w ∈ Submodule.span ℂ (g '' S) ↔ ∃ t : Fin ρ → ℂ, (∀ b, b ∉ S → t b = 0) ∧ ∑ b, t b • g b = w := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 h
    refine ⟨l, fun b hb => ?_, ?_⟩
    · by_contra h0
      exact hb (hl (Finsupp.mem_support_iff.2 h0))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨t, ht, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [ht b hb, zero_smul]; exact Submodule.zero_mem _

theorem mem_span_image_mulVec (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (g : Fin ρ → Fin n → ℂ)
    (S : Set (Fin ρ)) (w : Fin n → ℂ) :
    Q *ᵥ w ∈ Submodule.span ℂ ((fun b => Q *ᵥ g b) '' S) ↔ w ∈ Submodule.span ℂ (g '' S) := by
  rw [mem_span_image_iff, mem_span_image_iff]
  have hinj : ∀ u u' : Fin n → ℂ, Q *ᵥ u = Q *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (P *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec] using this
  have hsum : ∀ t : Fin ρ → ℂ, ∑ b, t b • Q *ᵥ g b = Q *ᵥ ∑ b, t b • g b := by
    intro t
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  refine exists_congr fun t => and_congr Iff.rfl ?_
  rw [hsum]
  exact ⟨hinj _ _, fun h => by rw [h]⟩

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

variable {n ρ : ℕ}

theorem cols_iff (f : Fin ρ → Fin n → ℂ) (d : Fin ρ → ℂ) (hd : ∀ a, d a ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ) :
    (∃ T : Matrix (Fin ρ) (Fin ρ) ℂ, GlobalTheory.BesselChar.StrictUp T ∧
      N * Matrix.of (fun k a => d a * f a k) = Matrix.of (fun k a => d a * f a k) + Matrix.of (fun k a => d a * f a k) * T) ↔
    ∀ i : Fin ρ, (N - 1) *ᵥ f i ∈ Submodule.span ℂ (f '' {b | b.1 < i.1}) := by
  have e1 : ∀ i k, d i * (N *ᵥ f i) k = ∑ j, N k j * (d i * f i j) := by
    intro i k
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rintro ⟨T, hT, h⟩ i
    rw [mem_span_image_iff]
    refine ⟨fun j => d j * T j i / d i, fun j hj => ?_, ?_⟩
    · have : i ≤ j := by
        simp only [Set.mem_setOf_eq, not_lt] at hj
        exact Fin.le_def.2 hj
      show d j * T j i / d i = 0
      rw [hT j i this]; simp
    · funext k
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply] at hk
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      have hdi := hd i
      have key : d i * (N *ᵥ f i) k = d i * f i k + ∑ j, d j * T j i * f j k := by
        have e2 : ∑ j, d j * T j i * f j k = ∑ j, d j * f j k * T j i :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [e1, hk, e2]
      have e4 : ∑ x, d x * T x i / d i * f x k = (∑ j, d j * T j i * f j k) / d i := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e4, div_eq_iff hdi]
      linear_combination -key
  · intro h
    choose t ht hts using fun i => (mem_span_image_iff f _ _).1 (h i)
    refine ⟨Matrix.of fun j i => d i * t i j / d j, fun j i hij => ?_, ?_⟩
    · have : ¬ j.1 < i.1 := by rw [Fin.le_def] at hij; omega
      simp [ht i j (by simpa using this)]
    · ext k i
      have hk := congrFun (hts i) k
      rw [Finset.sum_apply] at hk
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hk
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
      have e3 : ∑ j, d j * f j k * (d i * t i j / d j) = d i * ∑ j, t i j * f j k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := hd j
        field_simp
      rw [← e1, e3, hk]
      ring

theorem colspan_iff (f : Fin ρ → Fin n → ℂ) (d : Fin ρ → ℂ) (hd : ∀ a, d a ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) :
    (∃ a, N *ᵥ y = y + Matrix.of (fun k a => d a * f a k) *ᵥ a) ↔
      (N - 1) *ᵥ y ∈ Submodule.span ℂ (f '' {b | b.1 < ρ}) := by
  have hE : ∀ a : Fin ρ → ℂ, Matrix.of (fun k a => d a * f a k) *ᵥ a = ∑ b, (a b * d b) • f b := by
    intro a; funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [mem_span_image_iff, Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun b => a b * d b, fun b hb => absurd b.2 (by simpa using hb), ?_⟩
    rw [← hE, ha, add_sub_cancel_left]
  · rintro ⟨t, -, ht⟩
    refine ⟨fun b => t b / d b, ?_⟩
    rw [hE]
    have : ∀ b, t b / d b * d b = t b := fun b => div_mul_cancel₀ _ (hd b)
    simp only [this, ht, add_sub_cancel]

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

open Formalism.L2.SG.HidaSetting

variable {n ρ : ℕ}

theorem conj_sub_mulVec (Q P N : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (w : Fin n → ℂ) :
    (Q * N * P - 1) *ᵥ (Q *ᵥ w) = Q *ᵥ ((N - 1) *ᵥ w) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hPQ, Matrix.mul_one]

theorem hJ_frame (ε : Fin n → Bool) (P Q Jc : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hspec : Pᴴ * Jc * P = Formalism.REAL.Jm ε) (f y : Fin n → ℂ) :
    hJ ε (Q *ᵥ f) (Q *ᵥ y) = star f ⬝ᵥ (Jc *ᵥ y) := by
  unfold hJ
  rw [← hspec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, hPQ,
    Matrix.conjTranspose_one, Matrix.one_mulVec]

theorem emb_hform (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x z : Fin I.n → I.E) :
    I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x z) =
      star (fun i => I.φ v (x i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (z i)) := by
  rw [← Formalism.MainNotions.BridgeUnipRad.hform_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, starRingEnd_apply,
    Formalism.MainNotions.BridgeUnipRad.emb_star]

theorem perp_mulVec (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (y : Fin I.n → ℂ) :
    (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v) *ᵥ y =
      fun a => starRingEnd ℂ (I.φ v (c a)) * (star (fun i => I.φ v (x a i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ y)) := by
  funext a
  rw [Matrix.map_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_mul, starRingEnd_apply, Formalism.MainNotions.BridgeUnipRad.emb_star,
    Pi.star_apply, star_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

open Formalism.L2.SG.HidaSetting

theorem unip_iff_inN : ∀ (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) →
    ∀ (N : Matrix (Fin I.n) (Fin I.n) ℂ), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔
      Formalism.L2.SG.HidaSetting.InN (I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv I v (x a)) (Formalism.L2.SG.HidaSetting.rv I v z)
        ((I.P v)⁻¹ * N * I.P v) := by
  intro I v ρ x c z hc hz N
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hQP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hu
  set f : Fin ρ → Fin I.n → ℂ := fun a k => I.φ v (x a k) with hf
  set d : Fin ρ → ℂ := fun a => I.φ v (c a) with hdd
  have hd : ∀ a, d a ≠ 0 := fun a => (map_ne_zero (I.φ v)).2 (hc a)
  have hE : (Matrix.of fun k a => c a * x a k).map (I.φ v) = Matrix.of fun k a => d a * f a k := by
    ext k a; simp [hf, hdd]
  have hrv : ∀ w : Fin I.n → I.E, rv I v w = (I.P v)⁻¹ *ᵥ fun i => I.φ v (w i) := fun _ => rfl
  have hrx : (fun a => rv I v (x a)) = fun b => (I.P v)⁻¹ *ᵥ f b := rfl
  have hspan : ∀ (w : Fin I.n → ℂ) (S : Set (Fin ρ)),
      ((I.P v)⁻¹ * N * I.P v - 1) *ᵥ ((I.P v)⁻¹ *ᵥ w) ∈ Submodule.span ℂ ((fun a => rv I v (x a)) '' S) ↔
        (N - 1) *ᵥ w ∈ Submodule.span ℂ (f '' S) := by
    intro w S
    rw [conj_sub_mulVec _ _ _ hPQ, hrx]
    exact mem_span_image_mulVec _ _ hPQ f S _
  have hperp : ∀ y : Fin I.n → ℂ,
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) *ᵥ y = 0 ↔
        ∀ a, hJ (I.ε v) (rv I v (x a)) ((I.P v)⁻¹ *ᵥ y) = 0 := by
    intro y
    rw [perp_mulVec]
    simp only [hrv, hJ_frame (I.ε v) (I.P v) _ (I.J.map (I.φ v)) hPQ (I.P_spec v)]
    constructor
    · intro h a
      have := congrFun h a
      exact (mul_eq_zero.1 this).resolve_left ((map_ne_zero _).2 (hd a))
    · intro h
      funext a
      simp [h a]
  unfold GlobalTheory.BesselChar.Unip InN InS spanLt
  rw [hE, cols_iff f d hd N]
  have hB : (∀ y, ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) *ᵥ y = 0 →
        ∃ a, N *ᵥ y = y + (Matrix.of fun k a => d a * f a k) *ᵥ a) ↔
      ∀ y, (∀ a, hJ (I.ε v) (rv I v (x a)) y = 0) →
        ((I.P v)⁻¹ * N * I.P v - 1) *ᵥ y ∈ Submodule.span ℂ ((fun a => rv I v (x a)) '' {b | b.1 < ρ}) := by
    constructor
    · intro h y' hy'
      have hy : y' = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ y') := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
      rw [hy] at hy' ⊢
      rw [hspan, ← colspan_iff f d hd]
      exact h _ ((hperp _).2 hy')
    · intro h y hy
      rw [colspan_iff f d hd, ← hspan]
      exact h _ ((hperp y).1 hy)
  rw [hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun a => (hspan (f a) _).2 (h1 a), ?_⟩, h2⟩
    refine h2 _ fun a => ?_
    rw [hrv, hrv, hJ_frame (I.ε v) (I.P v) _ (I.J.map (I.φ v)) hPQ (I.P_spec v), ← emb_hform, hz a, map_zero]
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨fun a => (hspan (f a) _).1 (h1 a), h2⟩

end GlobalTheory.RealUnipFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotSqDvdOfRationalPrimeSplitsCompletely
section
open NumberField IsDedekindDomain

namespace GlobalTheory.St.G.SplitUnram

theorem not_sq_dvd_of_splitsIn : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T →
    ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  intro E _ _ T hT hs w hw hdvd
  have := w.isPrime
  have hnd := GlobalTheory.St.G.PsiLoc.not_dvd_different hT hs w.asIdeal hw
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  have hmax : (Ideal.span {(T : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) = Ideal.span {((T : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hw
  have : w.asIdeal.LiesOver (Ideal.span {(T : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(T : ℤ)} ≠ ⊥ := by simpa using hT.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(T : ℤ)}) w.asIdeal hb] at he
  have h2 := (Ideal.ramificationIdx'_ne_one_iff hle).2
  rw [hmap] at h2
  exact h2 (Ideal.le_of_dvd hdvd) he

end GlobalTheory.St.G.SplitUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralOneDoubleCosetEqMulValue
section
open MeasureTheory GlobalTheory.Grow

namespace GlobalTheory

theorem quotientIntegral_oneDoubleCoset_eq_mul_value (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G)
    (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (ρ : Measure R) (μ : Measure G) (hρ : ρ.IsHaarMeasure) (hρr : ρ.IsMulRightInvariant) (hμ : μ.IsHaarMeasure)
    (t : G) : ∃ w : ℂ, w ≠ 0 ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) →
      (∀ g, f g ≠ 0 → ∃ r ∈ R, ∃ k ∈ K, g = r * t * k) → IsQuotIntL1 ρ μ f (w * f t) := by

  set T : Set G := {g | t⁻¹ * g ∈ K} with hT
  set S : Set R := {r | t⁻¹ * ((r : G) * t) ∈ K} with hS
  have hemb : Topology.IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal

  have hAo : ∀ h : G, IsOpen {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h =>
    hKo.preimage (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  have hAc : ∀ h : G, IsCompact {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h => by
    have h1 : IsCompact ((fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G)) := by
      have e : (fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G) = (fun g => t * g * h⁻¹) '' (K : Set G) := by
        ext g; constructor
        · intro hg; exact ⟨t⁻¹ * (g * h), hg, by group⟩
        · rintro ⟨k, hk, rfl⟩; simpa [mul_assoc] using hk
      rw [e]; exact hKc.image (by fun_prop)
    exact hemb.isCompact_preimage h1
  have hTm : MeasurableSet T := (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμT : μ T = μ K := measure_preimage_mul μ t⁻¹ K
  have hμK0 : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hμKt : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hSo : IsOpen S := by simpa using hAo t
  have hSc : IsCompact S := by simpa using hAc t
  have hρS0 : ρ S ≠ 0 := (hSo.measure_pos ρ ⟨1, by simp [hS]⟩).ne'
  have hρSt : ρ S ≠ ⊤ := hSc.measure_lt_top.ne
  set c : ℝ := ρ.real S with hc
  have hc0 : c ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hρS0, hρSt⟩
  have hμK : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hμK0, hμKt⟩
  refine ⟨(μ.real K : ℂ) / (c : ℂ), div_ne_zero (by exact_mod_cast hμK) (by exact_mod_cast hc0), fun f hfl hfr hfs => ?_⟩
  set a : ℂ := f t / (c : ℂ) with ha
  refine ⟨T.indicator fun _ => a, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hTm).2 (integrableOn_const (by rw [hμT]; exact hμKt))
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e]
    exact (integrable_indicator_iff (hAo h).measurableSet).2
      (integrableOn_const (hAc h).measure_lt_top.ne)
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e, integral_indicator_const _ (hAo h).measurableSet]
    by_cases hne : ∃ s ∈ R, ∃ k ∈ K, h = s * t * k
    · obtain ⟨s, hs, k, hk, rfl⟩ := hne
      have eA : {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = (fun r : R => r * ⟨s, hs⟩) ⁻¹' S := by
        ext r
        simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul]
        have : t⁻¹ * ((r : G) * (s * t * k)) = t⁻¹ * ((r : G) * s * t) * k := by group
        rw [this, Subgroup.mul_mem_cancel_right _ hk]
      have e1 : ρ.real {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = c := by
        rw [eA, hc, measureReal_def, measureReal_def, measure_preimage_mul_right]
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [e1, ha, mul_assoc, hfl s hs, hfr k hk, Complex.real_smul]
      field_simp
    · have hf : f h = 0 := by
        by_contra hf; exact hne (hfs h hf)
      have eA : {r : R | t⁻¹ * ((r : G) * h) ∈ K} = ∅ := by
        ext r
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hr
        exact hne ⟨(r : G)⁻¹, inv_mem r.2, t⁻¹ * ((r : G) * h), hr, by group⟩
      rw [hf, eA]; simp
  · rw [integral_indicator_const _ hTm]
    have e2 : μ.real T = μ.real K := by simp only [measureReal_def, hμT]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
    rw [e2, ha, Complex.real_smul]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedEntryTypePrimeSupportPeriodSize
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.UnfoldS

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.PadicUnfold GlobalTheory.PadicUnfold.Period GlobalTheory.ColNorms.Unfold

theorem locSmall_XiAt_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (P : rowSG Pr sel mu), LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (N.R.N i) P.1) (stdAt X.E (N.R.N (i + 1)) P.1) (XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) ((Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2)) := by
  refine ⟨2, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be P => ?_⟩
  obtain ⟨hvG, hpr, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hP : P.1 ∈ Pr.vGs := hvG _ P.2
  obtain ⟨g, -, hg, -, hg2, -⟩ := hpr _ hP
  have hom := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i (by omega) P (I.h i al P) (I.h (i + 1) be P)
  obtain ⟨hH, -, -, -, -, hsharp, hI, -⟩ := H
  have hPr : Pr.Ok := hH.2.2.2.2.2.2.2.2.2.1
  have hq : (Formalism.L2.Col.qOf P.1).Prime := hg ▸ hPr.g_prime g
  rw [← hg] at hg2
  have hs' := hI.stabG (i + 1) be P hP
  replace hom := hom (hI.stabG i al P hP) hs'
  unfold lamYat at hom hs'
  rw [if_pos hP] at hom hs'
  have hE := unfolding_smallHomFunction_levelPrime_bounded hq (c' := cOf N.R i) (c := cOf N.R (i + 1)) (by unfold cOf; omega) cst.A cst.B (cst.psi P)
    (fun a ha => by
      have := GlobalTheory.GO.ChRoot.psi_root hI.cst_ok P a (by rwa [hI.depthG P hP, pow_one])
      rwa [hI.depthG P hP, pow_one] at this) _ hom
  refine ⟨fun x hx => hE.1 x (right_ne_zero_of_mul hx), fun x z hz => ?_, fun σ x => ?_⟩
  · unfold XiAt E1at
    rw [hE.2.1 x z hz]
  · have hq1 : (1 : ℝ) ≤ Formalism.L2.Col.qOf P.1 := by exact_mod_cast hq.one_le
    unfold XiAt E1at
    rw [map_mul, norm_mul]
    have h1 := (norm_volN_inv_le (K := X.K) _ _ σ).trans (Nat.cast_le.2
      (relIndex_le hg2 N.R.k N.R.rS N.R.r N.R.t (N.R.N (i + 1)) (cOf N.R (i + 1)) _ hs'))
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP, if_pos hsharp]
    refine (mul_le_mul h1 (hE.2.2 σ x) (norm_nonneg _) (Nat.cast_nonneg _)).trans ?_
    rw [Nat.cast_pow, ← pow_add]
    refine pow_le_pow_right₀ hq1 ?_
    have a1 := rank_le N.R (j := i) (by omega)
    have a2 := rank_le N.R (j := i + 1) (by omega)
    have a3 : cOf N.R i + 1 ≤ N.R.m := by unfold cOf; omega
    unfold NumDatum.Nm
    generalize N.R.N i + cOf N.R i = a at a1 ⊢
    generalize N.R.N (i + 1) + cOf N.R (i + 1) = b at a2 ⊢
    generalize N.R.N N.R.m = M at a1 a2 ⊢
    have b1 : b * b ≤ M * M := Nat.mul_le_mul a2 a2
    have b2 : b * a ≤ M * M := Nat.mul_le_mul a2 a1
    calc b * b + cOf N.R i * (b * a) ≤ M * M + cOf N.R i * (M * M) := by gcongr
      _ = (cOf N.R i + 1) * M ^ 2 := by ring
      _ ≤ (2 * N.R.m ^ 2) * M ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)

end GlobalTheory.Core.Ht2.UnfoldS
end

