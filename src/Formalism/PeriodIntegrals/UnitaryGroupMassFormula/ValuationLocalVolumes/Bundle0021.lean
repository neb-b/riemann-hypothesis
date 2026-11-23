module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0020

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoWGen
section
noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem isoW_gen {a : ℕ} (Y : TupV (E := E) v n a) (z : Fin a) (γ : Fv F v)
    (hγ : γ ∈ v.adicCompletionIntegers F) (hγm : Valued.v γ < 1)
    (hz : ∀ i, gramR (Fv F v) σ J Y i z = if i = z then sc (E := E) v γ else 0)
    (hPD : PrimDual σ J ψ v Λ a)
    (hTS : ∃ S : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E), (∀ i j, S i j ∈ OEv (E := E) v) ∧
      bordM v (gramR (Fv F v) σ J Y) z * S = 1) :
    IsoW σ J ψ v Λ a Y := by
  classical
  intro hG
  obtain ⟨hS, hL, hSD, hUn, -, hYp⟩ := hG
  have hcm := hS.1
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  have hconj : ∀ x y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x :=
    fun x y => PI.OmLocU.Orb.hR_conj σ J v hcm hJ x y
  have hsc : ∀ r : Fv F v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (sc (E := E) v r) = sc (E := E) v r :=
    fun r => PI.OmLocU.NormOneUnitFixedPoints.sigR_sc' σ v r
  set G := gramR (Fv F v) σ J Y with hGdef

  obtain ⟨S, hSi, hTS1⟩ := hTS
  have hGi : ∀ i j, G i j ∈ OEv (E := E) v := fun i j =>
    PI.OmLocU.hR_mem_oEv σ J v Λ hSD (hYp.1 i) (hYp.1 j)
  have hBi : ∀ i j, bordM v G z i j ∈ OEv (E := E) v := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [bordM, Fin.snoc_last]; exact oEv_zero v
      | cast j =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j => simp only [bordM, Fin.snoc_castSucc]; exact hGi i j
  refine ⟨bordM v G z, ⟨S.det, det_int v _ hSi, det_int v _ hBi, ?_⟩, ?_⟩
  · rw [← Matrix.det_mul, hTS1, Matrix.det_one]
  intro X hX hXY
  obtain ⟨W, hW, hWd⟩ := hPD hS hSD hUn hL X hX
  set g := sc (E := E) v γ with hg
  have hgO : g ∈ OEv (E := E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγ
  have hXz : ∀ i, hR (Fv F v) σ J (X i) (X z) = if i = z then g else 0 := by
    intro i
    have := congrFun (congrFun hXY i) z
    simp only [gramR] at this
    rw [this]; exact hz i
  set w0 := W z with hw0
  have hw0L : w0 ∈ latLoc (E := E) v Λ := hW z
  have hXw0 : ∀ i, hR (Fv F v) σ J (X i) w0 = if i = z then 1 else 0 := fun i => (hWd i z).1
  have hw0X : ∀ i, hR (Fv F v) σ J w0 (X i) = if i = z then 1 else 0 := fun i => (hWd i z).2
  set y := X z + (-g) • w0 with hy
  have hyL : y ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ (hX.1 z) (PI.OmLocU.Orb.oSmul v Λ hL _ (oEv_neg v hgO) _ hw0L)
  have hXy : ∀ i, hR (Fv F v) σ J (X i) y = 0 := by
    intro i
    rw [hy, hAddR, hSmulR, hXz, hXw0]
    split_ifs <;> ring
  have hyX : ∀ i, hR (Fv F v) σ J y (X i) = 0 := by
    intro i; rw [← hconj, hXy, map_zero]
  set b := hR (Fv F v) σ J w0 w0 with hb
  have hbO : b ∈ OEv (E := E) v := PI.OmLocU.hR_mem_oEv σ J v Λ hSD hw0L hw0L
  obtain ⟨β, hβ, hbβ⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hbO (hconj w0 w0)
  have h1 : hR (Fv F v) σ J w0 y = 1 + (-g) * b := by
    rw [hy, hAddR, hSmulR, hw0X, if_pos rfl]
  have h2 : hR (Fv F v) σ J y w0 = 1 + (-g) * b := by
    rw [← hconj, h1, map_add (f := _), map_one, map_mul, map_neg, hg, hsc, hconj]
  have h3 : hR (Fv F v) σ J y y = (-g) * (1 + (-g) * b) := by
    rw [hy, hAddR, hSmulR, ← hy, hyX, h2, zero_add]

  obtain ⟨θ, hθO, hθ⟩ := PI.OmLocU.Red.trOnto_holds σ J ψ v hS hUn 1 (oEv_one v) (map_one _)
  have hinv : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x) = x := PI.OmLocU.Orb.sigR_invol σ v hcm
  have hNO : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ * θ ∈ OEv (E := E) v := by
    refine oEv_mul v ?_ hθO
    have := hθ ▸ (oEv_one (E := E) v)
    have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ = (θ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) - θ := by ring
    rw [e]
    exact oEv_add v this (oEv_neg v hθO)
  have hNf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ * θ) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ * θ := by
    rw [map_mul, hinv, mul_comm]
  obtain ⟨ν, hν, hNν⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hNO hNf
  obtain ⟨s, hsO, hs⟩ := exists_integral_root_of_quadratic v β γ ν hβ hγ hγm hν
  set t := sc (E := E) v s * θ with ht
  have htO : t ∈ OEv (E := E) v := oEv_mul v (PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hsO) hθO
  have hσt : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ t = sc (E := E) v s * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ := by
    rw [ht, map_mul, hsc]
  set w := w0 + t • y with hw
  have hwL : w ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ hw0L (PI.OmLocU.Orb.oSmul v Λ hL _ htO _ hyL)
  have hXw : ∀ i, hR (Fv F v) σ J (X i) w = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddR, hSmulR, hXy, hXw0, mul_zero, add_zero]
  have hwX : ∀ i, hR (Fv F v) σ J w (X i) = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddL, hSmulL, hyX, hw0X, mul_zero, add_zero]
  have E0 : hR (Fv F v) σ J w w = b + t * hR (Fv F v) σ J w0 y +
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ t * hR (Fv F v) σ J y w0 + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ t * (t * hR (Fv F v) σ J y y)) := by
    rw [hw, hAddL, hAddR, hAddR, hSmulR, hSmulL, hSmulL, hSmulR]
  have key : sc (E := E) v (β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2) = 0 := by
    rw [hs]; simp [sc]
  have keyE : sc (E := E) v β + (1 - g * sc (E := E) v β) * sc (E := E) v s -
      g * (1 - g * sc (E := E) v β) * sc (E := E) v ν * sc (E := E) v s ^ 2 = 0 := by
    rw [← key, hg]
    simp only [PI.OmLocU.NormOneUnitFixedPoints.sc_eq, map_add (f := _), map_sub, map_mul, map_one, map_pow]
  have hww : hR (Fv F v) σ J w w = 0 := by
    rw [E0, h1, h2, h3, hσt, hbβ, ht]
    linear_combination keyE + ((1 - g * sc (E := E) v β) * sc (E := E) v s) * hθ -
      (g * (1 - g * sc (E := E) v β) * sc (E := E) v s ^ 2) * hNν
  refine ⟨w, hwL, ?_⟩
  rw [gram_augT σ J v X w z hXw hwX hww, hXY]

end PI.OmVf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResGen
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem leftInvRes_gen {a : ℕ} {K : Type} [CommRing K] (ϖ : Fv F v) (hϖ : IsUnif v ϖ)
    (π : Red.OR (E := E) v →+* K) (hsurj : Function.Surjective π)
    (hker : ∀ x : Red.OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ)
    (hLK : ∀ Mb : Matrix (Fin n) (Fin a) K, Function.Injective Mb.mulVec →
      ∃ Nb : Matrix (Fin a) (Fin n) K, Nb * Mb = 1)
    (M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E)) (hM : ∀ k i, M k i ∈ OEv (E := E) v)
    (hsat : ∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) :
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B := by
  classical
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  set Mo : Matrix (Fin n) (Fin a) (Red.OR (E := E) v) := fun k i => ⟨M k i, hM k i⟩ with hMo
  have hcoe : (Red.OR (E := E) v).subtype = (Red.OR (E := E) v).subtype := rfl

  have hinj : Function.Injective (Mo.map π).mulVec := by
    intro x y hxy
    have hz : (Mo.map π).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    obtain ⟨cO, hcO⟩ : ∃ cO : Fin a → Red.OR (E := E) v, ∀ i, π (cO i) = (x - y) i :=
      ⟨fun i => (hsurj ((x - y) i)).choose, fun i => (hsurj ((x - y) i)).choose_spec⟩
    have hred : ∀ k, π ((Mo.mulVec cO) k) = 0 := by
      intro k
      rw [RingHom.map_mulVec]
      have : (π ∘ cO) = x - y := funext hcO
      rw [this, hz]
      rfl
    have hPO : ∀ k, ∃ m ∈ OEv (E := E) v, ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
        sc (E := E) v ϖ * m := fun k => (hker _).1 (hred k)
    choose m hmO hm using hPO
    have hc : ∀ i, sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
      refine hsat _ fun k => ?_
      have e : Matrix.mulVec M (fun i => sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E)) k =
          sc (E := E) v ϖ⁻¹ * ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        rw [show ((∑ i, Mo k i * cO i : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
            ∑ i, ((Mo k i : Fv F v ⊗[F] E) * (cO i : Fv F v ⊗[F] E)) by push_cast; rfl]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hm k, ← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hmO k
    funext i
    have : π (cO i) = 0 := by
      rw [hker]
      refine ⟨sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E), hc i, ?_⟩
      rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
    rw [← sub_eq_zero, ← Pi.sub_apply, ← hcO i, this]
  obtain ⟨Nb, hNb⟩ := hLK _ hinj
  obtain ⟨NO, hNO⟩ : ∃ NO : Matrix (Fin a) (Fin n) (Red.OR (E := E) v), ∀ i k, π (NO i k) = Nb i k :=
    ⟨fun i k => (hsurj (Nb i k)).choose, fun i k => (hsurj (Nb i k)).choose_spec⟩
  have hmap : (NO * Mo).map π = 1 := by
    rw [Matrix.map_mul]
    have : NO.map π = Nb := by ext i k; exact hNO i k
    rw [this, hNb]
  set P : Matrix (Fin a) (Fin a) (Red.OR (E := E) v) := NO * Mo with hP
  have hPO : ∀ i j, ∃ b ∈ OEv (E := E) v, (((P - 1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j :
      Red.OR (E := E) v) : Fv F v ⊗[F] E) = sc (E := E) v ϖ * b := by
    intro i j
    refine (hker _).1 ?_
    have := congrFun (congrFun hmap i) j
    simp only [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    simp [Matrix.one_apply]
  choose B hBO hB using hPO
  refine ⟨NO.map (Red.OR (E := E) v).subtype, fun i j => B i j, fun i k => (NO i k).2, hBO, ?_⟩
  have hM' : M = Mo.map (Red.OR (E := E) v).subtype := by ext k i; rfl
  rw [hM', ← Matrix.map_mul, ← hP]
  ext i j
  have h1 := hB i j
  rw [Matrix.sub_apply] at h1
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : (Red.OR (E := E) v).subtype (P i j) =
      (((P i j - (1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E) +
        (((1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E)) := by
    show (P i j : Fv F v ⊗[F] E) = _
    push_cast; ring
  rw [e1, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [add_comm] <;> rfl

end PI.OmVd
end
end

