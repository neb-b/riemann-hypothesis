module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Int

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

private theorem int_qa {p q : K} (hp : p ∈ (algebraMap O K).range) (hq : q ∈ (algebraMap O K).range)
    {x : QuadraticAlgebra K p q} (h1 : x.re ∈ (algebraMap O K).range) (h2 : x.im ∈ (algebraMap O K).range) :
    IsIntegral O x := by
  obtain ⟨p0, rfl⟩ := hp
  obtain ⟨q0, rfl⟩ := hq
  obtain ⟨r0, hr⟩ := h1
  obtain ⟨i0, hi⟩ := h2
  have hw : IsIntegral O (QuadraticAlgebra.omega : QuadraticAlgebra K (algebraMap O K p0) (algebraMap O K q0)) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C q0 * Polynomial.X - Polynomial.C p0, ?_, ?_⟩
    · monicity!
    · rw [← Polynomial.aeval_def]
      simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap,
        IsScalarTower.algebraMap_apply O K (QuadraticAlgebra K _ _) p0,
        IsScalarTower.algebraMap_apply O K (QuadraticAlgebra K _ _) q0]
      ring
  have hx : x = algebraMap O _ r0 + algebraMap O _ i0 * QuadraticAlgebra.omega := by
    ext <;> simp [IsScalarTower.algebraMap_apply O K (QuadraticAlgebra K _ _), hr, hi]
  rw [hx]
  exact (isIntegral_algebraMap).add ((isIntegral_algebraMap).mul hw)

end Int

section Closure

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

private theorem gl_int (M : GL (Fin 2) A) (h1 : ∀ i j, IsIntegral R ((M : Matrix (Fin 2) (Fin 2) A) i j))
    (h2 : ∀ i j, IsIntegral R (((M⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j)) :
    M ∈ (GeneralLinearGroup.map ((integralClosure R A).val : integralClosure R A →+* A)).range := by
  let f : integralClosure R A →+* A := (integralClosure R A).val
  have hf : Function.Injective f := Subtype.val_injective
  let N : Matrix (Fin 2) (Fin 2) (integralClosure R A) := fun i j => ⟨_, h1 i j⟩
  let N' : Matrix (Fin 2) (Fin 2) (integralClosure R A) := fun i j => ⟨_, h2 i j⟩
  have eN : N.map f = (M : Matrix (Fin 2) (Fin 2) A) := by
    ext i j
    rfl
  have eN' : N'.map f = ((M⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := by
    ext i j
    rfl
  have e1 : N * N' = 1 := by
    apply Matrix.map_injective hf
    show (N * N').map f = (1 : Matrix (Fin 2) (Fin 2) _).map f
    rw [Matrix.map_mul, eN, eN', Matrix.map_one f (map_zero f) (map_one f)]
    exact M.mul_inv
  have e2 : N' * N = 1 := by
    apply Matrix.map_injective hf
    show (N' * N).map f = (1 : Matrix (Fin 2) (Fin 2) _).map f
    rw [Matrix.map_mul, eN, eN', Matrix.map_one f (map_zero f) (map_one f)]
    exact M.inv_mul
  refine ⟨⟨N, N', e1, e2⟩, ?_⟩
  ext i j
  rfl

private theorem unit_int (z : Aˣ) (h1 : IsIntegral R (z : A)) (h2 : IsIntegral R ((z⁻¹ : Aˣ) : A)) :
    z ∈ (Units.map ((integralClosure R A).val : integralClosure R A →* A)).range :=
  ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, Units.ext rfl⟩

end Closure

section Maps

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K)

private theorem lmap_star (x : Lsq K Δ) : lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

private def mapU : U3 Δ →* U3 (f Δ) where
  toFun g := ⟨(lmap f Δ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)), by
    have e : star ((lmap f Δ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) =
        (lmap f Δ).mapMatrix (star (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) := by
      ext i j : 1
      simp [Matrix.star_apply, lmap_star]
    constructor
    · rw [e, ← map_mul, g.2.1, map_one]
    · rw [e, ← map_mul, g.2.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private theorem map_wJ : GeneralLinearGroup.map (lmap f Δ) (wJ Δ) = wJ (f Δ) := by
  apply Units.ext
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [wJ]

private def mapD : DX Δ →* DX (f Δ) :=
  ((GeneralLinearGroup.map (lmap f Δ)).comp (DX Δ).subtype).codRestrict (DX (f Δ)) fun g => by
    have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (MulAut.conj (wJ Δ)⁻¹).toMonoidHom g.1 := g.2
    have c : GeneralLinearGroup.map (starRingEnd (Lsq K' (f Δ))) (GeneralLinearGroup.map (lmap f Δ) g.1) =
        GeneralLinearGroup.map (lmap f Δ) (GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1) := by
      apply Units.ext
      ext i j : 1
      simp [starRingEnd_apply, lmap_star]
    change GeneralLinearGroup.map (starRingEnd (Lsq K' (f Δ))) (GeneralLinearGroup.map (lmap f Δ) g.1) =
      (MulAut.conj (wJ (f Δ))⁻¹).toMonoidHom (GeneralLinearGroup.map (lmap f Δ) g.1)
    rw [c, h]
    simp [MulAut.conj_apply, map_wJ]

end Maps

section Places

variable {F : Type} [Field F] [NumberField F]

private theorem ae_int (x : F) : ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ (algebraMap (Ov v) (Kv v)).range := by
  have h := (FiniteAdeleRing.algebraMap (𝓞 F) F x).2
  filter_upwards [h] with v hv
  exact ⟨⟨_, hv⟩, rfl⟩

private theorem ae_lsq (Δ : F) (x : Lsq F Δ) : ∀ᶠ v : Pl F in Filter.cofinite, IsIntegral (Ov v) (lmap (cv v) Δ x) := by
  filter_upwards [ae_int Δ, ae_int x.re, ae_int x.im] with v h0 h1 h2
  exact int_qa (x := lmap (cv v) Δ x) h0 (algebraMap (Ov v) (Kv v)).range.zero_mem h1 h2

private theorem ae_et (τ : F) (x : Etau F τ) : ∀ᶠ v : Pl F in Filter.cofinite, IsIntegral (Ov v) (emap (cv v) τ x) := by
  filter_upwards [ae_int τ, ae_int x.re, ae_int x.im] with v h0 h1 h2
  have hm : cv v (-1 : F) ∈ (algebraMap (Ov v) (Kv v)).range := by
    rw [map_neg, map_one]
    exact (algebraMap (Ov v) (Kv v)).range.neg_mem (algebraMap (Ov v) (Kv v)).range.one_mem
  have e : cv v (-1 : F) = -1 := by simp
  exact int_qa (x := emap (cv v) τ x) (e ▸ hm) h0 h1 h2

private theorem ae_U (Δ : F) (g : U3 Δ) : ∀ᶠ v : Pl F in Filter.cofinite, mapU (cv v) Δ g ∈ KU (Ov v) (cv v Δ) := by
  have hall : ∀ᶠ v : Pl F in Filter.cofinite, ∀ i j : Fin 3,
      IsIntegral (Ov v) (lmap (cv v) Δ ((g : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j)) ∧
      IsIntegral (Ov v) (lmap (cv v) Δ (star ((g : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j))) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      (ae_lsq Δ _).and (ae_lsq Δ _)
  filter_upwards [hall] with v hv
  intro i j
  refine ⟨(hv i j).1, ?_⟩
  change IsIntegral (Ov v) (star (lmap (cv v) Δ ((g : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j)))
  rw [← lmap_star]
  exact (hv i j).2

private theorem ae_D (Δ : F) (g : DX Δ) : ∀ᶠ v : Pl F in Filter.cofinite, mapD (cv v) Δ g ∈ KD (cv v Δ) (Ov v) := by
  have hall : ∀ᶠ v : Pl F in Filter.cofinite, ∀ i j : Fin 2,
      IsIntegral (Ov v) (lmap (cv v) Δ (((g.1 : GL (Fin 2) (Lsq F Δ)) : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) i j)) ∧
      IsIntegral (Ov v) (lmap (cv v) Δ ((((g.1)⁻¹ : GL (Fin 2) (Lsq F Δ)) : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) i j)) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      (ae_lsq Δ _).and (ae_lsq Δ _)
  filter_upwards [hall] with v hv
  rw [KD, Subgroup.mem_subgroupOf]
  have e1 : ((mapD (cv v) Δ g : DX (cv v Δ)) : GL (Fin 2) (Lsq (Kv v) (cv v Δ))) =
      GeneralLinearGroup.map (lmap (cv v) Δ) g.1 := rfl
  rw [e1]
  apply gl_int
  · intro i j
    exact (hv i j).1
  · intro i j
    rw [← map_inv]
    exact (hv i j).2

private theorem ae_E (τ : F) (z : (Etau F τ)ˣ) : ∀ᶠ v : Pl F in Filter.cofinite,
    Units.map (emap (cv v) τ : Etau F τ →* Etau (Kv v) (cv v τ)) z ∈ Cu (Ov v) (cv v τ) := by
  filter_upwards [ae_et τ (z : Etau F τ), ae_et τ ((z⁻¹ : (Etau F τ)ˣ) : Etau F τ)] with v h1 h2
  exact unit_int _ h1 h2

end Places

private def toRP {I H : Type} [Group H] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (p : ∀ v, H →* Gv v)
    (h : ∀ g, ∀ᶠ v in Filter.cofinite, p v g ∈ K v) : H →* RP Gv K :=
  (Pi.monoidHom p).codRestrict (RP Gv K) h

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.iotaEx :
    UpperTheory.V.Z.Sym.Glob.IotaEx := by
  intro F _ _ Δ
  exact ⟨⟨toRP (fun v => mapU (cv v) Δ) (ae_U Δ), fun _ _ => rfl⟩, ⟨toRP (fun v => mapD (cv v) Δ) (ae_D Δ), fun _ _ => rfl⟩,
    fun τ => ⟨toRP (fun v => Units.map (emap (cv v) τ : Etau F τ →* Etau (Kv v) (cv v τ))) (ae_E τ), fun _ _ => rfl⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.PosLaw
section
namespace UpperTheory.V.Z.Sym.Glob

open Loc

section

variable {F : Type} [Field F] {Δ τ : F}

private theorem re_mul_star (x : Lsq F Δ) : (x * star x).re = x.re ^ 2 - Δ * x.im ^ 2 := by
  simp
  ring

private theorem nrm_nonneg (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) : 0 ≤ σ (x * star x).re := by
  rw [re_mul_star]
  simp only [map_sub, map_mul, map_pow]
  nlinarith [sq_nonneg (σ x.re), sq_nonneg (σ x.im)]

private theorem nrm_pos (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) (hx : x ≠ 0) : 0 < σ (x * star x).re := by
  rw [re_mul_star, map_sub, map_mul, map_pow, map_pow]
  have hne : x.re ≠ 0 ∨ x.im ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (QuadraticAlgebra.ext (by simp [hc.1]) (by simp [hc.2]))
  have ha := mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ x.im))
  have hb := sq_nonneg (σ x.re)
  rcases hne with h1 | h1
  · have h2 : σ x.re ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.re ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    nlinarith
  · have h2 : σ x.im ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    have h4 := mul_pos (neg_pos.mpr h) h3
    nlinarith

private theorem herm_re (c t : F) (m : EL Δ τ) (x : Sp Δ τ) :
    (herm c (t • m) x x).re = c * (x.1 * star x.1).re + t * (herm 1 m (0, x.2) (0, x.2)).re := by
  simp [herm]
  ring

private theorem sum_pos (σ : F →+* ℝ) (h : σ Δ < 0) (y : Fin 3 → Lsq F Δ) (hy : y ≠ 0) :
    0 < σ (∑ i, y i * star (y i)).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have h0 := nrm_nonneg σ h (y 0)
  have h1 := nrm_nonneg σ h (y 1)
  have h2 := nrm_nonneg σ h (y 2)
  have hp := nrm_pos σ h (y i) hi
  rw [Fin.sum_univ_three, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add, map_add (f := _), map_add (f := _)]
  fin_cases i
  · exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hp h1) h2
  · exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h0 hp) h2
  · exact add_pos_of_nonneg_of_pos (add_nonneg h0 h1) hp

end

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.posLaw :
    UpperTheory.V.Z.Sym.Glob.PosLaw := by
  intro F _ _ Δ D hD τ d m hm c t
  have hneg := hD.neg
  refine ⟨fun hc ht x hx σ => ?_, fun δ ι P hM => ?_⟩
  · rw [herm_re, map_add (f := _), map_mul, map_mul]
    have h1 := nrm_nonneg σ (hneg σ) x.1
    by_cases h2 : x.2 = 0
    · have hx1 : x.1 ≠ 0 := by
        intro h1'
        exact hx (Prod.ext h1' h2)
      have h4 := nrm_pos σ (hneg σ) x.1 hx1
      have h3 : (herm 1 m (0, x.2) (0, x.2)).re = 0 := by
        rw [h2]
        simp [herm]
      rw [h3, map_zero, mul_zero, add_zero]
      exact mul_pos (hc σ) h4
    · have hx2 : ((0 : Lsq F Δ), x.2) ≠ 0 := by
        intro h'
        exact h2 (congrArg Prod.snd h')
      have h4 := hm _ hx2 σ
      nlinarith [hc σ, ht σ, mul_nonneg (hc σ).le h1, mul_pos (ht σ) h4]
  · have key : ∀ x : Sp Δ τ, x ≠ 0 → TPos (herm c (t • m) x x).re := by
      intro x hx σ
      rw [hM.form x x]
      apply sum_pos σ (hneg σ)
      intro h0
      exact hx (P.injective (h0.trans (map_zero P).symm))
    refine ⟨fun σ => ?_, fun σ => ?_⟩
    · have h1 := key ((1 : Lsq F Δ), 0) (by simp) σ
      simpa [herm] using h1
    · have hx : ((0 : Lsq F Δ), (1 : EL Δ τ)) ≠ 0 := by simp
      have h1 := key _ hx σ
      have h2 : 0 < σ (herm 1 m (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2) (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2)).re := hm _ hx σ
      have hz : ((0 : Lsq F Δ) * star (0 : Lsq F Δ)).re = 0 := by simp
      rw [herm_re, map_add (f := _), map_mul, map_mul] at h1
      simp only [hz, map_zero, mul_zero, zero_add] at h1
      nlinarith
end

