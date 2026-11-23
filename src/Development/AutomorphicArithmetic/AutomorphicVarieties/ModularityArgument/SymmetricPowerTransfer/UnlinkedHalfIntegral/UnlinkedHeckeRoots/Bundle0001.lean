module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.ConjEig
section
open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

theorem conjEig : ConjEig := by
  intro k N χ g hg σ
  obtain ⟨f', h1, h2⟩ := hg σ
  refine ⟨⟨f', h1, ?_, ?_⟩, fun n hn => h2 n hn⟩
  · rw [h2 1 le_rfl, g.one, map_one]
  · intro p hp n hn
    have e := congrArg σ (g.eig p hp n hn)
    have hc : (cj σ χ) (p : ZMod N) = σ (χ p) := rfl
    show coef f' (p * n) + (cj σ χ) p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef f' (n / p) else 0) = coef f' p * coef f' n
    rw [h2 _ (Nat.mul_pos hp.pos hn), h2 _ hp.pos, h2 _ hn, hc]
    by_cases hd : p ∣ n
    · have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
      simp only [hd, if_true] at e ⊢
      rw [h2 _ hm]
      simpa [map_add (f := _), map_mul, map_pow, map_natCast] using e
    · simp only [hd, if_false] at e ⊢
      simpa [map_add (f := _), map_mul, map_pow, map_natCast] using e

end UpperTheory.V.Z.Sym.Unl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfAlg
section
open scoped ComplexConjugate

namespace UpperTheory.V.Z.Sym.Unl

private theorem sq_of_conj {a x : ℂ} (h : conj a * x = a) :
    a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) * x := by
  have h1 : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; rfl
  calc a * a = a * (conj a * x) := by rw [h]
    _ = (a * conj a) * x := by ring
    _ = _ := by rw [h1]

private theorem ratio_eq {p s t : ℝ} (hp : 2 ≤ p) (hs0 : 0 < s) (hs : s * s = p) {z : ℂ}
    (hz : z * conj z = (p : ℂ)) (ht : 0 ≤ t) (hzt : z + 2 + z⁻¹ = (t : ℂ)) : z = (s : ℂ) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : Complex.normSq z = p := by
    have e := Complex.mul_conj z
    rw [hz] at e
    exact_mod_cast e.symm
  have hre := congrArg Complex.re hzt
  have him := congrArg Complex.im hzt
  simp [Complex.inv_re, Complex.inv_im, hn] at hre him
  have hn2 : z.re * z.re + z.im * z.im = p := by rw [← hn, Complex.normSq_apply]
  have hv : z.im = 0 := by
    have e : z.im * (p - 1) = 0 := by
      have e2 : z.im * (p - 1) = p * (z.im + -z.im / p) := by
        field_simp
        ring
      rw [e2, him, mul_zero]
    rcases mul_eq_zero.mp e with h | h
    · exact h
    · exfalso
      linarith
  have hre' : (z.re + 2) * p + z.re = t * p := by
    rw [← hre]
    field_simp
  have hu : (z.re - s) * (z.re + s) = 0 := by
    rw [hv] at hn2
    linear_combination hn2 - hs
  have hr : z.re = s := by
    rcases mul_eq_zero.mp hu with h | h
    · linarith
    · exfalso
      have hm : z.re = -s := by linarith
      rw [hm, ← hs] at hre'
      have hs1 : 1 < s := by nlinarith
      nlinarith [mul_nonneg ht (mul_nonneg hs0.le hs0.le), mul_pos hs0 (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1))]
  apply Complex.ext
  · simp [hr]
  · simp [hv]

private theorem abs_ratio_ne_of_sqrt_flip (p m : ℕ) (a x α β : ℂ) (σ : ℂ ≃+* ℂ) (hp : 2 ≤ p) (hx : ‖x‖ = 1)
    (hσx : ‖σ x‖ = 1) (hσ : σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ))
    (ha : conj a * x = a) (hσa : conj (σ a) * σ x = σ a) (hsum : α + β = a)
    (hprod : α * β = x * (p : ℂ) ^ m) : ‖α‖ ^ 2 ≠ (p : ℝ) * ‖β‖ ^ 2 := by
  intro hab
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  have hσx0 : σ x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hσx
    exact zero_ne_one hσx
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hprod0 : α * β ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hx0 (pow_ne_zero _ hpC)
  have hβ : β ≠ 0 := right_ne_zero_of_mul hprod0
  have hα : α ≠ 0 := left_ne_zero_of_mul hprod0
  set s := Real.sqrt p with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hp0
  have hss : s * s = p := Real.mul_self_sqrt hp0.le
  have hn : Complex.normSq α = p * Complex.normSq β := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    exact hab
  have hnβ : (Complex.normSq β : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hβ).ne'
  have hz : (α / β) * conj (α / β) = ((p : ℝ) : ℂ) := by
    rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj, hn]
    push_cast
    field_simp
  have key : α / β + 2 + (α / β)⁻¹ = (a * a) / (α * β) := by
    rw [← hsum, inv_div]
    field_simp
    ring
  have hzt : α / β + 2 + (α / β)⁻¹ = ((‖a‖ ^ 2 / (p : ℝ) ^ m : ℝ) : ℂ) := by
    rw [key, sq_of_conj ha, hprod]
    push_cast
    field_simp
  have ht : (0 : ℝ) ≤ ‖a‖ ^ 2 / (p : ℝ) ^ m := by positivity
  have hz' := ratio_eq hpR hs0 hss hz ht hzt
  have hαs : α = (s : ℂ) * β := (div_eq_iff hβ).mp hz'
  have k2 : (s : ℂ) * (a * a) = (1 + (s : ℂ)) ^ 2 * (x * (p : ℂ) ^ m) := by
    rw [← hprod, ← hsum, hαs]
    ring
  have k3 := congrArg σ k2
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, map_one, hσ] at k3
  rw [sq_of_conj hσa] at k3
  push_cast at k3
  have k4 : (-(s * ‖σ a‖ ^ 2 : ℝ) : ℂ) * σ x = ((1 - s) ^ 2 * (p : ℝ) ^ m : ℝ) * σ x := by
    push_cast
    linear_combination k3
  have k5 := mul_right_cancel₀ hσx0 k4
  have k6 : -(s * ‖σ a‖ ^ 2) = (1 - s) ^ 2 * (p : ℝ) ^ m := by exact_mod_cast k5
  have hs1 : 1 < s := by nlinarith
  have hpm : 0 < (p : ℝ) ^ m := pow_pos hp0 m
  nlinarith [mul_nonneg hs0.le (sq_nonneg ‖σ a‖), mul_pos (pow_pos (sub_pos.mpr hs1) 2) hpm]

end UpperTheory.V.Z.Sym.Unl

theorem UpperTheory.V.Z.Sym.Unl.halfAlg :
    UpperTheory.V.Z.Sym.Unl.HalfAlg := by
  intro p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
  exact UpperTheory.V.Z.Sym.Unl.abs_ratio_ne_of_sqrt_flip p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.MapLk
section
open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

private lemma map_Lk (σ : ℂ ≃+* ℂ) (k : ℕ) (x : ℂ) : σ (Lk k x) = Lk k (σ x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm

private lemma exists_unit (N : ℕ) [NeZero N] (σ : ℂ ≃+* ℂ) :
    ∃ s : (ZMod N)ˣ, ∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpow : ∀ (m : ℕ) (c : ZMod N), (ZMod.stdAddChar ((m : ZMod N) * c) : ℂ) = (ZMod.stdAddChar c : ℂ) ^ m := by
    intro m c
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hone : (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ N = 1 := by
    rw [← hpow, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  have hz : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod N) : ℂ) N := by
    refine IsPrimitiveRoot.mk_of_lt _ hN hone fun l hl hlN h => ?_
    have h1 : (ZMod.stdAddChar ((l : ZMod N) * 1) : ℂ) = ZMod.stdAddChar (0 : ZMod N) := by
      rw [hpow, h, AddChar.map_zero_eq_one]
    have h2 := ZMod.injective_stdAddChar h1
    rw [mul_one, ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd hl h2) (by omega)
  have hz' := hz.map_of_injective (f := σ) σ.injective
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have hc : i.Coprime N := by
    rw [← hz.pow_iff_coprime hN, hi]
    exact hz'
  refine ⟨ZMod.unitOfCoprime i hc, fun b => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ZMod N) = b := ⟨b.val, ZMod.natCast_zmod_val b⟩
  have e1 : (ZMod.stdAddChar (m : ZMod N) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ m := by
    rw [← hpow, mul_one]
  have e2 : (ZMod.stdAddChar ((i : ZMod N) * (m : ZMod N)) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ (i * m) := by
    rw [← Nat.cast_mul, ← hpow, mul_one]
  rw [ZMod.coe_unitOfCoprime, e1, e2, map_pow, ← hi, pow_mul]

end UpperTheory.V.Z.Sym.Unl

open UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Sym.Unl.eisCj : UpperTheory.V.Z.Sym.Unl.EisCj := by
  intro N _ hN σ
  obtain ⟨s, hs⟩ := UpperTheory.V.Z.Sym.Unl.exists_unit N σ
  refine ⟨s, hs, fun k hk a n => ?_⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  have ha : ((a : (ZMod N)ˣ) : ZMod N) ≠ 0 := a.ne_zero
  have hsa : (((s * a : (ZMod N)ˣ)) : ZMod N) ≠ 0 := (s * a).ne_zero
  have hu : (((s * a : (ZMod N)ˣ)) : ZMod N) = (s : ZMod N) * a := Units.val_mul s a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(eisCoef N k hk _ hsa).1, (eisCoef N k hk _ ha).1, UpperTheory.V.Z.Sym.Unl.map_Lk, hs, hu]
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [(eisCoef N k hk _ hsa).2 n hn, (eisCoef N k hk _ ha).2 n hn, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul σ, map_pow σ, map_natCast σ, map_add σ, map_mul σ, map_pow σ, map_neg σ, map_one σ, hs, hs, hu]
    simp only [mul_assoc, mul_neg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.NeZeroRep
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

section Rep

private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := by
  have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
    rcases f.injective_or_eq_zero with hi | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · simp)
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
    by_contra hn
    push Not at hn
    refine hx ((Submodule.mem_bot R).1 ?_)
    rw [← IsSemisimpleModule.jacobson_eq_bot R M]
    exact Submodule.mem_sInf.2 hn
  obtain ⟨W, hc⟩ := exists_isCompl m
  haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
  obtain ⟨e⟩ := hiso W
  refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
  simpa using h0

variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add (f := _)]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩

private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])

private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ

end Rep

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}

private theorem root_lpTw (x : WD h) (s : ℝ) (g : Weil h) {z : ℂ} (hz : (x.charPol g).IsRoot z) :
    ((x.lpTw s).charPol g).IsRoot ((((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g * z) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk, WD.charPol_mk]
  rw [WD.charPol_mk] at hz
  have h1 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.2 hz
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1
    (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩)
  rw [Module.End.mem_eigenspace_iff, WDRep.tw_ρ, LinearMap.smul_apply, hv.apply_eq_smul, smul_smul]

end Gal

end UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Unl.tieU :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Z.Sym.Unl.TieU := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl n lam hn hl0 hU A h t ht
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨v, hv, hf, hUv⟩ := hU
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩ := jacqOfU P F w σ n (Units.mk0 lam hl0) hn
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hUv, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  let g : Weil h := (⟨t, mem_Weil_of_isFrob h ht⟩ : Weil h)⁻¹
  have hdeg : deg g = -1 := by
    rw [deg_inv, deg_eq_one_iff.2 ht]
  have hcont : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp H.cont
  have e1 := charPol_wdOf (h := h) hl ι hcont g
  rw [(hG.away w hl A h rc hrc σ hσ).pol, rec_algNorm hrc] at e1
  obtain ⟨b, hb, ε, -, hLw⟩ := id hrc
  have h1 := UpperTheory.V.AlgebraTools.jqRec F Ω A w h b hb ε rc hLw 2 ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g
  have hz : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g).IsRoot ((ψ 0 (b g) : ℂˣ) : ℂ) := by
    refine (?_ : (rc (cls ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩)).charPol g |>.IsRoot _)
    rw [h1, Fin.prod_univ_two]
    simp
  have h2 := root_lpTw _ ((1 - ((2 : ℕ) : ℝ)) / 2) g hz
  rw [e1] at h2
  have key : (((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ) = lam := by
    have hy : ord (w.adicCompletion F) (b g) = 1 := by rw [hb.ord_eq, hdeg, neg_neg]
    have hv0 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    have hv1 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      rw [SphCompletion.ord_completion] at hy
      rw [← WithZero.exp_log hv0]
      congr 1
      omega
    have hu : IsUnitAt w (b g * (atFin w (unif w))⁻¹) := by
      have h2 := unif_spec w
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, h2]
      exact mul_inv_cancel₀ (by simp)
    have hμy : μ₁ (b g) = μ₁ (atFin w (unif w)) := by
      exact mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact hμ _ hu)
    have hA := GlobalTheory.SatChar.absPow_art hb (1 / 2 : ℝ) g
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (zero_lt_one.trans this).ne'
    have hQ2 : ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((normV w : ℕ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hq]
      norm_num
    have hs' : ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      norm_num
    have hc : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hdeg] at hA
    rw [hψ0, Units.val_mul, Units.val_inv_eq_inv_val, hc, hA, hμy, hs', hdeg, Complex.cpow_neg]
    have hl' := hlam
    rw [Units.val_mk0] at hl'
    generalize ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = Q at hQ2 ⊢
    rw [← hl', ← hQ2]
    simp only [zpow_neg, zpow_one, inv_inv]
    ring
  rw [key] at h2
  refine ⟨ι.symm lam, ?_, by simp⟩
  have h3 : ι.toRingHom (ι.symm lam) = lam := ι.apply_symm_apply lam
  rw [← h3] at h2
  exact (Polynomial.isRoot_map_iff ι.injective).1 h2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.TieS
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Unl.tieS :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Z.Sym.Unl.TieS := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl B hB
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  have hS := ((satLoc P F 2 w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  intro A h
  exact satFrob P F Ω l ι 2 r H.cont w hl σ B hS (fun A h rc hrc => UpperTheory.GalN.V.isWDOf_satR hG hl hrc hσ hS) A h
end

