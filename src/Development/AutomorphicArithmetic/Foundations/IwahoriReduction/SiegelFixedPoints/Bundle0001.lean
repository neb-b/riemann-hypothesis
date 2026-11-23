module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
public import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Actcls
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private noncomputable def evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Fn l) :=
  Submodule.pi Set.univ fun _ => LinearMap.ker (AdicCompletion.eval (idl l) (X.Kl l) n)

private theorem mem_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l) :
    b ∈ evF X l n ↔ ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
  simp only [evF, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_ker]

private theorem eval_eq_zero_of_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {y : X.Khat l}
    (h : y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) : AdicCompletion.eval (idl l) (X.Kl l) n y = 0 := by
  refine Submodule.smul_induction_on h (fun r hr z _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n z)
    rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add (f := _), hx, hy, add_zero]

private theorem lnFn_le_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : lnFn X l n ≤ evF X l n := by
  intro b hb
  rw [mem_evF]
  intro u
  exact eval_eq_zero_of_mem X l n ((Submodule.mem_pi.mp hb) u (Set.mem_univ u))

private theorem eval_kmap_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) {y : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n y = 0) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) = 0 := by
  rw [AdicCompletion.eval_apply] at h ⊢
  simp only [Tower.kmap, LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply, h, map_zero]

private theorem act_mem_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    (hb : b ∈ evF X l n) : X.act l m b ∈ evF X l n := by
  rw [mem_evF] at hb ⊢
  intro u
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  exact eval_kmap_zero X l n _ (hb _)

private noncomputable def sf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n w : ℕ) (a : X.K) : X.Fn l :=
  fun u => (u 0) ^ w • clsK X l n a

private theorem eval_clsK_eq (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n a) =
      AdicCompletion.eval (idl l) (X.Kl l) n (GlobalTheory.ZetaB.clsHat X l a) := by
  by_cases ha : a = 0
  · subst ha
    rw [clsK_zero, map_zero, GlobalTheory.ZetaB.eval_clsHat, GlobalTheory.ZetaB.unitOf_zero]
    simp only [Tower.cls, ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]
  · rw [eval_clsK X l n ha, GlobalTheory.ZetaB.eval_clsHat]
    congr 1
    ext
    rw [Units.val_mk0, GlobalTheory.ZetaB.unitOf_val X ha]

private theorem sf_sub_secT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n w : ℕ) (a : X.K) :
    sf X l n w a - secT X l w a ∈ evF X l n := by
  rw [mem_evF]
  intro u
  simp only [sf, secT, Pi.sub_apply, map_sub, map_smul, eval_clsK_eq, sub_self]

private theorem act_congr_sf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n M : ℕ} (hM : l ^ n ∣ M) (w : ℕ) {a : X.K}
    (ha : a ∈ topL X M) {m m' : SL(2, ℤ)} (h : m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M) :
    X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) (sf X l n w a) - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) (sf X l n w a) ∈
      evF X l n := by
  have hd := sf_sub_secT X l n w a
  have h1 := lnFn_le_evF X l n ((invMod_secT X l hM w ha).act_congr h)
  have h2 := Submodule.sub_mem _ (act_mem_evF X l n (m : Matrix (Fin 2) (Fin 2) ℤ) hd)
    (act_mem_evF X l n (m' : Matrix (Fin 2) (Fin 2) ℤ) hd)
  convert add_mem h1 h2 using 1
  simp only [map_sub]
  abel

private theorem conj_mem_Gam {N l : ℕ} [NeZero N] {t h : SL(2, ℤ)}
    (ht : t ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (hh : h ∈ Gam N l) : t * h * t⁻¹ ∈ Gam N l := by
  unfold Gam at hh ⊢
  obtain ⟨htN, htl⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨hh1, hhl⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ htl hhl) (Subgroup.inv_mem _ htl)⟩
  have e := (CongruenceSubgroup.Gamma1_mem N h).mp hh1
  have hh0 : h ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma0_mem.mpr e.2.2
  let T : CongruenceSubgroup.Gamma0 N := ⟨t, htN⟩
  let H : CongruenceSubgroup.Gamma0 N := ⟨h, hh0⟩
  have hH : H ∈ CongruenceSubgroup.Gamma1' N := (CongruenceSubgroup.Gamma1_to_Gamma0_mem H).mpr e
  have hC : T * H * T⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem'] at hH ⊢
    rw [map_mul, map_mul, hH, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hC
  exact (CongruenceSubgroup.Gamma1_mem N _).mpr hC

private theorem sum_congr_conj (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n N M : ℕ} [NeZero N] [NeZero M] {f : X.Fn l}
    (S : Finset SL(2, ZMod M))
    (hS : ∀ γ, γ ∈ S ↔ γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))))
    (hf : ∀ m m' : SL(2, ℤ), m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M →
      X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) f - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) f ∈ evF X l n)
    (g : SL(2, ℤ)) {g₀ : SL(2, ℤ)} (h₀ : g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) :
    X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) (∑ γ ∈ S, X.act l ((g * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f) -
      ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f ∈ evF X l n := by
  have hg₀i : g₀⁻¹ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := inv_mem h₀
  have key : ∀ m m' : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) m =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) m' → m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    intro m m' h
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, h, mul_inv_cancel]
  let e : SL(2, ZMod M) ≃ SL(2, ZMod M) :=
    (MulAut.conj (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀)⁻¹).toEquiv
  have he : ∀ γ, e γ = (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀)⁻¹ * γ *
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀ := fun γ => by
    simp [e, MulAut.conj_apply]
  have hmem : ∀ γ, γ ∈ S ↔ e γ ∈ S := by
    intro γ
    rw [hS, hS, he]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨g₀⁻¹ * h * g₀⁻¹⁻¹, conj_mem_Gam hg₀i hh, ?_⟩
      simp only [map_mul, map_inv, inv_inv]
    · rintro ⟨h, hh, hE⟩
      refine ⟨g₀ * h * g₀⁻¹, conj_mem_Gam h₀ hh, ?_⟩
      rw [map_mul, map_mul, hE, map_inv]
      group
  have hsum : ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f =
      ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M (e γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f :=
    (Finset.sum_equiv e hmem (fun _ _ => rfl)).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun γ _ => ?_)
  rw [act_act_SL]
  apply hf
  apply key
  simp only [map_mul, map_liftSL, he]
  group

private theorem par_mul {l : ℕ} [Fact l.Prime] {N c d : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} (hP : Par l N c d gm) {g₀ : SL(2, ℤ)}
    (h₀ : g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) : Par l N c d (fun r => gm r * g₀) := by
  obtain ⟨h0N, h0l⟩ := Subgroup.mem_inf.mp h₀
  have hN := (CongruenceSubgroup.Gamma0_mem).mp h0N
  rw [CongruenceSubgroup.Gamma0_mem] at h0l
  refine ⟨hP.odd, hP.five, hP.cop, hP.c1, hP.d1, hP.cc, hP.dc, fun r => ?_, fun r => ?_, fun r => ?_⟩
  · exact Subgroup.mul_mem _ (hP.g0 r) h0N
  · have h := hP.ga r
    have hx : ((g₀.1 1 0 : ℤ) : ZMod N) = 0 := hN
    simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    push_cast
    simp only [hx, mul_zero, add_zero]
    exact congrArg (· * _) h
  · have h := hP.col r
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h0l, h]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.Kd.L.actcls :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, Par l N c d (fun r => gm r * g₀) ∧ ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → ∀ (σ : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) b → LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) (fun r => gm r * g₀) σ) (X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP g₀ h₀
  refine ⟨par_mul hP h₀, ?_⟩
  intro x w m n c₀ _ hm σ b hb
  obtain ⟨hbB, hbe⟩ := hb
  have hl : l.Prime := Fact.out
  have hNl : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hP.cop).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨h0N, h0l⟩ := Subgroup.mem_inf.mp h₀
  have hdet : ((g₀ 0 0 : ℤ) : ZMod N) * ((g₀ 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 := congrArg (fun z : ℤ => (z : ZMod N)) g₀.2
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
    rw [CongruenceSubgroup.Gamma0_mem.mp h0N, mul_zero, sub_zero] at h1
    exact h1
  have hu : IsUnit ((g₀ 1 1 : ℤ) : ZMod N) := ⟨⟨_, _, by rw [mul_comm]; exact hdet, hdet⟩, rfl⟩
  have hdiam : IsDiam N l (((g₀ 1 1 : ℤ) : ZMod N).val) g₀ := by
    refine ⟨h₀, ?_⟩
    rw [ZMod.natCast_zmod_val]
    rfl
  have hdc : (((g₀ 1 1 : ℤ) : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime hu.unit
  refine ⟨?_, ?_⟩
  · rw [Tower.act_isDiam_eq X hbB hdiam]
    exact GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w _ hN0 hNl hdc b hbB
  · set A := clsBmu X l n m N x c d (w + 2) gm σ with hAe
    set A' := clsBmu X l n m N x c d (w + 2) (fun r => gm r * g₀) σ with hA'e
    haveI : NeZero (topMu l n m N) :=
      ⟨by unfold topMu; exact mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
    have hdiv : l ^ n ∣ topMu l n m N := by
      unfold topMu
      exact Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_left n m)) _
    have hwk : wkMu X l n m N x c d σ ∈ topL X (topMu l n m N) := by
      unfold wkMu
      exact SetLike.coe_mem _
    have hf : ∀ m1 m2 : SL(2, ℤ), m1 * m2⁻¹ ∈ CongruenceSubgroup.Gamma (topMu l n m N) →
        X.act l (m1 : Matrix (Fin 2) (Fin 2) ℤ) (fun u => u 0 ^ (w + 2 - 2) • clsK X l n (wkMu X l n m N x c d σ)) -
          X.act l (m2 : Matrix (Fin 2) (Fin 2) ℤ) (fun u => u 0 ^ (w + 2 - 2) • clsK X l n (wkMu X l n m N x c d σ)) ∈
            evF X l n :=
      fun m1 m2 hmm => act_congr_sf X l hdiv (w + 2 - 2) hwk hmm
    have hkey : X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) A - A' ∈ evF X l n := by
      simp only [hAe, hA'e, clsBmu]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ (fun r₀ _ => ?_)
      exact sum_congr_conj X l _ (fun γ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) hf (gm r₀) h₀
    clear_value A A'
    have hA : b - (l : ℤ_[l]) ^ c₀ • A ∈ evF X l n := by
      rw [mem_evF]
      exact hbe
    have h1 := act_mem_evF X l n (g₀ : Matrix (Fin 2) (Fin 2) ℤ) hA
    have h2 := Submodule.smul_mem (evF X l n) ((l : ℤ_[l]) ^ c₀) hkey
    have h3 := Submodule.add_mem _ h1 h2
    rw [mem_evF] at h3
    intro u
    convert h3 u using 2
    simp only [map_sub, map_smul, smul_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    abel
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.DlgalMapMul
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem hahnSeries_map_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) := by
  have e : ∀ z : HahnSeries ℚ Ω, HahnSeries.map z ((s : Ω →+* Ω) : Ω →ₙ+* Ω) = HahnSeries.map z (s : Ω →+* Ω) := by
    intro z
    ext r
    simp [HahnSeries.map_coeff]
    rfl
  rw [← e, ← e, ← e]
  exact HahnSeries.map_mul _

private theorem theta_hahnSeries_map_comm {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (x : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map x (s : Ω →+* Ω)) = HahnSeries.map (theta q x) (s : Ω →+* Ω) := by
  ext r
  show algebraMap ℚ Ω (q * r) * (HahnSeries.map x (s : Ω →+* Ω)).coeff r = (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r) * x.coeff r)
  rw [HahnSeries.map_coeff, map_mul (s : Ω →+* Ω),
    show (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r)) = algebraMap ℚ Ω (q * r) from s.commutes _]

private theorem hahnSeries_map_sub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r
  simp [HahnSeries.map_coeff]

private theorem prim_hahnSeries_map_of_prim_comap {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω)
    (hA : ∀ x, x ∈ A' ↔ s x ∈ A) (x : HahnSeries ℚ Ω) (hx : Prim A' x) :
    Prim A (HahnSeries.map x (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr0, hr⟩ := hx
  refine ⟨fun t => ?_, r, ?_, ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (h1 t)
  · rw [HahnSeries.map_coeff]
    exact (map_ne_zero _).2 hr0
  · rw [HahnSeries.map_coeff, ← map_inv₀]
    exact (hA _).1 hr

set_option maxHeartbeats 800000 in
theorem UpperTheory.Kd.L.dlgal :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), (∀ x, x ∈ A' ↔ s x ∈ A) → ∀ (n : ℕ) (a : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A' l n a f φ → IsDl X A l n a (X.gal s f) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ _ ε X l _ A A' s hA n q f φ h
  obtain ⟨hφ, a, b, κ, hκ, hfb, ha, hb, hc⟩ := h
  have hM : ∀ g : X.K, X.exp (X.gal s g) = HahnSeries.map (X.exp g) (s : Ω →+* Ω) := by
    intro g
    ext r
    rw [HahnSeries.map_coeff, X.gal_exp]
    rfl
  have hsm : ∀ (c : Ω) (y : HahnSeries ℚ Ω) (r : ℚ),
      (algebraMap Ω (HahnSeries ℚ Ω) c * y).coeff r = c * y.coeff r := by
    intro c y r
    rw [HahnSeries.algebraMap_apply']
    simp [HahnSeries.C_mul_eq_smul]
  have hsκ : s κ ≠ 0 := (map_ne_zero _).2 hκ
  have hc0 : algebraMap Ω X.K (s κ) ≠ 0 := (map_ne_zero _).2 hsκ
  have hexpa : X.exp ((algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a)) =
      HahnSeries.map (X.exp a) (s : Ω →+* Ω) := by
    rw [← map_inv₀, map_mul, AlgHom.commutes, hM, map_mul, AlgHom.commutes]
    ext r
    rw [hsm, HahnSeries.map_coeff, HahnSeries.map_coeff, hsm, map_mul, ← mul_assoc,
      show (s κ)⁻¹ * (s : Ω →+* Ω) κ = 1 from inv_mul_cancel₀ hsκ, one_mul]
  refine ⟨fun r => ?_, (algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a), X.gal s b, s κ, hsκ,
    ?_, ?_, ?_, fun r => ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (hφ r)
  · rw [← map_mul, hfb, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  · rw [hexpa]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ ha
  · rw [hM]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ hb
  · rw [hexpa, hM, theta_hahnSeries_map_comm, theta_hahnSeries_map_comm, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_sub,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨s z, (hA z).1 hz, ?_⟩
    rw [← map_sub, e, map_mul]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsDlDivM
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_pow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hl : ((l : ℕ) : Ω) ∈ A.nonunits) (M : ℕ) (hM : 0 < M) : ∃ k : ℕ, ∃ u ∈ A, (l : Ω) ^ k = (M : Ω) * u := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hp.ne_one
  have hc : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hc' : IsCoprime (l : A) (m : A) := by simpa using hc.map (Int.castRingHom A)
  have hlu : ¬ IsUnit (l : A) := by
    have h1 : ((l : A) : Ω) ∈ A.nonunits := by simpa using hl
    have := (ValuationSubring.coe_mem_nonunits_iff).1 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have hmu : IsUnit (m : A) := by
    obtain ⟨a, b, e⟩ := hc'
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (e ▸ isUnit_one) with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hlu
    · exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hmu.exists_right_inv
  refine ⟨k, (u : Ω), u.2, ?_⟩
  have e : (m : Ω) * (u : Ω) = 1 := by simpa using congrArg (fun x : A => (x : Ω)) hu
  push_cast
  rw [mul_assoc, e, mul_one]

private theorem isDl_divM {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k M : ℕ) (hM : 0 < M) (u : Ω) (hu : u ∈ A)
    (hk : (l : Ω) ^ k = (M : Ω) * u) (F : X.K) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A)
    (h : IsDl X A l (n + k) (M : ℚ) F (HahnSeries.C (M : Ω) * ψ)) : IsDl X A l n 1 F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  refine ⟨u * z, mul_mem hu hz, ?_⟩
  have hm : algebraMap ℚ Ω (M : ℚ) = (M : Ω) := map_natCast _ _
  rw [NrmT.theta_eq_C_mul _ (X.exp a), NrmT.theta_eq_C_mul _ (X.exp c), hm] at e
  have hM0 : (M : Ω) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have e2 : HahnSeries.C (M : Ω) * ψ * X.exp a * X.exp c =
      HahnSeries.C (M : Ω) * (ψ * X.exp a * X.exp c) := by ring
  have e3 : HahnSeries.C (M : Ω) * theta 1 (X.exp a) * X.exp c -
      X.exp a * (HahnSeries.C (M : Ω) * theta 1 (X.exp c)) =
      HahnSeries.C (M : Ω) * (theta 1 (X.exp a) * X.exp c - X.exp a * theta 1 (X.exp c)) := by ring
  rw [e2, e3, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    smul_eq_mul, smul_eq_mul, ← mul_sub, pow_add, hk] at e
  apply mul_left_cancel₀ hM0
  rw [e]; ring

private theorem isDl_weak {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k : ℕ) (s : ℚ) (F : X.K) (φ : HahnSeries ℚ Ω)
    (h : IsDl X A l (n + k) s F φ) : IsDl X A l n s F φ := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hφ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  exact ⟨(l : Ω) ^ k * z, mul_mem (pow_mem (natCast_mem A l) k) hz, by rw [e, pow_add]; ring⟩

theorem UpperTheory.Kd.L.nrm :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n M : ℕ), 0 < M → ∀ (w : X.K) (φ φ' : HahnSeries ℚ Ω), w ∈ KT X M → IsDl X A l n (M : ℚ) w φ → (∀ r : ℚ, φ.coeff r ≠ 0 → (r * M).den = 1) → (∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) → IsDl X A l n 1 (nrmT X M w) φ' := by
  intro Ω _ _ _ _ ε X l _ A hl n M hM w φ φ' hw hφ _ hφ'
  have hj := X.j_hol.imp fun _ h => And.symm h
  obtain ⟨k, u, huA, hk⟩ := exists_pow_eq l A hl M hM
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨-, a, c, κ, hκ, he, ha, -, -⟩ := hφ
    rw [zero_mul] at he
    have ha0 : a = 0 := by
      rcases mul_eq_zero.1 he.symm with h | h
      · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).1 h) hκ
      · exact h
    obtain ⟨-, r, hr, -⟩ := ha
    exact hr (by rw [ha0, map_zero]; rfl)
  obtain ⟨φ2, h2, hs2⟩ := _root_.GlobalTheory.dl_exists ε X hj l A hl (n + k) M w hM hw0 hw
  have hu := _root_.GlobalTheory.Glue.isDl_unique ε X hj l A hl n (M : ℚ) w φ φ2 hφ (isDl_weak X A l n k _ w φ2 h2)
  have hT : ∀ b ∈ Finset.range M,
      IsDl X A l (n + k) (M : ℚ) (X.sl (ofSL (ModularGroup.T ^ b)) w) (NrmT.trT ε b φ2) :=
    fun b _ => NrmT.isLogDerivQExpansionModPrimePow_slash_T_pow X A l (n + k) _ w φ2 b h2
  have hP := _root_.GlobalTheory.isDl_finset_prod_zpow ε X hj l A hl (n + k) (M : ℚ) ℕ (Finset.range M)
    (fun b => X.sl (ofSL (ModularGroup.T ^ b)) w) (fun b => NrmT.trT ε b φ2) (fun _ => 1) hT
  simp only [zpow_one, one_smul] at hP
  rw [NrmT.sum_trT M φ2 hs2 (NrmT.resZ φ2) (NrmT.resZ_coeff φ2)] at hP
  have hN := isDl_divM X A l n k M hM u huA hk _ (NrmT.resZ φ2) (fun r => by
    rw [NrmT.resZ_coeff]; split_ifs
    · exact h2.1 r
    · exact zero_mem A) hP
  refine NrmT.isDl_congr X A l n 1 _ (NrmT.resZ φ2) φ' hN (fun r => ?_) (fun r => ?_)
  · rw [hφ']; split_ifs
    · exact hφ.1 r
    · exact zero_mem A
  · rw [hφ', NrmT.resZ_coeff]; split_ifs
    · exact hu r
    · exact ⟨0, zero_mem A, by ring⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Witalg
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem gal_mul' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (s t : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * t) f = X.gal s (X.gal t f) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  ext r
  simp [X.gal_exp]

private theorem kmap_comp' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = φ (ψ f)) (a : X.Khat l) : X.kmap l χ a = X.kmap l φ (X.kmap l ψ a) := by
  unfold Tower.kmap
  have e : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map χ.toMonoidHom))) =
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
        (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) := by
    ext u
    exact h _
  show AdicCompletion.map (idl l) _ a = AdicCompletion.map (idl l) _ (AdicCompletion.map (idl l) _ a)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, e]

theorem UpperTheory.Kd.L.witalg :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N n : ℕ), 1 ≤ N → (∀ (b b' : X.Fn l) (f f' : X.Kˣ), IsWit X N l n b f → IsWit X N l n b' f' → IsWit X N l n (b + b') (f * f')) ∧ IsWit X N l n 0 1 ∧ (∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (f : X.Kˣ), IsWit X N l n b f → IsWit X N l n (X.galB l s b) (Units.map (X.gal s).toMonoidHom f)) ∧ ∀ s t : Ω ≃ₐ[ℚ] Ω, ∀ b : X.Fn l, X.galB l (s * t) b = X.galB l s (X.galB l t b) := by
  intro Ω _ _ _ _ ε X l _ N n _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b b' f f' ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun γ hγ => ?_, ?_, fun δ a c => ?_⟩
    · rw [Units.val_mul, map_mul, h1 γ hγ, k1 γ hγ]
    · rw [Pi.add_apply, map_add (f := _), h2, k2]
      unfold Tower.cls
      rw [← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add, ofMul_mul]
    · obtain ⟨g, hg, e⟩ := h3 δ a c
      obtain ⟨g', hg', e'⟩ := k3 δ a c
      refine ⟨g * g', fun γ hγ => by rw [map_mul, hg γ hγ, hg' γ hγ], ?_⟩
      rw [Units.val_mul, map_mul, mul_pow, ← e, ← e']
      ring
  · refine ⟨fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩⟩
    simp [Tower.cls]
  · rintro s b f ⟨hfI, hcls, hδ⟩
    have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]; exact GlobalTheory.ThGal.inv_gal X s _ _ hfI
    · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
        funext i; fin_cases i <;> simp
      have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
      rw [hu] at hg
      rw [AdicCompletion.eval_apply] at hcls
      rw [hg, AdicCompletion.eval_apply, Tower.kmap]
      erw [AdicCompletion.map_val_apply]
      rw [hcls]
      simp [Tower.cls, LinearMap.reduceModIdeal_apply]
    · intro δ hδ1 hδ2
      obtain ⟨δ', h1, h2, hrec⟩ := GlobalTheory.ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
      obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
      refine ⟨X.gal s g, GlobalTheory.ThGal.inv_gal X s _ _ hg, ?_⟩
      rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · intro s t b
    funext u
    show X.kmap l (X.gal (s * t)) (b ![u 0, (cyclotomicCharacter Ω l (s * t).toRingEquiv : ℤ_[l]) * u 1]) =
      X.kmap l (X.gal s) (X.kmap l (X.gal t) (b ![u 0, (cyclotomicCharacter Ω l t.toRingEquiv : ℤ_[l]) *
        ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1)]))
    have hm : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [kmap_comp' X l _ _ _ (gal_mul' X s t), hm, map_mul, Units.val_mul, mul_left_comm, mul_assoc]
end

