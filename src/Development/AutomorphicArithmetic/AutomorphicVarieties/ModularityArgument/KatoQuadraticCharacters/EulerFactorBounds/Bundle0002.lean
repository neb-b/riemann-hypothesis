module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem ev_map {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M n x = 0) :
    AdicCompletion.eval I M n (AdicCompletion.map I f x) = 0 := by
  change (AdicCompletion.map I f x).val n = 0
  rw [AdicCompletion.map_val_apply]
  change (f.reduceModIdeal (I ^ n)) (AdicCompletion.eval I M n x) = 0
  rw [h, map_zero]

private theorem ev_succ {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M (n + 1) x = 0) :
    AdicCompletion.eval I M n x = 0 := by
  change x.val n = 0
  rw [← x.property (Nat.le_succ n)]
  change (AdicCompletion.transitionMap I M (Nat.le_succ n)) (AdicCompletion.eval I M (n + 1) x) = 0
  rw [h, map_zero]

private theorem ev_zero {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (x : AdicCompletion I M) : AdicCompletion.eval I M 0 x = 0 := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 0 x)
  rw [← hy, Submodule.Quotient.mk_eq_zero]
  simp

private theorem ev_smul {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (c : R) (hc : c ∈ I ^ n) (x : AdicCompletion I M) : AdicCompletion.eval I M n (c • x) = 0 := by
  rw [map_smul]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M n x)
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

private theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = ψ (φ f))
    (x : X.Khat l) : X.kmap l χ x = X.kmap l ψ (X.kmap l φ x) := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap =
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap ∘ₗ
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x =
    AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap)
      (AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap) x)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, hl]

private theorem kmap_id (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (χ : X.K ≃+* X.K) (h : ∀ f, χ f = f)
    (x : X.Khat l) : X.kmap l χ x = x := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap = LinearMap.id := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x = x
  rw [hl, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem sApi : SApi := by
  intro Ω _ _ _ ε X l _ n
  refine ⟨⟨fun a u => ?_, fun {a b} hab u => ?_, fun {a b c} hab hbc u => ?_⟩,
    fun a b a' b' h h' => ⟨fun u => ?_, fun u => ?_⟩, fun k a b h u => ?_,
    fun ι S a b h u => ?_, fun k k' a hk => ?_, fun m a b h u => ?_, fun s a b h u => ?_,
    fun a b h u => ev_succ _ _ _ (h u), fun a b u => ev_zero _ _, fun s t a => ?_, fun a => ?_⟩
  · rw [sub_self, map_zero]
  · rw [← neg_sub, map_neg, hab u, neg_zero]
  · rw [← sub_add_sub_cancel (a u) (b u) (c u), map_add (f := _), hab u, hbc u, add_zero]
  · rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add (f := _), h u, h' u, add_zero]
  · rw [Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm, map_sub, h u, h' u, sub_zero]
  · rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, map_smul, h u, smul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib, map_sum]
      exact Finset.sum_eq_zero (fun i hi => h i hi u)
  · rw [← sub_smul]
    apply ev_smul
    rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hk
  · simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have hst : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [hst, map_mul, Units.val_mul,
      show ((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]) * ((cyclotomicCharacter Ω l) t.toRingEquiv) * u 1 =
        ((cyclotomicCharacter Ω l) t.toRingEquiv) * (((cyclotomicCharacter Ω l) s.toRingEquiv) * u 1) by ring]
    exact kmap_comp X l _ _ _ (GlobalTheory.K4.gal_mul_apply X s t) _
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (AlgEquiv.toRingEquiv (1 : Gal(Ω/ℚ))) = 1 := rfl
    have hu : ![u 0, u 1] = u := by
      ext i
      fin_cases i <;> rfl
    rw [h1, map_one, Units.val_one, one_mul, hu]
    exact kmap_id X l _ (GlobalTheory.K4.gal_one_apply X) _

end UpperTheory.V.Z.Kato.Nb

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.NatCastNeOfCop
section
noncomputable section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

def rz (M : ℕ) (a : Fin 2 → ℤ) : Row M := fun i => ((a i : ℤ) : ZMod M)

def aU (l L N : ℕ) (x : ZMod N) : Fin 2 → ℤ := ![(N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L, 0]

def aV (l L N : ℕ) : Fin 2 → ℤ := ![(topT l L N : ℤ) * (l : ℤ) ^ L, (N : ℤ)]

def aUT (l L N p : ℕ) (x : ZMod N) : Fin 2 → ℤ :=
  ![bar l L N p * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) * p + N * (l : ℤ) ^ L, 0]

def aVT (l L N p : ℕ) : Fin 2 → ℤ :=
  ![bar l L N p * (topT l L N : ℤ) * (l : ℤ) ^ L * p, bar l L N p * N * p + N * (l : ℤ) ^ L]

theorem rz_toQ (M : ℕ) [NeZero M] (a : Fin 2 → ℤ) (i : Fin 2) :
    ∃ j : ℤ, ((a i : ℤ) : ℚ) / (M : ℚ) = toQ M (rz M a) i + j := by
  refine ⟨a i / M, ?_⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hv : (((a i : ZMod M).val : ℤ)) = a i % M := ZMod.val_intCast (a i)
  have k : a i % M + M * (a i / M) = a i := by rw [Int.emod_def]; ring
  simp only [toQ, rz]
  rw [div_add' _ _ _ hM, div_left_inj' hM]
  have e : (((a i : ZMod M).val : ℕ) : ℚ) = ((a i % M : ℤ) : ℚ) := by exact_mod_cast hv
  rw [e]
  have k' : ((a i % M + M * (a i / M) : ℤ) : ℚ) = ((a i : ℤ) : ℚ) := by exact_mod_cast k
  push_cast at k' ⊢
  linarith

theorem rz_congr {M : ℕ} {a b : Fin 2 → ℤ} (h : ∀ i, (M : ℤ) ∣ b i - a i) : rz M a = rz M b := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i)

theorem smul_rz (M : ℕ) (k : ℤ) (a : Fin 2 → ℤ) : (k : ZMod M) • rz M a = rz M (k • a) := by
  funext i
  simp [rz]

theorem up_rz (k M : ℕ) [NeZero M] (a : Fin 2 → ℤ) : up k M (rz M a) = rz (k * M) ((k : ℤ) • a) := by
  funext i
  simp only [up, rz, Pi.smul_apply, smul_eq_mul]
  have hv : (((a i : ZMod M).val : ℤ)) = a i % M := ZMod.val_intCast (a i)
  rw [show ((k * (a i : ZMod M).val : ℕ) : ZMod (k * M)) = (((k * (a i % M) : ℤ)) : ZMod (k * M)) by
    rw [← hv]; push_cast; rfl]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
  refine ⟨a i / M, ?_⟩
  have k' : a i % M + M * (a i / M) = a i := by rw [Int.emod_def]; ring
  push_cast
  linear_combination (-(k : ℤ)) * k'

theorem two_smul_rz_ne {M l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ M) (a : Fin 2 → ℤ) (i : Fin 2)
    (ha : ((a i : ℤ) : ZMod l) ≠ 0) : (2 : ZMod M) • rz M a ≠ 0 := by
  haveI := Fact.mk hl
  intro hz
  have h' := congrFun hz i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, rz] at h'
  have h'' := congrArg (ZMod.castHom h (ZMod l)) h'
  rw [map_mul, map_intCast, map_zero, map_ofNat] at h''
  rcases mul_eq_zero.1 h'' with h2' | h2'
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2'
    have h4 := (CharP.cast_eq_zero_iff (ZMod l) l 2).1 h3
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h4)
  · exact ha h2'

theorem natCast_ne_of_cop {l N : ℕ} (hl : l.Prime) (hc : Nat.Coprime l N) : (N : ZMod l) ≠ 0 := by
  intro h0
  have hd := (CharP.cast_eq_zero_iff (ZMod l) l N).1 h0
  exact hl.ne_one (Nat.Coprime.eq_one_of_dvd hc hd)

theorem bar_mul {l N p : ℕ} (L : ℕ) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((N * l ^ L : ℕ) : ℤ) ∣ bar l L N p * p - 1 := by
  have h1 : Nat.Coprime p l := Nat.Coprime.coprime_dvd_right (dvd_mul_right l N) hp
  have h2 : Nat.Coprime p N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hp
  have hcop : Nat.Coprime p (N * l ^ L) := Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)
  haveI : NeZero (N * l ^ L) := ⟨mul_ne_zero hN (pow_ne_zero _ hl)⟩
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ _).1
  unfold bar
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact (ZMod.coe_mul_inv_eq_one p hcop).symm.trans (mul_comm _ _)

theorem bar_mul_l {l N p L : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  have h6 := bar_mul L hl hN hp
  have hl' : (l : ℤ) ∣ ((N * l ^ L : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N)
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (bar l L N p * p) l).2 (dvd_trans hl' h6)
  push_cast at hd
  exact hd.symm

theorem aU_mod {l L N : ℕ} (hL : 1 ≤ L) (x : ZMod N) :
    ((aU l L N x 0 : ℤ) : ZMod l) = N ∧ ((aU l L N x 1 : ℤ) : ZMod l) = 0 := by
  constructor
  · simp only [aU, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
  · simp [aU]

theorem aV_mod {l L N : ℕ} (hL : 1 ≤ L) :
    ((aV l L N 0 : ℤ) : ZMod l) = 0 ∧ ((aV l L N 1 : ℤ) : ZMod l) = N := by
  constructor
  · simp only [aV, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero]
  · simp [aV]

theorem aUT_mod {l L N p : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) (x : ZMod N) :
    ((aUT l L N p x 0 : ℤ) : ZMod l) = N ∧ ((aUT l L N p x 1 : ℤ) : ZMod l) = 0 := by
  have hb := bar_mul_l hL hl hN hp
  constructor
  · simp only [aUT, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    linear_combination (N : ZMod l) * hb
  · simp [aUT]

theorem aVT_mod {l L N p : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((aVT l L N p 0 : ℤ) : ZMod l) = 0 ∧ ((aVT l L N p 1 : ℤ) : ZMod l) = N := by
  have hb := bar_mul_l hL hl hN hp
  constructor
  · simp only [aVT, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    ring
  · simp only [aVT, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    linear_combination (N : ZMod l) * hb

theorem ok_of_mod {M l N : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (h : l ∣ M) {a b : Fin 2 → ℤ}
    (ha : ((a 0 : ℤ) : ZMod l) = N) (hb : ((b 1 : ℤ) : ZMod l) = N) : Ok (rz M a) (rz M b) := by
  refine ⟨?_, ?_⟩
  · have hne := two_smul_rz_ne hl h2 h a 0 (by rw [ha]; exact natCast_ne_of_cop hl hc)
    intro hz
    apply hne
    funext j
    have hj := congrFun hz j
    simp only [Pi.smul_apply, Pi.zero_apply] at hj ⊢
    simpa [two_nsmul, two_zsmul, two_smul] using hj
  · have hne := two_smul_rz_ne hl h2 h b 1 (by rw [hb]; exact natCast_ne_of_cop hl hc)
    intro hz
    apply hne
    funext j
    have hj := congrFun hz j
    simp only [Pi.smul_apply, Pi.zero_apply] at hj ⊢
    simpa [two_nsmul, two_zsmul, two_smul] using hj

theorem ok_UV {M l L N : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (hL : 1 ≤ L) (h : l ∣ M) (x : ZMod N) :
    Ok (rz M (aU l L N x)) (rz M (aV l L N)) :=
  ok_of_mod hl h2 hc h (aU_mod hL x).1 (aV_mod hL).2

theorem ok_UVT {M l L N p : ℕ} [NeZero N] (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (hL : 1 ≤ L) (h : l ∣ M)
    (hp : Nat.Coprime p (l * N)) (x : ZMod N) : Ok (rz M (aUT l L N p x)) (rz M (aVT l L N p)) :=
  ok_of_mod hl h2 hc h (aUT_mod hL hl.ne_zero (NeZero.ne N) hp x).1 (aVT_mod hL hl.ne_zero (NeZero.ne N) hp).2

theorem ixU_toQ {M l L N : ℕ} [NeZero M] (hM : M = N * l ^ L) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixU l L N x i = toQ M (rz M (aU l L N x)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L) (aU l L N x) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixV_toQ {M l L N : ℕ} [NeZero M] (hM : M = N * l ^ L) (i : Fin 2) :
    ∃ j : ℤ, ixV l L N i = toQ M (rz M (aV l L N)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L) (aV l L N) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixUT_toQ {M l L N p : ℕ} [NeZero M] (hM : M = N * l ^ L * p) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixUT l L N p x i = toQ M (rz M (aUT l L N p x)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L * p) (aUT l L N p x) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixVT_toQ {M l L N p : ℕ} [NeZero M] (hM : M = N * l ^ L * p) (i : Fin 2) :
    ∃ j : ℤ, ixVT l L N p i = toQ M (rz M (aVT l L N p)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L * p) (aVT l L N p) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem Hyp.lv {l N c d : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (hl : l ≠ 0) (hN : N ≠ 0) {M L : ℕ} (hM : M = N * l ^ L) :
    Lv c d M := by
  subst hM
  refine ⟨Nat.pos_of_ne_zero (mul_ne_zero hN (pow_ne_zero _ hl)), ?_, ?_⟩
  · have h1 : c.Coprime l := Nat.Coprime.coprime_dvd_right (Dvd.intro (6 * N) (by ring)) H.cc
    have h2 : c.Coprime N := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (6 * l) rfl) H.cc
    exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)
  · have h1 : d.Coprime l := Nat.Coprime.coprime_dvd_right (Dvd.intro (6 * N) (by ring)) H.cd
    have h2 : d.Coprime N := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (6 * l) rfl) H.cd
    exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)

theorem Hyp.lvT {l N c d p : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (hl : l ≠ 0) (hN : N ≠ 0) (hp0 : p ≠ 0)
    (hp : Nat.Coprime p (l * N * c * d)) {M L : ℕ} (hM : M = N * l ^ L * p) : Lv c d M := by
  subst hM
  obtain ⟨h0, h1, h2⟩ := H.lv hl hN (rfl : N * l ^ L = N * l ^ L)
  exact ⟨Nat.mul_pos h0 (Nat.pos_of_ne_zero hp0),
    h1.mul_right (Nat.Coprime.coprime_mul_left_right (Nat.Coprime.coprime_mul_right_right hp)).symm,
    h2.mul_right (Nat.Coprime.coprime_mul_left_right hp).symm⟩

end UpperTheory.V.Z.Kato.Nb

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCycZ :
    UpperTheory.V.Z.Kato.Nb.SCycZ := by
  intro Ω _ _ _ l _ r s
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hval : ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
      PadicInt.toZModPow r (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := rfl
  have hspec : ∀ z : Ω, z ^ (l ^ r) = 1 →
      s z = z ^ ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro z hz
    rw [hval]
    exact cyclotomicCharacter.spec l s.toRingEquiv z hz
  have hM := cycM_spec (l ^ r) s ⟨_, hspec⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have heq : ReciprocityTheory.Gal.cycMod ℚ Ω l r s = cycM (l ^ r) s := by
    apply Units.ext
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      ((hspec ζ hζ.pow_eq_one).symm.trans (hM ζ hζ.pow_eq_one))
  refine ⟨heq, ?_⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, ← heq, hval, sub_self]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiScal
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem xs_cast {d M : ℕ} [NeZero M] (h : d ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod d) = ZMod.castHom h (ZMod d) z := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

private theorem xs_eval {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (k k' : ℤ_[l]) (a : X.Khat l) (h : PadicInt.toZModPow n k = PadicInt.toZModPow n k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • a - k' • a) = 0 := by
  have h1 : k - k' ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]
  rw [← sub_smul, map_smul]
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n a)
  rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

private theorem xs_cD (N M₀ M : ℕ) [NeZero N] [NeZero M] (hM : M = N * M₀) (c : ZMod M)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (h : ((m 1 0).val : ZMod N) = 0) :
    cD N M₀ (c • m) = ((c.val : ℕ) : ZMod M₀) • cD N M₀ m := by
  have hM₀ : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have key : ∀ z : ZMod M, ((c * z).val : ZMod M₀) = (c.val : ZMod M₀) * (z.val : ZMod M₀) := by
    intro z
    rw [xs_cast hM₀, xs_cast hM₀, xs_cast hM₀, map_mul]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h10 : (c * m 1 0).val / N = c.val * q % M₀ := by
    rw [ZMod.val_mul, hq]
    generalize c.val = cv
    rw [hM, mul_left_comm, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hN]
  have hq' : (m 1 0).val / N = q := by
    rw [hq, Nat.mul_div_cancel_left _ hN]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    ring
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, h10, hq', ZMod.natCast_mod, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]

private theorem xs_Cnd (l N M : ℕ) [Fact l.Prime] [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ)) (ν : (ZMod M)ˣ)
    (hν : ((ν : ZMod M).val : ZMod N) = 1) (m : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    Cnd l N g ((ν : ZMod M) • m) ↔ Cnd l N g m := by
  have key : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod N) = (z.val : ZMod N) := by
    intro z
    rw [xs_cast hN, xs_cast hN, map_mul, ← xs_cast hN, hν, one_mul]
  have key' : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod l) = ZMod.castHom hl (ZMod l) (ν : ZMod M) * (z.val : ZMod l) := by
    intro z
    rw [xs_cast hl, xs_cast hl, map_mul]
  have hu : IsUnit (ZMod.castHom hl (ZMod l) (ν : ZMod M)) := (ν.isUnit).map _
  simp only [Cnd, Matrix.smul_apply, smul_eq_mul, key, key']
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [mul_left_comm, mul_left_comm (↑(en g 0 0) : ZMod l)]
  exact hu.mul_right_inj

private theorem xs_sum {R ι A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (L : A →ₗ[R] B) (e : ι ≃ ι) (s t : Finset ι) (f g : ι → A) (h : ∀ i, i ∈ s ↔ e i ∈ t)
    (h' : ∀ i ∈ s, L (f i - g (e i)) = 0) : L (∑ i ∈ s, f i - ∑ i ∈ t, g i) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_equiv e (t := t) (g := g) h (fun _ _ => rfl), ← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_eq_zero h'

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sXiScal :
    UpperTheory.V.Z.Kato.Nb.SXiScal := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a ν hν
  have hM := hL.eq
  have hNM : N ∣ M := ⟨M₀, hM⟩
  have hM₀M : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have hlM₀ : l ^ n ∣ M₀ := hL.dl
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans (hlM₀.trans hM₀M)
  have hlnM : l ^ n ∣ M := hlM₀.trans hM₀M
  let U : GL (Fin 2) (ZMod M) := Units.map (Matrix.scalar (Fin 2) : ZMod M →+* Matrix (Fin 2) (Fin 2) (ZMod M)).toMonoidHom ν
  have hU : ∀ m : GL (Fin 2) (ZMod M), ((U * m : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν : ZMod M) • (m : Matrix _ _ _) := by
    intro m
    ext i j
    simp [U]
  have hdet : ∀ m : GL (Fin 2) (ZMod M), Matrix.GeneralLinearGroup.det (U * m) = ν ^ 2 * Matrix.GeneralLinearGroup.det m := by
    intro m
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hU, Matrix.det_smul, Fintype.card_fin]
  unfold CgF
  intro u
  simp only [Xi, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine xs_sum (AdicCompletion.eval (idl l) (X.Kl l) n) (Equiv.mulLeft U) _ _ _ _ ?_ ?_
  · intro m
    have hP : ν ^ 2 * Matrix.GeneralLinearGroup.det m * ν⁻¹ ^ 2 = Matrix.GeneralLinearGroup.det m := by
      rw [inv_pow, mul_right_comm, mul_inv_cancel, one_mul]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft, hU, hdet, hP, xs_Cnd l N M hNM hlM g ν hν]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [Equiv.coe_mulLeft, hU, hdet]
    rw [xs_cD N M₀ M hM _ _ hm.1.1, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.smul_vecMul]
    apply xs_eval
    simp only [map_mul, map_pow, map_add (f := _), map_natCast, Matrix.smul_apply, smul_eq_mul, xs_cast hlnM]
    rw [mul_inv, Units.val_mul, map_mul, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    have hee : ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M) * ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    set e := ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M)
    set e' := ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M)
    rw [mul_assoc e, mul_assoc e, ← mul_add, mul_pow]
    set D := ZMod.castHom hlnM (ZMod (l ^ n)) ((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ)
    set A := ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0) * PadicInt.toZModPow n (u 0) + ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)
    linear_combination (-(e ^ w * D * A ^ w * (e * e' + 1))) * hee
end

