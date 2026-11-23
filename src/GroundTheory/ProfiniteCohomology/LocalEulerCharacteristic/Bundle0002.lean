module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveSnake
public import GroundTheory.LocalFields.Bundle0002
public import GroundTheory.LocalFields.NormalLattice

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u v

open Representation

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem toFun_prod {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y] (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) :
    d.toFun (X × Y) (ρ.prod σ) = d.toFun X ρ + d.toFun Y σ :=
  d.additive ρ _ σ (LinearMap.inl _ X Y) (LinearMap.snd _ X Y)
    ⟨fun _ _ => by ext <;> simp⟩ ⟨fun _ _ => rfl⟩ LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective

theorem toFun_pi {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) Γ X) (n : ℕ) :
    d.toFun (Fin n → X) (piRep (Fin n) ρ) = n * d.toFun X ρ := by
  induction n with
  | zero => simp [d.toFun_eq_zero_of_subsingleton (X := Fin 0 → X)]
  | succ n ih =>
    rw [← d.toFun_congr (ρ.prod (piRep (Fin n) ρ)) (piRep (Fin (n + 1)) ρ)
      (Fin.consLinearEquiv (ZMod l) (fun _ => X)) ?_, d.toFun_prod, ih]
    · push_cast
      ring
    · intro γ x
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem g_eq_of_torsion_trivial (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    [Finite (ModN A l)] (hA : ∀ a : A, l • a = 0 → a = 0) :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) := by
  have : Subsingleton (TorsN A l) := ⟨fun x y => Subtype.ext (by
    rw [hA x ((mem_ker_lsmul_iff l (x : A)).1 x.2), hA y ((mem_ker_lsmul_iff l (y : A)).1 y.2)])⟩
  rw [d.g_eq A, d.toFun_eq_zero_of_subsingleton (X := TorsN A l), sub_zero]

theorem g_eq_zero_of_nsmul_eq_zero (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (hA : ∀ a : A, l • a = 0) : d.g A = 0 := by
  by_cases hfin : Finite (ModN A l) ∧ Finite (TorsN A l)
  · obtain ⟨_, _⟩ := hfin
    rw [d.g_eq A, sub_eq_zero]
    let φ : A →ₗ[ℤ] TorsN A l :=
      LinearMap.codRestrict _ LinearMap.id (fun a => (mem_ker_lsmul_iff l a).2 (hA a))
    let ψ := (LinearMap.range (LinearMap.lsmul ℤ A (l : ℤ))).liftQ φ (by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by simpa [φ] using hA y))
    refine d.toFun_congr _ _ (LinearEquiv.ofBijective (ψ.toAddMonoidHom.toZModLinearMap l)
      ⟨fun x y hxy => ?_, fun t => ⟨Submodule.Quotient.mk (t : A), Subtype.ext rfl⟩⟩) ?_
    · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (congrArg Subtype.val hxy : (a : A) = b)
    · intro γ x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
  · exact d.g_of_not_finite A hfin

theorem g_eq_zero_of_finite (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A] :
    d.g A = 0 := by
  suffices H : ∀ (N : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A],
      Nat.card A = N → d.g A = 0 from H _ A rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ _ _ hN
  by_cases hA : ∀ a : A, l • a = 0 → a = 0
  · have hs : Function.Surjective (fun a : A => l • a) :=
      Finite.injective_iff_surjective.1 (fun a b hab =>
        sub_eq_zero.1 (hA (a - b) (by rw [smul_sub, sub_eq_zero]; exact hab)))
    have : Subsingleton (ModN A l) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      rw [(modN_mk_eq_zero_iff l _).2 ⟨a', rfl⟩, (modN_mk_eq_zero_iff l _).2 ⟨b', rfl⟩]⟩
    rw [d.g_eq_of_torsion_trivial A hA, d.toFun_eq_zero_of_subsingleton (X := ModN A l)]
  · push Not at hA
    obtain ⟨a₀, ha₀, hne⟩ := hA
    let m : A →+ A := (LinearMap.lsmul ℤ A (l : ℤ)).toAddMonoidHom
    have hm : ∀ a, m a = l • a := fun a => by simp [m]
    have hK : ∀ (γ : Γ) (a : A), a ∈ m.ker → γ • a ∈ m.ker := fun γ a ha => by
      rw [AddMonoidHom.mem_ker, hm] at ha ⊢
      rw [← smul_comm γ l a, ha, smul_zero]
    have hH : ∀ (γ : Γ) (a : A), a ∈ m.range → γ • a ∈ m.range := by
      rintro γ _ ⟨b, rfl⟩
      exact ⟨γ • b, by rw [hm, hm, smul_comm]⟩
    let _ := subgroupDistribMulAction m.ker hK
    let _ := subgroupDistribMulAction m.range hH
    have hKl : ∀ x : m.ker, l • x = 0 := fun x =>
      Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← hm]; exact x.2)
    have hcard : Nat.card m.range < N := by
      have h₁ : Nat.card A = Nat.card m.range * Nat.card m.ker := by
        rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker,
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv]
      have h₂ : 1 < Nat.card m.ker := by
        have : Nontrivial m.ker :=
          ⟨⟨⟨a₀, by rw [AddMonoidHom.mem_ker, hm, ha₀]⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
        exact Finite.one_lt_card
      have h₃ : 0 < Nat.card m.range := Nat.card_pos
      rw [← hN, h₁]
      nlinarith
    have e := d.g_add m.ker.subtype m.rangeRestrict (fun _ _ => rfl)
      (fun γ a => Subtype.ext (show m (γ • a) = γ • m a by rw [hm, hm, smul_comm]))
      (AddSubgroup.subtype_injective _)
      (fun y => ⟨fun hy => ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩,
        by rintro ⟨x, rfl⟩; exact Subtype.ext (AddMonoidHom.mem_ker.1 x.2)⟩)
      m.rangeRestrict_surjective
    rw [e, d.g_eq_zero_of_nsmul_eq_zero _ hKl, ih _ hcard _ rfl, add_zero]

theorem g_eq_of_finite_cokernel {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN B l)] [Finite (TorsN B l)] : d.g A = d.g B := by
  have hR : ∀ (γ : Γ) (a : A), a ∈ f.range → γ • a ∈ f.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hfγ γ b⟩
  let _ := quotientDistribMulAction f.range hR
  rw [d.g_add f (QuotientAddGroup.mk' f.range) hfγ (fun _ _ => rfl) hf
    (fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl)
    (QuotientAddGroup.mk'_surjective _), d.g_eq_zero_of_finite (A ⧸ f.range), add_zero]

theorem g_eq_of_finite_cokernel' {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN A l)] [Finite (TorsN A l)] : d.g A = d.g B := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have hh := QuotientAddGroup.mk'_surjective f.range
  have := finite_torsN_of_injective (n := l) hf
  have : Finite (ModN B l) :=
    finite_of_exact (connecting hh hfh hf).toAddMonoidHom (modNMap l f).toAddMonoidHom
      (exact_connecting_modNMap hh hfh hf)
  exact d.g_eq_of_finite_cokernel f hfγ hf

theorem g_of_trivial_int [NeZero l] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (htriv : ∀ (γ : Γ) (a : A), γ • a = a) (e : A ≃+ ℤ) : d.g A = d.one := by
  have hA : ∀ a : A, l • a = 0 → a = 0 := fun a ha => by
    have h := congrArg e ha
    rw [map_nsmul, map_zero, nsmul_eq_mul] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)
    exact e.injective (by rw [h', map_zero])
  let b : Module.Basis Unit ℤ A := (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  let E : ModN A l ≃ₗ[ZMod l] ULift.{u} (ZMod l) := (ModN.basis b).equivFun.trans
    ((LinearEquiv.funUnique Unit (ZMod l) (ZMod l)).trans ULift.moduleEquiv.symm)
  have : Finite (ModN A l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial A hA]
  refine d.toFun_congr _ _ E (fun γ x => ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, htriv]
  rfl

end AdditiveFunction

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.UnitsPower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem one_add_pow_prime_eq {p : ℕ} (hp : p.Prime) {z : 𝒪[K]} (hz : z ∈ 𝓂[K]) :
    ∃ y ∈ 𝓂[K], (1 + z) ^ p = 1 + z ^ p + p * z * (1 + y) := by
  rw [add_comm (1 : 𝒪[K]) z, add_pow_prime_eq hp z 1]
  set r := ∑ k ∈ Finset.Ioo 0 p, z ^ (k - 1) * 1 ^ (p - k - 1) * ((p.choose k / p : ℕ) : 𝒪[K])
  refine ⟨r - 1, ?_, by ring⟩
  rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  have hz' : residue 𝒪[K] z = 0 := (residue_eq_zero_iff _).mpr hz
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [r, map_sum, map_mul, map_pow, hz', one_pow, map_natCast, mul_one]
  rw [Finset.sum_eq_single 1]
  · simp [Nat.div_self hp.pos]
  · intro k hk hk1
    have : k - 1 ≠ 0 := by simp at hk; omega
    simp [zero_pow this]
  · intro h
    exact absurd (by simp; exact hp.one_lt) h

theorem exists_pow_eq_of_mem_unitFiltration_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K 1) : ∃ u ∈ unitFiltration K 1, u ^ m = w := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hu : IsUnit (m : 𝒪[K]) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]; exact hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])
  obtain ⟨b, hb, hb1⟩ := exists_root_of_dvd hϖ f 1 0 hu.unit
    (by simp [f, derivative_X_pow])
    (by
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw)
      have e' : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e', dvd_neg]
      simpa using this)
  have hbm : b ^ m = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hm0).mp (hbm ▸ w.isUnit)
  refine ⟨hbu.unit, ?_, by ext; simp [hbm]⟩
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  simpa using hb1

variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ} (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ}
  (hpe : (p : 𝒪[K]) = ϖ ^ e * ε)
include hϖ hp hpe

theorem one_add_pow_sub_one_eq {j : ℕ} (hj : e + 1 ≤ j) (x : 𝒪[K]) :
    ∃ w : 𝒪[K], (1 + ϖ ^ j * x) ^ p - 1 = ϖ ^ (j + e) * (ε * x + ϖ * w) := by
  have hj1 : 1 ≤ j := by omega
  obtain ⟨y, hy, h⟩ := one_add_pow_prime_eq hp (z := ϖ ^ j * x)
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (uniformizer_mem_maximalIdeal hϖ) j hj1))
  obtain ⟨t, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hy
  have h2 : 2 * j ≤ p * j := Nat.mul_le_mul_right j hp.two_le
  obtain ⟨m, hm⟩ : ∃ m, p * j = j + e + 1 + m := ⟨p * j - (j + e + 1), by omega⟩
  refine ⟨ϖ ^ m * x ^ p + ε * x * t, ?_⟩
  have hpow : (ϖ ^ j * x) ^ p = ϖ ^ (j + e + 1 + m) * x ^ p := by
    rw [mul_pow, ← pow_mul, mul_comm j p, hm]
  rw [h, hpow, hpe]
  ring

theorem pow_mem_unitFiltration {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ p ∈ unitFiltration K (j + e) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val,
    show (u : 𝒪[K]) = 1 + ϖ ^ j * a by simp only at ha; rw [← ha]; ring, hw]
  exact dvd_mul_right _ _

theorem pow_mem_unitFiltration_succ_iff {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) :
    u ^ p ∈ unitFiltration K (j + e + 1) ↔ u ∈ unitFiltration K (j + 1) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  have hu' : (u : 𝒪[K]) = 1 + ϖ ^ j * a := by simp only at ha; rw [← ha]; ring
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val, hu', hw,
    mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, hu', add_sub_cancel_left, pow_succ,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero),
    mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero), dvd_add_left (dvd_mul_right ϖ w),
    Units.dvd_mul_left]

theorem eq_one_of_mem_unitFiltration_of_pow_eq_one {k : ℕ} (hk : e + 1 ≤ k) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K k) (h : u ^ p = 1) : u = 1 := by
  have hall : ∀ n, u ∈ unitFiltration K (k + n) := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih =>
      have := (pow_mem_unitFiltration_succ_iff hϖ hp hpe (by omega) ih).mp
        (by rw [h]; exact one_mem _)
      simpa [add_assoc] using this
  have h0 : (u : 𝒪[K]) - 1 = 0 := by
    refine eq_zero_of_forall_pow_dvd hϖ fun N => ?_
    have := unitFiltration_antitone K (Nat.le_add_left N k) (hall N)
    exact (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp this)
  ext
  simpa [sub_eq_zero] using h0

theorem exists_pow_eq_of_mem_unitFiltration {k : ℕ} (hk : e + 1 ≤ k) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K (k + e)) : ∃ u ∈ unitFiltration K k, u ^ p = w := by
  set f : 𝒪[K][X] := X ^ p - C (w : 𝒪[K])
  obtain ⟨b, hb, hb1⟩ := exists_root_of_dvd hϖ f 1 e ε
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
        eval_C, eval_pow, eval_X, one_pow, mul_one]
      exact hpe)
    (by
      have hw' := unitFiltration_antitone K (show 2 * e + 1 ≤ k + e by omega) hw
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw')
      have e' : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e', dvd_neg]
      exact this)
  have hbp : b ^ p = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hp.ne_zero).mp (hbp ▸ w.isUnit)
  set u := hbu.unit
  have hup : u ^ p = w := by ext; simp [u, hbp]
  refine ⟨u, ?_, hup⟩
  have hstep : ∀ i, e + 1 + i ≤ k → u ∈ unitFiltration K (e + 1 + i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
      simpa [u] using hb1
    | succ i ih =>
      intro hi
      have hmem := ih (by omega)
      have := (pow_mem_unitFiltration_succ_iff hϖ hp hpe (by omega) hmem).mp
        (by rw [hup]; exact unitFiltration_antitone K (by omega) hw)
      simpa [add_assoc] using this
  simpa [show e + 1 + (k - (e + 1)) = k by omega] using hstep (k - (e + 1)) (by omega)

end GroundTheory.ProfCoh
end

