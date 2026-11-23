module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchange
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem eq_zero_of_sum_joint_eigenvectors {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ) (hl : ∀ i j, i ≠ j → ∃ k, l i k ≠ l j k)
    (s : Finset ι) : ∀ u : ι → M, (∀ i k, T k (u i) = l i k • u i) → ∑ i ∈ s, u i = 0 →
      ∀ i ∈ s, u i = 0 := by
  first
  | exact @_root_.GlobalTheory.ComplexValueBound.main
  | exact _root_.GlobalTheory.ComplexValueBound.main
  | (apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplexValueBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplexValueBound.main ..)

theorem root_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  intro G _ _ M _ _ _ ρ B X Y χ hXB hBX hc hsep n v hv hvi
  have hmul : ∀ (g h : G) (m : M), ρ (g * h) m = ρ g (ρ h m) := fun g h m => by
    rw [map_mul]; rfl
  let S : M →ₗ[ℂ] M := ∑ x : X, ρ (x : G)
  have hS : ∀ m, S m = ∑ x : X, ρ (x : G) m := fun m => by
    simp only [S, LinearMap.sum_apply]
  have hinj : ∀ m : M, (∀ b ∈ B, ρ b m = χ b • m) → (∀ y ∈ Y, ρ y m = m) → S m = 0 → m = 0 := by
    intro m hb hy h0
    rw [hS] at h0
    have := eq_zero_of_sum_joint_eigenvectors (ι := X) (κ := Y) (fun y => ρ (y : G))
      (fun x y => χ ((y : G)⁻¹ * (x : G)⁻¹ * y * x))
      (fun x x' hne => by
        obtain ⟨y, hyY, h⟩ := hsep x x.2 x' x'.2 (fun h => hne (Subtype.ext h))
        exact ⟨⟨y, hyY⟩, h⟩) Finset.univ (fun x => ρ (x : G) m)
      (fun x y => by
        have e : (y : G) * x = x * (y * ((y : G)⁻¹ * (x : G)⁻¹ * y * x)) := by group
        show ρ (y : G) (ρ (x : G) m) = _
        rw [← hmul, e, hmul, hmul, hb _ (hc x x.2 y y.2), map_smul, hy y y.2, map_smul]) h0
      1 (Finset.mem_univ _)
    simpa using this
  refine ⟨fun i => S (v i), ?_, fun i => ⟨fun b hb => ?_, fun x hx => ?_⟩⟩
  · rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg
    apply hv g
    apply hinj
    · intro b hb
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).1 b hb, smul_comm]
    · intro y hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).2 y hy]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul] using hg
  · choose f hf g hg hfg hχ using hBX b hb
    let F : X → X := fun x => ⟨f x x.2, hf x x.2⟩
    have hF : Function.Injective F := by
      intro x1 x2 h
      have h' : f x1 x1.2 = f x2 x2.2 := congrArg Subtype.val h
      have e1 := hfg x1 x1.2
      have e2 := hfg x2 x2.2
      rw [← h'] at e2
      have e : (x1 : G)⁻¹ * x2 = (g x1 x1.2)⁻¹ * g x2 x2.2 := by
        calc (x1 : G)⁻¹ * x2 = (b * x1)⁻¹ * (b * x2) := by group
          _ = _ := by rw [e1, e2]; group
      have := hXB _ (X.mul_mem (X.inv_mem x1.2) x2.2)
        (e ▸ B.mul_mem (B.inv_mem (hg x1 x1.2)) (hg x2 x2.2))
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have hB : Function.Bijective F := Finite.injective_iff_bijective.1 hF
    show ρ b (S (v i)) = χ b • S (v i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective F hB _ _ fun x => ?_
    rw [← hmul, hfg x x.2, hmul, (hvi i).1 _ (hg x x.2), hχ, map_smul]
  · show ρ x (S (v i)) = S (v i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X)) _ _ fun z => ?_
    rw [← hmul]; rfl

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueAlgebraicPolynomialDivisible
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_int_poly_root_mod_p : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  intro p hpf Ωl _ _ hC v hv _ y b hy hyv hyb
  haveI : CharZero Ωl := Basic.charZero_of_isClo hC
  obtain ⟨P0, hP0, hP0y⟩ := hy
  have hprim : P0.primPart.IsPrimitive := Polynomial.isPrimitive_primPart P0
  have hPy : aeval y P0.primPart = 0 := by
    have e := P0.eq_C_content_mul_primPart
    have hc : P0.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
    rw [e, map_mul, aeval_C] at hP0y
    rcases mul_eq_zero.1 hP0y with h | h
    · exact absurd (by simpa using h) hc
    · exact h
  refine ⟨P0.primPart, ?_, ?_⟩
  · intro h0
    have hd : ∀ n, (p : ℤ) ∣ P0.primPart.coeff n := by
      intro n
      have := congrArg (fun Q => Q.coeff n) h0
      simp only [coeff_map, coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    have hu := hprim (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).2 hd)
    have := Int.isUnit_iff.1 hu
    have h2 := hpf.out.two_le
    omega
  · set P := P0.primPart
    set b' := algebraMap (O0 p) Ωl b
    have hb' : v b' ≤ 1 := (hv b').2 isIntegral_algebraMap
    let yi : v.integer := ⟨y, hyv⟩
    let bi : v.integer := ⟨b', hb'⟩
    obtain ⟨d, hd⟩ := Polynomial.sub_dvd_eval_sub yi bi (P.map (Int.castRingHom v.integer))
    have hev : ∀ z : v.integer, v.integer.subtype ((P.map (Int.castRingHom v.integer)).eval z) = aeval (z : Ωl) P := by
      intro z
      rw [Polynomial.eval_map, aeval_def]
      have := Polynomial.hom_eval₂ P (Int.castRingHom v.integer) v.integer.subtype z
      rw [show v.integer.subtype.comp (Int.castRingHom v.integer) = algebraMap ℤ Ωl from RingHom.ext_int _ _] at this
      exact this
    have hd' := congrArg v.integer.subtype hd
    rw [map_sub, map_mul, map_sub, hev, hev] at hd'
    have hd'' : aeval y P - aeval b' P = (y - b') * (d : Ωl) := hd'
    have hkey : aeval b' P = -((y - b') * (d : Ωl)) := by
      rw [← hd'', hPy]; ring
    have hmap : algebraMap (O0 p) Ωl (aeval b P) = aeval b' P := by
      rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_int _ _
    have hlt : v (algebraMap (O0 p) Ωl (aeval b P)) < 1 := by
      rw [hmap, hkey, Valuation.map_neg, Valuation.map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hyb d.2
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have hnu : ¬ IsUnit (aeval b P) := by
      rintro ⟨u, hu⟩
      have h1 : v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) ≤ 1 := (hv _).2 isIntegral_algebraMap
      have h2 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, Valuation.map_one]
      have h3 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left zero_le' hlt h1
      rw [h2] at h3
      exact lt_irrefl _ h3
    have hm : aeval b P ∈ IsLocalRing.maximalIdeal (O0 p) := hnu
    rw [hmax, Ideal.mem_span_singleton] at hm
    exact hm

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SgDistribution
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.SiegDist

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_int_mul (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_int_mul]; ring_nf

lemma ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_nat_mul]; ring_nf

lemma ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, ← Real.exp_zero, Real.exp_lt_exp]
  have := mul_pos Real.pi_pos τ.im_pos
  linarith

lemma ee_eq_one (u v : ℚ) (τ : ℍ) (h : ee ((u : ℂ) * τ + v) = 1) : u = 0 ∧ ∃ k : ℤ, v = k := by
  unfold ee at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (u : ℂ) * τ + v = k := by
    apply mul_left_cancel₀ hne
    rw [hk]; ring
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hu : u = 0 := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hu
  simp at hre
  exact ⟨rfl, k, by exact_mod_cast hre⟩

theorem sg_distribution : ∀ (c m : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ = sg c x τ := by
  intro c m x τ hA hm hcm
  obtain ⟨hc1, hc6, hnot⟩ := hA
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq0 : ee (τ : ℂ) ≠ 0 := ee_ne_zero _
  have hsplit : ∀ a b : ℕ, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = cth c (ee (τ : ℂ)) (ee ((((x 0 : ℂ) + a) * τ + x 1) / m) * ee ((b : ℂ) / m)) := by
    intro a b
    unfold sg
    rw [← ee_add]
    congr 2
    simp [pt]
    field_simp
    ring
  have hpow : ∀ a : ℕ, ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ m = ee (pt x τ) * ee (τ : ℂ) ^ a := by
    intro a
    rw [← ee_nat_mul, ← ee_nat_mul, ← ee_add]
    congr 1
    simp only [pt]
    field_simp
    ring
  have hND : ∀ n : ℤ, ee (τ : ℂ) ^ n * ee (pt x τ) ^ c ≠ 1 := by
    intro n h
    have h' : ee ((((n : ℚ) + c * x 0 : ℚ) : ℂ) * τ + ((c * x 1 : ℚ) : ℂ)) = 1 := by
      rw [← h, ← ee_int_mul, ← ee_nat_mul, ← ee_add]
      congr 1; simp only [pt]; push_cast; ring
    obtain ⟨h0, k, hk⟩ := ee_eq_one _ _ τ h'
    apply hnot
    refine ⟨⟨-n, ?_⟩, ⟨k, hk.symm⟩⟩
    push_cast; linarith
  have hD1 : ∀ a : ℕ, ∀ n : ℤ, ee (τ : ℂ) ^ n * ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ (c * m) ≠ 1 := by
    intro a n h
    rw [mul_comm c m, pow_mul, hpow a, mul_pow, ← pow_mul] at h
    apply hND (n + ((a * c : ℕ) : ℤ))
    rw [zpow_add₀ hq0, zpow_natCast, ← h]
    ring
  calc ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = ∏ a ∈ Finset.range m, cth c (ee (τ : ℂ) ^ m) (ee (pt x τ) * ee (τ : ℂ) ^ a) := by
        apply Finset.prod_congr rfl
        intro a _
        simp_rw [hsplit a]
        rw [_root_.GlobalTheory.Sieg.prod_cth_mul_ee c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) (hD1 a), hpow a]
    _ = cth c (ee (τ : ℂ)) (ee (pt x τ)) :=
        _root_.GlobalTheory.Sieg.prod_cth_mul_pow c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) hND
    _ = sg c x τ := rfl

end GlobalTheory.SiegDist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.EpsProj

variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}

omit [Fintype G] in
theorem pow_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (n : ℕ) :
    S (u ^ n) ∧ χ (u ^ n) = χ u ^ n := by
  induction n with
  | zero => simp [h1, c1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩

theorem inv_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) :
    S u⁻¹ ∧ χ u⁻¹ = (χ u)⁻¹ ∧ ‖χ u‖ = 1 := by
  have hc : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hi : u⁻¹ = u ^ (Fintype.card G - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]
  have hS : S u⁻¹ := by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1
  refine ⟨hS, ?_, ?_⟩
  · have := cm _ _ hu hS
    rw [mul_inv_cancel, c1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  · have := (pow_spec h1 hm c1 cm hu (Fintype.card G)).2
    rw [pow_card_eq_one, c1] at this
    exact Complex.norm_eq_one_of_pow_eq_one this.symm hc

theorem eps_mul (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by
  obtain ⟨hi, ci, -⟩ := inv_spec h1 hm c1 cm hu
  unfold eps
  by_cases hy : S y
  · rw [if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]
  · have : ¬ S (u⁻¹ * y) := fun h => hy (by simpa using hm _ _ hu h)
    rw [if_neg hy, if_neg this, mul_zero]

omit [Group G] in
theorem sum_ite_card : ∑ y, (if S y then (1 : ℂ) else 0) = (Nat.card {u // S u} : ℂ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_eps_chi (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) :
    ∑ y, eps S χ y * χ y = 1 := by
  haveI : Nonempty {u // S u} := ⟨⟨1, h1⟩⟩
  have hc : (Nat.card {u // S u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∀ y, eps S χ y * χ y = (if S y then (1 : ℂ) else 0) / (Nat.card {u // S u} : ℂ) := by
    intro y
    unfold eps
    by_cases hy : S y
    · have hn : χ y ≠ 0 := by
        intro h
        have := (inv_spec h1 hm c1 cm hy).2.2
        rw [h] at this
        simp at this
      rw [if_pos hy, if_pos hy]
      field_simp
    · simp [hy]
  simp_rw [this]
  rw [← Finset.sum_div, sum_ite_card, div_self hc]

theorem isProj_eps (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by
  refine ⟨?_, ?_⟩
  · funext x
    unfold conv
    have : ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x := by
      intro y
      by_cases hy : S y
      · rw [eps_mul h1 hm c1 cm hy, mul_assoc]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]
  · intro x
    unfold eps
    by_cases hx : S x
    · obtain ⟨hi, ci, hn⟩ := inv_spec h1 hm c1 cm hx
      rw [if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]
    · have : ¬ S x⁻¹ := fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)
      rw [if_neg hx, if_neg this, map_zero]

theorem mem_range_iff {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) (x : M) :
    x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x := by
  constructor
  · rintro ⟨z, rfl⟩ u hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_
    have := eps_mul h1 hm c1 cm hu (u * y)
    rw [inv_mul_cancel_left] at this
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
    rw [← this]
  · intro h
    refine ⟨x, ?_⟩
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply]
    have : ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x := by
      intro y
      by_cases hy : S y
      · rw [h y hy, smul_smul]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]

theorem eps_spec : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  intro G _ _ M _ _ _ ρ S χ h1 hm c1 cm
  refine ⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩
  · simp only [eps, if_pos h1, c1, inv_one, one_div]
  · intro n x hx h
    have hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ)) :=
      fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)
    have hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ)))) :=
      LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx
    simpa [rk] using hli.fintype_card_le_finrank

end GlobalTheory.BadShare.EpsProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem hahnSeries_order_eq_neg_one_of_coeff {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (h0 : ∀ r : ℚ, r < -1 → h.coeff r = 0) : h.order = -1 := by
  have h1' : h.coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_
  exact le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

theorem hahnSeries_pow_order_of_order_neg_one {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (ho : h.order = -1) (n : ℕ) :
    (h ^ n).order = -(n : ℚ) ∧ (h ^ n).coeff (-(n : ℚ)) = 1 := by
  have hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ) := fun k => by
    rw [HahnSeries.order_pow, ho]
    simp
  refine ⟨hord n, ?_⟩
  induction n with
  | zero => simp
  | succ k ih =>

    have hm := HahnSeries.coeff_mul_order_add_order (h ^ k) h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one] at hm
    have e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1 := by push_cast; ring
    rw [pow_succ, e, hm]

private theorem hahnSeries_coeff_algebra_smul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (r : Ω) (y : HahnSeries ℚ Ω) (a : ℚ) :
    (@HSMul.hSMul Ω (HahnSeries ℚ Ω) (HahnSeries ℚ Ω) (@instHSMul _ _ Algebra.toSMul) r y).coeff a =
      r * y.coeff a := by
  rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

theorem Tower.jK_transcendental {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  unfold Transcendental IsAlgebraic
  rintro ⟨p, hp0, hp⟩
  obtain ⟨h1, h0, -⟩ := X.j_exp
  have ho := hahnSeries_order_eq_neg_one_of_coeff h1 h0
  have hz : Polynomial.aeval (X.exp X.jK) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hp, map_zero]

  have hc : (Polynomial.aeval (X.exp X.jK) p).coeff (-(p.natDegree : ℚ)) = p.leadingCoeff := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single p.natDegree]
    · rw [hahnSeries_coeff_algebra_smul, (hahnSeries_pow_order_of_order_neg_one h1 ho _).2, mul_one]
      rfl
    · intro i hi hne
      have hlt : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      have hlt' : (i : ℚ) < p.natDegree := by exact_mod_cast hlt
      rw [hahnSeries_coeff_algebra_smul, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahnSeries_pow_order_of_order_neg_one h1 ho i).1]
      linarith
    · intro hn
      exact absurd (Finset.self_mem_range_succ _) hn
  rw [hz, HahnSeries.coeff_zero] at hc
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hc.symm)

end GlobalTheory.KZ
end

