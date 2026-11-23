module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmul
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_mod (m v : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (m : ℂ)) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  conv_rhs => rw [← Nat.mod_add_div v m]
  push_cast
  have : 2 * Real.pi * Complex.I * ((v % m : ℕ) + (m : ℂ) * (v / m : ℕ)) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ) + ((v / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_smul (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) (h : Kum X l n x χ) :
    Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hrel⟩ := h
  set k := (PadicInt.toZModPow n c).val with hk
  refine ⟨f ^ k, fun z => a z ^ k, fun z => b z ^ k, M, hM, ?_, ⟨ha.pow k, hb.pow k, ?_, ?_⟩, ?_⟩
  · rw [map_smul, hx, ((_root_.GlobalTheory.KZ.H3.cls_props Ω ε X l n).2.2.2.2.1 c f)]
  · intro h0
    apply hb0
    have e1 := ((_root_.GlobalTheory.KZ.Germ.main).1 (fun z => b z ^ k) (fun _ => 0) (hb.pow k) (differentiableOn_const 0)).1 h0
    have e2 : ∀ z ∈ Hs, b z = 0 := fun z hz => (pow_eq_zero_iff' (M₀ := ℂ)).1 (e1 z hz) |>.1
    exact ((_root_.GlobalTheory.KZ.Germ.main).1 b (fun _ => 0) hb (differentiableOn_const 0)).2 e2
  · have e : ∀ (g : ℂ → ℂ), ((fun z => g z ^ k : ℂ → ℂ) : Mero) = (g : Mero) ^ k := fun g => rfl
    rw [e, e, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, mul_comm k, pow_mul, ← mul_pow, hr, ← pow_mul, ← pow_mul,
      mul_comm k]
  · intro δ hδ z hz
    have hl : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    haveI : NeZero (l ^ n) := ⟨hl.ne'⟩
    simp only
    rw [← mul_pow, hrel δ hδ z hz, mul_pow, mul_pow, ZMod.val_mul]
    push_cast
    have em := exp_val_mod (l ^ n) (k * (χ δ).val) hl
    push_cast at em
    rw [em, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculus
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue

section Calc

variable {Ω : Type} [Field Ω]

def DvA (A : ValuationSubring Ω) (l n : ℕ) (D : HahnSeries ℚ Ω) : Prop :=
  ∀ r, ∃ z ∈ A, D.coeff r = (l : Ω) ^ n * z

theorem coeffA_mul (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hQ : ∀ r, Q.coeff r ∈ A) (r : ℚ) : (P * Q).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => x ∈ A) (fun x y hx hy => add_mem hx hy) (zero_mem A)
    (fun ij _ => mul_mem (hP _) (hQ _))

theorem dvA_mul (A : ValuationSubring Ω) (l n : ℕ) (P D : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hD : DvA A l n D) : DvA A l n (P * D) := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = (l : Ω) ^ n * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, add_mem hz hw, by ring⟩
  · exact ⟨0, (zero_mem A), by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hD ij.2
    exact ⟨P.coeff ij.1 * z, mul_mem (hP _) hz, by rw [e]; ring⟩

theorem dvA_add (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω) (hD : DvA A l n D)
    (hE : DvA A l n E) : DvA A l n (D + E) := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  exact ⟨z + w, add_mem hz hw, by rw [HahnSeries.coeff_add, e, e']; ring⟩

theorem cgA_iff (A : ValuationSubring Ω) (l n : ℕ) (P Q : HahnSeries ℚ Ω) :
    (∀ r, CgA A l n (P.coeff r) (Q.coeff r)) ↔ DvA A l n (P - Q) := by
  simp only [CgA, DvA, HahnSeries.coeff_sub]

end Calc

theorem isDl_calc : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  intro Ω _ _ _ ε X _ l _ A _ n s f g φ ψ
  have lei := fun P Q => (_root_.GlobalTheory.Glue.theta_leibniz_add_const (Ω := Ω) s P Q).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ ⟨hψ, a2, b2, κ2, hκ2, hgb, hpa2, hpb2, hc2⟩
    refine ⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hψ r),
      a * a2, b * b2, κ * κ2, mul_ne_zero hκ hκ2, ?_, ?_, ?_, ?_⟩
    · calc f * g * (b * b2) = (f * b) * (g * b2) := by ring
        _ = _ := by rw [hfb, hgb, map_mul]; ring
    · rw [map_mul]; exact _root_.GlobalTheory.Glue.Prim.mul A _ _ hpa hpa2
    · rw [map_mul]; exact _root_.GlobalTheory.Glue.Prim.mul A _ _ hpb hpb2
    · rw [cgA_iff] at hc hc2 ⊢
      rw [map_mul, map_mul, lei, lei]
      have key : (φ + ψ) * (X.exp a * X.exp a2) * (X.exp b * X.exp b2) -
          ((theta s (X.exp a) * X.exp a2 + X.exp a * theta s (X.exp a2)) * (X.exp b * X.exp b2) -
            X.exp a * X.exp a2 * (theta s (X.exp b) * X.exp b2 + X.exp b * theta s (X.exp b2))) =
          (X.exp a2 * X.exp b2) * (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) +
          (X.exp a * X.exp b) * (ψ * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) := by
        ring
      rw [key]
      exact dvA_add A l n _ _ (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa2.1 hpb2.1) hc)
        (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa.1 hpb.1) hc2)
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    have hf : f ≠ 0 := by
      rintro rfl
      have ha : a = 0 := by
        have : algebraMap Ω X.K κ * a = 0 := by rw [← hfb, zero_mul]
        rcases mul_eq_zero.mp this with h | h
        · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).mp h) hκ
        · exact h
      obtain ⟨r, hr, _⟩ := hpa.2
      exact hr (by rw [ha, map_zero, HahnSeries.coeff_zero])
    refine ⟨fun r => by rw [HahnSeries.coeff_neg]; exact neg_mem (hφ r), b, a, κ⁻¹, inv_ne_zero hκ, ?_, hpb, hpa, ?_⟩
    · have hk : algebraMap Ω X.K κ ≠ 0 := (map_ne_zero _).mpr hκ
      rw [map_inv₀]
      field_simp
      rw [mul_comm, hfb]
    · rw [cgA_iff] at hc ⊢
      have key : -φ * X.exp b * X.exp a - (theta s (X.exp b) * X.exp a - X.exp b * theta s (X.exp a)) =
          -(φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by ring
      rw [key]
      intro r
      obtain ⟨z, hz, e⟩ := hc r
      exact ⟨-z, neg_mem hz, by rw [HahnSeries.coeff_neg, e]; ring⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ hψ hcg
    refine ⟨hψ, a, b, κ, hκ, hfb, hpa, hpb, ?_⟩
    rw [cgA_iff] at hc hcg ⊢
    have key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) =
        (-(X.exp a * X.exp b)) * (φ - ψ) + (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by
      ring
    rw [key]
    refine dvA_add A l n _ _ (dvA_mul A l n _ _ ?_ hcg) hc
    intro r
    rw [HahnSeries.coeff_neg]
    exact neg_mem (coeffA_mul A _ _ hpa.1 hpb.1 r)
  · intro κ hκ
    have hp1 : Prim A (X.exp 1) := by
      rw [map_one]
      refine ⟨fun r => ?_, 0, ?_, ?_⟩
      · rw [HahnSeries.coeff_one]; split_ifs <;> simp
      · simp [HahnSeries.coeff_one]
      · simp [HahnSeries.coeff_one]
    refine ⟨fun r => by simp, 1, 1, κ, hκ, by simp, hp1, hp1, fun r => ⟨0, (zero_mem A), ?_⟩⟩
    simp
  · rintro n' hn ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    refine ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨(l : Ω) ^ (n - n') * z, mul_mem (pow_mem (natCast_mem A l) _) hz, ?_⟩
    rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hn]

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruence
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KumHom

theorem germ_zero_of_vanish {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : ∀ z ∈ Hs, b z = 0) :
    (b : Mero) = 0 :=
  (_root_.GlobalTheory.KZ.Germ.main.1 b (fun _ => 0) hb (differentiableOn_const 0)).2 h

theorem vanish_of_comp {b : ℂ → ℂ} (g : GQ) (h : ∀ z ∈ Hs, b (mob g z) = 0) : ∀ z ∈ Hs, b z = 0 := by
  intro w hw
  have h1 := _root_.GlobalTheory.KZ.mob_laws.2.1 g g⁻¹ w hw
  rw [mul_inv_cancel, _root_.GlobalTheory.KZ.mob_laws.2.2.1] at h1
  rw [h1]
  exact h _ (_root_.GlobalTheory.KZ.mob_laws.1 _ w hw)

theorem diff_comp {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (g : GQ) :
    DifferentiableOn ℂ (fun z => b (mob g z)) Hs :=
  hb.comp (_root_.GlobalTheory.KZ.mob_laws.2.2.2.1 g) (fun z hz => _root_.GlobalTheory.KZ.mob_laws.1 g z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem num_not_vanish {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {f : X.Kˣ} {a b : ℂ → ℂ} (h : IsRoot X m f a b) :
    ¬ ∀ z ∈ Hs, a z = 0 := by
  intro ha
  obtain ⟨hda, hdb, hb0, he⟩ := h
  rw [germ_zero_of_vanish hda ha, zero_pow hm.ne'] at he
  have hbm : (b : Mero) ^ m = 0 := by
    have := congrArg (X.an ((f⁻¹ : X.Kˣ) : X.K) * ·) he
    simp only [mul_zero, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this
    exact this
  have hdbm : DifferentiableOn ℂ (fun z => b z ^ m) Hs := hdb.pow m
  have h0 : ((fun z => b z ^ m : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := hbm
  have hz := (_root_.GlobalTheory.KZ.Germ.main.1 _ (fun _ => 0) hdbm (differentiableOn_const 0)).1 h0
  exact hb0 (germ_zero_of_vanish hdb fun z hz' => (pow_eq_zero_iff hm.ne').1 (hz z hz'))

end GlobalTheory.KZ.H3.KumHom

namespace GlobalTheory.KZ.H3.KumHom

theorem zmod_eq_of_exp {m : ℕ} [NeZero m] (u v w : ZMod m)
    (h : Complex.exp (2 * Real.pi * Complex.I * (u.val : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / (m : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (w.val : ℂ) / (m : ℂ))) : u = v + w := by
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : ((u.val : ℤ) : ℂ) = ((v.val + w.val + k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hk
  have hi : (u.val : ℤ) = v.val + w.val + k * m := Int.cast_injective hc
  have := congrArg (Int.cast : ℤ → ZMod m) hi
  push_cast at this
  simpa [ZMod.natCast_val, ZMod.cast_id', ZMod.natCast_self] using this

theorem kum_hom : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ,
    ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧
      ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  intro Ω _ _ ε X l _ n x χ hK
  obtain ⟨f, a, b, M, hM, -, hr, hrel⟩ := hK
  refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  set E : ZMod (l ^ n) → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / ((l : ℂ) ^ n)) with hE
  obtain ⟨hda, hdb, hb0, -⟩ := id hr
  set g := ofSL δ
  set g' := ofSL δ'
  have key : ∀ z ∈ Hs, ((E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) * (b (mob g (mob g' z)) * b (mob g' z)) = 0 := by
    intro z hz
    have h1 := hrel (δ * δ') (Subgroup.mul_mem _ hδ hδ') z hz
    rw [map_mul, _root_.GlobalTheory.KZ.mob_laws.2.1 _ _ z hz] at h1
    have h2 := hrel δ hδ (mob g' z) (_root_.GlobalTheory.KZ.mob_laws.1 _ z hz)
    have h3 := hrel δ' hδ' z hz
    simp only [hE]
    linear_combination (-b (mob g' z)) * h1 + b z * h2 +
      Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * b (mob g (mob g' z)) * h3
  have hA : DifferentiableOn ℂ (fun z => (E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) Hs :=
    (differentiableOn_const _).mul hda
  have hB : DifferentiableOn ℂ (fun z => b (mob g (mob g' z)) * b (mob g' z)) Hs := by
    refine DifferentiableOn.mul ?_ (diff_comp hdb g')
    have := diff_comp hdb (g * g')
    refine this.congr fun z hz => ?_
    simp only [_root_.GlobalTheory.KZ.mob_laws.2.1 g g' z hz]
  have hc : E (χ (δ * δ')) - E (χ δ) * E (χ δ') = 0 := by
    rcases _root_.GlobalTheory.KZ.Germ.main.2.1 _ _ hA hB key with h | h
    · by_contra hne
      exact num_not_vanish hpos hr fun z hz => (mul_eq_zero.1 (h z hz)).resolve_left hne
    · exfalso
      rcases _root_.GlobalTheory.KZ.Germ.main.2.1 _ _ (diff_comp (diff_comp hdb g) g') (diff_comp hdb g') h with h' | h'
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g (vanish_of_comp g' h')))
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g' h'))
  have := sub_eq_zero.1 hc
  simp only [hE] at this
  exact zmod_eq_of_exp _ _ _ (by exact_mod_cast this)

end GlobalTheory.KZ.H3.KumHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruence
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

namespace KumUniq

theorem gamma_mem_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

end KumUniq

open KumUniq

theorem kum_near : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  intro Ω _ _ ε X l _ n x χ χ' hK hK'
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := _root_.GlobalTheory.KZ.mob_laws
  obtain ⟨G1, G2, G3, -, G5⟩ := _root_.GlobalTheory.KZ.Germ.main
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hχ⟩ := hK
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hab'⟩, hχ'⟩ := hK'
  have hl : l.Prime := Fact.out
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨g, hfg⟩ := ((_root_.GlobalTheory.KZ.H3.cls_props Ω ε X l n).2.1 f f').1 (hx.symm.trans hx')
  obtain ⟨p, q, hp, hq, hq0, hpq⟩ := X.an_mero (g : X.K)
  obtain ⟨M'', hM'', hlev⟩ := X.level (g : X.K)

  have nz : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → ∃ z ∈ Hs, u z ≠ 0 := by
    intro u hu hu0
    by_contra hc
    push_neg at hc
    exact hu0 (((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 hc).trans Filter.Germ.coe_zero)

  have unz : ∀ (h : X.Kˣ) (u : ℂ → ℂ) (v : Mero) (k : ℕ), k ≠ 0 → X.an (h : X.K) * (u : Mero) ^ k = v →
      DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → v ≠ 0 := by
    intro h u v k hk heq hu hu0 hv0
    have h0 : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := by
      have e : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = (u : Mero) ^ k := Filter.Germ.coe_pow u k
      rw [e]
      calc (u : Mero) ^ k = X.an (((h⁻¹ : X.Kˣ) : X.K) * (h : X.K)) * (u : Mero) ^ k := by simp
        _ = X.an ((h⁻¹ : X.Kˣ) : X.K) * (X.an (h : X.K) * (u : Mero) ^ k) := by rw [map_mul, mul_assoc]
        _ = 0 := by rw [heq, hv0, mul_zero]
        _ = _ := Filter.Germ.coe_zero.symm
    have h1 := (G1 _ _ (hu.pow k) (differentiableOn_const 0)).1 h0
    apply hu0
    refine ((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 fun z hz => ?_).trans Filter.Germ.coe_zero
    exact pow_eq_zero_iff hk |>.1 (h1 z hz)

  have nzmul : ∀ u v : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ v Hs → (∃ z ∈ Hs, u z ≠ 0) →
      (∃ z ∈ Hs, v z ≠ 0) → ∃ z ∈ Hs, u z * v z ≠ 0 := by
    rintro u v hu hv ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
    by_contra hc
    push_neg at hc
    rcases G2 u v hu hv hc with h | h
    · exact h1 (h z1 hz1)
    · exact h2 (h z2 hz2)

  have hf : X.an (f : X.K) = X.an (f' : X.K) * X.an (g : X.K) ^ (l ^ n) := by
    rw [hfg, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  have key : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) =
      ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
    have e1 : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a : Mero) * b' * q) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    have e2 : ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a' : Mero) * b * p) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    rw [e1, e2, ← hpq]
    linear_combination (-((b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n))) * hab +
      ((b : Mero) ^ (l ^ n) * (b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hf +
      ((b : Mero) ^ (l ^ n) * (X.an (g : X.K)) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hab'
  have key' := (G1 _ _ (((ha.mul hb').mul hq).pow (l ^ n)) (((ha'.mul hb).mul hp).pow (l ^ n))).1 key
  obtain ⟨k, hk⟩ := G5 (l ^ n) (fun z => a z * b' z * q z) (fun z => a' z * b z * p z) hm
    ((ha.mul hb').mul hq) ((ha'.mul hb).mul hp) key'

  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (g : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (g : X.K)) (p := fun F => ∃ φ : ℂ → ℂ, F = (φ : Mero)) fun φ => ⟨φ, rfl⟩
  have hmap : ∀ γ : SL(2, ℤ), Set.MapsTo (mob (ofSL γ)) Hs Hs := fun γ z hz => hH _ z hz
  have hpqδ : ∀ δ ∈ CongruenceSubgroup.Gamma M'', ∀ z ∈ Hs,
      p (mob (ofSL δ) z) * q z = p z * q (mob (ofSL δ) z) := by
    intro δ hδ
    have h1 : (φ : Mero) = ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by
      rw [← hφ, ← X.an_sl (ofSL δ) _ φ hφ, hlev δ hδ]
    have h2 : ((fun z => φ z * q z : ℂ → ℂ) : Mero) = (p : Mero) := by
      rw [← hpq, hφ]; exact Filter.Germ.coe_mul φ q
    have h3 := G3 (ofSL δ) _ _ h2
    have e3 : ((fun z => φ (mob (ofSL δ) z) * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) :=
      Filter.Germ.coe_mul _ _
    have h2' : (φ : Mero) * (q : Mero) = (p : Mero) := by rw [← h2]; exact (Filter.Germ.coe_mul φ q).symm
    have h3' : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by rw [← e3]; exact h3
    have hpδ : DifferentiableOn ℂ (fun z => p (mob (ofSL δ) z)) Hs := hp.comp (hdiff _) (hmap δ)
    have hqδ : DifferentiableOn ℂ (fun z => q (mob (ofSL δ) z)) Hs := hq.comp (hdiff _) (hmap δ)
    refine (G1 (fun z => p (mob (ofSL δ) z) * q z) (fun z => p z * q (mob (ofSL δ) z))
      (hpδ.mul hq) (hp.mul hqδ)).1 ?_
    have e4 : ((fun z => p (mob (ofSL δ) z) * q z : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * (q : Mero) := Filter.Germ.coe_mul _ _
    have e5 : ((fun z => p z * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        (p : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := Filter.Germ.coe_mul _ _
    rw [e4, e5]
    linear_combination (-((q : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero))) * h1 +
      ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * h2' + (-(q : Mero)) * h3'

  refine ⟨M * M' * M'', by positivity, fun δ hδ => ?_⟩
  have hδ1 : δ ∈ CongruenceSubgroup.Gamma M :=
    gamma_mem_of_dvd (Dvd.intro (M' * M'') (by ring)) hδ
  have hδ2 : δ ∈ CongruenceSubgroup.Gamma M' :=
    gamma_mem_of_dvd (Dvd.intro (M * M'') (by ring)) hδ
  have hδ3 : δ ∈ CongruenceSubgroup.Gamma M'' := gamma_mem_of_dvd (Dvd.intro_left (M * M') rfl) hδ
  set e1 := Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) with he1
  set e2 := Complex.exp (2 * Real.pi * Complex.I * ((χ' δ).val : ℂ) / ((l : ℂ) ^ n)) with he2
  set ζ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) with hζ
  have hP : ∀ z ∈ Hs, (e1 - e2) * (a z * a' z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) *
      p (mob (ofSL δ) z) * q z) = 0 := by
    intro z hz
    have hw := hH (ofSL δ) z hz
    have K1 := hχ δ hδ1 z hz
    have K2 := hχ' δ hδ2 z hz
    have K3 := hpqδ δ hδ3 z hz
    have Dz : a z * b' z * q z = ζ * (a' z * b z * p z) := hk z hz
    have Dw : a (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) =
        ζ * (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) := hk _ hw
    linear_combination (a' z * b z * p z) * Dw
      - (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * Dz
      - (b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) * a' z * p z) * K1
      + e1 * (a z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * a' z) * K3
      + (a z * q z * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * K2

  have nzδ : ∀ u : ℂ → ℂ, (∃ z ∈ Hs, u z ≠ 0) → ∃ z ∈ Hs, u (mob (ofSL δ) z) ≠ 0 := by
    rintro u ⟨z, hz, hu⟩
    refine ⟨mob (ofSL δ⁻¹) z, hH _ z hz, ?_⟩
    rwa [← hmul _ _ z hz, ← map_mul, mul_inv_cancel, map_one, hone]
  have dδ : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ (fun z => u (mob (ofSL δ) z)) Hs :=
    fun u hu => hu.comp (hdiff _) (hmap δ)
  have na : ∃ z ∈ Hs, a z ≠ 0 := nz a ha fun h0 => unz f b _ (l ^ n) hm.ne' hab hb hb0 (by rw [h0, zero_pow hm.ne'])
  have na' : ∃ z ∈ Hs, a' z ≠ 0 := nz a' ha' fun h0 => unz f' b' _ (l ^ n) hm.ne' hab' hb' hb0' (by rw [h0, zero_pow hm.ne'])
  have np : ∃ z ∈ Hs, p z ≠ 0 := nz p hp (unz g q _ 1 one_ne_zero (by rw [pow_one]; exact hpq) hq hq0)
  obtain ⟨z0, hz0, hne⟩ := nzmul _ _ ((((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')).mul (dδ p hp)) hq
    (nzmul _ _ (((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')) (dδ p hp)
      (nzmul _ _ ((ha.mul ha').mul (dδ b hb)) (dδ b' hb')
        (nzmul _ _ (ha.mul ha') (dδ b hb) (nzmul _ _ ha ha' na na') (nzδ b (nz b hb hb0)))
        (nzδ b' (nz b' hb' hb0'))) (nzδ p np)) (nz q hq hq0)
  have he : e1 = e2 := by
    rcases mul_eq_zero.1 (hP z0 hz0) with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne

  haveI : NeZero (l ^ n) := ⟨hm.ne'⟩
  have hprim := Complex.isPrimitiveRoot_exp (l ^ n) hm.ne'
  have ex : ∀ v : ℕ, Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ n)) =
      (Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ))) ^ v := by
    intro v
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  apply ZMod.val_injective (l ^ n)
  exact hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← ex, ← ex]; exact he)

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZeroStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_nonunits_pow_modEq_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ x ∈ A.nonunits, ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  first | exact @GlobalTheory.cgA_pow_of_mem_nonunits | exact GlobalTheory.cgA_pow_of_mem_nonunits | (intros; apply GlobalTheory.cgA_pow_of_mem_nonunits <;> assumption)
end

