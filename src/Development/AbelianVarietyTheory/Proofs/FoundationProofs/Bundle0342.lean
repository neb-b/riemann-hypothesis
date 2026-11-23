module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitOfForallMaximal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.OddInvolution

theorem exists_pos_pow_idem {M : Type} [Monoid M] [Finite M] (x : M) :
    ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
  have key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
    intro i d hd h
    have h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k) := by
      intro t k
      induction t with
      | zero => simp
      | succ t ih =>
        have : i + k + (t + 1) * d = (i + d) + (k + t * d) := by ring
        rw [this, pow_add, h, ← pow_add, ← add_assoc, ih]
    have hle : i ≤ (i + 1) * d := by nlinarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    have := h1 (i + 1) k
    rw [← hk] at this
    exact this
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
  · exact key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

theorem pow_idem_field {F : Type} [Field F] {u : F} {m : ℕ} (hm : 0 < m)
    (he : IsIdempotentElem (u ^ m)) : (u = 0 → u ^ m = 0) ∧ (u ≠ 0 → u ^ m = 1) := by
  refine ⟨fun h => by rw [h, zero_pow hm.ne'], fun h => ?_⟩
  have h2 : u ^ m * u ^ m = u ^ m * 1 := by rw [mul_one]; exact he
  exact mul_left_cancel₀ (pow_ne_zero _ h) h2

theorem isUnit_of_forall_maximal {R : Type} [CommRing R] {s : R}
    (h : ∀ m : Ideal R, m.IsMaximal → Ideal.Quotient.mk m s ≠ 0) : IsUnit s := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := exists_max_ideal_of_mem_nonunits (show s ∈ nonunits R from hs)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.mpr hsm)

theorem exists_anticommuting {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R))
    (a b c : R) (h : a * a + b * c = 1) :
    ∃ p q r : R, IsUnit (p * p + q * r) ∧ 2 * a * p + b * r + c * q = 0 := by
  obtain ⟨n1, hn1, he1⟩ := exists_pos_pow_idem (b * c)
  obtain ⟨n2, hn2, he2⟩ := exists_pos_pow_idem ((b + c) ^ 2 + 4 * a ^ 2)
  set e1 := (b * c) ^ n1 with he1d
  set e2 := ((b + c) ^ 2 + 4 * a ^ 2) ^ n2 with he2d
  refine ⟨(1 - e1) * e2 * (b + c) + (1 - e1) * (1 - e2) * (b - c),
    e1 * b + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (2 * a),
    e1 * (-c) + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (-2 * a), ?_, by ring⟩
  apply isUnit_of_forall_maximal
  intro m hm
  letI := Ideal.Quotient.field m
  have h2' : Ideal.Quotient.mk m (2 : R) ≠ 0 := (h2.map (Ideal.Quotient.mk m)).ne_zero
  have hh := congrArg (Ideal.Quotient.mk m) h
  have q1 : Ideal.Quotient.mk m e1 = (Ideal.Quotient.mk m (b * c)) ^ n1 := by rw [he1d, map_pow]
  have q2 : Ideal.Quotient.mk m e2 = (Ideal.Quotient.mk m ((b + c) ^ 2 + 4 * a ^ 2)) ^ n2 := by
    rw [he2d, map_pow]
  have k1 := pow_idem_field hn1 (q1 ▸ he1.map (Ideal.Quotient.mk m))
  have k2 := pow_idem_field hn2 (q2 ▸ he2.map (Ideal.Quotient.mk m))
  rw [← q1] at k1
  rw [← q2] at k2
  simp only [map_add (f := _), map_mul, map_sub, map_one, map_neg, map_pow, map_ofNat] at hh k1 k2 h2' ⊢
  generalize Ideal.Quotient.mk m e1 = E1 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m e2 = E2 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m a = A at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m b = B at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m c = C at hh k1 k2 ⊢
  have h8 : (2 : R ⧸ m) * 2 * 2 ≠ 0 := by simp [h2']
  by_cases hBC : B * C = 0
  · rw [k1.1 hBC]
    by_cases hU : (B + C) ^ 2 + 4 * A ^ 2 = 0
    · rw [k2.1 hU]
      intro hz
      apply h8
      linear_combination -hz + hU - 8 * hh + 4 * hBC
    · rw [k2.2 hU]
      intro hz
      apply hU
      linear_combination hz
  · rw [k1.2 hBC]
    intro hz
    apply hBC
    linear_combination -hz

theorem exists_swap {R : Type} [CommRing R] [Finite R] (X : Matrix (Fin 2) (Fin 2) R)
    (h2 : IsUnit (2 : R)) (hdet : X.det = -1) (htr : X.trace = 0) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) R) (s : R), IsUnit s ∧ Y * Y = s • (1 : Matrix (Fin 2) (Fin 2) R) ∧
      X * Y = -(Y * X) := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hd : X 1 1 = -X 0 0 := by linear_combination htr
  have h : X 0 0 * X 0 0 + X 0 1 * X 1 0 = 1 := by
    rw [hd] at hdet; linear_combination -hdet
  obtain ⟨p, q, r, hs, hanti⟩ := exists_anticommuting h2 (X 0 0) (X 0 1) (X 1 0) h
  refine ⟨!![p, q; r, -p], p * p + q * r, hs, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd, Matrix.vecMul, dotProduct] <;>
      first | linear_combination hanti | ring

theorem card_fixed_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) (h2 : IsUnit (2 : R)) (hXX : X * X = 1) (hdet : X.det = -1)
    (htr : X.trace = 0) : Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R := by
  obtain ⟨Y, s, hs, hYY, hXY⟩ := exists_swap X h2 hdet htr
  have hXXv : ∀ v : Fin 2 → R, X *ᵥ (X *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
  have hYYv : ∀ v : Fin 2 → R, Y *ᵥ (Y *ᵥ v) = s • v := fun v => by
    rw [Matrix.mulVec_mulVec, hYY]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  have hXYv : ∀ v : Fin 2 → R, X *ᵥ (Y *ᵥ v) = -(Y *ᵥ (X *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, hXY, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  have hsu : ((hs.unit⁻¹ : Rˣ) : R) * s = 1 := by simp
  let e : {v : Fin 2 → R // X *ᵥ v = v} ≃ {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => ⟨Y *ᵥ v.1, by rw [hXYv, v.2]⟩
      invFun := fun w => ⟨((hs.unit⁻¹ : Rˣ) : R) • (Y *ᵥ w.1), by
        rw [Matrix.mulVec_smul, hXYv, w.2, Matrix.mulVec_neg, neg_neg]⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp only [hYYv, smul_smul, hsu, one_smul]
      right_inv := fun w => by
        apply Subtype.ext
        simp only [Matrix.mulVec_smul, hYYv, smul_smul, hsu, one_smul] }
  have ht : ((h2.unit⁻¹ : Rˣ) : R) * 2 = 1 := by simp
  set t : R := ((h2.unit⁻¹ : Rˣ) : R)
  let f : (Fin 2 → R) ≃ {v : Fin 2 → R // X *ᵥ v = v} × {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => (⟨t • (v + X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_add, hXXv, add_comm]⟩,
        ⟨t • (v - X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hXXv, ← smul_neg, neg_sub]⟩)
      invFun := fun pq => pq.1.1 + pq.2.1
      left_inv := fun v => by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        linear_combination (v i) * ht
      right_inv := fun pq => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
        ext i
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            smul_eq_mul]
          linear_combination (p i) * ht
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            Pi.sub_apply, smul_eq_mul]
          linear_combination (q i) * ht }
  have h1 : Nat.card (Fin 2 → R) =
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = -v} := by
    rw [Nat.card_congr f, Nat.card_prod]
  have h3 : Nat.card (Fin 2 → R) = Nat.card R * Nat.card R := by
    rw [Nat.card_fun]; simp [sq]
  have hsq : Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = v} =
      Nat.card R * Nat.card R := by
    rw [← h3, h1, Nat.card_congr e]
  exact Nat.mul_self_inj.mp hsq

theorem card_fixed (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) : IsUnit (2 : R) → X * X = 1 → X.det = -1 → X.trace = 0 →
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R :=
  fun h2 hXX hdet htr => card_fixed_eq l R X h2 hXX hdet htr

end GlobalTheory.OddInvolution
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevels
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocChar

private def repOverZMod {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (N : ℕ)
    [Module (ZMod N) M] (ρ : Representation O Γ M) : Representation (ZMod N) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap N
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul, Module.End.mul_apply]

theorem local_character_h1_bound : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  open Formalism.GaloisCohomology IsLocalRing UpperTheory.V.Base UpperTheory.V.X in
  set_option synthInstance.maxHeartbeats 200000 in
  intro hF hT hE l _ Ω _ _ _ c A hA θ hθc hne₁ hne₂
  obtain ⟨g₁, hne₁⟩ := hne₁
  obtain ⟨g₂, hne₂⟩ := hne₂
  obtain ⟨v, hv, hlv⟩ := hA
  have hd₁ : (θ g₁ : c.O) - 1 ≠ 0 := fun h => hne₁ (Units.ext (sub_eq_zero.1 h))
  have hd₂ : ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 ≠ 0 := fun h => hne₂ (by
    have h' : chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ = 1 := Units.ext (sub_eq_zero.1 h)
    rw [map_inv, mul_inv_eq_one] at h'
    exact h'.symm)
  set d₂ := ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 with hd₂def
  have hK : Finite (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))) := by
    rw [← ((So.cardLen l c.O).2 _).1, (qoFacts l c.O).2.2.2]
    exact fun h => hd₂ (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  refine ⟨Nat.card (c.O ⧸ Ideal.span {(θ g₁ : c.O) - 1}) *
    Nat.card (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))), fun n hn => ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have ha : ((l : ℕ) : c.O) ^ n ≠ 0 := pow_ne_zero _ hl0
  set a := ((l : ℕ) : c.O) ^ n with hadef
  obtain ⟨hM, ⟨r, hr, hkill⟩, htor⟩ := So.levFacts l c.O a ha (Lev a) ⟨LinearEquiv.refl c.O _⟩
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) (Lev a)) := ⟨AddCommGroup.zmodModule hkill⟩
  set ρ := Formalism.GaloisCohomology.scalRep (Lev a) θ with hρ
  let ρ' : Representation (ZMod (l ^ r)) (Dec (F := ℚ) A) (Lev a) := repOverZMod (l ^ r) ρ
  have hact : ∀ (g : Dec (F := ℚ) A) (m : Lev a), ρ' g m = (θ g : c.O) • m := fun g m => rfl
  have hc : ContAction ρ' := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨x, rfl⟩ := Lev.mk_surjective a m
    have h1 : Continuous fun g : Dec (F := ℚ) A => Lev.mk a ((θ g : c.O) * x) :=
      ((So.adicCont l c).1 a ha).comp (hθc.mul continuous_const)
    refine h1.congr fun g => ?_
    show Lev.mk a ((θ g : c.O) * x) = (θ g : c.O) • Lev.mk a x
    rw [← smul_eq_mul, map_smul]
  obtain ⟨f1, -, c2⟩ := So.locCard hF hT ℚ Ω l r hr v A hv (Lev a) ρ' hc
    (twDual ((cycMod ℚ Ω l r).comp (Dec (F := ℚ) A).subtype) ρ') fun g φ m => twDual_apply _ _ _ _ _
  have he := (hE ℚ Ω l r (Lev a) A ρ' v hr hv hc).1 hlv
  rw [GlobalTheory.OrdLoc.Dcmp.locDeg_rat hlv, pow_one] at he
  obtain ⟨-, ⟨e1⟩, -⟩ := So.scal c.O (ZMod (l ^ r)) _ (Lev a) ρ ρ' fun _ _ => rfl
  refine ⟨Finite.of_equiv _ e1.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, he, c2]
  refine Nat.mul_le_mul (Nat.mul_le_mul (le_trans ?_ (htor _ hd₁)) ?_) le_rfl
  · refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩)
      fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 x.2 g₁
    rw [hact] at this
    exact (sub_smul _ _ _).trans (by rw [one_smul, this, sub_self])
  · obtain ⟨ι, hι, -, hιs⟩ := So.dualEmb l c.O a ha r (Lev a) ⟨LinearEquiv.refl c.O _⟩
    refine Nat.card_le_card_of_injective (fun x => ⟨ι x.1, ?_⟩)
      fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy))
    have hx := (Representation.mem_invariants _ _).1 x.2 g₂
    have := hιs (cycZ ℚ Ω l (g₂ : G ℚ Ω) : ℤ_[l]ˣ) ((θ g₂⁻¹ : c.Oˣ) : c.O) x.1 x.1 fun m => by
      conv_lhs => rw [← hx, twDual_apply, hact]
      rfl
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, hd₂def, sub_smul, one_smul, sub_eq_zero]
    exact this.symm

end GlobalTheory.LocChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOver
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

open Pointwise

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cocycle_mulVec {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (g h : G ℚ Ω) :
    z (g * h) = z g + mat W g *ᵥ z h :=
  hz.2 g h

theorem mat_mul' (W : R2 Ω l) (g h : G ℚ Ω) : mat W (g * h) = mat W g * mat W h := by
  simp [mat, map_mul, Units.val_mul]

theorem mat_one' (W : R2 Ω l) : mat W 1 = 1 := by
  simp [mat]

theorem cob_conj {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ t : G ℚ Ω)
    (x : Fin 2 → Qbar l) (ht : z t = mat W t *ᵥ x - x) :
    z (γ * t * γ⁻¹) = mat W (γ * t * γ⁻¹) *ᵥ (mat W γ *ᵥ x - z γ) - (mat W γ *ᵥ x - z γ) := by
  have h0 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  have h2 : z γ⁻¹ = -(mat W γ⁻¹ *ᵥ z γ) := by
    have := cocycle_mulVec hz γ⁻¹ γ
    rw [inv_mul_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hinv : mat W γ⁻¹ * mat W γ = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
  rw [cocycle_mulVec hz, cocycle_mulVec hz, ht, h2, mat_mul', mat_mul', mat_mul']
  simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]
  abel

theorem cob_of_conj_le {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ : G ℚ Ω)
    (H H' : Subgroup (G ℚ Ω)) (hH : ∀ s ∈ H', γ⁻¹ * s * γ ∈ H)
    (h : ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x) :
    ∃ x : Fin 2 → Qbar l, ∀ s ∈ H', z s = mat W s *ᵥ x - x := by
  obtain ⟨x, hx⟩ := h
  refine ⟨mat W γ *ᵥ x - z γ, fun s hs => ?_⟩
  have e : s = γ * (γ⁻¹ * s * γ) * γ⁻¹ := by group
  rw [e]
  exact cob_conj hz γ _ x (hx _ (hH s hs))

theorem place_indep : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω),
    IsPlaceOver B w → IsPlaceOver B' w →
    ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  intro l _ Ω _ _ _ W z hz w B B' hB hB'
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  refine ⟨cob_of_conj_le hz γ _ _ (fun s hs => ?_), cob_of_conj_le hz γ _ _ (fun s hs => ?_)⟩
  · have := conj_mem_Ine_smul (F := ℚ) (A := B') (γ := γ⁻¹) (σ := s) hs
    rw [inv_inv, ← hγ, inv_smul_smul] at this
    exact this
  · have hs' : s • B' = B' := hs
    show (γ⁻¹ * s * γ) • B = B
    rw [mul_smul, mul_smul, hγ, hs', ← hγ, inv_smul_smul]

end GlobalTheory.Ord2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfFinTwo
section
namespace GlobalTheory.FinTwoMembership

open Matrix

theorem mem_of_fin_two {R : Type*} [CommRing R] (S : Subring R) (M : Matrix (Fin 2) (Fin 2) R)
    (y z : Fin 2 → R) (u : R) (hM : ∀ i j, M i j ∈ S) (hy : ∀ i, y i ∈ S) (hz : ∀ i, z i ∈ S)
    (hu : u ∈ S) :
    M.det * u - ((M.adjugate *ᵥ y) 0 * z 1 - (M.adjugate *ᵥ y) 1 * z 0) ∈ S := by
  have hadj : ∀ i j, M.adjugate i j ∈ S := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [S.neg_mem, hM]
  have hv : ∀ i, (M.adjugate *ᵥ y) i ∈ S := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact S.add_mem (S.mul_mem (hadj _ _) (hy _)) (S.mul_mem (hadj _ _) (hy _))
  have hdet : M.det ∈ S := by
    rw [Matrix.det_fin_two]
    exact S.sub_mem (S.mul_mem (hM _ _) (hM _ _)) (S.mul_mem (hM _ _) (hM _ _))
  exact S.sub_mem (S.mul_mem hdet hu)
    (S.sub_mem (S.mul_mem (hv _) (hz _)) (S.mul_mem (hv _) (hz _)))

theorem ht_mem : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
    (c : UpperTheory.V.HV.Coef l) (W : GlobalTheory.Ord2.R2 Ω l) (y z : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)
    (u : Formalism.ConjugateSelfDual.G ℚ Ω → Formalism.ConjugateSelfDual.Qbar l),
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i j : Fin (2 : ℕ)), GlobalTheory.Ord2.mat W s i j ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), y s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), z s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), u s ∈ UpperTheory.V.HV.Coef.O c) →
    ∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), GlobalTheory.Ord2.ht W y z u s ∈ UpperTheory.V.HV.Coef.O c := by
  intro Ω _ _ l _ c W y z u hW hy hz hu s
  have hM : ∀ i j, (GlobalTheory.Ord2.mat W s - 1) i j ∈ c.O.toSubring := by
    intro i j
    rw [Matrix.sub_apply]
    refine c.O.toSubring.sub_mem (hW s i j) ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact c.O.toSubring.one_mem
    · exact c.O.toSubring.zero_mem
  exact mem_of_fin_two c.O.toSubring _ (y s) (z s) (u s) hM (hy s) (hz s) (hu s)

end GlobalTheory.FinTwoMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOne
section
namespace GlobalTheory.ScalarNormBound

variable {l : ℕ} [Fact (Nat.Prime l)]

theorem norm_smul_le_self (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have ha : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  have hs : a • y = (a : ℚ_[l]) • y := (algebraMap_smul ℚ_[l] a y).symm
  rw [hs, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg y) ha

theorem exists_bound (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [Module.Finite ℤ_[l] O] :
    ∃ C : ℝ, ∀ y : O, ‖(y : PadicAlgCl l)‖ ≤ C := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  have hnn : ∀ z ∈ s, 0 ≤ ‖((z : O) : PadicAlgCl l)‖ := fun z _ => norm_nonneg _
  refine ⟨∑ z ∈ s, ‖((z : O) : PadicAlgCl l)‖, fun y => ?_⟩
  have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact Finset.single_le_sum hnn hx
  | zero => simpa using Finset.sum_nonneg hnn
  | add x z _ _ hx hz =>
    have e : ((x + z : O) : PadicAlgCl l) = (x : PadicAlgCl l) + (z : PadicAlgCl l) := rfl
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hz)
  | smul a x _ hx =>
    have e : ((a • x : O) : PadicAlgCl l) = a • (x : PadicAlgCl l) := rfl
    rw [e]
    exact (norm_smul_le_self a _).trans hx

theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (x : ↥(UpperTheory.V.HV.Coef.O c)), ‖(↑x : PadicAlgCl l)‖ ≤ (1 : ℝ) := by
  intro l _ c x
  obtain ⟨C, hC⟩ := exists_bound (UpperTheory.V.HV.Coef.O c)
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hb := hC (x ^ n)
  have e : ‖((x ^ n : UpperTheory.V.HV.Coef.O c) : PadicAlgCl l)‖ = ‖(x : PadicAlgCl l)‖ ^ n := by
    rw [SubmonoidClass.coe_pow, norm_pow]
  linarith

end GlobalTheory.ScalarNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralPadicInt
section
namespace GlobalTheory.PadicIntegralNorm

theorem norm_le_one_of_isIntegral {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [Algebra R K]
    (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (x : K) (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hpm, hpx⟩ := hx
  by_contra hlt
  rw [not_le] at hlt
  have h0 : (0 : ℝ) < ‖x‖ := zero_lt_one.trans hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hpx

  have hxn : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * x ^ i := by
    linear_combination hpx

  have hterm : ∀ i ∈ Finset.range p.natDegree,
      ‖algebraMap R K (p.coeff i) * x ^ i‖ < ‖x‖ ^ p.natDegree := by
    intro i hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap R K (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by gcongr; exact hR _
      _ = ‖x‖ ^ i := one_mul _
      _ < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rcases (Finset.range p.natDegree).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, neg_zero] at hxn
    have h1 : ‖x ^ p.natDegree‖ = 0 := by rw [hxn, norm_zero]
    rw [norm_pow] at h1
    exact (pow_pos h0 _).ne' h1
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i => algebraMap R K (p.coeff i) * x ^ i)
    have h2 := congrArg norm hxn
    rw [norm_neg, norm_pow] at h2
    linarith [hterm i hi]

theorem norm_le_one_of_isIntegral_padicInt {l : ℕ} [inst : Fact (Nat.Prime l)] (x : Formalism.ConjugateSelfDual.Qbar l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  refine norm_le_one_of_isIntegral (R := ℤ_[l]) (fun r => ?_) x hx
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Formalism.ConjugateSelfDual.Qbar l), norm_algebraMap']
  exact PadicInt.norm_le_one r

end GlobalTheory.PadicIntegralNorm
end

