module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0038
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesWithGramMatrixResidueRing
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_eq_sum_tail {α : Type} [Fintype α] {m : ℕ} (S : Set (Fin (m + 1) → α))
    (T : Set (Fin m → α)) (h : ∀ X ∈ S, Fin.tail X ∈ T) :
    S.ncard = ∑ x ∈ T.toFinset, Set.ncard {y : α | (Fin.cons y x : Fin (m + 1) → α) ∈ S} := by
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := fun X => Fin.tail X) (t := T.toFinset)
      (by intro X hX; simpa using h X (by simpa using hX))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun y _ => (Fin.cons y x : Fin (m + 1) → α)) ?_ ?_ ?_
  · intro y hy
    simpa using hy
  · intro y _ y' _ hyy
    simpa using congrFun hyy 0
  · intro X hX
    simp only [Finset.mem_filter, Set.mem_toFinset] at hX
    obtain ⟨h1, rfl⟩ := hX
    exact ⟨X 0, by simpa using h1, by simp⟩

variable {B : Type} [CommRing B]

theorem tail_mem_sols (c : B →+* B) {m n : ℕ} (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (X : Fin (m + 1) → Fin n → B) (hX : X ∈ sols c n G) :
    Fin.tail X ∈ sols c n (G.submatrix Fin.succ Fin.succ) := by
  obtain ⟨⟨y, hy⟩, h2⟩ := hX
  refine ⟨⟨Fin.tail y, fun a b => ?_⟩, fun a b => h2 _ _⟩
  simpa [Fin.tail] using hy a.succ b.succ

theorem cons_mem_sols (c : B →+* B) (hc : ∀ u, c (c u) = u) {m n : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (hG : ∀ a b, c (G b a) = G a b)
    (x : Fin m → Fin n → B) (hx : x ∈ sols c n (G.submatrix Fin.succ Fin.succ))
    (y : Fin n → B) :
    (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G ↔
      Prim c (Fin.cons y x : Fin (m + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = G i.succ 0) ∧
        ip c y y = G 0 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => by simpa using h2 i.succ 0, by simpa using h2 0 0⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simpa using h3
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [← cj_ip c hc, h2, hG]
    · simpa using h2 a
    · simpa using hx.2 a b

theorem pow_le_eta_mul {q m n : ℕ} (hq : 2 ≤ q) (h : 2 * m + 1 ≤ n) :
    (q : ℝ) ^ n ≤ (2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n - (2 * m + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : 2 * (2 * m + 1 + d) - (2 * m + 1) = (2 * m + 1 + d) + d := by omega
  have h2 : (2 : ℝ) ^ d ≤ (q : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) d
  have h3 : (2 : ℝ) ^ (2 * m + 1) / 2 ^ (2 * m + 1 + d) = 1 / 2 ^ d := by
    rw [pow_add (2 : ℝ) (2 * m + 1) d]; field_simp
  rw [h1, h3, pow_add (q : ℝ) (2 * m + 1 + d) d, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  gcongr

theorem eta_le {m n : ℕ} (h : 2 * m + 3 ≤ n) : (2 : ℝ) ^ (2 * m + 1) / 2 ^ n ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (2 * m + 3) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
  have h2 : (2 : ℝ) ^ (2 * m + 3) = 4 * 2 ^ (2 * m + 1) := by ring
  linarith

theorem ncard_sols_eta [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) (ω : B)
    (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (n m : ℕ) :
    2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) →
      (1 - 2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n * m - m ^ 2)
          ≤ (Set.ncard (sols c n G) : ℝ) ∧
        (Set.ncard (sols c n G) : ℝ)
          ≤ (1 + 2 * (2 ^ (2 * m + 1) / 2 ^ n)) * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  induction m with
  | zero =>
    intro _ G _
    have h1 : sols c n G = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact ⟨⟨x, fun a => a.elim0⟩, fun a => a.elim0⟩
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * 0 + 1) / 2 ^ n := by positivity
    rw [h1, Set.ncard_univ, Nat.card_unique]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsub_self,
      pow_zero, mul_one, Nat.cast_one] at h2 ⊢
    constructor <;> linarith
  | succ m ih =>
    intro hn G hG
    obtain ⟨i1, i2⟩ := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    have hη := eta_le (m := m) (n := n) (by omega)
    have hp := pow_le_eta_mul (m := m) (n := n) hq (by omega)
    have he : (2 : ℝ) ^ (2 * (m + 1) + 1) / 2 ^ n = 4 * (2 ^ (2 * m + 1) / 2 ^ n) := by ring
    have hx : 2 * n * (m + 1) - (m + 1) ^ 2 = (2 * n * m - m ^ 2) + (2 * n - (2 * m + 1)) := by
      have h1 : m ^ 2 ≤ 2 * n * m := by nlinarith
      have h2 : 2 * n * (m + 1) = 2 * n * m + 2 * n := by ring
      have h3 : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      omega
    have hη0 : (0 : ℝ) ≤ 2 ^ (2 * m + 1) / 2 ^ n := by positivity
    rw [he, hx, pow_add (q : ℝ)]
    set η : ℝ := 2 ^ (2 * m + 1) / 2 ^ n
    set Q : ℝ := (q : ℝ) ^ (2 * n * m - m ^ 2) with hQ
    set R : ℝ := (q : ℝ) ^ (2 * n - (2 * m + 1)) with hR
    have hQ0 : 0 ≤ Q := by positivity
    have hR0 : 0 ≤ R := by positivity
    have key : ∀ x ∈ (sols c n (G.submatrix Fin.succ Fin.succ)).toFinset,
        (1 - 3 * η) * R ≤ (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ∧
          (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ≤ (1 + 3 * η) * R := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      have := _root_.GlobalTheory.GramCount.ncard_extend_prim_one c hc ω hω hf q hq hB m n (by omega) x hx.1 (fun i => G i.succ 0)
        (G 0 0) (hG 0 0)
      simp only [cons_mem_sols c hc G hG x hx]
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    rw [ncard_eq_sum_tail _ _ (tail_mem_sols c G), Nat.cast_sum]
    rw [Set.ncard_eq_toFinset_card'] at i1 i2
    have k1 := Finset.card_nsmul_le_sum _ _ _ (fun x hx => (key x hx).1)
    have k2 := Finset.sum_le_card_nsmul _ _ _ (fun x hx => (key x hx).2)
    rw [nsmul_eq_mul] at k1 k2
    have hQR : 0 ≤ Q * R := mul_nonneg hQ0 hR0
    constructor
    · refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_right i1
        (mul_nonneg (by linarith) hR0)) k1)
      nlinarith [mul_nonneg (mul_nonneg hη0 hη0) hQR]
    · refine le_trans k2 (le_trans (mul_le_mul_of_nonneg_right i2
        (mul_nonneg (by linarith) hR0)) ?_)
      nlinarith [mul_nonneg (mul_nonneg hη0 (show 0 ≤ 1 / 4 - η by linarith)) hQR,
        mul_nonneg hη0 hQR]

theorem ncard_sols_residue : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  intro B _ _ c hc ω hω hf q hq hB m n hn G hG
  obtain ⟨h1, h2⟩ := ncard_sols_eta c hc ω hω hf q hq hB n m hn G hG
  have hη := eta_le hn
  have hQ : (0 : ℝ) ≤ (q : ℝ) ^ (2 * n * m - m ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right hη hQ
  constructor <;> nlinarith

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolume
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem coset_fibre_card {G : Type} [Group G] (D H : Subgroup G) (h : D ≤ H) (hDH : D.relIndex H ≠ 0)
    (z : G ⧸ H) : Finite {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex H := by
  let e := Subgroup.quotientEquivProdOfLE (α := G) h
  have he : ∀ y, (e y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H a => rfl
  let e2 : {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ≃ (H ⧸ D.subgroupOf H) :=
    { toFun := fun y => (e y.1).2
      invFun := fun c => ⟨e.symm (z, c), by rw [← he, Equiv.apply_symm_apply]⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply e.injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext ((he y.1).trans y.2).symm rfl
      right_inv := fun c => by simp }
  haveI : (D.subgroupOf H).FiniteIndex := ⟨hDH⟩
  refine ⟨Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e2]
  rfl

theorem mass_orbit_eq : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V₀ : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V₀ * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0
  let M : Subgroup G → ℝ≥0∞ := fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U),
    ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
  have hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H := by
    intro D H h hDH
    have e := _root_.GlobalTheory.MassFibre.mass_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_
      (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)
    · simp only [Set.mem_univ, ite_true] at e
      exact e
    · intro g y
      induction y using QuotientGroup.induction_on with
      | H a => rfl
  refine ⟨M K0, fun X _ x h1 h2 => ?_⟩
  have hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) =
      M (MulAction.stabilizer G x) := by
    have e := _root_.GlobalTheory.MassFibre.mass_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x)
      (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y)
      (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ ?_
    · rw [Nat.cast_one, one_mul] at e
      exact e.symm
    · intro z hz
      have hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z} :=
        ⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩
      obtain ⟨a, rfl⟩ := hz
      have hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x} :=
        ⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    · intro z hz
      refine ⟨fun y => hz ?_⟩
      rw [← y.2]
      induction y.1 using QuotientGroup.induction_on with
      | H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩
  rw [hX]
  set U := MulAction.stabilizer G x
  have ha := hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)
  have hb := hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.inf_relIndex_right] at hb
  rw [ha] at hb
  have hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞) := by
    rw [invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hA : (K0.relIndex U : ℝ≥0∞) ≠ 0 := by exact_mod_cast h1
  have hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingConjInverseAdjointCloseToOne
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Sloc.CloseConj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cT_mul (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cT_one (L : LocE F E) {n : ℕ} : cT L (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  simp only [cT, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem cT_sub (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A - B) = cT L A - cT L B := by
  ext i j
  simp [cT, map_sub]

theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  intro F _ _ _ E _ _ _ L n Z Zi M Mi M' t e ht htc hZiZ heZ heZi hMiM hMMi hclose hM'
  have hc : cT L Mi * cT L M = 1 := by rw [← cT_mul, hMMi, cT_one]
  have hM'eq : M' = Zi * cT L Mi * Z := by
    calc M' = Zi * (cT L Mi * cT L M) * Z * M' := by rw [hc, Matrix.mul_one, hZiZ, Matrix.one_mul]
      _ = Zi * cT L Mi * (cT L M * Z * M') := by simp only [Matrix.mul_assoc]
      _ = Zi * cT L Mi * Z := by rw [hM']
  have hsub : M' - 1 = Zi * cT L (Mi - 1) * Z := by
    rw [hM'eq, cT_sub, cT_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hZiZ]
  choose o ho hoe using hclose
  intro i j
  refine ⟨∑ l, ∑ k, (e * Zi i k) * L.cj (o l k) * (e * Z l j), ?_, ?_⟩
  · refine Subring.sum_mem _ fun l _ => Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (Subring.mul_mem _ (heZi i k) (cj_mem L (ho l k))) (heZ l j)
  · rw [hsub]
    simp only [Matrix.mul_apply, cT, hoe, map_mul, htc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end GlobalTheory.Sloc.CloseConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdResQZpow
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.ResProd

theorem vE_eq_neg_log {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {E : Type} [CommRing E] [Algebra K E] [TopologicalSpace E] (L : LocE K E)
    (ι : F →+* K) (hd : DenseRange ι)
    (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
    {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap K E (ι x)) = -WithZero.log (p.valuation F x) := by
  have hιx : ι x ≠ 0 := (map_ne_zero ι).mpr hx
  obtain ⟨k, u, hku⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hιx
  rw [hku, GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ k u]

  obtain ⟨g, hg⟩ := p.valuation_exists_uniformizer F
  obtain ⟨q, hq, hqg⟩ := GlobalTheory.LocSplit.exists_irreducible p ι hd hv g hg
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hϖ hq
  have h0 : p.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set n := WithZero.log (p.valuation F x) with hn
  have hvx : p.valuation F x = WithZero.exp n := (WithZero.exp_log h0).symm

  have hone : p.valuation F (x * g ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hvx, hg, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hunit : ∀ v : (𝒪[K])ˣ, valuation K ((v : 𝒪[K]) : K) = 1 := fun v =>
    (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp v.isUnit
  have hϖ0 : valuation K (ϖ : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hvq : valuation K (ι g) = valuation K (ϖ : K) := by
    rw [← hqg, ← hw]
    push_cast
    rw [map_mul, hunit, mul_one]

  have hvz : valuation K (ι (x * g ^ n)) = 1 := by
    apply le_antisymm
    · simpa using (hv (x * g ^ n) 1).mpr (by rw [hone, map_one])
    · simpa using (hv 1 (x * g ^ n)).mpr (by rw [hone, map_one])
  simp only [map_mul, map_zpow₀, hku, hunit, mul_one, hvq] at hvz
  rw [← zpow_add₀ hϖ0] at hvz

  have hle := (GlobalTheory.UnramVal.zpow_mul_unit_mem_iff hϖ (k + n) 1).mp (by
    rw [Valuation.mem_integer_iff]
    simp only [Units.val_one, OneMemClass.coe_one, mul_one, map_zpow₀, hvz, le_refl])
  have hge := (GlobalTheory.UnramVal.zpow_mul_unit_mem_iff hϖ (-(k + n)) 1).mp (by
    rw [Valuation.mem_integer_iff]
    simp only [Units.val_one, OneMemClass.coe_one, mul_one, map_zpow₀, zpow_neg, map_inv₀, hvz, inv_one,
      le_refl])
  omega

theorem place_eq_zpow {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {x : F} (hx : x ≠ 0) :
    FinitePlace.equivHeightOneSpectrum.symm p x =
      (Ideal.absNorm p.asIdeal : ℝ) ^ WithZero.log (p.valuation F x) := by
  have h0 : p.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
    NumberField.FinitePlace.norm_embedding', WithZeroMulInt.toNNReal_neg_apply _ h0,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem prod_resQ_zpow : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → ∀ x : F, x ≠ 0 → {p | vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) ≠ 0}.Finite ∧ ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  intro F E _ _ _ _ _ sig A ϖ hϖ x hx

  have key : ∀ p, vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) =
      -WithZero.log (p.valuation F x) := fun p => by
    haveI := (A.loc p).lf
    exact vE_eq_neg_log p (A.L p) (A.loc p).ιF (A.loc p).dense
      (GlobalTheory.HL.PlacesInt.val_le_iff (A.loc p)) (hϖ p) hx
  have hterm : ∀ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p)
      (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) =
      (NumberField.FinitePlace.equivHeightOneSpectrum.symm p x)⁻¹ := fun p => by
    rw [key, GlobalTheory.HL.PlacesInt.resQ_eq_absNorm (A.loc p) (ϖ p) (hϖ p), place_eq_zpow p hx, zpow_neg]
  have hfin : (Function.mulSupport fun w : NumberField.FinitePlace F => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  constructor
  · refine (hfin.image NumberField.FinitePlace.equivHeightOneSpectrum).subset ?_
    intro p hp
    refine ⟨NumberField.FinitePlace.equivHeightOneSpectrum.symm p, ?_, by simp⟩
    simp only [Set.mem_setOf_eq, key] at hp
    rw [Function.mem_mulSupport, place_eq_zpow p hx]
    intro h1
    have hgt : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
    rw [zpow_eq_one_iff_right₀ (by positivity) hgt.ne'] at h1
    exact hp (by rw [h1, neg_zero])
  · simp_rw [hterm]
    rw [finprod_inv_distrib,
      finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm (f := fun w => w x),
      NumberField.FinitePlace.prod_eq_inv_abs_norm hx]
    push_cast
    simp

end GlobalTheory.ResProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelf
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GFrames

theorem lead_last_eq_det {R : Type} [CommRing R] {N : ℕ} (Z : Matrix (Fin N) (Fin N) R) :
    lead Z (Fin.last N) = Z.det := by
  unfold lead
  congr 1

theorem Zh_map_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F)) :
    G.Zh.map (A.loc p).ιE =
      Matrix.diagonal (fun a : Fin (r + 1) =>
          algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) *
        (G.S p).Zh *
      Matrix.diagonal (fun a : Fin (r + 1) =>
          algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have h := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)
  have hZ : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j) := rfl
  rw [hZ, ← h, ← G.f_eq p a, ← G.f'_eq p b, ← G.Hm_eq p]
  simp only [Frames.Zh, Frames.h, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul, map_mul,
    AlgEquiv.commutes, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Zh_inv_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) : G.Zh⁻¹ * G.Zh = 1 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have hS : IsUnit ((G.S p).Zh.det) := by
    have := (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).2.2.2.1
    rwa [Frames.D, lead_last_eq_det] at this
  have hd : IsUnit (Matrix.diagonal (fun a : Fin (r + 1) =>
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))))).det := by
    rw [Matrix.det_diagonal, ← map_prod]
    exact (IsUnit.prod_univ_iff.2 fun a => ((G.c p).isUnit.pow _)).map (algebraMap (A.loc p).Fp (A.loc p).Ep)
  have hι : IsUnit ((A.loc p).ιE G.Zh.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Zh_map_eq, Matrix.det_mul, Matrix.det_mul]
    exact (hd.mul hS).mul hd
  have hne : G.Zh.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hι
    exact not_isUnit_zero hι
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)

end GlobalTheory.HL.GFrames
end

