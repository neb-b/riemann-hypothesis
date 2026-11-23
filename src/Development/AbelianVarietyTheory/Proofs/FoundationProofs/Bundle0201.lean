module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZe
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zv_unit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h1
  rw [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans h1⟩

theorem zv_apply_ne_zero {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h
  have h1 : χ ((u : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) = 1 := by rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem zv_inv_mul {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ⁻¹ x * χ x = 1 := by
  rw [MulChar.inv_apply_eq_inv']
  exact inv_mul_cancel₀ (zv_apply_ne_zero χ hx)

theorem zv_ch_changeLevel_mul {N l : ℕ} (cop : N.Coprime l) (A : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (d : ℤ) : ch (A.changeLevel (dvd_mul_right N l) * ψ.changeLevel (dvd_mul_left l N)) d = ch A d * ch ψ d := by
  unfold ch
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit ((d : ZMod (N * l)))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (dvd_mul_right N l), ZMod.cast_intCast (dvd_mul_left l N)]
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    have hn : ¬ (IsUnit (d : ZMod N) ∧ IsUnit (d : ZMod l)) := by
      rintro ⟨h1, h2⟩
      apply hu
      have : IsUnit (ZMod.chineseRemainder cop (d : ZMod (N * l))) := by
        rw [map_intCast]
        exact Prod.isUnit_iff.mpr ⟨by simpa using h1, by simpa using h2⟩
      exact (isUnit_map_iff (ZMod.chineseRemainder cop) _).mp this
    rcases not_and_or.mp hn with h | h
    · rw [MulChar.map_nonunit _ h, zero_mul]
    · rw [MulChar.map_nonunit _ h, mul_zero]

theorem zv_root {N l : ℕ} (hN : 0 < N) (cop : l.Coprime N) (θ : DirichletCharacter ℂ N) :
    ∃ n : ℕ, 0 < n ∧ (θ (l : ZMod N)) ^ n = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l cop, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem eigF_value_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g →
    α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) →
    θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧
      val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro l _ ι e N χ θ ψ g α β he hN hlN hg hsum hprod hα hpar hθχ
  have hp : l.Prime := Fact.out
  have hl0 : 0 < l := hp.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have cop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlN).symm
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.wt_exists (N * l) hNl
  have hprod' : α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hprod
  obtain ⟨B, c, hEig, hlam⟩ := _root_.GlobalTheory.EisM.eigF_of_prim (2 * e + 1) N l χ g ρ α β (by omega) hN hp hlN hg hρ hsum hprod'
  refine ⟨B, c, hEig, ?_⟩
  have hχm : χ (-1) = -1 :=
    (_root_.GlobalTheory.EisM.twisted_lvalue_ne_zero_edge (2 * e + 1) N 1 χ 1 g ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2) ⟨e, rfl⟩ hN one_pos hg le_rfl).1

  obtain ⟨φ, hφ⟩ : ∃ φ : DirichletCharacter ℂ (N * l), ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d :=
    ⟨_, zv_ch_changeLevel_mul cop _ _⟩
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hθχ
    ext a
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder cop (a : ZMod N).val 1
    haveI : NeZero N := ⟨hN.ne'⟩
    have hkN : ((k : ℕ) : ZMod N) = a := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk1, ZMod.natCast_zmod_val]
    have hkl : ((k : ℕ) : ZMod l) = 1 := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2, Nat.cast_one]
    have hk : ch φ ((k : ℕ) : ℤ) = (θ * χ) a := by
      rw [hφ]; unfold ch; push_cast; rw [hkN, hkl, map_one, mul_one]
    rw [h1] at hk
    unfold ch at hk
    rw [MulChar.one_apply_coe]
    by_cases hu : IsUnit ((((k : ℕ) : ℤ)) : ZMod (N * l))
    · rw [MulChar.one_apply hu] at hk; exact hk.symm
    · rw [MulChar.map_nonunit _ hu] at hk; exact absurd hk.symm (zv_apply_ne_zero (θ * χ) a.isUnit)

  have hψ2 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hφm : ch φ (-1) = (-1) ^ e * ψ (-1) * (-1) * ψ (-1) := by
    rw [hφ]; unfold ch; push_cast; rw [MulChar.mul_apply, hpar, hχm]

  obtain ⟨c₀, hFF⟩ := _root_.GlobalTheory.eis_periodic_weights e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (by unfold ch; push_cast; exact MulChar.map_zero ψ)
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun d _ => ⟨fun x => by unfold ch; push_cast; rw [map_mul, mul_comm],
      fun x => by unfold ch; push_cast; rw [map_mul, mul_comm]⟩)
    (by unfold ch; push_cast; rw [hpar]; linear_combination (-1 : ℂ) ^ e * hψ2)
  rw [mul_comm l N] at hFF

  have hat0 : hat φ 0 = 0 := ((_root_.GlobalTheory.EisM.hat_char_props).1 (N * l) φ hNl).2.2 hφ1
  obtain ⟨c₁, hE, hlat⟩ := _root_.GlobalTheory.EisForm.eis_latF_mf (e + 1) (N * l) 1 (fun _ => 1) (ch φ⁻¹) (fun _ => 1) φ (by omega) hNl one_pos
    hat0 (fun _ => rfl)
    (fun d hd => by
      have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime (by simpa using hd)
      refine ⟨fun y => ?_, fun x => by ring⟩
      unfold ch
      rw [map_mul, ← mul_assoc, mul_comm (φ⁻¹ _), mul_assoc, zv_inv_mul φ hu, mul_one])
    (by
      rw [mul_one]
      unfold ch
      rw [MulChar.inv_apply_eq_inv']
      have := hφm; unfold ch at this; rw [this]
      apply inv_eq_of_mul_eq_one_left
      have hm : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linear_combination ((-1 : ℂ) ^ e) ^ 2 * hψ2 + hm)
  rw [mul_one] at hE
  have hE' : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat ⇑φ) fun _ => 1) := by
    simpa only [mul_one] using hE

  set FF := eis e c₀ (ch ψ) (ch θ) with hFFdef
  set E := eis (e + 1) c₁ (hat ⇑φ) fun _ => 1 with hEdef
  have hX : MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF E) := by
    have h1 := (_root_.GlobalTheory.EisM.mul_main).2 e (e + 1) (N * l) _ _ FF E hFF hE'
    rw [show e + (e + 1) = 2 * e + 1 by ring] at h1
    refine (_root_.GlobalTheory.EisM.mf_linear (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime hd
    have hd' : IsCoprime d (N : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_left
    have hd'' : IsCoprime d (l : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_right
    have uN := zv_unit_of_isCoprime hd'
    have ul := zv_unit_of_isCoprime hd''
    have e1 := hφ d
    unfold ch at e1 ⊢
    rw [MulChar.mul_apply] at e1
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', e1]
    have := zv_apply_ne_zero θ uN
    have := zv_apply_ne_zero χ uN
    have := zv_apply_ne_zero ψ ul
    field_simp
  have hqs : qs (mul FF E) = fun τ => qs FF τ * qs E τ := ((_root_.GlobalTheory.EisM.mul_main).1 FF E hFF.1 hE'.1).2
  obtain ⟨κ, hκ, hlat'⟩ : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℍ,
      lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ = κ * qs E τ :=
    ⟨_, by
      have : ((N * l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNl.ne'
      have h2 : (-2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (((e + 1 - 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      exact div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (div_ne_zero h2 this))) h3, hlat⟩
  have hpet : ∀ h : ℍ → ℂ, pet (2 * e + 1) ρ h (qs (mul FF E)) =
      κ⁻¹ * pet (2 * e + 1) ρ h (fun τ => qs FF τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) := by
    intro h
    unfold pet
    rw [← integral_const_mul]
    congr 1
    funext τ
    rw [hqs]
    beta_reduce
    rw [hlat' τ]
    field_simp
  obtain ⟨P, hP0, hP1, hP2⟩ := _root_.GlobalTheory.EisM.rankin_values_at_zero e N l χ θ ψ φ g ρ c₀ he hN hp hlN hg hρ hφ hφ1 hFF

  have copl : l.Coprime N := cop.symm
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have fθ := _root_.GlobalTheory.FactorsAtL.factors_ne_zero l ι e N χ g α β (θ l) he hN hlN hg hsum hprod hα (zv_root hN copl θ)
  have fχ := _root_.GlobalTheory.FactorsAtL.factors_ne_zero l ι e N χ g α β (χ⁻¹ l) he hN hlN hg hsum hprod hα (zv_root hN copl χ⁻¹)
  have hlamX : lam B c (mul FF E) ≠ 0 := by
    rw [hlam _ hX, hpet, hpet, hP1, hP2]
    intro h0
    have hl : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    have hκi : κ⁻¹ ≠ 0 := inv_ne_zero hκ
    have h3 : κ⁻¹ * P / (l : ℂ) ^ (2 * e + 1) * ((l : ℂ) * θ l - β) = 0 := by
      rw [← h0]; field_simp; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact div_ne_zero (mul_ne_zero hκi hP0) (pow_ne_zero _ hl) h4
    · exact fθ.2.1 (by linear_combination -h4)
  exact _root_.GlobalTheory.EisM.val_depleted_ne_zero e N l χ θ ψ φ (fun q => χ⁻¹ q * g q) α c₀ c₁ B c he hN hp hlN hα0 hEig hpar hχm hθχ hφ hFF hE'
    hlamX fθ.1 (fχ.2.2 e he)

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMember
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockMinorExtremal

open MvPolynomial GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor GlobalTheory.Capelli

section General

variable {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {n l : ℕ}
  (y : Matrix (Fin n) (Fin l) A)

theorem der_minor {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0)
    {m : ℕ} (row : Fin m → Fin n) (h : m ≤ l) :
    D (y.submatrix row (Fin.castLE h)).det =
      (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) • (y.submatrix row (Fin.castLE h)).det := by
  rw [← Matrix.det_transpose, derivation_det]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, hD]
  by_cases hb : b.1 < m
  · rw [Finset.sum_eq_single (⟨b.1, hb⟩ : Fin m)]
    · have e : Fin.castLE h ⟨b.1, hb⟩ = b := rfl
      simp only [e, if_true]
      split_ifs with h1 h2
      · subst h1
        rw [one_smul]
        congr 1
        exact Matrix.updateRow_eq_self _ _
      · exact absurd (h1 ▸ hb) h2
      · have hlt : a.1 < b.1 := lt_of_le_of_ne hab fun e => h1 (Fin.ext e)
        have hne : (⟨a.1, hlt.trans hb⟩ : Fin m) ≠ ⟨b.1, hb⟩ := fun e => by
          rw [Fin.ext_iff] at e; simp at e; omega
        rw [zero_smul]
        refine Matrix.det_zero_of_row_eq hne ?_
        rw [Matrix.updateRow_self, Matrix.updateRow_ne hne]
        rfl
    · intro i _ hi
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hi (Fin.ext (congrArg Fin.val e :))]
    · simp
  · have h0 : (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb
      · rfl
      · rfl
    rw [h0, zero_smul]
    refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hb (e ▸ i.2)]

theorem sum_rows (α : Fin l → ℕ) (hα : Antitone α) (a : Fin l) :
    ∑ i : Fin l, ((α i - nextRow α i : ℕ) : ℂ) * (if a.1 < i.1 + 1 then 1 else 0) = α a := by
  let f : ℕ → ℕ := fun i => if h : i < l then α ⟨i, h⟩ else 0
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [f]
    split_ifs with h1 h2 h2
    · exact hα (by simp [Fin.le_def])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := telescope f hf a l
  have hl : f l = 0 := by simp [f]
  rw [if_pos a.2.le, hl, ← Fin.sum_univ_eq_sum_range
    (fun i => ((f i - f (i + 1) : ℕ) : ℂ) * (if a.1 < i + 1 then 1 else 0))] at h
  have e1 : ∀ i : Fin l, f i = α i := fun i => by simp [f, i.2]
  have e2 : ∀ i : Fin l, f (i + 1) = nextRow α i := fun i => rfl
  simpa only [e1, e2, Nat.cast_zero, sub_zero] using h

theorem der_minorProd (α : Fin l → ℕ) (hα : Antitone α) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0) :
    D (minorProd α y row) = (if a = b then (α a : ℂ) else 0) • minorProd α y row := by
  rw [minorProd, derivation_prod_pow D _ _ _ _ fun i => der_minor D y hab hD (row i) i.2]
  congr 1
  split_ifs with h
  · exact sum_rows α hα a
  · simp

theorem der_minorProd_zero (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    (hD : ∀ i c k, D (y (row i c) k) = 0) : D (minorProd α y row) = 0 := by
  rw [minorProd, derivation_prod_pow D _ _ _ (fun _ => 0) fun i => ?_]
  · simp
  · rw [zero_smul, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self, Matrix.submatrix_apply, hD]

end General

theorem minorProd_ne_zero {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (hz : Function.Injective z)
    (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n) (hrow : ∀ i, Function.Injective (row i)) :
    minorProd α (Matrix.of fun c k => (X (z (c, k)) : MvPolynomial σ ℂ)) row ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
    (lead_ne_zero (fun w : Fin (i.1 + 1) × Fin l => z (row i w.1, w.2))
      (hz.comp ((hrow i).prodMap Function.injective_id)) le_rfl i.2)

variable {p q n : ℕ}

def vPlus (p q n : ℕ) : Fin p × Fin n → Ln p q n 0 := fun w => (.inl w.1, .inl w.2)

def vMinus (p q n : ℕ) : Fin q × Fin n → Ln p q n 0 := fun w => (.inr w.1, .inl w.2)

theorem vPlus_inj : Function.Injective (vPlus p q n) := fun u w h => by
  simpa [vPlus, Prod.ext_iff] using h

theorem vMinus_inj : Function.Injective (vMinus p q n) := fun u w h => by
  simpa [vMinus, Prod.ext_iff] using h

theorem act_plus (i j : Fin p) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inl i) (.inl j)) P =
      rowDer (vPlus p q n) i j P + (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.1, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zA, vPlus, cPair]

theorem act_minus (i j : Fin q) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inr j) (.inr i)) P =
      -rowDer (vMinus p q n) i j P - (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.2, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zD, vMinus, cPair, eq_comm]

theorem der_plus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hp : Antitone ap) {i j : Fin p}
    (hij : i ≤ j) :
    rowDer (vPlus p q n) i j (delta hn ap am) = (if i = j then (ap i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zPlus p q n) ap hp _ hij
    fun c k => rowDer_X _ vPlus_inj i j k c, der_minorProd_zero _ (zMinus p q n) am _ fun _ c k => ?_]
  · simp [mul_comm]
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zMinus, vPlus, pderiv_X, Pi.single_apply]

theorem der_minus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hm : Antitone am) {i j : Fin q}
    (hij : i ≤ j) :
    rowDer (vMinus p q n) i j (delta hn ap am) = (if i = j then (am i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zMinus p q n) am hm _ hij
    fun c k => rowDer_X _ vMinus_inj i j k c, der_minorProd_zero _ (zPlus p q n) ap _ fun _ c k => ?_]
  · simp
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zPlus, vMinus, pderiv_X, Pi.single_apply]

theorem lower (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro a b
  rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.lowerOp]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h1 : pderiv ((.inr b, .inl c) : Ln p q n 0) (minorProd ap (zPlus p q n) (topRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  have h2 : pderiv ((.inl a, .inl c) : Ln p q n 0) (minorProd am (zMinus p q n) (botRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  rw [delta, Derivation.leibniz, h1, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, pderiv_swap, h2,
    map_zero, smul_zero, zero_add, smul_eq_mul]
  by_cases hc : c.1 < p
  · rw [der_minorProd_zero (pderiv ((.inr b, .inl c) : Ln p q n 0)) (zMinus p q n) am (botRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      zero_mul]
    have := i.2
    simp only [botRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega
  · rw [der_minorProd_zero (pderiv ((.inl a, .inl c) : Ln p q n 0)) (zPlus p q n) ap (topRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      mul_zero]
    have := i.2
    have := d.2
    simp only [topRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega

theorem delta_extremal : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro p q n hn ap am hp hm
  refine ⟨mul_ne_zero ?_ ?_, ?_, fun i j h => ?_, fun i j h => ?_, lower hn ap am⟩
  · exact minorProd_ne_zero (fun w => vPlus p q n w.swap) (vPlus_inj.comp Prod.swap_injective) ap _
      fun i c d h => by simpa [topRows, Fin.ext_iff] using h
  · exact minorProd_ne_zero (fun w => vMinus p q n w.swap) (vMinus_inj.comp Prod.swap_injective) am _
      fun i c d h => by simpa [botRows, Fin.ext_iff] using h
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Sum.forall, sub_eq_zero]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [act_plus, der_plus hn ap am hp le_rfl]
      simp [wtExt, add_smul]
    · rw [act_minus, der_minus hn ap am hm le_rfl]
      simp [wtExt, sub_smul]
  · rw [act_plus, der_plus hn ap am hp h.le]
    simp [h.ne]
  · rw [act_minus, der_minus hn ap am hm h.le]
    simp [h.ne]

end GlobalTheory.FockMinorExtremal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCong
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThBCompat

private theorem cast_eq_of_dvd {N M : ℕ} (h : N ∣ M) (x y : ℤ) (hxy : (x : ZMod M) = (y : ZMod M)) :
    (x : ZMod N) = (y : ZMod N) := by
  have := congrArg (ZMod.castHom h (ZMod N)) hxy
  simpa only [map_intCast] using this

private theorem gamma_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h4)

private theorem gamma1_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)

theorem isThB_succ_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l hl l2 hN hN1 hlA n b φ φ' h1 h2
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  have hfc' : AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f := by
    have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) (b ![1, 0])
    change (b ![1, 0]).val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n)
      (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) (b ![1, 0])) = _
    rw [hfc]
    rfl
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc'.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hle : CongruenceSubgroup.Gamma1 (N * l ^ (n + 1)) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le (Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ n)))
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l (n + 1) hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ
      rw [pow_succ, pow_mul, hL, map_pow, map_mul, map_inv₀, hfI γ hγ, hf'I γ (hle hγ)]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ (gamma_le (pow_dvd_pow l (Nat.le_succ n)) hδ')
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g ^ l, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, map_pow, hgI γ hγ, hg'I γ (hle hγ)]
      · have key : ((u : X.K) * X.sl (ofSL δ) u) ^ (l ^ n) = (g' / g ^ l) ^ (l ^ n) := by
          rw [div_pow, ← pow_mul, ← pow_succ', ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring
        rw [pow_succ, pow_mul, pow_mul, key])
  have hfD' : IsDl X A l n 1 (f : X.K) φ := by
    obtain ⟨hA, a, c, κ, hκ, hac, ha, hc, hcg⟩ := hfD
    refine ⟨hA, a, c, κ, hκ, hac, ha, hc, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hcg r
    exact ⟨l * z, A.mul_mem _ _ (natCast_mem A l) hz, by rw [e, pow_succ, mul_assoc]⟩
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, GlobalTheory.Glue.DlPow.isAlgebraic_of_tower X⟩
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD' (by rw [← hu]; exact hf'D)

end GlobalTheory.ThBCompat
end

