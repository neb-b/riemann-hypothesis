module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersPowersOfOmega
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameIner

theorem mem_IK_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 :=
  _root_.GlobalTheory.IKRes.mem_IK_ql_iff

theorem minpoly_root : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 :=
  _root_.GlobalTheory.MinpolyKummerUr.aeval_mul_root

theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y :=
  _root_.GlobalTheory.LiftKur.exists_gal_fix_Kur_map

theorem exists_open_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 :=
  _root_.GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal

theorem exists_pow_fix : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x :=
  _root_.GlobalTheory.PowFixNear.main

theorem near_of_fix_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ :=
  _root_.GlobalTheory.NearRoot.near_root

variable {l : ℕ} [hl : Fact l.Prime]


open GlobalTheory.MemLoc.FrobLaws in
theorem fix_root (g : Gl l) (hg : g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) {ζ : Om l} {m : ℕ} (hm : 0 < m)
    (hlm : ¬ l ∣ m) (hζ : ζ ^ m = 1) : (g : GQ l) ζ = ζ := by
  have h1 := (mem_IK_iff l g).1 hg ζ (norm_root hm hζ).le
  have hgζ : ((g : GQ l) ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  let a : OO l := ⟨(g : GQ l) ζ, show ‖(g : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩
  let b : OO l := ⟨ζ, show ‖ζ‖ ≤ 1 from (norm_root hm hζ).le⟩
  have := res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ))
    (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζ)) ((res_eq_iff a b).2 h1)
  exact congrArg Subtype.val this


open GlobalTheory.MemLoc.FrobLaws in
theorem frob_root (Fr : Gl l) (hFr : ∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1)
    {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (hζ : ζ ^ m = 1) : (Fr : GQ l) ζ = ζ ^ l := by
  have hK : ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩
  have h1 := hFr ζ hK (norm_root hm hζ).le
  have hgζ : ((Fr : GQ l) ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  have hζl : (ζ ^ l) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  let a : OO l := ⟨(Fr : GQ l) ζ, show ‖(Fr : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩
  let b : OO l := ⟨ζ ^ l, show ‖ζ ^ l‖ ≤ 1 from (norm_root hm hζl).le⟩
  have := res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ))
    (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζl)) ((res_eq_iff a b).2 h1)
  exact congrArg Subtype.val this


open GlobalTheory.MemLoc.FrobLaws in
theorem mem_IK_of_fix_Kur (g : Gl l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x) :
    g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖(g : GQ l) y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rw [mem_IK_iff]
  intro x hx
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := exists_root x h
    have e : (g : GQ l) x - x = (g : GQ l) (x - ζ) - (x - ζ) := by
      rw [map_sub, hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩)]; ring
    rw [e]
    exact key _ hn

theorem exists_inertia {M : ℕ} (hM : 0 < M) (ρ ζ : Om l) (hρ : ρ ^ M = -(l : Om l)) (hζ : ζ ^ M = 1) :
    ∃ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (g : GQ l) ρ = ζ * ρ := by
  obtain ⟨g, hgK, hgρ⟩ := exists_lift l ρ (ζ * ρ) (minpoly_root l M hM ρ ζ hρ hζ)
  have hmem : g ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ (⊥ : IntermediateField ℚ_[l] (Om l)) at hx
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes c
  exact ⟨⟨g, hmem⟩, mem_IK_of_fix_Kur _ hgK, hgρ⟩

theorem chi_trivial (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ)
    (ho : IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)))) (hc : Nat.Coprime (orderOf χ) l) :
    ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) →
      ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), ((g : Gl l) : GQ l) ρ = ρ → χ g = 1 := by
  obtain ⟨F, hFn, hF⟩ := exists_open_normal l LL χ ho
  obtain ⟨M, hM, hlM, hnear⟩ := near_of_fix_root l F
  refine ⟨M, hM, hlM, fun ρ hρ g hg => ?_⟩
  have hres := (mem_IK_iff l (g : Gl l)).1 g.2
  have h1 := hnear ρ hρ _ hres hg
  obtain ⟨s, hs⟩ := exists_pow_fix l F hFn _ h1
  have h2 : χ (g ^ l ^ s) = 1 := hF _ (fun x hx => by simpa using hs x hx)
  have h3 : χ g ^ orderOf χ = 1 := by rw [← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
  rw [map_pow] at h2
  have := pow_gcd_eq_one.2 ⟨h3, h2⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right s hc), pow_one] at this

end GlobalTheory.TameIner

namespace GlobalTheory.TameIner

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ w ^ e = 1) ∧ (∃ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ IsPrimitiveRoot w e) ∧ ∀ (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → Nat.Coprime (orderOf χ) l → (∀ (Fr : Gl l), (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1) → ∀ g h : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (g : Gl l) = Fr⁻¹ * h * Fr → χ h = χ g ^ l) ∧ (χ ^ e = 1 → ∃ c : ZMod e, ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (w : ↥LL.1), (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0) → (χ g : ↥LL.1) = w ^ c.val) := by
  intro l _ a e _ _ ϖ LL _ _
  have hp : l.Prime := Fact.out
  obtain ⟨z, hz⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  have he0 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hle : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ l ^ a := dvd_pow_self l (NeZero.ne a)
    rw [← TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a)] at h1
    exact hp.not_dvd_one ((Nat.dvd_add_right h).1 h1)
  have hzO : IsPrimitiveRoot ((z : ↥LL.1) : Om l) e := hz.map_of_injective (f := LL.1.val) LL.1.val.injective
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hπ0 : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
  have hroot : ∀ w : Om l, w ^ e = 1 → ∃ k < e, ((z ^ k : ↥LL.1) : Om l) = w := by
    intro w hw
    obtain ⟨k, hk, h⟩ := hzO.eq_pow_of_pow_eq_one hw
    exact ⟨k, hk, by rw [← h]; rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g _
    have hw : ((g : GQ l) (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, ϖ.seq_zero, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]
    obtain ⟨k, -, hk⟩ := hroot _ hw
    refine ⟨z ^ k, ?_, ?_⟩
    · rw [hk]; field_simp
    · rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  · obtain ⟨g, hg, hgπ⟩ := exists_inertia he0 (ϖ.seq 0) _ ϖ.seq_zero hzO.pow_eq_one
    exact ⟨g, hg, z, hgπ.symm, hz⟩
  · intro χ hχo hχc
    obtain ⟨M0, hM0, hlM0, hM0χ⟩ := chi_trivial LL χ hχo hχc
    have hM : 0 < M0 * e := Nat.mul_pos hM0 he0
    have hlM : ¬ l ∣ M0 * e := fun h => ((Nat.Prime.dvd_mul hp).1 h).elim hlM0 hle
    haveI : NeZero (M0 * e) := ⟨hM.ne'⟩
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (-(l : Om l)) hM
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Om l, IsPrimitiveRoot ζ (M0 * e) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (M0 * e)
    obtain ⟨σ, hσ, hσρ⟩ := exists_inertia hM ρ ζ hρ hζ.pow_eq_one
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
      exact hl0 hρ
    have hζσ : ∀ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → (g : GQ l) ζ = ζ := fun g hg =>
      fix_root g hg hM hlM hζ.pow_eq_one
    have hrat : ∀ g : Gl l, ∃ j : ℕ, (g : GQ l) ρ = ζ ^ j * ρ := by
      intro g
      have h1 : ((g : GQ l) ρ / ρ) ^ (M0 * e) = 1 := by
        rw [div_pow, ← map_pow, hρ, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
      exact ⟨j, by rw [hj]; field_simp⟩
    have hσpow : ∀ j : ℕ, ((σ ^ j : Gl l) : GQ l) ρ = ζ ^ j * ρ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Subgroup.coe_mul, AlgEquiv.mul_apply, hσρ, map_mul, ih, hζσ _ (Subgroup.pow_mem _ hσ j), pow_succ]
        ring
    set σ' : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) := ⟨σ, hσ⟩ with hσ'
    have hχg : ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (j : ℕ), ((g : Gl l) : GQ l) ρ = ζ ^ j * ρ →
        χ g = χ σ' ^ j := by
      intro g j hj
      have hfix : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) ρ = ρ := by
        have h2 := hσpow j
        have h3 : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) =
            ((σ ^ j : Gl l) : GQ l)⁻¹ * ((g : Gl l) : GQ l) := by
          simp [σ']
        rw [h3, AlgEquiv.mul_apply, hj, ← h2]
        exact AlgEquiv.symm_apply_apply _ ρ
      have h1 : χ ((σ' ^ j)⁻¹ * g) = 1 := by
        refine hM0χ (ρ ^ e) (by rw [← pow_mul, mul_comm e M0]; exact hρ) _ ?_
        rw [map_pow, hfix]
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h1
      exact h1.symm
    refine ⟨?_, ?_⟩
    · intro Fr hFr g h hgh
      obtain ⟨j, hj⟩ := hrat g
      obtain ⟨i, hi⟩ := hrat Fr⁻¹
      have hFrζ : (Fr : GQ l) ζ = ζ ^ l := frob_root Fr hFr hM hlM hζ.pow_eq_one
      have hh : (h : Gl l) = Fr * g * Fr⁻¹ := by rw [hgh]; group
      have hFr1 : (Fr : GQ l) (ζ ^ i * ρ) = ρ := by
        rw [← hi]
        show (Fr : GQ l) (((Fr⁻¹ : Gl l) : GQ l) ρ) = ρ
        rw [← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, AlgEquiv.one_apply]
      have hhρ : ((h : Gl l) : GQ l) ρ = ζ ^ (j * l) * ρ := by
        rw [hh, Subgroup.coe_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hi, map_mul,
          map_pow, hζσ g g.2, hj]
        have e1 : ζ ^ i * (ζ ^ j * ρ) = ζ ^ j * (ζ ^ i * ρ) := by ring
        rw [e1, map_mul, hFr1, map_pow, hFrζ, ← pow_mul, mul_comm l j]
      rw [hχg h _ hhρ, hχg g j hj, pow_mul]
    · intro hχe
      have h1 : ((χ σ' : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχe]; rfl
      have hζe : IsPrimitiveRoot (ζ ^ M0) e := hζ.pow hM rfl
      obtain ⟨s, -, hs⟩ := hroot (ζ ^ M0) hζe.pow_eq_one
      have hzs : IsPrimitiveRoot (z ^ s) e := by
        rw [← hs] at hζe
        exact (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val) LL.1.val.injective).1 hζe
      obtain ⟨c, hc, hcz⟩ := hzs.eq_pow_of_pow_eq_one h1
      refine ⟨(c : ZMod e), fun g w hw => ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc]
      obtain ⟨j, hj⟩ := hrat g
      rw [hχg g j hj, Units.val_pow_eq_pow_val, ← hcz]

      have hη : (ϖ.seq 0 / ρ ^ M0) ^ e = 1 := by
        rw [div_pow, ϖ.seq_zero, ← pow_mul, hρ, div_self (neg_ne_zero.2 hl0)]
      have hgη := fix_root (g : Gl l) g.2 he0 hle hη
      have hgπ : ((g : Gl l) : GQ l) (ϖ.seq 0) = (ζ ^ M0) ^ j * ϖ.seq 0 := by
        have e1 : ϖ.seq 0 = (ϖ.seq 0 / ρ ^ M0) * ρ ^ M0 := by field_simp
        rw [e1, map_mul, hgη, map_pow, hj]
        ring
      have hw' : w = (z ^ s) ^ j := by
        apply Subtype.ext
        have e2 : (w : Om l) * ϖ.seq 0 = (ζ ^ M0) ^ j * ϖ.seq 0 := hw.trans hgπ
        rw [mul_left_inj' hπ0, ← hs] at e2
        rw [e2]; rfl
      rw [hw']
      ring

end GlobalTheory.TameIner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

section Scal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem galOD_crisToOD (g : GQ l) (x : OCr l O) :
    galOD O g (crisToOD l O x) = crisToOD l O (galOCr O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.crisP_unique_equivariant l (crisP l) (isCrisP_crisP l)).2.1 g w).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isUnit_natCast_OD {n : ℕ} (hn : n ≠ 0) : IsUnit (n : OD l O) := by
  have h0 : ((n : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  have h1 := congrArg (algebraMap ℤ_[l] (OD l O)) (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul (isUnit_l_OD.pow _)

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]


variable (O K) in
theorem dvd_toOD_mu (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) :
    ϖ.iAl O K (EIn l e _) ∣ toOD l O (1 ⊗ₜ ϖ.mu g) := by
  have hξ : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  have hmem : ϖ.mu g ∈ Ideal.span {ϖ.ev 1 (eis l 1 e)} := by
    rw [ϖ.span_ev_eis 1]
    exact ϖ.theta_mu (ϖ.gal_pi a g)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨1 ⊗ₜ ainfToBdRp l c, ?_⟩
  rw [hξ, ← hc]
  change (1 : O) ⊗ₜ[ℤ_[l]] ainfToBdRp l (c * _) = _
  rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]


variable (O) in
theorem crisToOD_muDiv (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    crisToOD l O (ϖ.muDiv a O g i) = toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) := by
  have h1 := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O)
    (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
  rw [map_mul, map_natCast, map_pow] at h1
  have h2 := congrArg (crisToOD l O) h1
  rw [map_mul, map_natCast, map_pow, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply, ← toOCr_tmul, crisToOD_toOCr] at h2
  have hu := isUnit_natCast_OD (l := l) (O := O) i.factorial_ne_zero
  rw [← h2, mul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rfl


variable (K) in
theorem taylor_S_mod (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (s : S O K e) (R : ℕ) :
    ϖ.iAl O K (EIn l e _) ^ R ∣ galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
  obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ R
  refine GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ R _ fun k => ?_
  obtain ⟨M₀, hM₀⟩ := ϖ.taylor_S a O K g s (N + k)
  obtain ⟨z, hz⟩ := hM₀ (max M₀ R) (le_max_left _ _)
  obtain ⟨y, hy⟩ := hN z
  refine ⟨y, ?_⟩
  have hz' := congrArg (crisToOD l O) hz
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, map_pow, map_natCast, crisToOD_muDiv] at hz'
  rw [← galOD_crisToOD, ← Finset.sum_range_add_sum_Ico _ (le_max_right M₀ R)] at hz'
  have key : galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) - (l : OD l O) ^ k * toOD l O y =
      (l : OD l O) ^ k * ((l : OD l O) ^ N * crisToOD l O z - toOD l O y) +
        ∑ i ∈ Finset.Ico R (max M₀ R), toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    linear_combination hz'
  rw [key]
  refine dvd_add (Dvd.dvd.mul_left hy _) (Finset.dvd_sum fun i hi => ?_)
  have hi' : R ≤ i := (Finset.mem_Ico.1 hi).1
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ hi').trans
    (pow_dvd_pow_of_dvd (dvd_toOD_mu O K ϖ g) i)) _) _

end Scal

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

section Scal2

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] [CompleteSpace K]

theorem taylor_invL_mod (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {f : K⟦X⟧}
    (hf : f ∈ invL l (S O K e)) (R : ℕ) :
    galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i *
      Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f)) ∈
      Ideal.span {ϖ.iAl O K (EIn l e _) ^ R} := by
  have hiHat : ∀ (f' : K⟦X⟧) (hf' : f' ∈ invL l (S O K e)), ϖ.iHat O K (hatR O f') = ϖ.iSD O K ⟨f', hf'⟩ :=
    fun f' hf' => (GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ ⟨f', hf'⟩ (hatR O f') (by
      rw [hatR_of_mem (O := O) (invL_S_le_Rpi l e hf')]
      exact hat_coe_Rpi l e ⟨f', invL_S_le_Rpi l e hf'⟩)).symm
  obtain ⟨n, hn⟩ := hf
  have hC : ((l : S O K e) : K⟦X⟧) ^ n = C ((l : K) ^ n) := by simp
  have hlin : ∀ (i : ℕ) (x : K⟦X⟧), ((l : S O K e) : K⟦X⟧) ^ n * descN K i x =
      descN K i (((l : S O K e) : K⟦X⟧) ^ n * x) := fun i x => by
    rw [hC, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  have hdesc : ∀ i : ℕ, descN K i f ∈ invL l (S O K e) := fun i =>
    ⟨n, by rw [hlin]; exact descN_mem_S e i hn⟩
  set s : S O K e := ⟨_, hn⟩ with hs
  have e0 : (l : OD l O) ^ n * ϖ.iSD O K ⟨f, ⟨n, hn⟩⟩ = crisToOD l O (ϖ.iS O K s) := by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨f, ⟨n, hn⟩⟩ = algebraMap (S O K e) (invL l (S O K e)) s :=
      Subtype.ext (by simp [s])
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K s.2 _
  have ei : ∀ i : ℕ, (l : OD l O) ^ n * ϖ.iSD O K ⟨descN K i f, hdesc i⟩ =
      crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := fun i => by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨descN K i f, hdesc i⟩ =
        algebraMap (S O K e) (invL l (S O K e)) ⟨descN K i s, descN_mem_S e i s.2⟩ :=
      Subtype.ext (by
        change ((l : K⟦X⟧)) ^ n * descN K i f = descN K i (((l : S O K e) : K⟦X⟧) ^ n * f)
        rw [← hlin]
        simp)
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K (descN_mem_S e i s.2) _
  have g0 := congrArg (galOD O g) e0
  rw [map_mul, map_pow, map_natCast] at g0
  have key : (l : OD l O) ^ n * (galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f))) =
      galOD O g (crisToOD l O (ϖ.iS O K s)) -
        ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    rw [hiHat f ⟨n, hn⟩, ← g0, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hiHat _ (hdesc i), ← ei i]
    ring
  have hW := Ideal.mem_span_singleton.2 (taylor_S_mod K ϖ g s R)
  rw [← key] at hW
  exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_l_OD.pow n)).1 hW

theorem galOD_idem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (τ : ZMod a) :
    galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  have h : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (ϖ.Kunr_le_field a hx)
  change galOD O g (toOD l O (constA t _)) = toOD l O (constA t _)
  rw [← crisToOD_toOCr, galOD_crisToOD, galOCr_toOCr, galOA_constA t h]

end Scal2

theorem taylor_iD_mod_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ g hg f hf R
  let g' : ↥(GK (ϖ.field a)) := ⟨g, hg⟩
  have hED : ED K t ϖ = ϖ.iAl O K (EIn l e _) := (glue_const _ _ _).trans (ϖ.iHat_ofAl O K _)
  rw [hED]
  have hfix : ∀ τ, galOD O g (idem (constD t) τ) = idem (constD t) τ := galOD_idem t ϖ g'
  have hsplit : galOD O g (ϖ.iD t K (fun τ => hatR O (f τ))) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) =
      ∑ τ, idem (constD t) τ * (galOD O g (ϖ.iHat O K (hatR O (f τ))) - ∑ i ∈ Finset.range R,
        toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          ϖ.iHat O K (hatR O (descN K i (f τ)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PiSys.iD, glue_apply, map_sum, map_mul, hfix, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  exact Ideal.sum_mem _ fun τ _ => Ideal.mul_mem_left _ _ (taylor_invL_mod t ϖ g' (hf τ) R)

end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerTiltMinusOneAssociated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.EpsilonAssociated

theorem isEps_bk {l : ℕ} [Fact l.Prime] {e : OCb l} (h : IsEps e) : GlobalTheory.BKGal.IsEps e :=
  ⟨h.1, (frobeniusEquiv (OCb l) l).symm e, frobeniusEquiv_symm_pow_p (OCb l) l e, h.2⟩

theorem mu_associated : ∀ (l : ℕ) [Fact l.Prime] (e e' : OCb l), IsEps e → IsEps e' →
    Associated (mu e) (mu e') := by
  intro l _ e e' he he'
  have h1 : mu e ∣ mu e' := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he) he'.1
  have h2 : mu e' ∣ mu e := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he') he.1
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hne : mu e ≠ 0 := GlobalTheory.MuOfEps.muOf_ne_zero (isEps_bk he)
  have hab : a * b = 1 := by
    have h3 : (a * b - 1) * mu e = 0 := by
      have : mu e = mu e * a * b := by rw [← ha]; exact hb
      linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end GlobalTheory.EpsilonAssociated
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectiv
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem injective_of_charZero {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {K : Type} [Field K] [CharZero K]
    (f : Wq l a →+* K) : Function.Injective f := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l a) w h0
  rw [map_mul, map_pow, map_natCast] at hw
  have hb : f b ≠ 0 := (b.isUnit.map f).ne_zero
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  exact mul_ne_zero (pow_ne_zero m hl) hb hw

theorem emb_algebraMap_injective : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact injective_of_charZero ((algebraMap O K).comp (emb t τ).toRingHom)

end GlobalTheory.CrysPrism
end
end

