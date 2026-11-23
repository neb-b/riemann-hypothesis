module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermZeroRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRed
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open PI.VolStabSW PI.OmLocU.CntFF
open scoped TensorProduct

theorem prod_fin_rev (f : ℕ → ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, f (n - (j : ℕ)) = ∏ i ∈ Finset.Icc (n - a + 1) n, f i := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show n - (a + 1) + 1 = n - a by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n - a ≤ n by omega), Finset.prod_insert (by simp), mul_comm]

theorem prod_pow_rev (q : ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) = q ^ (2 * n * a - a ^ 2) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), ← pow_add]
    congr 1
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * m * a := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * m * (a + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2, show 2 * (a + 1 + m - a) - 1 = 2 * m + 1 by omega]
    ring

theorem inert_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    ∏ j : Fin a, (q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1) =
      q ^ (2 * (n - (j : ℕ)) - 1) * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf]
    have e : q ^ (2 * (n - (j : ℕ)) - 1) * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (n - (j : ℕ) - 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub (show 1 ≤ 2 * (n - (j : ℕ)) by omega), Nat.cast_sub hj.le,
        Nat.cast_sub (show 1 ≤ n - (j : ℕ) by omega)]
      ring
    rw [mul_sub, mul_one, ← e]
    ring
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_pow_rev q n a ha,
    prod_fin_rev f n a ha]

theorem split_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    (∏ i : Fin a, (q ^ n - q ^ (i : ℕ))) * q ^ (a * (n - a)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ n - q ^ (j : ℕ) = q ^ n * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf, one_pow, one_mul]
    have e : q ^ n * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (j : ℕ) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub hj.le]
      ring
    rw [mul_sub, mul_one, e]
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_fin_rev f n a ha,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have e : n * a + a * (n - a) = 2 * n * a - a ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [show a + m - a = m by omega]
    symm; apply Nat.sub_eq_of_eq_add; ring
  rw [← e, pow_add]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T'}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T'}))

theorem clsU_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedU σ J ψ v Λ a Y) : ClsU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, fFInert2_holds k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact inert_prod (qv v) hq n a ha
  · rw [hc, fFSplit_holds k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact split_prod (qv v) hq n a ha

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfUnitV
section
noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PerpG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Set (Fin n → Fv F v ⊗[F] E) :=
  {w | w ∈ latLoc (E := E) v Λ ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0}

def gramG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Matrix ι ι (Fv F v ⊗[F] E) :=
  fun a b => hR (Fv F v) σ J (X a) (X b)

def UniG {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ w ∈ OEv (E := E) v, (gramG σ J v X).det * w = 1

def UnitV : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, hR (Fv F v) σ J p p = 1 ∧ ∀ i, hR (Fv F v) σ J p (X i) = 0

theorem hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perp_full {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hU : UniG σ J v X) (hc : Fintype.card ι = n) (w : Fin n → Fv F v ⊗[F] E)
    (hw : ∀ i, hR (Fv F v) σ J (X i) w = 0) : w = 0 := by
  obtain ⟨u, -, hu⟩ := hU
  have hG : IsUnit (gramG σ J v X).det := ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  let eq : ι ≃ Fin n := Fintype.equivFinOfCardEq hc
  let M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun i m => X (eq.symm m) i
  have hA : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) M * JR (Fv F v) J * M = (gramG σ J v X).submatrix eq.symm eq.symm := by
    ext p q
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply, gramG, hR, hform, Matrix.submatrix_apply]
    exact Finset.sum_comm
  have hdA : IsUnit (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) M * JR (Fv F v) J).det := by
    have h1 := congrArg det hA
    rw [det_submatrix_equiv_self, det_mul] at h1
    rw [← h1] at hG
    exact isUnit_of_mul_isUnit_left hG
  have hB : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) M * JR (Fv F v) J) *ᵥ w = 0 := by
    funext m
    have h2 := hw (eq.symm m)
    simp only [hR, hform] at h2
    simp only [Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact h2
  have h3 := congrArg (fun y => (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) M * JR (Fv F v) J)⁻¹ *ᵥ y) hB
  simpa [mulVec_mulVec, nonsing_inv_mul _ hdA] using h3

theorem orthoGen (hU : UnitV σ J ψ v Λ) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) (hun : UnramAt (E := E) v) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E),
      Fintype.card ι + k = n → (∀ i, X i ∈ latLoc (E := E) v Λ) → UniG σ J v X →
      ∃ e : Fin k → Fin n → Fv F v ⊗[F] E, (∀ j, e j ∈ PerpG σ J v Λ X) ∧
        (∀ i j, hR (Fv F v) σ J (e j) (X i) = 0) ∧ gramR (Fv F v) σ J e = 1 ∧
        ∀ w ∈ PerpG σ J v Λ X, ∃ d : Fin k → Fv F v ⊗[F] E, (∀ j, d j ∈ OEv (E := E) v) ∧
          w = ∑ j, d j • e j := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ X hc hX hUX
    refine ⟨Fin.elim0, fun j => j.elim0, fun i j => j.elim0, ?_, ?_⟩
    · ext i
      exact i.elim0
    · intro w hw
      refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact perp_full σ J v X hUX (by omega) w hw.2
  | succ k ih =>
    intro ι _ _ X hc hX hUX
    obtain ⟨p, hp, hpp, hpX⟩ := hU hstd hL hsd hun ι X hX hUX (by omega)
    let X' : ι ⊕ Unit → Fin n → Fv F v ⊗[F] E := Sum.elim X (fun _ => p)
    have hG' : gramG σ J v X' = Matrix.fromBlocks (gramG σ J v X) 0 0 1 := by
      ext s t
      rcases s with i | ⟨⟩ <;> rcases t with j | ⟨⟩
      · rfl
      · simp [gramG, X', hp.2 i]
      · simp [gramG, X', hpX j]
      · simp [gramG, X', hpp]
    have hU' : UniG σ J v X' := by
      obtain ⟨u, hu0, hu⟩ := hUX
      refine ⟨u, hu0, ?_⟩
      rw [hG', det_fromBlocks_zero₂₁, det_one, mul_one, hu]
    have hX' : ∀ s, X' s ∈ latLoc (E := E) v Λ := by
      rintro (i | ⟨⟩)
      · exact hX i
      · exact hp.1
    obtain ⟨e', he'P, he'X, he'e, he'span⟩ :=
      ih (ι ⊕ Unit) X' (by rw [Fintype.card_sum, Fintype.card_unit]; omega) hX' hU'
    refine ⟨Fin.cons p e', ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases hp (fun j => ⟨(he'P j).1, fun i => (he'P j).2 (Sum.inl i)⟩) j
    · intro i j
      refine Fin.cases (hpX i) (fun j => he'X (Sum.inl i) j) j
    · ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa [gramR] using hpp
      · have h1 : hR (Fv F v) σ J p (e' j) = 0 := (he'P j).2 (Sum.inr ())
        simpa [gramR, Matrix.one_apply, (Fin.succ_ne_zero j).symm] using h1
      · have h1 : hR (Fv F v) σ J (e' i) p = 0 := he'X (Sum.inr ()) i
        simpa [gramR, Matrix.one_apply, Fin.succ_ne_zero] using h1
      · simpa [gramR, Matrix.one_apply] using congrFun (congrFun he'e i) j
    · intro w hw
      set c := hR (Fv F v) σ J p w with hcdef
      have hc0 : c ∈ OEv (E := E) v := (hsd w).1 hw.1 p hp.1
      have hw' : w - c • p ∈ PerpG σ J v Λ X' := by
        refine ⟨Submodule.sub_mem _ hw.1 (oSmul v Λ hL c hc0 p hp.1), ?_⟩
        rintro (i | ⟨⟩)
        · show hR (Fv F v) σ J (X i) (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hw.2 i, hp.2 i, mul_zero, sub_zero]
        · show hR (Fv F v) σ J p (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hpp, mul_one, ← hcdef, sub_self]
      obtain ⟨d', hd'O, hd'⟩ := he'span _ hw'
      refine ⟨Fin.cons c d', fun j => Fin.cases hc0 hd'O j, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hd']
      abel

theorem orthoB_of (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrthoB σ J ψ v Λ a Y := by
  intro h hG X hX hXY
  obtain ⟨w, hw0, -, hw⟩ := hG.2.2.2.2.2.2
  rw [← hXY] at hw
  exact orthoGen σ J ψ v Λ hU hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 (n - a) (Fin a) X
    (by rw [Fintype.card_fin]; omega) hX ⟨w, hw0, hw⟩

theorem orbAll_of_unitV (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_orthoB σ J ψ v Λ a Y (oSub v) (oSmul v Λ) (orthoB_of σ J ψ v Λ a Y hU)

end PI.OmLocU.Orb
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.SdUniqW
open scoped TensorProduct

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LW (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun {_ _} hx hy i => Submodule.add_mem _ (hx i) (hy i)
  zero_mem' := fun _ => Submodule.zero_mem _
  neg_mem' := fun {_} hx i => Submodule.neg_mem _ (hx i)

theorem coe_LW (a : ℕ) : (LW v Λ a : Set (TupV (E := E) v n a)) = LamT v Λ a := rfl

theorem smul_mem_LW {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {X : TupV (E := E) v n a} (hX : X ∈ LW v Λ a) : s • X ∈ LW v Λ a :=
  fun i => Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) (hX i)

def TopW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsCompact (LamT (E := E) v Λ a) ∧ IsOpen (LamT (E := E) v Λ a)

def DualW (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    {Y : TupV (E := E) v n a | ∀ X ∈ LamT v Λ a,
      dV v * BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (LW v Λ a) : Set (TupV (E := E) v n a))

def IdxW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v →
    ((LW v Λ a).relIndex (smulSub (dV v)⁻¹ (LW v Λ a)) : ℝ) = absV v (dV v) ^ (-(2 * ((n : ℝ) * a)))

theorem sdVolW_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopW v Λ a) (hD : DualW σ J ψ v Λ a)
    (hI : IdxW v Λ a) : SdVolW σ J ψ v Λ a := by
  intro hS hL hSD hU hμ
  have hd0 := dV_ne_zero v
  have hμsd : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    simp only [dX, dif_pos hμ]
    exact hμ.choose_spec
  have := hμsd.1
  set μ := dX σ J ψ v a with hμdef
  set L := LW v Λ a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT hL
  rw [← coe_LW] at hLc hLo
  have hL'c : IsCompact (L' : Set (TupV (E := E) v n a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (TupV (E := E) v n a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J (t + x) y) =
      psiV F ψ v (BR (Fv F v) σ J t y) * psiV F ψ v (BR (Fv F v) σ J x y) := by
    intro x t y
    rw [BR_add, psiV_add]
  have h0 : ∀ y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J y 0) = 1 := by
    intro y
    have e := SdDualW.BR_smul_right v σ J 0 y y
    rw [zero_smul, zero_mul] at e
    rw [e, psiV_zero]
  have hA : ann (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) (L : Set (TupV (E := E) v n a)) = L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (BR (Fv F v) σ J) _ (hC hS)]
    · exact hD hS hL hSD hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_LW v Λ hs hx, fun y => SdDualW.BR_smul_left v σ J s x y⟩
  have hle : L ≤ L' := by
    intro X hX
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • X, smul_mem_LW v Λ (dV_int v) hX, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hN1 := hI hL hU
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-(2 * ((n : ℝ) * a)))
    linarith
  have key := Sd.vol_sq_mul_index hμsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have e1 : absV v (dV v) ^ (-(2 * ((n : ℝ) * a))) = (absV v (dV v) ^ (2 * ((n : ℝ) * a)))⁻¹ :=
    Real.rpow_neg hp.le _
  have e2 : (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 = absV v (dV v) ^ (2 * ((n : ℝ) * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    ring_nf
  have hA2 : 0 < absV v (dV v) ^ (2 * ((n : ℝ) * a)) := Real.rpow_pos_of_pos hp _
  rw [e1] at key
  have e3 : μ.real (L : Set (TupV (E := E) v n a)) ^ 2 = (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 := by
    rw [e2]
    field_simp at key
    rw [key, mul_assoc]
  have hvol := (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  rw [← coe_LW, ← ENNReal.ofReal_toReal hLc.measure_lt_top.ne, ← measureReal_def, hvol]

end Steps

end PI.OmLocU
end
end

