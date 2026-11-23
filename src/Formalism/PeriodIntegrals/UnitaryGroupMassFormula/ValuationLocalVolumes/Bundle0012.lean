module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0010

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CorOneRed
section
noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem card_clsP (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K)
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (PI.OmVd.clsP σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K //
        ffGram τ 1 X = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K X} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M =>
    ffGram τ 1 M = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K M with hP
  have hset : PI.OmVd.clsP σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, ⟨hyP, hyN⟩, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact ⟨(nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hyN,
          (prim_iff σ J v Λ hSD he he1 hL hϖ hπ y).1 hyP⟩
      · intro hx
        have h2 : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at h2
        exact ⟨x, ⟨(prim_iff σ J v Λ hSD he he1 hL hϖ hπ x).2 h2.2,
          (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 h2.1⟩, rfl⟩
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

def GramCor (ϖ : Fv F v) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j ∈ PO (E := E) v ϖ) ∧ (∀ j, T j i₀ ∈ PO (E := E) v ϖ) ∧
    ∃ w ∈ OEv (E := E) v, (T + Matrix.single i₀ i₀ 1).det * w = 1

theorem corOne_red {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) (hC : GramCor v ϖ T) :
    PI.OmVd.CorOne (fun i j => π ⟨T i j, hT i j⟩ : Matrix (Fin a) (Fin a) K) := by
  obtain ⟨i₀, hr, hc, w, hw, hd⟩ := hC
  refine ⟨i₀, fun j => (hπ.2.1 _).2 (hr j), fun j => (hπ.2.1 _).2 (hc j), ?_⟩
  have hT' : ∀ i j, (T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OR (E := E) v := by
    intro i j
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (OR (E := E) v).add_mem (hT i j) (OR (E := E) v).one_mem
    · simpa using hT i j
  convert det_red v π _ hT' hw hd using 2
  congr 1
  ext i j
  by_cases h : i₀ = i ∧ i₀ = j
  · obtain ⟨h1', h2'⟩ := h
    subst h1'
    subst h2'
    have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i₀ i₀, hT' i₀ i₀⟩ :
        OR (E := E) v) = ⟨T i₀ i₀, hT i₀ i₀⟩ + 1 := by
      apply Subtype.ext
      simp [Matrix.add_apply]
    rw [h1, map_add (f := _), map_one]
    show π ⟨T i₀ i₀, hT i₀ i₀⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i₀ i₀ = _
    simp
  · have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hT' i j⟩ :
        OR (E := E) v) = ⟨T i j, hT i j⟩ := by
      apply Subtype.ext
      simp [Matrix.add_apply, Matrix.single_apply, h]
    rw [h1]
    show π ⟨T i j, hT i j⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i j = _
    simp [Matrix.single_apply, h]

theorem redP_of_gramCor (a : ℕ) (Y : TupV (E := E) v n a)
    (hC : ∀ ϖ : Fv F v, IsUnif v ϖ → GramCor v ϖ (gramR (Fv F v) σ J Y)) :
    PI.OmVd.RedP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hR : ResAlg σ J ψ v := resAlg_of_sp σ J ψ v (etaSp_holds σ J ψ v)
  have hU : Orb.UnitV σ J ψ v Λ :=
    Orb.unitV_of σ J ψ v Λ (NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  have hL := hG.2.1
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hL hSD hG.2.2.2.1
  have hY := hG.2.2.2.2.2.1
  have hT : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OR (E := E) v := fun i j =>
    (hSD (Y j)).1 (hY j) (Y i) (hY i)
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmVg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHoldsAlt
section
noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix

theorem fFInertB_holds : PI.OmVd.FFInertB := by
  intro k K _ _ _ _ σ hσ h2 hne M a haM J hJ hdJ T hT hTu
  classical
  obtain ⟨i₀, hr, hc, hu⟩ := hTu
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := i₀.pos; omega⟩
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hJ' : ∀ i j, (σ : K →+* K) (J j i) = J i j := hJ
  have hu0 : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
    have e := det_corOne T i₀ hr 1
    rw [one_mul] at e
    rw [← e]; exact hu
  have hTt : ∀ c : k, c ≠ 0 →
      (∀ i j, σ ((T + Matrix.single i₀ i₀ (algebraMap k K c)) j i) =
        (T + Matrix.single i₀ i₀ (algebraMap k K c)) i j) ∧
      IsUnit (T + Matrix.single i₀ i₀ (algebraMap k K c)).det := by
    intro c hc0
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), hT, Matrix.single_apply, Matrix.single_apply]
      congr 1
      split_ifs with h1 h2 h2 <;> first | exact AlgEquiv.commutes σ c | exact map_zero σ | (exfalso; tauto)
    · rw [det_corOne T i₀ hr]
      exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hc0)).mul hu0
  have hN : ∀ c : k, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K c)} =
      Nat.card {X : Fin (a' + 1) → Fin M → K //
        ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K 1)} := by
    intro c hc0
    have e1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt c hc0).1 (hTt c hc0).2
    have e2 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
      (hTt 1 one_ne_zero).2
    exact_mod_cast e1.trans e2.symm
  have hD : ∀ Y : Fin a' → Fin M → K, ffGram (σ : K →+* K) J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH (σ : K →+* K) J (Y j) x = 0) ∧ ffH (σ : K →+* K) J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = 1 := by
    intro Y _
    rw [Nat.card_eq_one_iff_unique]
    have h0 : ∀ z : Fin M → K, ¬ (∀ c : K, c • z = 0 → c = 0) → z = 0 := fun z hz => by
      by_contra h0
      exact hz (fun c hc => (smul_eq_zero.1 hc).resolve_right h0)
    refine ⟨⟨fun x y => Subtype.ext ((h0 x.1 x.2.2.2).trans (h0 y.1 y.2.2.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩
    exact ⟨fun j => ffH_zero_right _ _ _, ffH_zero_left _ _ _, fun h => one_ne_zero (h 1 (smul_zero 1))⟩
  have hcnt := count_gen (σ : K →+* K) J hσ' hJ' T i₀ hr hc hu (by omega) (ι := algebraMap k K)
    (algebraMap k K).injective (map_zero _)
    (fun x => fixed_mem_range σ h2 hne _ (ffH_herm (σ : K →+* K) J hσ' hJ' x x).symm) _ 1 hN hD
  have hF0 := fFInert2_holds k K σ hσ h2 hne M a' (by omega) J hJ hdJ
    (T.submatrix i₀.succAbove i₀.succAbove) (fun i j => hT _ _) hu0
  have hN1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
    (hTt 1 one_ne_zero).2
  have h1k : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hKk : Nat.card K = Nat.card k ^ 2 := by simp only [Nat.card_eq_fintype_card]; exact hK
  rw [hKk] at hcnt
  have hR := congrArg (fun n : ℕ => (n : ℝ)) hcnt
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_one] at hR
  rw [hF0, hN1] at hR
  have hx : (Nat.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [prodInert_closed _ hx M a' (by omega), prodInert_closed _ hx M (a' + 1) haM] at hR
  obtain ⟨n, hn⟩ : ∃ n, M = a' + 1 + n := ⟨M - (a' + 1), by omega⟩
  have eE : 2 * M * (a' + 1) - (a' + 1) ^ 2 = (2 * M * a' - a' ^ 2) + (2 * n + 1) := by
    subst hn
    have h3 : a' ^ 2 ≤ 2 * (a' + 1 + n) * a' := by nlinarith
    have h4 : (a' + 1) ^ 2 ≤ 2 * (a' + 1 + n) * (a' + 1) := by nlinarith
    zify [h3, h4]
    ring
  have i1 : Finset.Icc (M - (a' + 1) + 1) M = insert (n + 1) (Finset.Icc (n + 2) M) := by
    rw [show M - (a' + 1) + 1 = n + 1 by omega]
    exact (Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm
  have i0 : Finset.Icc (M - (a' + 1)) M = insert n (insert (n + 1) (Finset.Icc (n + 2) M)) := by
    rw [show M - (a' + 1) = n by omega, ← Finset.insert_Icc_add_one_left_eq_Icc (show n ≤ M by omega),
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n + 1 ≤ M by omega)]
    rfl
  rw [show M - a' + 1 = n + 2 by omega, show M - a' = n + 1 by omega, eE, pow_add, i1,
    Finset.prod_insert (by simp)] at hR
  rw [eE, pow_add, i0, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  set P0 := ∏ j ∈ Finset.Icc (n + 2) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))
  set x := (Nat.card k : ℝ)
  set E0 := 2 * M * a' - a' ^ 2
  linear_combination hR + (x ^ E0 * P0) * keyInert x hx n

end PI.OmVe
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFSplitBHolds
section
noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem fFSplitB_holds : PI.OmVd.FFSplitB := by
  intro k _ _ M a haM J hJ hJdet T hT hcor
  obtain ⟨i₀, hrow, hcol, hunit⟩ := hcor
  cases a with
  | zero => exact i₀.elim0
  | succ a' =>
    have hσ : ∀ x : k × k, RingEquiv.prodComm.toRingHom x = x.swap := fun x => rfl
    have hsub : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
      have := PI.OmVe.det_corOne T i₀ hrow 1
      rw [this, one_mul] at hunit
      exact hunit
    have hinv : ∀ x : k × k, RingEquiv.prodComm.toRingHom (RingEquiv.prodComm.toRingHom x) = x := fun x => by simp [hσ]
    have hJ' : ∀ i j, RingEquiv.prodComm.toRingHom (J j i) = J i j := fun i j => by rw [hσ]; exact hJ i j
    have hdiag : ∀ x : Fin M → k × k, ∃ c : k, PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x = (c, c) := by
      intro x
      have h := PI.OmVe.ffH_herm RingEquiv.prodComm.toRingHom J hinv hJ' x x
      refine ⟨(PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x).1, ?_⟩
      rw [hσ] at h
      ext
      · rfl
      · exact (congrArg Prod.fst h).symm.trans rfl
    have hTs : ∀ i j, ((T.submatrix i₀.succAbove i₀.succAbove) j i).swap = (T.submatrix i₀.succAbove i₀.succAbove) i j := fun i j => hT _ _
    have hY := PI.VolStabSW.fFSplit_holds k M a' (by omega) J hJ hJdet _ hTs hsub
    have hNr : ∀ c : k, c ≠ 0 → (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ (c, c) } : ℝ) = (∏ i : Fin (a' + 1), ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) * (Nat.card k : ℝ) ^ ((a' + 1) * (M - (a' + 1))) := by
      intro c hc
      have hdet : IsUnit (T + Matrix.single i₀ i₀ (c, c)).det := by
        rw [PI.OmVe.det_corOne T i₀ hrow]
        refine IsUnit.mul ?_ hsub
        exact (Prod.isUnit_iff).2 ⟨isUnit_iff_ne_zero.2 hc, isUnit_iff_ne_zero.2 hc⟩
      have hh : ∀ i j, ((T + Matrix.single i₀ i₀ (c, c)) j i).swap = (T + Matrix.single i₀ i₀ (c, c)) i j := by
        intro i j
        rw [Matrix.add_apply, Matrix.add_apply, ← hT i j, Matrix.single_apply, Matrix.single_apply]
        by_cases h1 : i₀ = i <;> by_cases h2 : i₀ = j <;> ext <;> simp [h1, h2] <;> split_ifs <;> rfl
      exact PI.VolStabSW.fFSplit_holds k M (a' + 1) haM J hJ hJdet _ hh hdet
    have key := PI.OmVe.count_gen RingEquiv.prodComm.toRingHom J hinv hJ' T i₀ hrow hcol hunit (by omega) (k := k) (fun c => (c, c)) (fun c d h => by simpa using congrArg Prod.fst h) rfl
    specialize key hdiag
    clear hinv hJ' hdiag hσ
    have hk1 : 1 ≤ Nat.card k := Nat.card_pos
    have hk := key (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ ((1 : k), (1 : k)) }) (2 * Nat.card k ^ (M - a') - 1)
      (fun c hc => Nat.cast_injective (R := ℝ) ((hNr c hc).trans (hNr 1 one_ne_zero).symm))
      (fun Y hY' => by
        have := PI.OmVe.dcount_split J (by omega) _ hsub Y hY'
        have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1
        omega)
    have hN1 := hNr 1 one_ne_zero
    clear key hNr
    rw [Nat.card_prod] at hk
    have hkR := congrArg (fun n : ℕ => (n : ℝ)) hk
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk1, Nat.cast_one] at hkR
    rw [Nat.cast_sub (by have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1; omega)] at hkR
    rw [hY, hN1] at hkR
    push_cast at hkR
    have hq : (1 : ℝ) ≤ Nat.card k := by exact_mod_cast hk1
    generalize ((Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T ∧ LinearIndependent (k × k) X } : ℕ) : ℝ) = C at hkR ⊢
    generalize (Nat.card k : ℝ) = q at hkR hq ⊢
    clear hk hY hN1 hTs hsub hunit hrow hcol hT hJdet hJ
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le haM
    clear haM T J i₀
    have hq0 : q ≠ 0 := by positivity
    have e1 : a' + 1 + r - a' = r + 1 := by omega
    have e2 : a' + 1 + r - (a' + 1) = r := by omega
    have e3 : 2 * (a' + 1 + r) * (a' + 1) - (a' + 1) ^ 2 = (a' + 1) ^ 2 + 2 * r * (a' + 1) := Nat.sub_eq_of_eq_add (by ring)
    have hP := PI.OmVe.prodSplit_closed q hq0 (a' + 1 + r) a' (by omega)
    rw [e1] at hP hkR
    rw [e2] at hkR
    rw [e2, e3]
    simp only [one_pow, one_mul]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r ≤ a' + 1 + r), Finset.prod_insert (by simp), ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r + 1 ≤ a' + 1 + r), Finset.prod_insert (by simp)]
    rw [Fin.prod_univ_castSucc] at hkR
    simp only [Fin.coe_castSucc, Fin.val_last] at hkR
    rw [hP] at hkR
    have hK := PI.OmVe.keySplit q hq0 r
    have e : q ^ (2 * r + 1) * (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = (q ^ (r + 1) - 1) * q ^ r := by
      rw [_root_.zpow_neg, zpow_natCast]
      field_simp
      ring
    generalize (∏ j ∈ Finset.Icc (r + 1 + 1) (a' + 1 + r), (1 - q ^ (-(j : ℤ)))) = Pi' at hkR ⊢
    generalize (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = B at hK e ⊢
    generalize (1 - q ^ (-(r : ℤ))) = A at hK ⊢
    linear_combination hkR + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1))) * hK + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1)) * (q - 1)) * e

end PI.OmVe
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFourX
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LatBasOP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
    ∀ x, x ∈ latLoc (E := E) v Λ ↔ ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i

def IdxVP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

theorem localLattice_hasBasis
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set _) = Λ) (a : ℕ) (Y : TupV (E := E) v n a) : LatBasOP σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, -, -⟩
  obtain ⟨L, hLat, rfl⟩ := hFull
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem idxVP_of (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasOP σ J ψ v Λ a Y) (hR : ResIdx v) :
    IdxVP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := hB hG
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem idxP_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxVP σ J ψ v Λ a Y) : IdxP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem MeasP₂
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set _) = Λ) (a : ℕ) (Y : TupV (E := E) v n a) : MeasP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := (lamOC_holds v Λ a hFull hG.2.1).1
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

theorem idxP_holds
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set _) = Λ) (a : ℕ) (Y : TupV (E := E) v n a) : IdxP σ J ψ v Λ a Y :=
  idxP_of σ J ψ v Λ a Y (idxVP_of σ J ψ v Λ a Y (localLattice_hasBasis σ J ψ v Λ hFull a Y) (resIdx_holds v))

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_primDual_cls (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ := by
  have hFull : ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧ (L : Set _) = abelian₂ X :=
    ⟨X.B.I.L, { toIsLattice := Submodule.IsLattice.of_fg _ X.B.I.L_fg, span_eq_top := X.B.I.L_span }, rfl⟩
  exact omVBadT_of_steps X u' ψ hStd hLat hGram hExt hPC hPD (fun v => MeasP₂ _ _ _ _ _ hFull _ _)
    (fun v => idxP_holds _ _ _ _ _ hFull _ _) hCl

end Loc

end PI.OmVd
end
end

