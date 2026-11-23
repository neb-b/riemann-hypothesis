module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.IsUnitDetOfOneAdd
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem dvd_pow_of_vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp0 : (p : O) ≠ 0) (hpm : ¬ IsUnit (p : O)) {z : O} (hz : z ≠ 0) {D : ℕ} (h : vLEO p z D) :
    z ∣ (p : O) ^ D := by
  classical
  unfold vLEO at h
  obtain ⟨q, hq, hqD⟩ := h
  unfold vO vK ordW at hq
  have hx0 : algebraMap O (KK O) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz
  rw [if_neg hx0] at hq
  dsimp only at hq
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab
    at hq hspec
  have h1 : ab.1 = z * (ab.2 : O) := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul]
    exact hspec.symm
  have hs0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [h1, AddValuation.map_mul, ENat.toNat_add hzt hst] at hq
  simp only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq
  have he1 : 1 ≤ ramE p O := by
    unfold ramE
    by_contra hlt
    have h0 : (IsDiscreteValuationRing.addVal O (p : O)).toNat = 0 := by omega
    have h0' : IsDiscreteValuationRing.addVal O (p : O) = 0 := by
      rcases ENat.toNat_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hpt
    apply hpm
    apply isUnit_of_dvd_one
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, h0']
    exact zero_le
  have hepos : (0 : ℝ) < (ramE p O : ℝ) := by exact_mod_cast he1
  have hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) ≤ (D : ℝ) * (ramE p O : ℝ) := by
    rw [← hq] at hqD
    push_cast at hqD
    rwa [div_le_iff₀ hepos] at hqD
  have hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ D * ramE p O := by exact_mod_cast hreal
  unfold ramE at hnat
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, ← ENat.coe_toNat hzt,
    ← ENat.coe_toNat hpt, nsmul_eq_mul]
  exact_mod_cast hnat

theorem isUnit_det_of_one_add {O : Type*} [CommRing O] [IsLocalRing O] {M : ℕ} (P : Matrix (Fin M) (Fin M) O)
    (h : ∀ i l, P i l - (1 : Matrix (Fin M) (Fin M) O) i l ∈ IsLocalRing.maximalIdeal O) : IsUnit P.det := by
  have hmap : P.map (IsLocalRing.residue O) = 1 := by
    ext i l
    have h2 : IsLocalRing.residue O (P i l) =
        IsLocalRing.residue O ((1 : Matrix (Fin M) (Fin M) O) i l) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h i l
    rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
    Matrix.det_one]
  exact one_ne_zero

theorem goodRank_core {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module O X]
    (π : O) (A : Submodule O X) {M : ℕ} (φ : Fin M → X → Kf) (D : ℕ)
    (hadd : ∀ i G G', φ i (G + G') = φ i G + φ i G') (hsmul : ∀ i (c : O) G, φ i (c • G) = algebraMap O Kf c * φ i G)
    (Y : Fin M → X) (hY : ∀ l, Y l ∈ A) (P : Matrix (Fin M) (Fin M) O) (zc zc' : Fin M → O)
    (hz : ∀ l, zc' l * zc l = π ^ D) (hφ : ∀ i l, φ i (Y l) = algebraMap O Kf (P i l * zc l))
    (hP : IsUnit P.det) : GoodRankK π A φ M D := by
  classical
  have hsum : ∀ i (G : Fin M → X), φ i (∑ l, G l) = ∑ l, φ i (G l) := fun i G =>
    map_sum (AddMonoidHom.mk' (φ i) (hadd i)) G Finset.univ
  let v : (Fin M → O) →ₗ[O] X :=
    { toFun := fun x => ∑ l, (zc' l * x l) • Y l
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]
        congr 1
        ring }
  have hv : ∀ x, v x ∈ A := fun x => by
    show (∑ l, (zc' l * x l) • Y l) ∈ A
    exact A.sum_mem fun l _ => A.smul_mem _ (hY l)
  have key : ∀ x i, φ i (v x) = algebraMap O Kf (π ^ D * (P.mulVec x) i) := by
    intro x i
    show φ i (∑ l, (zc' l * x l) • Y l) = _
    rw [hsum]
    simp only [hsmul, hφ]
    simp only [Matrix.mulVec, dotProduct]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← map_mul]
    congr 1
    rw [← hz l]
    ring
  refine ⟨LinearMap.codRestrict A v hv, P⁻¹, fun x j => ?_⟩
  have hx : x j = ∑ i, P⁻¹ j i * (P.mulVec x) i := by
    have h2 : P⁻¹.mulVec (P.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]
    conv_lhs => rw [← h2]
    simp only [Matrix.mulVec, dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.codRestrict_apply, key x i, ← map_mul]
  congr 1
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestHLTransport
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure RSIso {p n' : ℕ} (R₁ R₂ : RS p n') where
  φW : R₁.W ≃+* R₂.W
  φQ : R₁.Qq ≃+* R₂.Qq
  φO : R₁.O ≃+* R₂.O
  φK : R₁.Kf ≃+* R₂.Kf
  hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq (φW x)
  hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x)
  hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x)
  hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x)
  hj : ∀ x, φO (R₁.jO x) = R₂.jO (φW x)
  hw : φO R₁.w = R₂.w

def RestRSIso : Prop := ∀ (p n' : ℕ) (R₁ R₂ : RS p n'), Nonempty (RSIso R₁ R₂)

def RestHLTransport : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (I : RSIso R₁ R₂) (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ),
    ∃ (Φ : Submodule R₁.W (Fin (m + 1) → R₁.Qq) ≃ Submodule R₂.W (Fin (m + 1) → R₂.Qq))
      (Ψ : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0),
      (∀ (c : R₁.Kf) v, Ψ (c • v) = I.φK c • Ψ v) ∧
      (∀ L, IsLattice R₁.W L ↔ IsLattice R₂.W (Φ L)) ∧
      (∀ (r : ℕ) (e : Edge R₁.W R₁.Qq (m + 1)), IsEdge p n' r e ↔ IsEdge p n' r ⟨Φ e.src, Φ e.tgt⟩) ∧
      (∀ L x, x ∈ HL (O := R₁.O) R₁.ι R₁.σ lam0 L ↔ Ψ x ∈ HL (O := R₂.O) R₂.ι R₂.σ lam0 (Φ L)) ∧
      (∀ (e : Edge R₁.W R₁.Qq (m + 1)) x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 e ↔
        Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 ⟨Φ e.src, Φ e.tgt⟩) ∧
      dimV R₁.Kf lam0 = dimV R₂.Kf lam0

section Formal

variable {O₁ K₁ V₁ O₂ K₂ V₂ : Type*} [CommRing O₁] [Field K₁] [Algebra O₁ K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Module O₁ V₁] [IsScalarTower O₁ K₁ V₁] [CommRing O₂] [Field K₂] [Algebra O₂ K₂] [AddCommGroup V₂] [Module K₂ V₂]
  [Module O₂ V₂] [IsScalarTower O₂ K₂ V₂] (φO : O₁ ≃+* O₂) (φK : K₁ ≃+* K₂) (Ψ : V₁ ≃+ V₂)

theorem sl_symm (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₂) (v : V₂) :
    Ψ.symm (c • v) = φK.symm c • Ψ.symm v := by
  apply Ψ.injective
  rw [hΨ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

def dT (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (G : Module.Dual K₁ V₁) : Module.Dual K₂ V₂ where
  toFun v := φK (G (Ψ.symm v))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' c x := by
    rw [sl_symm φK Ψ hΨ, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, RingHom.id_apply, smul_eq_mul]

theorem dT_apply (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (G : Module.Dual K₁ V₁) (v : V₁) : dT φK Ψ hΨ G (Ψ v) = φK (G v) := by
  show φK (G (Ψ.symm (Ψ v))) = _
  rw [AddEquiv.symm_apply_apply]

theorem dT_smul (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₁) (G : Module.Dual K₁ V₁) : dT φK Ψ hΨ (c • G) = φK c • dT φK Ψ hΨ G := by
  ext v
  show φK ((c • G) (Ψ.symm v)) = φK c • φK (G (Ψ.symm v))
  rw [LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem sl_scale (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₁) {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {x : V₁}
    (hx : x ∈ scale c M) : Ψ x ∈ scale (φK c) M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨Ψ y, (h y).1 hy, (hΨ c y).symm⟩

theorem sl_scale2 (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c d : K₁) {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {x : V₁}
    (hx : x ∈ scale c (scale d M)) : Ψ x ∈ scale (φK c) (scale (φK d) M') := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨Ψ y, sl_scale φK Ψ hΨ d h hy, (hΨ c y).symm⟩

theorem sl_dual (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (hOK : ∀ x, φK (algebraMap O₁ K₁ x) = algebraMap O₂ K₂ (φO x)) {M : Submodule O₁ V₁}
    {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {G : Module.Dual K₁ V₁}
    (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O₁ K₁ M) : dT φK Ψ hΨ G ∈ Formalism.GradedWeylDivisibility.dualLat O₂ K₂ M' := by
  intro v hv
  have h1 : Ψ.symm v ∈ M := (h _).2 (by rwa [AddEquiv.apply_symm_apply])
  obtain ⟨a, ha⟩ := hG _ h1
  exact ⟨φO a, by show _ = φK (G (Ψ.symm v)); rw [← ha, hOK]⟩

theorem sl_scale_dual (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (hOK : ∀ x, φK (algebraMap O₁ K₁ x) = algebraMap O₂ K₂ (φO x)) (c : K₁)
    {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {G : Module.Dual K₁ V₁}
    (hG : G ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O₁ K₁ M)) :
    dT φK Ψ hΨ G ∈ scale (φK c) (Formalism.GradedWeylDivisibility.dualLat O₂ K₂ M') := by
  obtain ⟨G₀, hG₀, rfl⟩ := hG
  exact ⟨dT φK Ψ hΨ G₀, sl_dual φO φK Ψ hΨ hOK h hG₀, (dT_smul φK Ψ hΨ c G₀).symm⟩

end Formal

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SgSegUnique
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.TopChoiceBounds

variable {n' : ℕ}

theorem sg_cdist (a b : Fin n') :
    cdist a b = if a.val ≤ b.val then b.val - a.val else b.val + n' - a.val := by
  have ha := a.isLt
  have hb := b.isLt
  unfold cdist
  split_ifs with h
  · rw [show b.val + n' - a.val = (b.val - a.val) + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma posAdd_cdist_eq_self (x y : Fin n') : posAdd x (cdist x y) = y := by
  have hx := x.isLt
  have hy := y.isLt
  apply Fin.ext
  show (x.val + (y.val + n' - x.val) % n') % n' = y.val
  rw [Nat.add_mod_mod, show x.val + (y.val + n' - x.val) = y.val + n' by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hy]

theorem sg_pos_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val ∧
      cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i ∧
      0 < cdist (segStart TT j) (segPos TT j i) ∧ cdist (segStart TT j) (segPos TT j i) < segG TT j := by
  obtain ⟨s, hs, hsd⟩ := Finset.mem_image.1 ((Finset.mem_sort _).1 (List.get_mem (segDists TT j) i))
  obtain ⟨hsT, hodd, hpos, hlt⟩ := Finset.mem_filter.1 hs
  have hp : segPos TT j i = s := by
    unfold segPos
    rw [← hsd]
    exact posAdd_cdist_eq_self _ _
  rw [hp]
  exact ⟨hsT, hodd, hsd, hpos, hlt⟩

theorem sg_next_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segNext TT j ∈ TT ∧ Even (segNext TT j).val :=
  (bs_mem TT (segNext TT j)).1 (List.get_mem _ _)

theorem sg_dists_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (segDists TT j).get :=
  List.nodup_iff_injective_get.1 (by unfold segDists; apply Finset.sort_nodup)

theorem sg_pos_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (segPos TT j) := by
  intro i i' h
  have e1 := (sg_pos_spec TT j i).2.2.1
  have e2 := (sg_pos_spec TT j i').2.2.1
  rw [h] at e1
  exact sg_dists_inj TT j (e1.symm.trans e2)

def sgTop (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Option (Fin (segS TT j)) → TT
  | none => ⟨segNext TT j, (sg_next_mem TT j).1⟩
  | some i => ⟨segPos TT j i, (sg_pos_spec TT j i).1⟩

theorem sgTop_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (sgTop TT j) := by
  rintro (_ | i) (_ | i') h
  · rfl
  · exfalso
    have h' : segNext TT j = segPos TT j i' := congrArg Subtype.val h
    have e := (sg_next_mem TT j).2
    rw [h'] at e
    exact (sg_pos_spec TT j i').2.1 e
  · exfalso
    have h' : segPos TT j i = segNext TT j := congrArg Subtype.val h
    have e := (sg_next_mem TT j).2
    rw [← h'] at e
    exact (sg_pos_spec TT j i).2.1 e
  · exact congrArg some (sg_pos_inj TT j (congrArg Subtype.val h))

def sgAll (TT : Finset (Fin n')) : (Σ j : Fin (numSeg TT), Option (Fin (segS TT j))) → TT
  | ⟨j, none⟩ => ⟨segStart TT j, (bs_start_mem TT j).1⟩
  | ⟨j, some i⟩ => ⟨segPos TT j i, (sg_pos_spec TT j i).1⟩

theorem sg_seg_unique (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j j' : Fin (numSeg TT)) (i : Fin (segS TT j))
    (i' : Fin (segS TT j')) (h : segPos TT j i = segPos TT j' i') : j = j' := by
  by_contra hne
  have hs : segStart TT j ≠ segStart TT j' := fun e => hne ((bs_mono TT).injective e)
  have m1 := bs_min TT h2 j (segStart TT j') (bs_start_mem TT j').1 (bs_start_mem TT j').2 hs.symm
  have m2 := bs_min TT h2 j' (segStart TT j) (bs_start_mem TT j).1 (bs_start_mem TT j).2 hs
  have hG1 : segG TT j = cdist (segStart TT j) (segNext TT j) := by
    unfold segG
    rw [if_neg (by omega)]
  have hG2 : segG TT j' = cdist (segStart TT j') (segNext TT j') := by
    unfold segG
    rw [if_neg (by omega)]
  have A := (sg_pos_spec TT j i).2.2.2.2
  have B := (sg_pos_spec TT j' i').2.2.2.2
  rw [h, hG1] at A
  rw [hG2] at B
  have X1 := lt_of_lt_of_le A m1.2
  have X2 := lt_of_lt_of_le B m2.2
  have ha := (segStart TT j).isLt
  have hb := (segStart TT j').isLt
  have hp := (segPos TT j' i').isLt
  rw [sg_cdist, sg_cdist] at X1 X2
  split_ifs at X1 X2 <;> omega

theorem sgAll_inj (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) : Function.Injective (sgAll TT) := by
  rintro ⟨j, _ | i⟩ ⟨j', _ | i'⟩ h
  · have h' : segStart TT j = segStart TT j' := congrArg Subtype.val h
    obtain rfl := (bs_mono TT).injective h'
    rfl
  · exfalso
    have h' : segStart TT j = segPos TT j' i' := congrArg Subtype.val h
    have e := (bs_start_mem TT j).2
    rw [h'] at e
    exact (sg_pos_spec TT j' i').2.1 e
  · exfalso
    have h' : segPos TT j i = segStart TT j' := congrArg Subtype.val h
    have e := (bs_start_mem TT j').2
    rw [← h'] at e
    exact (sg_pos_spec TT j i).2.1 e
  · have h' : segPos TT j i = segPos TT j' i' := congrArg Subtype.val h
    obtain rfl := sg_seg_unique TT h2 j j' i i' h'
    rw [sg_pos_inj TT j h']

theorem sg_count (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) :
    ∑ j : Fin (numSeg TT), (segS TT j + 1) ≤ TT.card := by
  have hc := Fintype.card_le_of_injective _ (sgAll_inj TT h2)
  simpa [Fintype.card_sigma] using hc

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfIntermediateBounds
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem kF_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : 0 ≤ X.kF K R al be :=
  Real.sInf_nonneg fun _ h => h.1

open Classical in
theorem kText_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (hb : 0 < X.b') (aa bb : X.TT → ℤ) :
    0 ≤ X.kText K R aa bb := by
  unfold Dat.kText
  have h1 : 0 ≤ (if X.Inside aa bb then
      X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1) := by
    split_ifs
    · exact kF_nonneg _ _ _ _ _
    · exact zero_le_one
  have h2 := kF_nonneg X K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat)
  have h3 : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b' := by
    unfold Dat.k
    positivity
  linarith

theorem theorem_I_of_intermediate_bounds (D : Formalism.BasicNotions.D7) (FM : Cst → Dat → Prop) (hR : LPRingIndep) (hLP : ∀ K C, MidLP K C)
    (hMean : ∀ K : Cst, K.Pos → MidMean D K (FM K)) (hN1 : ∀ K : Cst, K.Pos → TransportedAlt K (FactsLP K))
    (hN2 : ∀ K : Cst, K.Pos → TransportedAlt K (fun _ => FM K)) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, hT0, h0⟩ := hA 4 (by norm_num)
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  obtain ⟨T2, hT2, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, hCA, hCkap, hCt, hCs, hAdm⟩ := h2 T2 le_rfl
  let K : Cst := ⟨C₀, T2, CA, T1, T1, T1, Ckap, Ct, Cs⟩
  have hK : K.Pos := ⟨lt_of_lt_of_le hT0 hC₀, hT2, hCA, hT1, hT1, hT1, hCkap, hCt, hCs⟩
  obtain ⟨Ta, Ca, hTa, hCa, hFa⟩ := hN1 K hK
  obtain ⟨Tb, Cb, hTb, hCb, hFb⟩ := hN2 K hK
  refine ⟨max Ta Tb, max (max Ca Cb) K.Cmean, lt_max_of_lt_left hTa,
    lt_max_of_lt_left (lt_max_of_lt_left hCa), fun CH hCH => ?_⟩
  intro p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar hH
  have hm : m ≠ 0 := by
    have := hH.2.2.2.2.2.2.1
    omega
  have hY : 1 ≤ Y := hH.1
  let X : Dat := ⟨p, n', m, hm, TT, G', N₁, Y, Yb, a, b', bl, bu, ccl, Dp, cStar⟩
  have hX : X.Hyp K.C₀ CH := hH
  have hLPf : FactsLP K (max (max Ca Cb) K.Cmean) X :=
    hFa CH (le_trans (le_max_left _ _) hCH) _ (le_trans (le_max_left _ _) (le_max_left _ _)) X hX
  have hMf : FM K X :=
    hFb CH (le_trans (le_max_right _ _) hCH) (max (max Ca Cb) K.Cmean)
      (le_trans (le_max_right _ _) (le_max_left _ _)) X hX
  have hnn : 0 ≤ (TT.card : ℝ) * N₁ / Y := by positivity
  by_cases hne : Nonempty (RS p n')
  · obtain ⟨R₀⟩ := hne
    refine ⟨X.kText K R₀, kText_nonneg X K R₀ hLPf.bpos, ?_, ?_⟩
    · have h := hMean K hK hAdm X hMf R₀
      have h' : K.Cmean * (TT.card : ℝ) * N₁ / Y ≤ max (max Ca Cb) K.Cmean * (TT.card : ℝ) * N₁ / Y := by
        have := mul_le_mul_of_nonneg_right (le_max_right (max Ca Cb) K.Cmean) hnn
        calc K.Cmean * (TT.card : ℝ) * N₁ / Y = K.Cmean * ((TT.card : ℝ) * N₁ / Y) := by ring
          _ ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
          _ = _ := by ring
      exact le_trans h h'
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd aw bw lam0 hW t ht
      let R : RS p n' := ⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩
      exact hR p n' R₀ R m 1 lam0 t Dp _ cStar (hLP K _ X hLPf R₀ aw bw lam0 hW t ht)
  · refine ⟨fun _ _ => 0, fun _ _ => le_rfl, ?_, ?_⟩
    · have h0 : meanKap TT m Y a bl bu (fun _ _ => (0 : ℝ)) = 0 := by simp [meanKap]
      rw [h0]
      have hC : 0 ≤ max (max Ca Cb) K.Cmean := le_of_lt (lt_max_of_lt_left (lt_max_of_lt_left hCa))
      have := mul_nonneg hC hnn
      calc (0 : ℝ) ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
        _ = _ := by ring
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd
      exact absurd ⟨(⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩ : RS p n')⟩ hne

end Formalism.MainNotions.flipOneThree.Pf

end
end

