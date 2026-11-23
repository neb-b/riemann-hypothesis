module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupLaw
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobenius

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupInverse
section
namespace GroundTheory.Arith.Abelian

noncomputable section

section Neg

variable {A : Type*} [CommRing A] (V : WeierstrassCurve A)

theorem zwPoly_neg_mul {z w e : A} (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = -e ^ 3 * zwPoly V z w := by
  unfold zwPoly
  linear_combination (-e * w * (e + 1)) * he

end Neg

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

section Apply

variable {T : Type*} [CommRing T] [Algebra R T] (ψ : MvPowerSeries (Fin 2) R →ₐ[R] T)

theorem algHom_C (r : R) : ψ (MvPowerSeries.C r) = algebraMap R T r := by
  have : MvPowerSeries.C r = algebraMap R (MvPowerSeries (Fin 2) R) r := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [this, ψ.commutes]

theorem map_C_algHom :
    (W.map (MvPowerSeries.C (σ := Fin 2))).map (ψ : MvPowerSeries (Fin 2) R →+* T) =
      W.map (algebraMap R T) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  ext r
  exact algHom_C ψ r

theorem apply_wAt_X_zero :
    ψ (wAt W (MvPowerSeries.X 0)) = ψ (addSlope W) * ψ (MvPowerSeries.X 0) + ψ (addIntercept W) := by
  rw [wAt_X_zero_eq, map_add (f := _), map_mul]

theorem apply_wAt_X_one :
    ψ (wAt W (MvPowerSeries.X 1)) = ψ (addSlope W) * ψ (MvPowerSeries.X 1) + ψ (addIntercept W) := by
  rw [wAt_X_one_eq, map_add (f := _), map_mul]

theorem zwPoly_apply_wAt_X (i : Fin 2) :
    zwPoly (W.map (algebraMap R T)) (ψ (MvPowerSeries.X i)) (ψ (wAt W (MvPowerSeries.X i))) = 0 := by
  have := congrArg (ψ : MvPowerSeries (Fin 2) R →+* T)
    (zwPoly_wAt W (MvPowerSeries.constantCoeff_X (R := R) i))
  rwa [map_zwPoly, map_zero, map_C_algHom] at this

theorem secantB_apply_mul :
    secantB (W.map (algebraMap R T)) (ψ (addSlope W)) *
      ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) = 1 := by
  have := congrArg (ψ : MvPowerSeries (Fin 2) R →+* T) (mul_invOfUnit_one (constantCoeff_secantB W))
  rwa [map_mul, map_one, map_secantB, map_C_algHom] at this

theorem apply_thirdZ :
    ψ (thirdZ W) = -ψ (MvPowerSeries.X 0) - ψ (MvPowerSeries.X 1) -
      secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W)) *
        ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) := by
  have h := map_secantA (W.map (MvPowerSeries.C (σ := Fin 2))) (ψ : MvPowerSeries (Fin 2) R →+* T)
    (addSlope W) (addIntercept W)
  rw [map_C_algHom] at h
  have h' : ψ (secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W)) =
      secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W)) := h
  rw [thirdZ, map_sub, map_sub, map_neg, map_mul, h']

theorem apply_thirdW : ψ (thirdW W) = ψ (addSlope W) * ψ (thirdZ W) + ψ (addIntercept W) := by
  rw [thirdW, map_add (f := _), map_mul]

theorem negDen_apply_mul :
    (1 - algebraMap R T W.a₁ * ψ (thirdZ W) - algebraMap R T W.a₃ * ψ (thirdW W)) *
      ψ (MvPowerSeries.invOfUnit (negDen W) 1) = 1 := by
  have := congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))
  rwa [map_mul, map_one, negDen, map_sub, map_sub, map_one, map_mul, map_mul, algHom_C,
    algHom_C] at this

theorem apply_addSeries :
    ψ (addSeries W) = -ψ (thirdZ W) * ψ (MvPowerSeries.invOfUnit (negDen W) 1) := by
  rw [addSeries, map_mul, map_neg]

end Apply

section Inverse

def invDen : PowerSeries R :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W

theorem constantCoeff_invDen : MvPowerSeries.constantCoeff (invDen W) = 1 := by
  have h : MvPowerSeries.constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  simp [invDen, PowerSeries.C_apply, h, PowerSeries.X]

def invSeries : PowerSeries R :=
  -PowerSeries.X * MvPowerSeries.invOfUnit (invDen W) 1

theorem constantCoeff_invSeries : MvPowerSeries.constantCoeff (invSeries W) = 0 := by
  simp [invSeries, PowerSeries.X]

theorem wAt_X_unit : wAt W (PowerSeries.X : PowerSeries R) = formalW W :=
  PowerSeries.X_subst _

theorem wAt_invSeries :
    wAt W (invSeries W) = -formalW W * MvPowerSeries.invOfUnit (invDen W) 1 := by
  set e := MvPowerSeries.invOfUnit (invDen W) 1 with he_def
  have he : (1 - (W.map MvPowerSeries.C).a₁ * (PowerSeries.X : PowerSeries R) -
      (W.map MvPowerSeries.C).a₃ * formalW W) * e = 1 :=
    mul_invOfUnit_one (constantCoeff_invDen W)
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
    PowerSeries.constantCoeff_X
  have h0 : zwPoly (W.map MvPowerSeries.C) PowerSeries.X (formalW W) = 0 := by
    have := zwPoly_wAt W hX
    rwa [wAt_X_unit] at this
  have hneg := zwPoly_neg_mul (W.map MvPowerSeries.C) he
  rw [h0, mul_zero] at hneg
  have hi := constantCoeff_invSeries W
  refine eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hi) hneg ?_
  refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
  have hw : MvPowerSeries.constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  simp [hi, constantCoeff_wAt W hi, hw]

theorem map_invDen {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f (invDen W) = invDen (W.map f) := by
  have h : MvPowerSeries.map f (formalW W) = formalW (W.map f) := map_formalW W f
  simp only [invDen, map_sub, map_one, map_mul, h, PowerSeries.C_apply, MvPowerSeries.map_C,
    PowerSeries.X, MvPowerSeries.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

theorem map_invSeries {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f (invSeries W) = invSeries (W.map f) := by
  rw [invSeries, map_mul, map_neg, map_invOfUnit_one f (constantCoeff_invDen W), map_invDen,
    invSeries, PowerSeries.X, MvPowerSeries.map_X]
  rfl

theorem subst_X_invSeries_of_isDomain [IsDomain R] (h2 : (2 : R) ≠ 0) :
    MvPowerSeries.subst ![PowerSeries.X, invSeries W] (addSeries W) = (0 : PowerSeries R) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
    PowerSeries.constantCoeff_X
  have hi := constantCoeff_invSeries W
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair hX hi
  set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef
  have hψ : ∀ f, MvPowerSeries.subst ![PowerSeries.X, invSeries W] f = ψ f := fun f => by
    rw [hψdef, MvPowerSeries.coe_substAlgHom]
  have ψX0 : ψ (MvPowerSeries.X 0) = PowerSeries.X := by
    rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψX1 : ψ (MvPowerSeries.X 1) = invSeries W := by
    rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![PowerSeries.X, invSeries W] i) :=
    fun i => by
      rw [← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst
        (PowerSeries.HasSubst.X i) hab, MvPowerSeries.subst_X hab, wAt]
  set V := W.map (algebraMap R (PowerSeries R)) with hV
  set u : PowerSeries R := PowerSeries.X with hu
  set e := MvPowerSeries.invOfUnit (invDen W) 1 with he
  set w := formalW W with hw
  set l := ψ (addSlope W) with hl
  set n := ψ (addIntercept W) with hn
  set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb
  have hu' : invSeries W = -u * e := rfl
  have r₁ : w = l * u + n := by
    have := apply_wAt_X_zero W ψ
    rwa [ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit] at this
  have r₂ : -w * e = l * invSeries W + n := by
    have := apply_wAt_X_one W ψ
    rwa [ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries] at this
  have he1 : e + 1 ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    simp [he, MvPowerSeries.constantCoeff_invOfUnit] at this
    exact h2 (by linear_combination this)
  have hlu : l * u = w := by
    have h : (e + 1) * (l * u - w) = 0 := by rw [hu'] at r₂; linear_combination r₂ - r₁
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left he1)
  have hn0 : n = 0 := by linear_combination -r₁ - hlu
  have z₁ : zwPoly V u w = 0 := by
    have := zwPoly_apply_wAt_X W ψ 0
    rwa [ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit] at this
  have z₂ : zwPoly V (invSeries W) (-w * e) = 0 := by
    have := zwPoly_apply_wAt_X W ψ 1
    rwa [ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries] at this
  have hcub : ∀ t, zwPoly V t (l * t) =
      t * (secantB V l * t ^ 2 + secantA V l n * t - l) := by
    intro t; simp only [zwPoly, secantB, secantA, hn0]; ring
  have q₁ : u * (secantB V l * u ^ 2 + secantA V l n * u - l) = 0 := by
    rw [← hcub, hlu, z₁]
  have q₂ : invSeries W * (secantB V l * invSeries W ^ 2 + secantA V l n * invSeries W - l) = 0 := by
    rw [← hcub, ← z₂]; congr 1; linear_combination -r₂ - hn0
  have hu0 : u ≠ 0 := PowerSeries.X_ne_zero
  have heu : IsUnit e := by
    refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
    simp [he, MvPowerSeries.constantCoeff_invOfUnit]
  have hu'0 : invSeries W ≠ 0 := by
    rw [hu']; exact mul_ne_zero (neg_ne_zero.2 hu0) heu.ne_zero
  have p₁ := (mul_eq_zero.1 q₁).resolve_left hu0
  have p₂ := (mul_eq_zero.1 q₂).resolve_left hu'0
  have hd : u - invSeries W ≠ 0 := by
    rw [hu', show u - -u * e = u * (e + 1) by ring]
    exact mul_ne_zero hu0 he1
  have hs : secantB V l * (u + invSeries W) + secantA V l n = 0 := by
    have : (u - invSeries W) * (secantB V l * (u + invSeries W) + secantA V l n) = 0 := by
      linear_combination p₁ - p₂
    exact (mul_eq_zero.1 this).resolve_left hd
  have rb := secantB_apply_mul W ψ
  have hz : ψ (thirdZ W) = 0 := by
    rw [apply_thirdZ, ψX0, ψX1]
    linear_combination (u + invSeries W) * rb - b * hs
  rw [hψ, apply_addSeries, hz, neg_zero, zero_mul]

theorem two_ne_zero_univ : (2 : MvPolynomial (Fin 5) ℤ) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (0 : Fin 5 → ℤ)) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

theorem subst_X_invSeries :
    MvPowerSeries.subst ![PowerSeries.X, invSeries W] (addSeries W) = (0 : PowerSeries R) := by
  have h := congrArg (MvPowerSeries.map (univMap W))
    (subst_X_invSeries_of_isDomain univCurve two_ne_zero_univ)
  have hX : MvPowerSeries.constantCoeff
      (PowerSeries.X : PowerSeries (MvPolynomial (Fin 5) ℤ)) = 0 := PowerSeries.constantCoeff_X
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair hX (constantCoeff_invSeries univCurve)
  rw [MvPowerSeries.map_subst hab, map_zero] at h
  rw [← h, addSeries_eq_map]
  congr 1
  funext i
  fin_cases i
  · simp [PowerSeries.X, MvPowerSeries.map_X]
  · simp [map_invSeries, univCurve_map]

theorem inv_formalGroup : GroundTheory.LocalField.FormalGroup.inv (formalGroup W) = invSeries W :=
  (GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero _ (constantCoeff_invSeries W)
    (subst_X_invSeries W)).symm

end Inverse

end

end GroundTheory.Arith.Abelian
end

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobeniusSep
section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def powAdjoin (M : IntermediateField F E.toAffine.FunctionField) (a : ℕ) :
    IntermediateField M E.toAffine.FunctionField :=
  M⟮genX E ^ p ^ a, genY E ^ p ^ a⟯

theorem powAdjoin_succ_eq_top (M : IntermediateField F E.toAffine.FunctionField)
    (h1 : powAdjoin E p M 1 = ⊤) {a : ℕ} (ha : powAdjoin E p M a = ⊤) :
    powAdjoin E p M (a + 1) = ⊤ := by
  set T := powAdjoin E p M (a + 1) with hT
  let Q : IntermediateField M E.toAffine.FunctionField :=
    (T.toSubfield.comap (frobenius E.toAffine.FunctionField p)).toIntermediateField fun m => by
      show (algebraMap M E.toAffine.FunctionField m) ^ p ∈ T
      rw [← map_pow]
      exact IntermediateField.algebraMap_mem T _
  have hQ : powAdjoin E p M a ≤ Q := by
    rw [powAdjoin, adjoin_le_iff]
    rintro w (rfl | rfl)
    · show (genX E ^ p ^ a) ^ p ∈ T
      rw [← pow_mul, ← pow_succ]
      exact subset_adjoin _ _ (by simp)
    · show (genY E ^ p ^ a) ^ p ∈ T
      rw [← pow_mul, ← pow_succ]
      exact subset_adjoin _ _ (by simp)
  have hall : ∀ z : E.toAffine.FunctionField, z ^ p ∈ T := fun z =>
    hQ (show z ∈ powAdjoin E p M a by rw [ha]; trivial)
  have h1le : powAdjoin E p M 1 ≤ T := by
    rw [powAdjoin, adjoin_le_iff]
    rintro w (rfl | rfl)
    · rw [pow_one]; exact hall _
    · rw [pow_one]; exact hall _
  rw [h1] at h1le
  exact top_le_iff.mp h1le

variable [PerfectRing F p]

theorem le_powField_of_finSepDegree_lt (M : IntermediateField F E.toAffine.FunctionField)
    [FiniteDimensional M E.toAffine.FunctionField]
    (h : Field.finSepDegree M E.toAffine.FunctionField <
      Module.finrank M E.toAffine.FunctionField) : M ≤ powField E p := by
  by_contra hM
  set N := M ⊔ powField E p
  have t := relfinrank_mul_relfinrank (le_sup_right : powField E p ≤ N) (le_top : N ≤ ⊤)
  have hp' : relfinrank (powField E p) ⊤ = p := by rw [relfinrank_top_right, finrank_powField]
  rw [hp'] at t
  rcases (Nat.prime_mul_iff.mp (t ▸ hp.out)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · have hN : N = ⊤ := top_le_iff.mp ((relfinrank_eq_one_iff).mp h1)
    have hT1 : powAdjoin E p M 1 = ⊤ := by
      rw [← IntermediateField.restrictScalars_eq_top_iff (K := F)]
      refine top_le_iff.mp ?_
      rw [← hN]
      refine sup_le ?_ ?_
      · intro m hm
        exact (powAdjoin E p M 1).algebraMap_mem ⟨m, hm⟩
      · rw [powField, adjoin_le_iff]
        rintro w (rfl | rfl)
        · exact (subset_adjoin _ _ (by simp) : genX E ^ p ∈ powAdjoin E p M 1)
        · exact (subset_adjoin _ _ (by simp) : genY E ^ p ∈ powAdjoin E p M 1)
    have hall : ∀ a, 1 ≤ a → powAdjoin E p M a = ⊤ := fun a ha =>
      Nat.le_induction hT1 (fun n _ ih => powAdjoin_succ_eq_top E p M hT1 ih) a ha
    set S := separableClosure M E.toAffine.FunctionField
    haveI : CharP S p := charP_of_injective_algebraMap (algebraMap F S).injective p
    haveI : ExpChar S p := ExpChar.prime hp.out
    obtain ⟨nx, hnx⟩ := IsPurelyInseparable.pow_mem S p (genX E)
    obtain ⟨ny, hny⟩ := IsPurelyInseparable.pow_mem S p (genY E)
    have hmem : ∀ (z : E.toAffine.FunctionField) (n a : ℕ),
        z ^ p ^ n ∈ (algebraMap S E.toAffine.FunctionField).range → n ≤ a → z ^ p ^ a ∈ S := by
      intro z n a hz hn
      obtain ⟨s, hs⟩ := hz
      have e : z ^ p ^ a = (z ^ p ^ n) ^ p ^ (a - n) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn]
      rw [e, ← hs]
      exact pow_mem s.2 _
    have hle : powAdjoin E p M (nx + ny + 1) ≤ S := by
      rw [powAdjoin, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact hmem _ nx _ hnx (by omega)
      · exact hmem _ ny _ hny (by omega)
    rw [hall _ (by omega), top_le_iff, separableClosure.eq_top_iff] at hle
    rw [Field.finSepDegree_eq_finrank_of_isSeparable] at h
    exact lt_irrefl _ h
  · exact hM (le_sup_left.trans ((relfinrank_eq_one_iff).mp h1))

end GroundTheory.Arith.Abelian
end

