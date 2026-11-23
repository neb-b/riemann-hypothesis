module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometriesFixingSubspaceLeQuasiReflectionClosure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuasiReflectionStabilizesLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TupleJac

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_int_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ c : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, c.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hu : IsUnit (ω - L.cj ω) := IsUnit.of_mul_eq_one e hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, map_zero] at h'
    have hb : algebraMap F E b = 0 := hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap F E a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  let c : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = ω := by simp [c]
  have hx : ∀ x, x = algebraMap F E (c.repr x 0) + algebraMap F E (c.repr x 1) * ω := by
    intro x
    have := c.sum_repr x
    simp only [Fin.sum_univ_two, hc0, hc1, Algebra.smul_def, mul_one] at this
    exact this.symm
  have hr : ∀ a b : F, c.repr (algebraMap F E a + algebraMap F E b * ω) 0 = a ∧
      c.repr (algebraMap F E a + algebraMap F E b * ω) 1 = b := by
    intro a b
    have : algebraMap F E a + algebraMap F E b * ω = a • c 0 + b • c 1 := by
      simp [hc0, hc1, Algebra.smul_def]
    rw [this]
    simp
  refine ⟨c, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg L.cj (hx x)
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes] at h1
    have hb : algebraMap F E (c.repr x 1) ∈ L.O := by
      have : algebraMap F E (c.repr x 1) = (x - L.cj x) * e := by
        linear_combination (-e) * hx x + e * h1 - algebraMap F E (c.repr x 1) * hωe
      rw [this]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have ha : algebraMap F E (c.repr x 0) ∈ L.O := by
      have : algebraMap F E (c.repr x 0) = x - algebraMap F E (c.repr x 1) * ω := by
        linear_combination - hx x
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem hb hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 ha
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hb
  · rw [hx x]
    exact L.O.add_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 0))
      (L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 1)) hω)
  · obtain ⟨t, ht⟩ := (L.cj_fix (ω + L.cj ω)).1 (by simp [L.cj_cj, add_comm])
    obtain ⟨N, hN⟩ := (L.cj_fix (ω * L.cj ω)).1 (by simp [L.cj_cj, mul_comm])
    obtain ⟨a, b, rfl⟩ : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * ω := ⟨_, _, hx x⟩
    have h2 : (algebraMap F E a + algebraMap F E b * ω) * ω
        = algebraMap F E (-(b * N)) + algebraMap F E (a + b * t) * ω := by
      simp only [map_add (f := _), map_mul, map_neg, ht, hN]; ring
    rw [Algebra.norm_eq_matrix_det c, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hc1, mul_one, h2, (hr _ _).1, (hr _ _).2]
    simp only [map_add (f := _), map_mul, map_neg, map_sub, ht, hN, AlgEquiv.commutes]
    ring

theorem exists_lat_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) :
    ∃ B : Module.Basis (Fin n) E (Fin n → E), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ L.O := by
  obtain ⟨b, hb, rfl⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
  have hli : LinearIndependent E b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun x => hf L Hm x (b j)
        map_add' := fun x y => by simp [hf, add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [hf, Finset.mul_sum, mul_assoc] }
    have hfb : ∀ i, f (b i) = if i = j then 1 else 0 := fun i => hb i j
    have := congrArg f hg
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hfb] using this
  have hsp : ⊤ ≤ Submodule.span E (Set.range b) := by
    rw [← hΛ.1.2, Submodule.span_span_of_tower]
  refine ⟨Module.Basis.mk hli hsp, fun x => ?_⟩
  set B := Module.Basis.mk hli hsp with hB
  have hBb : ∀ i, B i = b i := fun i => by simp [hB]
  constructor
  · intro hx i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    have : ∑ j, c j • b j = ∑ j, (c j : E) • B j := by simp only [hBb]; rfl
    rw [this, B.repr_sum_self]
    exact (c i).2
  · intro hx
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hx i⟩, ?_⟩
    conv_rhs => rw [← B.sum_repr x]
    simp only [hBb]; rfl

theorem cont_linearEquiv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (m : ℕ) (φ : (Fin m → Fin n → E) ≃ₗ[E] (Fin m → Fin n → E))
    (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det φ.toLinearMap * L.cj (LinearMap.det φ.toLinearMap)
      = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) (φ '' T) ∧
      cont (tupLat L Λ m) (φ '' T) = (resQ ϖ : ℝ) ^ (-a) * cont (tupLat L Λ m) T := by
  obtain ⟨c, hc, hN⟩ := exists_int_basis L
  obtain ⟨B, hB⟩ := exists_lat_basis L Hm hH Λ hΛ
  have := L.free
  have h := _root_.GlobalTheory.HL.LatDet.relVol_map ϖ hϖ (Pi.basis fun _ : Fin m => c.smulTower B) (φ.restrictScalars F) a u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hd, ← hN, ← LinearMap.det_restrictScalars]
      rfl) (tupLat L Λ m) (by
      intro x
      simp only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff,
        Submodule.mem_toAddSubgroup, hB, hc, Pi.basis_repr, Module.Basis.smulTower_repr]
      exact ⟨fun h i => h _ _ _, fun h j i k => h ⟨j, (k, i)⟩⟩)
  intro T hT
  have h2 := GlobalTheory.HL.ContAut.cont_image (tupLat L Λ m) (φ.restrictScalars F).toAddEquiv h.1 h.2.1 T hT
  rw [h.2.2] at h2
  exact h2

def rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (Fin m → Fin n → E) →ₗ[E] (Fin m → Fin n → E) where
  toFun x := rmul x A
  map_add' x y := by ext j k; simp [rmul, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext j k; simp [rmul, Finset.mul_sum, mul_left_comm]

def swapL (n m : ℕ) : (Fin n → Fin m → E) ≃ₗ[E] (Fin m → Fin n → E) where
  toFun x := fun j k => x k j
  invFun x := fun j k => x k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace E] in
theorem det_rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulL (n := n) A) = A.det ^ n := by
  have h : rmulL (n := n) A = (swapL n m).toLinearMap ∘ₗ
      (LinearMap.pi fun i : Fin n => (Matrix.toLin' A.transpose) ∘ₗ LinearMap.proj i) ∘ₗ
      (swapL n m).symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    ext j k
    simp [rmulL, rmul, swapL, Matrix.mulVec, dotProduct]
  rw [h, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

theorem det_isom (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (hH : IsUnit Hm.det)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : g ∈ isomG L Hm) :
    LinearMap.det g.toLinearMap * L.cj (LinearMap.det g.toLinearMap) = 1 := by
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  have h : M.transpose * Hm * (L.cj.toRingEquiv.toRingHom.mapMatrix M) = Hm := by
    ext i j
    have h1 := hg (Pi.single i 1) (Pi.single j 1)
    have h2 : hf L Hm (Pi.single i 1) (Pi.single j 1) = Hm i j := by
      simp [hf, Pi.single_apply, apply_ite L.cj]
    rw [h2] at h1
    rw [← h1, hf, Finset.sum_comm]
    simp [hM, Matrix.mul_apply, Finset.sum_mul, LinearMap.toMatrix'_apply]
  have h3 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hM,
    LinearMap.det_toMatrix'] at h3
  refine hH.mul_left_cancel ?_
  rw [mul_one]
  conv_rhs => rw [← h3]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.coe_toRingEquiv]
  ring

end GlobalTheory.HL.TupleJac

theorem GlobalTheory.HL.TupleJac.tuple_jacobian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m
  refine ⟨fun A hA => ?_, fun g hg T hT => ?_⟩
  · obtain ⟨N, hN⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by simp [L.cj_cj, mul_comm])
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [map_zero] at hN
      exact (hA.mul (hA.map L.cj)).ne_zero hN.symm
    obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 N hN0
    have hdet : IsUnit (LinearMap.det (TupleJac.rmulL (n := n) A)) := by
      rw [TupleJac.det_rmulL]; exact hA.pow n
    have hφ : (LinearMap.equivOfIsUnitDet hdet).toLinearMap = TupleJac.rmulL (n := n) A :=
      LinearMap.coe_equivOfIsUnitDet hdet
    have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearMap.equivOfIsUnitDet hdet)
      (vE L ϖ (A.det * L.cj A.det) * n) (u ^ n) (by
        rw [hφ, TupleJac.det_rmulL, map_pow, ← mul_pow, ← hN, ← map_pow]
        congr 1
        conv_lhs => rw [hu]
        rw [mul_pow, zpow_mul, zpow_natCast]
        simp)
    have hfun : (LinearMap.equivOfIsUnitDet hdet : _ → _) = fun x => rmul x A :=
      funext fun x => LinearMap.congr_fun hφ x
    rw [hfun] at key
    exact key
  · have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m
      (LinearEquiv.piCongrRight fun _ => g) 0 1 (by
        have h : (LinearEquiv.piCongrRight fun _ : Fin m => g).toLinearMap =
            LinearMap.pi fun i : Fin m => g.toLinearMap ∘ₗ LinearMap.proj i := rfl
        rw [h, LinearMap.det_pi, Finset.prod_const, map_pow, ← mul_pow,
          TupleJac.det_isom L Hm hH.2 g hg]
        simp) T hT
    rw [neg_zero, zpow_zero, one_mul] at key
    exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Unimod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_swap (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm x y = L.cj (hf L Hm y x) := by
  have h : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun hH i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, L.cj_cj, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qrefl_mem (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) {a : Fin n → E} (ha : a ∈ perp L Hm Y)
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : IsQRefl L Hm a g) : g ∈ fixG L Hm Y := by
  obtain ⟨_, hi, c, hc⟩ := hg
  have hfix : ∀ v ∈ Y, g v = v := fun v hv => by
    have h0 : hf L Hm a v = 0 := ha v hv
    rw [hc, hf_swap L hH v a, h0]; simp
  refine ⟨hi, fun v => ⟨fun hv => ?_, fun hv => by rw [hfix v hv]; exact hv⟩, fun v hv => ?_⟩
  · have : g v = v := g.injective (hfix _ hv)
    rwa [this] at hv
  · rw [hfix v hv]; simp

theorem conj_self {G : Type} [Group G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
  constructor
  · intro hy
    have := H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hy
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem inf_stab_smul (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {h} (hh : h ∈ H) :
    H ⊓ stabL L (h • Λ) = MulAut.conj h • (H ⊓ stabL L Λ) := by
  rw [((_root_.GlobalTheory.LatComm.stab_commensurable L Λ Λ hΛ hΛ H).2 h).2, Subgroup.smul_inf, conj_self hh]

theorem comm_conj (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) : ∀ h ∈ H,
    (H ⊓ stabL L Λ).relIndex (MulAut.conj h • (H ⊓ stabL L Λ)) ≠ 0 ∧
      (MulAut.conj h • (H ⊓ stabL L Λ)).relIndex (H ⊓ stabL L Λ) ≠ 0 := by
  intro h hh
  have hl := ((_root_.GlobalTheory.LatComm.stab_commensurable L Λ Λ hΛ hΛ H).2 h).1
  rw [← inf_stab_smul L H hΛ hh]
  exact ⟨(_root_.GlobalTheory.LatComm.stab_commensurable L _ _ hl hΛ H).1, (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ hΛ hl H).1⟩

theorem invVol_self {G : Type} [Group G] (K : Subgroup G) : invVol K K = 1 := by
  simp [invVol]

theorem delta_inv (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {g} (hg : g ∈ H) :
    invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) *
      invVol (H ⊓ stabL L Λ) (MulAut.conj g⁻¹ • (H ⊓ stabL L Λ)) = 1 := by
  rw [← (_root_.GlobalTheory.HL.invVol_conj_modular H _ inf_le_left (comm_conj L H hΛ)).1 g hg g⁻¹ (H.inv_mem hg)]
  simp [invVol_self]

theorem delta_indep (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ0 Λ : Submodule L.O (Fin n → E)} (h0 : IsLat L Λ0) (hΛ : IsLat L Λ) {g} (hg : g ∈ H)
    (h1 : invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) = 1) :
    invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
  have a := (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ hΛ h0 H).1
  have b := (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ h0 hΛ H).1
  have hl := ((_root_.GlobalTheory.LatComm.stab_commensurable L Λ Λ hΛ hΛ H).2 g).1
  have c := (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ hl h0 H).1
  have d := (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ h0 hl H).1
  rw [inf_stab_smul L H hΛ hg] at c d
  have e1 := ((_root_.GlobalTheory.HL.invVol_conj_modular H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b g hg).1
  have e2 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b c d).1
  have e3 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b a b).2.1
  rw [e1, h1, mul_one] at e2
  exact mul_right_cancel₀ e3.ne' (by rw [e2, one_mul])

theorem unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0 Λ : Submodule L.O (Fin n → E), IsLat L Λ0 → IsLat L Λ → ∀ h ∈ fixG L Hm (Submodule.span E (Set.range x)), invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (h • Λ)) = invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx Λ0 Λ h0 hΛ h hh
  have hgen := _root_.GlobalTheory.HL.QReflGen.fixG_le_closure L Hm hH m x hx
  have hq := _root_.GlobalTheory.QRefl.qrefl_inverted L Hm hH m x hx
  have hmem := fun a ha g hg => qrefl_mem L hH.1 (Submodule.span E (Set.range x)) (a := a) ha (g := g) hg
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have key : ∀ g ∈ Subgroup.closure
      {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g},
      g ∈ H ∧ invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, hg⟩ := hg
      have hgH := hmem a ha g hg
      refine ⟨hgH, ?_⟩
      obtain ⟨Λ1, h1, α, hα, hαg⟩ := hq a ha g hg
      refine delta_indep L H h0 h1 hgH ?_
      have M := _root_.GlobalTheory.HL.invVol_conj_modular H _ inf_le_left (comm_conj L H h1)
      have e1 := M.2.2.1 α hα g hgH
      have e2 := M.2.1 g hgH
      have e3 := delta_inv L H h1 hgH
      rw [hαg] at e1
      rw [e1] at e3
      nlinarith
    | one => exact ⟨H.one_mem, by simp [invVol_self]⟩
    | mul a b _ _ ha hb =>
      refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
      rw [(_root_.GlobalTheory.HL.invVol_conj_modular H _ inf_le_left (comm_conj L H h0)).1 a ha.1 b hb.1, ha.2, hb.2, one_mul]
    | inv a _ ha =>
      refine ⟨H.inv_mem ha.1, ?_⟩
      have := delta_inv L H h0 ha.1
      rwa [ha.2, one_mul] at this
  have a := (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ hΛ h0 H).1
  have b := (_root_.GlobalTheory.LatComm.stab_commensurable L _ _ h0 hΛ H).1
  rw [inf_stab_smul L H hΛ hh,
    ((_root_.GlobalTheory.HL.invVol_conj_modular H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b h hh).1, (key h (hgen hh)).2, one_mul]

end GlobalTheory.HL.Unimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseClose
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem unitriangular_inv_close {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E) (ht : t ∈ L.O) (hlow : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i = 1) (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) : ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  have hMO : ∀ i j, M i j ∈ L.O := by
    intro i j
    obtain ⟨o, ho, he⟩ := hcl i j
    have : M i j = t * o + (1 : Matrix (Fin n) (Fin n) E) i j := by
      rw [← he]; simp
    rw [this]
    refine L.O.add_mem (L.O.mul_mem ht ho) ?_
    by_cases h : i = j
    · subst h; simp [L.O.one_mem]
    · simp [h, L.O.zero_mem]
  let f : L.O →+* E := L.O.subtype
  let M' : Matrix (Fin n) (Fin n) L.O := Matrix.of fun i j => ⟨M i j, hMO i j⟩
  have hM' : f.mapMatrix M' = M := by
    ext i j; rfl
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : f M'.det = (f.mapMatrix M').det := RingHom.map_det f M'
    have h2 : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (M := M) (fun i j hij => hlow i j hij)]
      simp [hdiag]
    change f M'.det = f 1
    rw [h1, hM', h2, map_one]
  have hu : IsUnit M'.det := by rw [hdet]; exact isUnit_one
  refine ⟨f.mapMatrix M'⁻¹, ?_, ?_, ?_⟩
  · rw [← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  · rw [← hM', ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  · intro i j
    set Mi := f.mapMatrix M'⁻¹ with hMi
    have hinv : Mi * M = 1 := by
      rw [hMi, ← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    have key : Mi - 1 = -(Mi * (M - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
    choose o ho he using hcl
    refine ⟨-(∑ k, (M'⁻¹ i k : E) * o k j), ?_, ?_⟩
    · exact L.O.neg_mem (L.O.sum_mem fun k _ => L.O.mul_mem (M'⁻¹ i k).2 (ho k j))
    · rw [key, Matrix.neg_apply, Matrix.mul_apply]
      simp only [he]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hMi, f]
      ring

end GlobalTheory
end

