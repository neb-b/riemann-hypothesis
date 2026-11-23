module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDet
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace DetIdxW

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

def ιc (K : Type) [Field K] [NumberField K] (k : ℕ) : (Fin k → 𝓞 K) →+ (Fin k → K) :=
  (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k)).toAddMonoidHom

lemma ιc_apply (t : Fin k → 𝓞 K) (i : Fin k) : ιc K k t i = algebraMap (𝓞 K) K (t i) := rfl

lemma ιc_inj : Function.Injective (ιc K k) := fun x y h => funext fun c =>
  IsFractionRing.injective (𝓞 K) K (by have := congrFun h c; rwa [ιc_apply, ιc_apply] at this)

lemma oLat_eq : (oLat K k).toAddSubgroup = (⊤ : AddSubgroup (Fin k → 𝓞 K)).map (ιc K k) := by
  ext x
  simp [oLat, ιc, AddSubgroup.mem_map, LinearMap.mem_range]

def vm (M : Matrix (Fin k) (Fin k) K) : (Fin k → K) →+ (Fin k → K) where
  toFun s := s ᵥ* M
  map_zero' := Matrix.zero_vecMul M
  map_add' a b := by simp [Matrix.add_vecMul]

lemma vm_apply (M : Matrix (Fin k) (Fin k) K) (s : Fin k → K) : vm M s = s ᵥ* M := rfl

lemma idx_int (γ : Matrix (Fin k) (Fin k) (𝓞 K)) (hγ : γ.det ≠ 0) :
    ((oLat K k).toAddSubgroup.map (vm (γ.map (algebraMap (𝓞 K) K)))).relIndex (oLat K k).toAddSubgroup =
      (Algebra.norm ℤ γ.det).natAbs := by
  classical
  have hGinj : Function.Injective γᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    by_contra hne
    exact hγ (Matrix.det_transpose γ ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨t, hne, ht⟩)
  let Gz : (Fin k → 𝓞 K) →ₗ[ℤ] (Fin k → 𝓞 K) := γᵀ.mulVecLin.restrictScalars ℤ
  have hGz : Function.Injective Gz := hGinj
  let e := LinearEquiv.ofInjective Gz hGz
  have hcard := Submodule.natAbs_det_equiv (LinearMap.range Gz) e
  have hcomp : (LinearMap.range Gz).subtype ∘ₗ
      (e : (Fin k → 𝓞 K) →+ LinearMap.range Gz).toIntLinearMap = Gz := by
    ext x
    rfl
  have hdetG : LinearMap.det γᵀ.mulVecLin = γ.det := by
    rw [← Matrix.det_transpose γ]
    exact LinearMap.det_toLin' γᵀ
  rw [hcomp, LinearMap.det_restrictScalars, hdetG] at hcard
  have hcomm : (vm (γ.map (algebraMap (𝓞 K) K))).comp (ιc K k) = (ιc K k).comp Gz.toAddMonoidHom := by
    refine AddMonoidHom.ext fun t => funext fun j => ?_
    simp only [AddMonoidHom.comp_apply, vm_apply, ιc_apply, LinearMap.toAddMonoidHom_coe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Gz, Matrix.vecMul, dotProduct, ιc_apply, map_sum, map_mul, mul_comm]
  have hr : (⊤ : AddSubgroup (Fin k → 𝓞 K)).map Gz.toAddMonoidHom = (LinearMap.range Gz).toAddSubgroup := by
    ext x
    simp [LinearMap.mem_range]
  rw [oLat_eq, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _ ιc_inj, AddSubgroup.relIndex_top_right, hr, hcard,
    AddSubgroup.index_eq_card]
  rfl

lemma natAbs_norm_real (x : 𝓞 K) :
    ((Algebra.norm ℤ x).natAbs : ℝ) = |((Algebra.norm ℚ (algebraMap (𝓞 K) K x) : ℚ) : ℝ)| := by
  have h1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 K) K x) := Algebra.coe_norm_int x
  rw [Nat.cast_natAbs, Int.cast_abs, ← h1, Rat.cast_intCast]

lemma vecMul_inj (N : Matrix (Fin k) (Fin k) K) (hN : N.det ≠ 0) {s s' : Fin k → K}
    (h : s ᵥ* N = s' ᵥ* N) : s = s' := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have := congrArg (fun v => v ᵥ* N⁻¹) h
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] using this

end DetIdxW

open DetIdxW in
theorem determinant_index_formula : DetIdx := by
  intro K _ _ k N Q D hOQ hOQ0 hDO hDO0 hDQ
  classical
  by_cases hN : N.det = 0
  · rw [hN, Algebra.norm_zero, Rat.cast_zero, abs_zero]
    positivity
  set O := (oLat K k).toAddSubgroup with hOdef

  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin k × Fin k => N p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set dK := algebraMap (𝓞 K) K d with hdKdef
  have hdK : dK ≠ 0 := by
    rw [hdKdef, Ne, ← map_zero (algebraMap (𝓞 K) K)]
    exact fun h => hd0 (IsFractionRing.injective (𝓞 K) K h)
  have hG : ∀ i j, ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = dK * N i j := by
    intro i j
    obtain ⟨x, hx⟩ := hdT (N i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose G hGe using hG
  let Gm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of G
  have hGmap : Gm.map (algebraMap (𝓞 K) K) = dK • N := by
    ext i j
    simp [Gm, hGe]
  have hdetG : algebraMap (𝓞 K) K Gm.det = dK ^ k * N.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGmap, Matrix.det_smul, Fintype.card_fin]
  have hGdet0 : Gm.det ≠ 0 := by
    intro h
    have h2 := hdetG
    rw [h, map_zero] at h2
    exact (mul_ne_zero (pow_ne_zero _ hdK) hN) h2.symm
  let Dm : Matrix (Fin k) (Fin k) (𝓞 K) := d • (1 : Matrix (Fin k) (Fin k) (𝓞 K))
  have hDmap : Dm.map (algebraMap (𝓞 K) K) = dK • (1 : Matrix (Fin k) (Fin k) K) := by
    ext i j
    by_cases h : i = j <;> simp [Dm, h, hdKdef]
  have hDdet : Dm.det = d ^ k := by simp [Dm]
  have hDdet0 : Dm.det ≠ 0 := by rw [hDdet]; exact pow_ne_zero _ hd0
  set T := vm (Gm.map (algebraMap (𝓞 K) K)) with hTdef
  set S := vm (Dm.map (algebraMap (𝓞 K) K)) with hSdef
  have hT : ∀ s, T s = dK • (s ᵥ* N) := by
    intro s; rw [hTdef, vm_apply, hGmap, Matrix.vecMul_smul]
  have hS : ∀ s, S s = dK • s := by
    intro s; rw [hSdef, vm_apply, hDmap, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hTinj : Function.Injective T := by
    intro s s' h
    rw [hT, hT] at h
    exact vecMul_inj N hN (smul_right_injective _ hdK h)
  have hSinj : Function.Injective S := by
    intro s s' h
    rw [hS, hS] at h
    exact smul_right_injective _ hdK h
  set X := O.map T with hX
  set Y := Q.map T with hY
  set Z := D.map S with hZ
  set dO := O.map S with hdO
  have hXO : X.relIndex O = (Algebra.norm ℤ Gm.det).natAbs := idx_int Gm hGdet0
  have hdOO : dO.relIndex O = (Algebra.norm ℤ Dm.det).natAbs := idx_int Dm hDdet0
  have hXY : X.relIndex Y = O.relIndex Q := AddSubgroup.relIndex_map_map_of_injective _ _ hTinj
  have hZdO : Z.relIndex dO = D.relIndex O := AddSubgroup.relIndex_map_map_of_injective _ _ hSinj
  have hZle_dO : Z ≤ dO := AddSubgroup.map_mono hDO
  have hdO_le : dO ≤ O := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hS]
    have := (oLat K k).smul_mem d hs
    rwa [← algebraMap_smul K d s] at this
  have hZO_le : Z ≤ O := hZle_dO.trans hdO_le
  have hZY : Z ≤ Y := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hsr⟩ := hDQ r hr
    exact ⟨s, hs, by rw [hT, hS, hsr]⟩
  have hZO : Z.relIndex O = D.relIndex O * (Algebra.norm ℤ Dm.det).natAbs := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := hZle_dO) (hKL := hdO_le), hZdO, hdOO]
  have hXY0 : X.relIndex Y ≠ 0 := hXY ▸ hOQ0
  have hXZ0 : X.relIndex Z ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right (hKL := hZY)) hXY0
  have hZO0 : Z.relIndex O ≠ 0 := by
    rw [hZO]
    exact mul_ne_zero hDO0 (Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDdet0))
  have hmul : (X ⊓ Z).relIndex O = X.relIndex Z * Z.relIndex O := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := (inf_le_right : X ⊓ Z ≤ Z)) (hKL := hZO_le),
      AddSubgroup.inf_relIndex_right]
  have h1 : X.relIndex O ≤ (X ⊓ Z).relIndex O :=
    AddSubgroup.relIndex_le_of_le_left (hHK := (inf_le_left : X ⊓ Z ≤ X)) (hHL := by rw [hmul]; exact mul_ne_zero hXZ0 hZO0)
  have h2 : X.relIndex Z ≤ X.relIndex Y := AddSubgroup.relIndex_le_of_le_right (hKL := hZY) (hHL := hXY0)
  have key : X.relIndex O ≤ X.relIndex Y * Z.relIndex O := by
    rw [hmul] at h1
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  rw [hXO, hXY, hZO] at key
  have keyR : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤
      (O.relIndex Q : ℝ) * ((D.relIndex O : ℝ) * ((Algebra.norm ℤ Dm.det).natAbs : ℝ)) := by
    exact_mod_cast key
  rw [natAbs_norm_real, natAbs_norm_real, hdetG, hDdet, map_pow, map_mul, map_pow] at keyR
  simp only [Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow] at keyR
  have ha : 0 < |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k := by
    apply pow_pos
    rw [abs_pos, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hdK
  have : |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * ((O.relIndex Q : ℝ) * (D.relIndex O : ℝ)) := by
    calc _ ≤ _ := keyR
      _ = _ := by ring
  exact le_of_mul_le_mul_left this ha

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDual
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace DIdx

def qI {S : Type} [CommRing S] (𝔞 : Ideal S) (a : S) : Ideal S where
  carrier := {y | ∀ c ∈ 𝔞, c * y ∈ Ideal.span {a}}
  add_mem' := by
    intro y y' hy hy' c hc
    rw [mul_add]
    exact add_mem (hy c hc) (hy' c hc)
  zero_mem' := by
    intro c _
    rw [mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro r y hy c hc
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r (hy c hc)

def aI {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) (x : Fin k → K) :
    Ideal (𝓞 K) where
  carrier := {c | c • x ∈ X}
  add_mem' := by
    intro c c' hc hc'
    rw [Set.mem_ofPred_eq, add_smul]
    exact add_mem hc hc'
  zero_mem' := by
    rw [Set.mem_ofPred_eq, zero_smul]
    exact zero_mem _
  smul_mem' := by
    intro r c hc
    rw [Set.mem_ofPred_eq, smul_eq_mul, mul_smul]
    exact X.smul_mem r hc

theorem absNorm_eq_index {S : Type} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) : Ideal.absNorm I = I.toAddSubgroup.index := by
  letI : Infinite S := Module.Free.infinite ℤ S
  exact Ideal.absNorm_eq_index I

theorem quot_le (K : Type) [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (a : 𝓞 K)
    (ha0 : a ≠ 0) :
    Ideal.span {a} ≤ qI 𝔞 a ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≤ Ideal.absNorm 𝔞 := by
  have hle : Ideal.span {a} ≤ qI 𝔞 a := by
    intro y hy c _
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [Ideal.mem_span_singleton']
    exact ⟨c * z, by ring⟩
  have hmul : 𝔞 * qI 𝔞 a ≤ Ideal.span {a} := Ideal.mul_le.mpr fun r hr s hs => hs r hr
  have hq0 : qI 𝔞 a ≠ ⊥ := by
    intro h
    have : a ∈ qI 𝔞 a := hle (Ideal.mem_span_singleton_self a)
    rw [h, Ideal.mem_bot] at this
    exact ha0 this
  have hNq : Ideal.absNorm (qI 𝔞 a) ≠ 0 := fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNa : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact ha0 h
  have hN𝔞 : Ideal.absNorm 𝔞 ≠ 0 := fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.mp h)
  have hrel : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) =
      Ideal.absNorm (Ideal.span {a}) := by
    rw [absNorm_eq_index, absNorm_eq_index]
    exact AddSubgroup.relIndex_mul_index ((Submodule.toAddSubgroup_le _ _).mpr hle)
  have hdvd : Ideal.absNorm (Ideal.span {a}) ∣ Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    have := Ideal.absNorm_dvd_absNorm_of_le hmul
    rwa [map_mul] at this
  have hr0 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    exact hNa hrel.symm
  refine ⟨hle, hr0, ?_⟩
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) ≤
      Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    rw [hrel]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hN𝔞 hNq)) hdvd
  exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hNq)

theorem dualL_anti {K : Type} [Field K] [NumberField K] {k : ℕ} {X Y : Submodule (𝓞 K) (Fin k → K)}
    (h : X ≤ Y) : dualL Y ≤ dualL X :=
  fun _ ht s hs => ht s (h hs)

theorem smul_dot {K : Type} [Field K] [NumberField K] {k : ℕ} (c : 𝓞 K) (x t : Fin k → K) :
    (c • x) ⬝ᵥ t = algebraMap (𝓞 K) K c * (x ⬝ᵥ t) := by
  simp only [dotProduct, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem step (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)) (hXY : X ≤ Y)
    (hne : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (x : Fin k → K) (hxY : x ∈ Y) :
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤
      X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
  have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
    sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
  have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hneX1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := fun h =>
    hne (AddSubgroup.relIndex_eq_zero_of_le_right ((Submodule.toAddSubgroup_le _ _).mpr hX1Y) h)

  let g : 𝓞 K →+ (Fin k → K) := AddMonoidHom.mk' (fun c => c • x) (fun c c' => add_smul c c' x)
  have e1 : (aI X x).toAddSubgroup = X.toAddSubgroup.comap g := by
    ext c
    exact Iff.rfl
  have hrange : g.range ≤ (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rintro _ ⟨c, rfl⟩
    exact (X ⊔ Submodule.span (𝓞 K) {x}).smul_mem c hxX1
  have hN : Ideal.absNorm (aI X x) = X.toAddSubgroup.relIndex g.range := by
    rw [absNorm_eq_index, e1, AddSubgroup.index_comap]
  have hNne : Ideal.absNorm (aI X x) ≠ 0 := by
    rw [hN]
    exact fun h => hneX1 (AddSubgroup.relIndex_eq_zero_of_le_right hrange h)
  have hNle : Ideal.absNorm (aI X x) ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rw [hN]
    exact AddSubgroup.relIndex_le_of_le_right hrange hneX1
  have h𝔞 : aI X x ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hNne
    exact hNne rfl
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  have hax : a • x ∈ X := ha
  obtain ⟨hle, hq0, hqle⟩ := quot_le K (aI X x) h𝔞 a ha0

  let ψ : (Fin k → K) →+ K := AddMonoidHom.mk' (fun t => algebraMap (𝓞 K) K a * (x ⬝ᵥ t))
    (fun t t' => by simp only [dotProduct_add, mul_add])
  let mO : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hinj : Function.Injective mO := IsFractionRing.injective (𝓞 K) K
  have ha0K : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha0 (hinj (h.trans (map_zero _).symm))
  have claim1 : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).comap ψ ⊓ (dualL X).toAddSubgroup := by
    ext t
    constructor
    · intro ht
      refine ⟨?_, dualL_anti le_sup_left ht⟩
      obtain ⟨o, ho⟩ := ht x hxX1
      refine ⟨a * o, Ideal.mul_mem_right o _ (Ideal.mem_span_singleton_self a), ?_⟩
      show algebraMap (𝓞 K) K (a * o) = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [map_mul, ho]
    · rintro ⟨⟨r, hr, hrt⟩, htX⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have hrt' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t) := by
        rw [← map_mul, mul_comm a o]
        exact hrt
      have hxt : x ⬝ᵥ t = algebraMap (𝓞 K) K o := (mul_left_cancel₀ ha0K hrt').symm
      intro s hs
      obtain ⟨s0, hs0, s1, hs1, rfl⟩ := Submodule.mem_sup.mp hs
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs1
      rw [add_dotProduct, smul_dot, hxt, ← map_mul]
      exact add_mem (htX s0 hs0) ⟨c * o, rfl⟩
  have claim2 : (dualL X).toAddSubgroup.map ψ ≤ (qI (aI X x) a).toAddSubgroup.map mO := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨o, ho⟩ := (show t ∈ dualL X from ht) (a • x) hax
    refine ⟨o, ?_, ?_⟩
    · intro c hc
      obtain ⟨o', ho'⟩ := (show t ∈ dualL X from ht) (c • x) hc
      have : c * o = o' * a := by
        apply hinj
        show algebraMap (𝓞 K) K (c * o) = algebraMap (𝓞 K) K (o' * a)
        rw [map_mul, map_mul, ho, ho', smul_dot, smul_dot]
        ring
      rw [this, Ideal.mem_span_singleton']
      exact ⟨o', rfl⟩
    · show algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [ho, smul_dot]
  have hmapQ : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) =
      (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hrel : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ) := by
    rw [claim1, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  have hQne : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) ≠ 0 := by
    rw [hmapQ]; exact hq0
  rw [hrel]
  refine ⟨fun h => hQne (AddSubgroup.relIndex_eq_zero_of_le_right claim2 h), ?_⟩
  calc ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ)
      ≤ ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) :=
        AddSubgroup.relIndex_le_of_le_right claim2 hQne
    _ = (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup := hmapQ
    _ ≤ Ideal.absNorm (aI X x) := hqle
    _ ≤ _ := hNle

end DIdx

open DIdx in
theorem dual_index_formula : DualIdx := by
  intro K _ _ k X Y hXY hne
  suffices H : ∀ m : ℕ, ∀ X Y : Submodule (𝓞 K) (Fin k → K), X ≤ Y →
      X.toAddSubgroup.relIndex Y.toAddSubgroup = m → m ≠ 0 →
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
        (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup from
    H _ X Y hXY rfl hne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X Y hXY hm hm0
  by_cases hYX : Y ≤ X
  · have e : X = Y := le_antisymm hXY hYX
    subst e
    rw [AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]
    exact ⟨one_ne_zero, le_rfl⟩
  · obtain ⟨x, hxY, hxX⟩ := Set.not_subset.mp hYX
    have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
      sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
    have hXX1 : X ≤ X ⊔ Submodule.span (𝓞 K) {x} := le_sup_left
    have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    obtain ⟨h0, hle⟩ := step K k X Y hXY (by rw [hm]; exact hm0) x hxY
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXX1)
      ((Submodule.toAddSubgroup_le _ _).mpr hX1Y)
    rw [hm] at hmul
    have hb0 : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
      intro h; rw [h, mul_zero] at hmul; exact hm0 hmul.symm
    have ha0 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := by
      intro h; rw [h, zero_mul] at hmul; exact hm0 hmul.symm
    have ha1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 1 := by
      intro h
      rw [AddSubgroup.relIndex_eq_one] at h
      exact hxX (h hxX1)
    have hlt : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup < m := by
      rw [← hmul]
      have h2 : 2 ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by omega
      have hbpos := Nat.pos_of_ne_zero hb0
      nlinarith
    obtain ⟨ih0, ihle⟩ := ih _ hlt (X ⊔ Submodule.span (𝓞 K) {x}) Y hX1Y rfl hb0
    have hdmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hX1Y))
      ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hXX1))
    rw [← hdmul, hm, ← hmul]
    refine ⟨mul_ne_zero ih0 h0, ?_⟩
    rw [mul_comm (X.toAddSubgroup.relIndex _)]
    exact Nat.mul_le_mul ihle hle

end PI.UnitaryGroupMassFormula.LCG
end
end

