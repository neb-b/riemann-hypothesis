module

public import Mathlib
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLcIso
section
noncomputable section

open GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem norm_symm_le_one (i : ℚ_[g] ≃+* k) (hi : Continuous i) {x : k}
    (hx : x ∈ (ValuativeRel.valuation k).integer) : ‖i.symm x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hy⟩ : ∃ y, i.symm x = y := ⟨_, rfl⟩
  rw [hy] at hlt
  have hix : i y = x := by rw [← hy, RingEquiv.apply_symm_apply]
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hlt; exact absurd hlt (by norm_num)
  have hx0 : x ≠ 0 := by rw [← hix]; exact (map_ne_zero i).2 hy0
  have hz : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hlt
  have hϖ1 : ValuativeRel.valuation k (GLnLocal.uniformizer k : k) < 1 := GLnLocal.valuation_uniformizer_lt_one k
  have hϖ0 : (GLnLocal.uniformizer k : k) ≠ 0 := fun h =>
    GLnLocal.valuation_uniformizer_ne_zero k (by rw [h, map_zero])
  have h1 : Filter.Tendsto (fun m : ℕ => y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).mul_const (i.symm (GLnLocal.uniformizer k : k)⁻¹)
  have hT : Filter.Tendsto (fun m : ℕ => i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹)) Filter.atTop
      (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hO : ((ValuativeRel.valuation k).integer : Set k) ∈ nhds (0 : k) :=
    Valuation.isOpen_integer.mem_nhds (zero_mem _)
  obtain ⟨m, hm⟩ := (hT.eventually hO).exists
  have hm' : i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) ∈ (ValuativeRel.valuation k).integer := hm
  have hval := (Valuation.mem_integer_iff _ _).1 hm'
  have hxv := (Valuation.mem_integer_iff _ _).1 hx
  have hiy : i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) * x ^ m = (GLnLocal.uniformizer k : k)⁻¹ := by
    rw [map_mul, map_pow, map_inv₀, hix, RingEquiv.apply_symm_apply, inv_pow,
      mul_comm ((x ^ m)⁻¹) _, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx0), mul_one]
  have hle : ValuativeRel.valuation k (GLnLocal.uniformizer k : k)⁻¹ ≤ 1 := by
    rw [← hiy, map_mul, map_pow]
    exact mul_le_one' hval (pow_le_one' hxv m)
  have hge : (1 : ValuativeRel.ValueGroupWithZero k) ≤ ValuativeRel.valuation k (GLnLocal.uniformizer k : k) := by
    calc (1 : ValuativeRel.ValueGroupWithZero k)
        = ValuativeRel.valuation k ((GLnLocal.uniformizer k : k) * (GLnLocal.uniformizer k : k)⁻¹) := by
          rw [mul_inv_cancel₀ hϖ0, map_one]
      _ = ValuativeRel.valuation k (GLnLocal.uniformizer k : k) *
          ValuativeRel.valuation k (GLnLocal.uniformizer k : k)⁻¹ := map_mul _ _ _
      _ ≤ ValuativeRel.valuation k (GLnLocal.uniformizer k : k) * 1 := by gcongr
      _ = _ := mul_one _
  exact absurd hϖ1 (not_lt.2 hge)

theorem exists_inc_eq (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (k0 : GL (Fin n) k)
    (hk : k0 ∈ GLnLocal.integralGL k n) :
    ∃ κ : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = k0 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff k n).1 hk
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b =>
    ⟨i.symm ((k0 : Matrix (Fin n) (Fin n) k) a b), norm_symm_le_one i hi (h1 a b)⟩
  let M' : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b =>
    ⟨i.symm (((k0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b), norm_symm_le_one i hi (h2 a b)⟩
  let φ : ℤ_[g] →+* k := i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])
  have hφ : Function.Injective φ := fun a b h => Subtype.ext (i.injective h)
  have hMφ : M.map φ = (k0 : Matrix (Fin n) (Fin n) k) := by
    ext a b
    exact i.apply_symm_apply _
  have hM'φ : M'.map φ = ((k0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    ext a b
    exact i.apply_symm_apply _
  have hMM : M * M' = 1 := by
    apply Matrix.map_injective hφ
    show (M * M').map φ = (1 : Matrix (Fin n) (Fin n) ℤ_[g]).map φ
    rw [Matrix.map_mul, hMφ, hM'φ, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hM'M : M' * M = 1 := by
    apply Matrix.map_injective hφ
    show (M' * M).map φ = (1 : Matrix (Fin n) (Fin n) ℤ_[g]).map φ
    rw [Matrix.map_mul, hMφ, hM'φ, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨⟨M, M', hMM, hM'M⟩, Matrix.GeneralLinearGroup.ext fun a b => ?_⟩
  exact i.apply_symm_apply _

theorem exists_lift (i : ℚ_[g] ≃+* k) {n a : ℕ} (u : GL (Fin n) (ZMod g))
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) :
    ∃ κ : GL (Fin n) ℤ_[g], GlobalTheory.GLp.red g n κ = u ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) ∈
        GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) := by
  classical
  have hu' := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  have hoff : ∀ x y, x ≠ y → GlobalTheory.FiniteGL.twoBlocks n a y ≤ GlobalTheory.FiniteGL.twoBlocks n a x →
      (u : Matrix (Fin n) (Fin n) (ZMod g)) x y = 0 := by
    intro x y hxy h
    have := hu' x y h
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hxy, sub_zero] at this
  have hdiag : ∀ x, (u : Matrix (Fin n) (Fin n) (ZMod g)) x x = 1 := by
    intro x
    have := hu' x x le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun x y =>
    if x = y then 1 else (((u : Matrix (Fin n) (Fin n) (ZMod g)) x y).val : ℤ_[g])
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (u : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext x y
    show PadicInt.toZMod (M x y) = _
    simp only [M]
    split_ifs with h
    · subst h
      rw [map_one, hdiag]
    · rw [map_natCast, ZMod.natCast_zmod_val]
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]
      exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit u)).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, Units.ext hM, ?_⟩
  refine GlobalTheory.FiniteGL.mem_unipRadical.2 fun x y hxy => ?_
  rw [Matrix.sub_apply]
  show i.toRingHom (algebraMap ℤ_[g] ℚ_[g] (M x y)) - (1 : Matrix (Fin n) (Fin n) k) x y = 0
  by_cases h : x = y
  · subst h
    simp [M]
  · have h0 := hoff x y h hxy
    simp [M, h, h0]

end DiscreteGroups.sglob.DzLc
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLcPerm
section
noncomputable section

open Matrix

namespace DiscreteGroups.sglob.DzLc

variable {F : Type} [Field F] {N : ℕ}

theorem strict_left_mul {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) F}
    (hX : X.BlockTriangular b) (hY : GlobalTheory.FiniteGL.IsStrictBlock b Y) : GlobalTheory.FiniteGL.IsStrictBlock b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (b l) (b i) with h | h
  · rw [hX h, zero_mul]
  · rw [hY l j (le_trans hij h), mul_zero]

theorem conj_mem_unipRadical {b : Fin N → ℕ} {p u : GL (Fin N) F}
    (hp : (p : Matrix (Fin N) (Fin N) F).BlockTriangular b) (hu : u ∈ GlobalTheory.FiniteGL.unipRadical F b) :
    p * u * p⁻¹ ∈ GlobalTheory.FiniteGL.unipRadical F b := by
  have hpi : ((p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F).BlockTriangular b := by
    let _ := p.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hp
  have h1 : (p : Matrix (Fin N) (Fin N) F) * ((p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : ((p * u * p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) - 1 =
      (p : Matrix (Fin N) (Fin N) F) * ((u : Matrix (Fin N) (Fin N) F) - 1) *
        ((p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h1]
  refine GlobalTheory.FiniteGL.mem_unipRadical.2 fun i j hij => ?_
  rw [e, Matrix.mul_assoc]
  exact strict_left_mul hp
    (GlobalTheory.FiniteGL.IsStrictBlock.mul_blockTriangular (GlobalTheory.FiniteGL.mem_unipRadical.1 hu) hpi) i j hij

theorem monotone_twoBlocks (a : ℕ) : Monotone (GlobalTheory.FiniteGL.twoBlocks N a) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [GlobalTheory.FiniteGL.twoBlocks]
  split_ifs <;> omega

theorem blockUpper_le_normalizer (b : Fin N → ℕ) :
    GroundTheory.Automorphic.Iwasawa.blockUpper F N b ≤
      Subgroup.normalizer (GlobalTheory.FiniteGL.unipRadical F b : Set (GL (Fin N) F)) := by
  intro p hp
  refine Subgroup.mem_normalizer_iff.2 fun u => ⟨fun hu => conj_mem_unipRadical hp hu, fun hu => ?_⟩
  have hp' : p⁻¹ ∈ GroundTheory.Automorphic.Iwasawa.blockUpper F N b := inv_mem hp
  have := conj_mem_unipRadical hp' hu
  have e : p⁻¹ * (p * u * p⁻¹) * p⁻¹⁻¹ = u := by group
  rwa [e] at this

theorem exists_cut (f : Fin N → ℕ) (hf : Monotone f) (h : ∃ x y, f x ≠ f y) :
    ∃ a, 0 < a ∧ a < N ∧ ∀ i j : Fin N, (i : ℕ) < a → a ≤ (j : ℕ) → f i < f j := by
  classical
  obtain ⟨x, y, hxy⟩ := h
  have hN : 0 < N := x.pos
  have hex : ∃ m, ∃ hm : m < N, f ⟨m, hm⟩ ≠ f ⟨0, hN⟩ := by
    by_contra hcon
    push Not at hcon
    exact hxy ((hcon x x.2).trans (hcon y y.2).symm)
  obtain ⟨hm, hne⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ?_, hm, fun i j hi hj => ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · exact absurd (congrArg f (Fin.ext h0 : (⟨Nat.find hex, hm⟩ : Fin N) = ⟨0, hN⟩)) hne
    · exact h0
  · have h1 : f i = f ⟨0, hN⟩ := by
      by_contra hc
      exact Nat.find_min hex hi ⟨i.2, hc⟩
    have h2 : f ⟨Nat.find hex, hm⟩ ≤ f j := hf (show (⟨Nat.find hex, hm⟩ : Fin N) ≤ j from hj)
    have h3 : f ⟨0, hN⟩ ≤ f ⟨Nat.find hex, hm⟩ :=
      hf (show (⟨0, hN⟩ : Fin N) ≤ ⟨Nat.find hex, hm⟩ from Nat.zero_le _)
    rw [h1]
    exact lt_of_lt_of_le (lt_of_le_of_ne h3 (Ne.symm hne)) h2

theorem exists_perm_conj {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (he : GlobalTheory.SmGL.unipRad F e ≠ ⊥) :
    ∃ (Q : GL (Fin N) F) (a : ℕ), 0 < a ∧ a < N ∧
      ∀ x ∈ GlobalTheory.FiniteGL.unipRadical F (GlobalTheory.FiniteGL.twoBlocks N a), Q * x * Q⁻¹ ∈ GlobalTheory.SmGL.unipRad F e := by
  classical
  obtain ⟨β, hβ⟩ : ∃ β : Fin N → ℕ, β = fun x => ((GlobalTheory.SmGL.blk e x : Fin s) : ℕ) := ⟨_, rfl⟩
  have hβe : ∀ c (i : Fin (d c)), β (e ⟨c, i⟩) = c := fun c i => by subst hβ; simp
  obtain ⟨x0, y0, hxy⟩ : ∃ x y, β x ≠ β y := by
    by_contra hcon
    push Not at hcon
    apply he
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
    obtain ⟨-, hdiag⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
    refine Matrix.GeneralLinearGroup.ext fun x y => ?_
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨c', j⟩, rfl⟩ := e.surjective y
    have hcc : c = c' := by
      have := hcon (e ⟨c, i⟩) (e ⟨c', j⟩)
      rw [hβe, hβe] at this
      exact Fin.ext this
    subst hcc
    rw [hdiag c i j]
    simp [Matrix.one_apply, e.injective.eq_iff]
  obtain ⟨ν, hν⟩ : ∃ ν : Equiv.Perm (Fin N), ν = Tuple.sort β := ⟨_, rfl⟩
  have hmono : Monotone (β ∘ ν) := hν ▸ Tuple.monotone_sort β
  obtain ⟨a, ha0, haN, hcut⟩ := exists_cut (β ∘ ν) hmono
    ⟨ν.symm x0, ν.symm y0, by simpa using hxy⟩
  have h12 : (ν.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) * ν.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext u v
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]
  have h21 : (ν.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) * ν.symm.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext u v
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]
  let Q : GL (Fin N) F := ⟨_, _, h12, h21⟩
  have hQ : ∀ X : GL (Fin N) F, ∀ u v, ((Q * X * Q⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) u v =
      (X : Matrix (Fin N) (Fin N) F) (ν.symm u) (ν.symm v) := by
    intro X u v
    show (((ν.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) * (X : Matrix (Fin N) (Fin N) F) *
      ν.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F)) u v = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp
  refine ⟨Q, a, ha0, haN, fun x hx => ?_⟩
  have hxe := GlobalTheory.FiniteGL.mem_unipRadical.1 hx
  have key : ∀ p q : Fin N, (x : Matrix (Fin N) (Fin N) F) p q ≠ (1 : Matrix (Fin N) (Fin N) F) p q →
      β (ν p) < β (ν q) := by
    intro p q hpq
    by_cases hp : (p : ℕ) < a
    · by_cases hq : a ≤ (q : ℕ)
      · exact hcut p q hp hq
      · exfalso
        apply hpq
        have h := hxe p q (by unfold GlobalTheory.FiniteGL.twoBlocks; split_ifs <;> omega)
        rw [Matrix.sub_apply, sub_eq_zero] at h
        exact h
    · exfalso
      apply hpq
      have h := hxe p q (by unfold GlobalTheory.FiniteGL.twoBlocks; split_ifs <;> omega)
      rw [Matrix.sub_apply, sub_eq_zero] at h
      exact h
  refine GlobalTheory.SmGL.mem_unipRad.2 ⟨GlobalTheory.SmGL.mem_parab.2 fun u v huv => ?_, fun c i j => ?_⟩
  · rw [hQ x u v]
    have hne : u ≠ v := fun h => by subst h; exact lt_irrefl _ huv
    have h1 : (1 : Matrix (Fin N) (Fin N) F) (ν.symm u) (ν.symm v) = 0 :=
      Matrix.one_apply_ne fun h => hne (ν.symm.injective h)
    by_contra hc
    have h2 := key (ν.symm u) (ν.symm v) (by rw [h1]; exact hc)
    simp only [Equiv.apply_symm_apply] at h2
    have h3 : β v < β u := by rw [hβ]; exact huv
    exact lt_asymm h2 h3
  · rw [hQ x]
    by_cases hij : i = j
    · subst hij
      have h := hxe (ν.symm (e ⟨c, i⟩)) (ν.symm (e ⟨c, i⟩)) le_rfl
      rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply_eq] at h
      rw [h, Matrix.one_apply_eq]
    · have hne : e ⟨c, i⟩ ≠ e ⟨c, j⟩ := fun h => hij (by simpa using e.injective h)
      rw [Matrix.one_apply_ne hij]
      by_contra hc
      have h2 := key _ _ (by rwa [Matrix.one_apply_ne (fun h => hne (ν.symm.injective h))])
      simp only [Equiv.apply_symm_apply] at h2
      rw [hβe, hβe] at h2
      exact lt_irrefl _ h2

end DiscreteGroups.sglob.DzLc
end
end

