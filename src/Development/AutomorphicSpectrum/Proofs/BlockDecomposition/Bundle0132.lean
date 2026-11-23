module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegative
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

universe w v u

theorem HU_subsingleton_of_obj {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    (F : C ⥤ ModuleCat.{w} R) (U : ObjectProperty C) (j : ℕ)
    (h : ∀ T : C, Subsingleton (F.obj T)) : Subsingleton (HU F U j) := by
  have hC : Subsingleton (CH.Cn (U.ι ⋙ F) j) :=
    ⟨fun f g => funext fun s => (h _).elim _ _⟩
  have hZ : Subsingleton ((CH.cx (U.ι ⋙ F)).Z j) :=
    ⟨fun x y => Subtype.ext (hC.elim _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg _ (hZ.elim x y)

theorem sq_obj_subsingleton {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (T : C) (h : a.S T = b.S T) :
    Subsingleton ((sq a b).obj T) := by
  have h0 : ∀ x : sqM a b T, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    refine Subtype.ext ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h ▸ hy)
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

theorem HU_gr_neg {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ) (hr : r < 0) (j : ℕ) :
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  refine HU_subsingleton_of_obj _ Q j fun T => sq_obj_subsingleton _ _ T ?_
  have e : r.toNat = (r + 1).toNat := by omega
  change T.pdPow r.toNat = T.pdPow (r + 1).toNat
  rw [e]

end GlobalTheory.CompanionTheory.Cone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoUnit

theorem awayMap_ratio_mul {K : Type} [Field K] {N e : ℕ} {a b : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ grK K N e) (hb : b ∈ grK K N e) (hb1 : b ∈ grK K N (1 • e)) (ha1 : a ∈ grK K N (1 • e)) :
    HomogeneousLocalization.awayMap (grK K N) hb (x := a * b) rfl
        (HomogeneousLocalization.Away.mk _ ha 1 b hb1) *
      HomogeneousLocalization.awayMap (grK K N) ha (x := a * b) (mul_comm a b)
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) = 1 := by
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

theorem tV_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (k : Fin d) : IsUnit (tV i y hy V hV k) := by
  have h0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy 0)
  have h1 : y k.succ ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy k.succ)
  have h0' : y 0 ∈ grK K N (1 • e) := by rw [one_smul]; exact h0
  have h1' : y k.succ ∈ grK K N (1 • e) := by rw [one_smul]; exact h1
  have hle : Proj.basicOpen (grK K N) (y 0 * y k.succ) ≤ Proj.basicOpen (grK K N) (y 0) := by
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have hU : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * y k.succ) := by
    rw [Proj.basicOpen_mul]
    exact le_inf (hV.trans (iInf_le _ 0)) (hV.trans (iInf_le _ k.succ))
  have hu : IsUnit (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
      (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1')) :=
    isUnit_iff_exists_inv.mpr ⟨_, awayMap_ratio_mul h0 h1 h1' h0'⟩
  have e1 := Scheme.Hom.map_appLE i hU (homOfLE hle).op
  have e2 := Proj.awayMap_awayToSection (grK K N) h1 (f := y 0) (x := y 0 * y k.succ) rfl
  have key : tV i y hy V hV k =
      (Scheme.Hom.appLE i _ V hU).hom ((Proj.awayToSection (grK K N) (y 0 * y k.succ)).hom
        (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
          (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1'))) := by
    unfold tV yRatio
    rw [← e1, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e2, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [key]
  exact (hu.map _).map _

end GlobalTheory.CompanionTheory.GeoUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRange
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTpow

open HomogeneousLocalization

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

theorem evV_awayMap (i : X ⟶ PSpace K N) {f g x : MvPolynomial (Fin (N + 1)) K} {n : ℕ}
    (hg : g ∈ grK K N n) (hx : x = f * g) (V : X.Opens)
    (hf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (hxV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x)
    (a : Away (grK K N) f) :
    evV i x V hxV (awayMap (grK K N) hg hx a) = evV i f V hf a := by
  have h := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (grK K N) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  change (i.appLE _ V hxV).hom ((Proj.awayToSection (grK K N) x).hom (awayMap (grK K N) hg hx a)) = _
  rw [h]
  change ((_ ≫ i.appLE _ V hxV).hom) _ = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem prod_pow_mem {n e p : ℕ} (y : Fin n → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (α : Fin n → ℕ) (hp : (∑ j, α j) * e = p) :
    ∏ j, y j ^ α j ∈ grK K N p := by
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun j => y j ^ α j) (fun j => e * α j)
    (fun j _ => (hy j).pow (α j))
  rw [MvPolynomial.mem_homogeneousSubmodule, ← hp, mul_comm, Finset.mul_sum]
  exact h

theorem prod_mk_pow {n e c : ℕ} {g : MvPolynomial (Fin (N + 1)) K} (hg : g ∈ grK K N e)
    (y : Fin n → MvPolynomial (Fin (N + 1)) K) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (α : Fin n → ℕ)
    (hc : ∑ j, α j = c) (hm : ∏ j, y j ^ α j ∈ grK K N (c • e)) :
    ∏ j, Away.mk (grK K N) hg 1 (y j) (h1 j) ^ α j = Away.mk (grK K N) hg c (∏ j, y j ^ α j) hm := by
  have hpow : ∀ k : ℕ, g ^ k ∈ Submonoid.powers g := fun k => ⟨k, rfl⟩
  let v : Localization (Submonoid.powers g) := Localization.mk 1 ⟨g, 1, pow_one g⟩
  have hv : ∀ k : ℕ, v ^ k = Localization.mk 1 ⟨g ^ k, hpow k⟩ := by
    intro k
    induction k with
    | zero => simpa using Localization.mk_one.symm
    | succ k ih =>
      rw [pow_succ, ih, Localization.mk_mul]
      simp [pow_succ]
  have key : ∀ (k : ℕ) (x) (hx : x ∈ grK K N (k • e)),
      (Away.mk (grK K N) hg k x hx).val = algebraMap _ _ x * v ^ k := by
    intro k x hx
    rw [Away.val_mk, hv, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp
  apply HomogeneousLocalization.val_injective
  rw [← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp_rw [map_pow, HomogeneousLocalization.algebraMap_apply, key, pow_one, mul_pow,
    Finset.prod_mul_distrib, map_prod, map_pow, Finset.prod_pow_eq_pow_sum, hc]

theorem exists_shift {n : ℕ} (S : Finset (Fin n)) (v : Fin n → ℤ) (h : ∀ j, j ∉ S → 0 ≤ v j) :
    ∃ (r : ℕ) (α : Fin n → ℕ), ∀ j, (α j : ℤ) = v j + if j ∈ S then (r : ℤ) else 0 := by
  refine ⟨∑ j, (v j).natAbs, fun j => (v j + if j ∈ S then ((∑ j, (v j).natAbs : ℕ) : ℤ) else 0).toNat, fun j => ?_⟩
  refine Int.toNat_of_nonneg ?_
  by_cases hj : j ∈ S
  · have h1 : (v j).natAbs ≤ ∑ j, (v j).natAbs :=
      Finset.single_le_sum (f := fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hj, if_true]
    omega
  · simpa [hj] using h j hj

theorem cross_mul {c r e₁ e₂ : ℕ} {f g a : MvPolynomial (Fin (N + 1)) K}
    (hf : f ∈ grK K N e₁) (hg : g ∈ grK K N e₂) (ha : a ∈ grK K N (r • e₁)) (ha' : a ∈ grK K N (c • e₂))
    (hF : f ^ r ∈ grK K N (c • e₂)) :
    awayMap (grK K N) hg (mul_comm g f) (Away.mk (grK K N) hf r a ha) *
      awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c (f ^ r) hF) =
    awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c a ha') := by
  simp only [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  simp only [Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
  ring

theorem core {d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (V : X.Opens) (h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (hy0 : y 0 ∈ grK K N e) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (r : ℕ) (α : Fin (d + 1) → ℕ)
    (hα : ∑ j, α j = r * S.card)
    (ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e))) :
    evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
        ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ (if j ∈ S then r else 0) =
      ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ α j := by
  have hP : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * yS y S) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h0 hS
  have hβ : ∑ j, (if j ∈ S then r else 0) = r * S.card := by
    simp [Finset.sum_ite_mem, mul_comm]
  have ha' : ∏ j, y j ^ α j ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy α (by rw [hα, smul_eq_mul])
  have hF' : ∏ j, y j ^ (if j ∈ S then r else 0) ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy _ (by rw [hβ, smul_eq_mul])
  have hFeq : ∏ j, y j ^ (if j ∈ S then r else 0) = yS y S ^ r := by
    simp [yS, pow_ite, Finset.prod_ite_mem, Finset.prod_pow]
  have hF : yS y S ^ r ∈ grK K N ((r * S.card) • e) := hFeq ▸ hF'
  simp_rw [← map_pow, ← map_prod]
  rw [prod_mk_pow hy0 y h1 α hα ha', prod_mk_pow hy0 y h1 _ hβ hF']
  simp only [hFeq]
  rw [← evV_awayMap i hy0 (mul_comm (y 0) (yS y S)) V hS hP,
    ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← map_mul,
    cross_mul (yS_mem y hy S) hy0 ha ha' hF]

theorem tpow_mem_range {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) : 0 < e →
    ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
      (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S,
      tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  intro _ S hS ht m hm
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have h1 : ∀ j, y j ∈ grK K N (1 • e) := fun j => by
    simpa using (MvPolynomial.mem_homogeneousSubmodule e (y j)).2 (hy j)
  let n : Fin (d + 1) → ℤ := Fin.cons (-∑ k, m k) m
  have hn0 : n 0 = -∑ k, m k := rfl
  have hns : ∀ k : Fin d, n k.succ = m k := fun _ => rfl
  have hn : ∀ j, j ∉ S → 0 ≤ n j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · intro hj
      have := hm.2 hj
      rw [hn0]
      omega
    · intro hj
      rw [hns]
      exact hm.1 k hj
  obtain ⟨r, α, hα⟩ := exists_shift S n hn
  have hsum : ∑ j, n j = 0 := by
    rw [Fin.sum_univ_succ, hn0]
    simp only [hns]
    ring
  have hαs : ∑ j, α j = r * S.card := by
    have : ((∑ j, α j : ℕ) : ℤ) = ((r * S.card : ℕ) : ℤ) := by
      push_cast
      simp_rw [hα]
      rw [Finset.sum_add_distrib, hsum]
      simp [Finset.sum_ite_mem, mul_comm]
    exact_mod_cast this
  have ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e)) :=
    prod_pow_mem y hy α (by rw [hαs, smul_eq_mul, mul_assoc])
  refine ⟨Away.mk (grK K N) (yS_mem y hy S) r _ ha, ?_⟩
  have hc := core i y hy V h0 S hS hy0 h1 r α hαs ha
  let T : Fin (d + 1) → (Γ(X, V))ˣ := Fin.cons 1 (fun k => (ht k).unit)
  have hT0 : T 0 = 1 := rfl
  have hTs : ∀ k : Fin d, T k.succ = (ht k).unit := fun _ => rfl
  have hT : ∀ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) = (T j : Γ(X, V)) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · have : Away.mk (grK K N) hy0 1 (y 0) (h1 0) = 1 := by
        apply HomogeneousLocalization.val_injective
        rw [Away.val_mk, HomogeneousLocalization.val_one]
        simpa using Localization.mk_self (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))
      rw [this, map_one, hT0, Units.val_one]
    · rw [hTs, IsUnit.unit_spec]
      rfl
  simp only [hT] at hc
  have hU : ∏ k, (ht k).unit ^ m k = ∏ j, T j ^ n j := by
    rw [Fin.prod_univ_succ, hT0, one_zpow, one_mul]
    simp only [hTs, hns]
  have hA : ∏ j, T j ^ α j = (∏ j, T j ^ n j) * ∏ j, T j ^ (if j ∈ S then r else 0) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add, hα]
    split_ifs <;> simp
  have hc' : evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
      ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) =
      ((∏ j, T j ^ n j : (Γ(X, V))ˣ) : Γ(X, V)) * ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) := by
    rw [← Units.val_mul, ← hA]
    simpa [Units.coe_prod] using hc
  have := (Units.mul_left_inj _).1 hc'
  rw [this, tpow, hU]

end GlobalTheory.CompanionTheory.GeoTpow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniversalCoefficientDegreeZero
section
set_option autoImplicit false

open TensorProduct MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfUnit

theorem exists_unit_on_model : ∀ (R A₀ A₁ P₀ P₁ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] (d₀ : A₀ →ₗ[R] A₁) (a₀ : P₀ →ₗ[R] P₁) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (e : A₀), ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → d₀ e = 0 → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] A₀) (d₀.lTensor M) (ψ₀.lTensor M)) → (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x) → ∃ u : P₀, a₀ u = 0 ∧ ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧ ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x := by
  intro R A₀ A₁ P₀ P₁ _ _ _ _ _ _ _ _ _ d₀ a₀ ψ₀ ψ₁ e hchain hde hq he
  have lid_nat : ∀ {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
      (f : X →ₗ[R] Y) (t : R ⊗[R] X),
      f (TensorProduct.lid R X t) = TensorProduct.lid R Y (f.lTensor R t) := by
    intro X Y _ _ _ _ f t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨x, y, hx, hxy⟩ := (hq R).2 ((1 : R) ⊗ₜ[R] e) (by simp [hde])
  have hxe : ψ₀.lTensor R x = (1 : R) ⊗ₜ[R] e := by
    simpa [sub_eq_zero] using hxy
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [lid_nat, hx, map_zero]
  have hu : ψ₀ (TensorProduct.lid R P₀ x) = e := by
    rw [lid_nat, hxe]; simp
  set u := TensorProduct.lid R P₀ x with hudef
  have hu0 : a₀ u = 0 := by rw [hudef, lid_nat, hx, map_zero]
  intro M _ _
  have hψ : ∀ m : M, ψ₀.lTensor M (m ⊗ₜ[R] u) = m ⊗ₜ[R] e := by
    intro m; simp [hu]
  refine ⟨?_, ?_⟩
  · intro m m' h
    apply (he M).1
    have h' : m ⊗ₜ[R] u = m' ⊗ₜ[R] u := h
    show m ⊗ₜ[R] e = m' ⊗ₜ[R] e
    rw [← hψ, ← hψ, h']
  · intro z hz
    have hd : d₀.lTensor M (ψ₀.lTensor M z) = 0 := by
      have h1 : (d₀.lTensor M) ∘ₗ (ψ₀.lTensor M) = (ψ₁.lTensor M) ∘ₗ (a₀.lTensor M) := by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hchain]
      have h2 := LinearMap.congr_fun h1 z
      simpa [hz] using h2
    obtain ⟨m, hm⟩ := (he M).2 _ hd
    refine ⟨m, ?_⟩
    have ha : a₀.lTensor M (z - m ⊗ₜ[R] u) = 0 := by
      simp [hz, hu0]
    have hp : ψ₀.lTensor M (z - m ⊗ₜ[R] u) = 0 := by
      rw [map_sub, hψ, hm, sub_self]
    obtain ⟨y', hy'⟩ := (hq M).1 _ ha ⟨0, by simp [hp]⟩
    have : z - m ⊗ₜ[R] u = 0 := by
      rw [← hy']; simp
    exact (sub_eq_zero.mp this).symm

end GlobalTheory.CompanionTheory.PerfUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorBundleOfLocalFreeness
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Cot

theorem vb_of_free_on_basicOpens :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ),
      (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
        Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  intro R W _ _ _ g h
  choose r hr hfree hfin hrank using h
  have hs : Ideal.span (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have hfp : Module.FinitePresentation R W := by
    refine Module.FinitePresentation.of_localizationSpan' (Set.range r) hs
      (Rₚ := fun x => Localization.Away x.1) (Mₚ := fun x => Localization.Away x.1 ⊗[R] W)
      (fun x => TensorProduct.mk R (Localization.Away x.1) W 1) (fun x => ?_)
    obtain ⟨x, p, rfl⟩ := x
    have := hfree p
    have := hfin p
    exact Module.finitePresentation_of_projective (Localization.Away (r p))
      (Localization.Away (r p) ⊗[R] W)
  have hproj : Module.Projective R W := by
    rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro p
    have hsub : (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R W := by
      rw [Module.basicOpen_subset_freeLocus_iff]
      have := hfree p
      exact Module.Projective.of_equiv
        (LocalizedModule.equivTensorProduct (Submonoid.powers (r p)) W).symm
    exact hsub (hr p)
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hfl := hfree p
  have hfi := hfin p
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (r p)) (r p)
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r p)))) := by
    rw [hrange]
    exact hr p
  obtain ⟨q', hq'⟩ := hp
  rw [← hq', ← Module.rankAtStalk_baseChange q', Module.rankAtStalk_eq_finrank_of_free]
  exact hrank p

end GlobalTheory.CompanionTheory.Cot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩

def sqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem sqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedge_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) (h2 : Function.Bijective m.pull2) (h : Wedge F') : Wedge F := by
  obtain ⟨e, he⟩ := h
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  let E2 : H2 F ≃ₗ[R] H2 F' := LinearEquiv.ofBijective m.pull2 h2
  refine ⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]
  exact (m.pullCohomologyTwo_cup a b).symm

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

end GlobalTheory.CompanionTheory.Hodge.WedgeField
end
end

