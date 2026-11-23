module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingTensorFiltration
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrTens

variable {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ]
  {I : Ideal A} {γ : DividedPowers I} {m : ℕ} (S : GrSplit O γ m)

theorem dividedPowerFiltration_le {r r' : ℕ} (h : r ≤ r') : pdP γ r' ≤ pdP γ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem dividedPowerFiltration_zero_eq (γ : DividedPowers I) : pdP γ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

def sumMap : (∀ i, S.N i) →ₗ[O] A := ∑ i, (S.ν i).comp (LinearMap.proj i)

theorem sumMap_apply (n : ∀ i, S.N i) : sumMap S n = ∑ i, S.ν i (n i) := by
  simp [sumMap, LinearMap.sum_apply]

theorem sumMap_single (i : Fin m) (x : S.N i) : sumMap S (Pi.single i x) = S.ν i x := by
  rw [sumMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem sumMap_mem (n : ∀ i, S.N i) (r : ℕ) (h : ∀ i : Fin m, (i : ℕ) < r → n i = 0) :
    sumMap S n ∈ pdP γ r := by
  rw [sumMap_apply]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hi : (i : ℕ) < r
  · rw [h i hi, map_zero]
    exact zero_mem _
  · exact dividedPowerFiltration_le (not_lt.1 hi) (S.mem i _)

theorem eq_zero_of_mem (n : ∀ i, S.N i) (r : ℕ) :
    sumMap S n ∈ pdP γ r → ∀ i : Fin m, (i : ℕ) < r → n i = 0 := by
  induction r with
  | zero => intro _ i hi; omega
  | succ r ih =>
    intro h i hi
    have h0 := ih (dividedPowerFiltration_le (Nat.le_succ r) h)
    by_cases hlt : (i : ℕ) < r
    · exact h0 i hlt
    · have hir : (i : ℕ) = r := by omega
      subst hir
      apply S.inj i
      have hs : sumMap S (Function.update n i 0) ∈ pdP γ ((i : ℕ) + 1) := by
        refine sumMap_mem S _ _ fun j hj => ?_
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          refine h0 j ?_
          have : (j : ℕ) ≠ i := fun e => hji (Fin.ext e)
          omega
      have hn : n = Function.update n i 0 + Pi.single i (n i) := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Function.update_of_ne hji, Pi.single_eq_of_ne hji]
      have e : sumMap S n = sumMap S (Function.update n i 0) + S.ν i (n i) := by
        rw [← sumMap_single, ← map_add (f := _), ← hn]
      rw [eq_sub_of_add_eq' e.symm]
      exact sub_mem h hs

theorem exists_sumMap (k : ℕ) : ∀ r, r + k = m → ∀ x ∈ pdP γ r, ∃ n, sumMap S n = x := by
  induction k with
  | zero =>
    intro r hr x hx
    obtain rfl : r = m := by omega
    rw [S.nil] at hx
    exact ⟨0, by rw [map_zero]; exact ((Ideal.mem_bot).1 hx).symm⟩
  | succ k ih =>
    intro r hr x hx
    have hlt : r < m := by omega
    obtain ⟨n₀, hn⟩ := S.surj ⟨r, hlt⟩ x hx
    obtain ⟨n, hn'⟩ := ih (r + 1) (by omega) _ hn
    refine ⟨n + Pi.single ⟨r, hlt⟩ n₀, ?_⟩
    rw [map_add (f := _), sumMap_single, hn']
    exact sub_add_cancel _ _

theorem sumMap_bij : Function.Bijective (sumMap S) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun n h => funext fun i => ?_, fun x => ?_⟩
  · refine eq_zero_of_mem S n m ?_ i i.2
    rw [h]
    exact zero_mem _
  · exact exists_sumMap S m 0 (by omega) x (by rw [dividedPowerFiltration_zero_eq]; trivial)

def sumEquiv : (∀ i, S.N i) ≃ₗ[O] A := LinearEquiv.ofBijective (sumMap S) (sumMap_bij S)

theorem piLeft_tmul_apply (n : ∀ i, S.N i) (x : Γ) (i : Fin m) :
    TensorProduct.piLeft O Γ S.N (n ⊗ₜ x) i = n i ⊗ₜ x := by
  simp [TensorProduct.piLeft, TensorProduct.piRight]

def tensEquiv (Γ : Type) [CommRing Γ] [Algebra O Γ] : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ :=
  (TensorProduct.piLeft O Γ S.N).symm ≪≫ₗ LinearEquiv.rTensor Γ (sumEquiv S)

theorem piLeft_symm_single (i : Fin m) (n : S.N i) (x : Γ) :
    (TensorProduct.piLeft O Γ S.N).symm (Pi.single i (n ⊗ₜ x)) = (Pi.single i n : ∀ i, S.N i) ⊗ₜ x := by
  rw [LinearEquiv.symm_apply_eq]
  funext j
  rw [piLeft_tmul_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem tensEquiv_single (i : Fin m) (n : S.N i) (x : Γ) :
    tensEquiv S Γ (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x := by
  simp only [tensEquiv, LinearEquiv.trans_apply, piLeft_symm_single]
  change sumMap S (Pi.single i n) ⊗ₜ[O] x = _
  rw [sumMap_single]

def coord (i : Fin m) : A →ₗ[O] S.N i := (LinearMap.proj i).comp (sumEquiv S).symm.toLinearMap

theorem coord_eq_zero (i : Fin m) {r : ℕ} (hi : (i : ℕ) < r) {a : A} (ha : a ∈ pdP γ r) : coord S i a = 0 := by
  have e : sumMap S ((sumEquiv S).symm a) = a := (sumEquiv S).apply_symm_apply a
  have h : sumMap S ((sumEquiv S).symm a) ∈ pdP γ r := e.symm ▸ ha
  exact eq_zero_of_mem S _ r h i hi

theorem coord_tensEquiv (i : Fin m) (z : ∀ i, S.N i ⊗[O] Γ) :
    (coord S i).rTensor Γ (tensEquiv S Γ z) = z i := by
  obtain ⟨y, rfl⟩ := (TensorProduct.piLeft O Γ S.N).surjective z
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul n x =>
    have e : tensEquiv S Γ (TensorProduct.piLeft O Γ S.N (n ⊗ₜ x)) = sumEquiv S n ⊗ₜ x := by
      simp only [tensEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    have e' : coord S i (sumEquiv S n) = n i := by
      simp only [coord, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl
    rw [e, LinearMap.rTensor_tmul, e', piLeft_tmul_apply]
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

theorem coord_map_eq_zero (i : Fin m) {r : ℕ} (hi : (i : ℕ) < r) {w : A ⊗[O] Γ}
    (hw : w ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ))) :
    (coord S i).rTensor Γ w = 0 := by
  have key : ∀ c : A ⊗[O] Γ, (coord S i).rTensor Γ (c * w) = 0 := by
    refine Submodule.span_induction (p := fun w _ => ∀ c : A ⊗[O] Γ, (coord S i).rTensor Γ (c * w) = 0)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨p, hp, rfl⟩ c
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        have e : (a ⊗ₜ[O] x) * Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ) p
            = (a * p) ⊗ₜ[O] x := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [e, LinearMap.rTensor_tmul, coord_eq_zero S i hi (Ideal.mul_mem_left _ _ hp), TensorProduct.zero_tmul]
      | add a b ha hb => rw [add_mul, map_add (f := _), ha, hb, add_zero]
    · intro c
      simp
    · intro u v _ _ hu hv c
      rw [mul_add, map_add (f := _), hu, hv, add_zero]
    · intro b u _ hu c
      rw [smul_eq_mul, ← mul_assoc]
      exact hu _
  simpa using key 1

theorem single_mem_map (i : Fin m) {r : ℕ} (hi : r ≤ (i : ℕ)) (t : S.N i ⊗[O] Γ) :
    tensEquiv S Γ (Pi.single i t) ∈
      (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x =>
    rw [tensEquiv_single]
    have e : S.ν i n ⊗ₜ[O] x = Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ) (S.ν i n)
        * ((1 : A) ⊗ₜ[O] x) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (dividedPowerFiltration_le hi (S.mem i n)))
  | add a b ha hb =>
    rw [Pi.single_add, map_add (f := _)]
    exact add_mem ha hb

theorem tensEquiv_mem_iff (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ) :
    tensEquiv S Γ z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
      ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  constructor
  · intro h i hi
    rw [← coord_tensEquiv S i z]
    exact coord_map_eq_zero S i hi h
  · intro h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single z, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < r
    · rw [h i hi, Pi.single_zero, map_zero]
      exact zero_mem _
    · exact single_mem_map S i (not_lt.1 hi) _

theorem main : ∀ {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ] [Module.Flat O Γ]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m),
    ∃ g : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ, (∀ i n x, g (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x) ∧
      ∀ (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ), g z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
        ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  intro O A Γ _ _ _ _ _ _ I γ m S
  exact ⟨tensEquiv S Γ, tensEquiv_single S, tensEquiv_mem_iff S⟩

end GlobalTheory.CompanionTheory.GrTens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioCocycle
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeYq

theorem awayMap_ratio_trans {K : Type} [Field K] {N e : ℕ} {a b c : MvPolynomial (Fin (N + 1)) K}
    (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (hc : c ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (ha1 : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e))
    (hb1 : b ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e)) :
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hc (x := b * c) rfl
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) *
      HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hb (x := b * c)
        (mul_comm b c) (HomogeneousLocalization.Away.mk _ hc 1 b hb1) =
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hb (x := b * c)
        (mul_comm b c) (HomogeneousLocalization.Away.mk _ hc 1 a ha1) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, pow_one]
  ring

theorem away_self {K : Type} [Field K] {N e : ℕ} {a : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (ha1 : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e)) :
    HomogeneousLocalization.Away.mk _ ha 1 a ha1 = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp

theorem appLE_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N e : ℕ} (i : X ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) (hx : x = f * g) (W : X.Opens)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen _ x) (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen _ f)
    (u : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    (i.appLE _ W hW').hom ((Proj.awayToSection _ f).hom u) =
      (i.appLE _ W hW).hom ((Proj.awayToSection _ x).hom
        (HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hg hx u)) := by
  have h := congrArg (fun φ => φ.hom u)
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [h]
  exact (congrArg (fun φ => φ.hom ((Proj.awayToSection _ f).hom u)) (Scheme.Hom.map_appLE i hW _)).symm

theorem yQ_mul_yQ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c) :
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := by
  have mem : ∀ k, y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e :=
    fun k => (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have mem1 : ∀ k, y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e) :=
    fun k => by simpa using mem k
  constructor
  · have hW : W ≤ i ⁻¹ᵁ Proj.basicOpen _ (y b * y c) := by
      rw [Proj.basicOpen_mul]
      exact le_inf hb hc
    have e1 : (i.appLE _ W hb).hom (yQ y hy a b) = _ :=
      appLE_awayMap i (mem c) (x := y b * y c) rfl W hW hb
        (HomogeneousLocalization.Away.mk _ (mem b) 1 (y a) (mem1 a))
    have e2 : (i.appLE _ W hc).hom (yQ y hy b c) = _ :=
      appLE_awayMap i (mem b) (x := y b * y c) (mul_comm _ _) W hW hc
        (HomogeneousLocalization.Away.mk _ (mem c) 1 (y b) (mem1 b))
    have e3 : (i.appLE _ W hc).hom (yQ y hy a c) = _ :=
      appLE_awayMap i (mem b) (x := y b * y c) (mul_comm _ _) W hW hc
        (HomogeneousLocalization.Away.mk _ (mem c) 1 (y a) (mem1 a))
    rw [e1, e2, e3, ← map_mul, ← map_mul, awayMap_ratio_trans (mem b) (mem c) (mem1 a) (mem1 b)]
  · have : yQ y hy a a = 1 := by
      unfold yQ
      rw [away_self (mem a) (mem1 a), map_one]
    rw [this, map_one]

end GlobalTheory.CompanionTheory.ConeYq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnit
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeUnit

theorem yQ_appLE_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m)
    (W : X.Opens) (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k') :
    IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  have ha : y k' ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hb : y k ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have ha1 : y k' ∈ grK K N (1 • e) := by simpa using ha
  have hb1 : y k ∈ grK K N (1 • e) := by simpa using hb
  have hVx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k' * y k) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h2 h1
  have e1 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))
    (Proj.awayMap_awayToSection (grK K N) hb (x := y k' * y k) rfl)
  have e2 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1))
    (Proj.awayMap_awayToSection (grK K N) ha (x := y k' * y k) (mul_comm _ _))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  have e3 : (i.appLE _ W h2).hom (yQ y hy k k') = (i.appLE _ W hVx).hom
      ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) hb (x := y k' * y k) rfl
          (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))) := by
    rw [e1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  refine IsUnit.of_mul_eq_one ((i.appLE _ W hVx).hom ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) ha (x := y k' * y k) (mul_comm _ _)
          (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1)))) ?_
  rw [e3, ← map_mul, ← map_mul, GlobalTheory.CompanionTheory.GeoUnit.awayMap_ratio_mul ha hb hb1 ha1, map_one, map_one]

end GlobalTheory.CompanionTheory.ConeUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebra
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem jacSpan_le_jacS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  intro K _ X V W h _ B hB d m D κ
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨b, bs, rfl⟩
  have hm : ∀ c : Γ(X, W), rs h c ∈ B := fun c => by
    have : rs h c ∈ (B : Set Γ(X, V)) := hB ▸ Set.mem_range_self c
    exact this
  exact AddSubgroup.subset_closure ⟨⟨rs h b, hm b⟩, fun l => ⟨rs h (bs l), hm (bs l)⟩, rfl⟩

end GlobalTheory.CompanionTheory.Cone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSqLePullToSq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedTower

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem pull_sqLe_pull_toSq {a b a' b' : IdF A} (ha : ∀ T, a.S T = ⊤) (ha' : ∀ T, a'.S T = ⊤)
    (hle : ∀ T, a.S T ≤ a'.S T) (hb : ∀ T, b.S T ≤ b'.S T) (j : ℕ) (z : CH.H (CH.modF A) j) :
    (sqLe hle hb).pull j ((toSq a b ha).pull j z) = (toSq a' b' ha').pull j z := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

end Sq

theorem trM_redM {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) (n j : ℕ) (z : HO Q j) :
    trM Q r c n j (redM Q r (c ^ (n + 1)) j z) = redM Q r (c ^ n) j z :=
  pull_sqLe_pull_toSq (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl) (stdI_le Q r c n) j z

end GlobalTheory.CompanionTheory.RedTower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentativeRestrict
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRep

theorem rep_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (a b : IdF A)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (z : CH.Cn (CH.modF (U.ι ⋙ A)) j) (c : HU (sq a b) U j) :
    Rep (a.res U.ι) (b.res U.ι) z c → Rep (a.res V.ι) (b.res V.ι) (resB A h z) ((resU (sq a b) h).pull j c) := by
  rintro ⟨f, hf, hc, hz⟩
  have hf' : CH.d (U.ι ⋙ sq a b) j f = 0 := hf
  have hb : CH.d (V.ι ⋙ sq a b) j ((resU (sq a b) h).pullC j f) = 0 := by
    rw [(resU (sq a b) h).d_pullC, hf', map_zero]
  have hcl : (resU (sq a b) h).pull j c = (CH.cx (V.ι ⋙ sq a b)).cls ((resU (sq a b) h).pullC j f) hb := by
    have hc' : c = (CH.cx (U.ι ⋙ sq a b)).cls f hf' := hc
    rw [hc']
    rfl
  exact ⟨(resU (sq a b) h).pullC j f, hb, hcl, fun s => hz (s ⋙ ObjectProperty.ιOfLE h)⟩

end GlobalTheory.CompanionTheory.ConeRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRs

theorem rs_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)) : rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  change ((f.appLE U W hW) ≫ X.presheaf.map (homOfLE h).op).hom s = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.CompanionTheory.ConeRs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LecShift

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  intro O A _ _ _ I γ X q l s 𝒱 i a ha r T x hx
  have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ (r - i).toNat := hx
  have h1 : T.obj.i a ∈ pdP T.obj.δ i := dividedPowerFiltration_map T.obj.compat i ha
  have h2 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ i (r - i).toNat (Ideal.mul_mem_mul h1 hx')
  exact T.obj.pdPow_anti (show r.toNat ≤ i + (r - i).toNat by omega) h2

end GlobalTheory.CompanionTheory.LecShift
end

