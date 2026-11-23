module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix

namespace GlobalTheory.RiemannRel

theorem map_im_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.im = P.map Complex.re * Q.map Complex.im + P.map Complex.im * Q.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

theorem map_re_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.re = P.map Complex.re * Q.map Complex.re - P.map Complex.im * Q.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

theorem hermForm_cols {h : ℕ} (Hm P Q : Matrix (Fin h) (Fin h) ℂ) (i j : Fin h) :
    (Pᵀ * Hm * Q.map star) i j = hermForm Hm (fun k => P k i) (fun k => Q k j) := by
  rw [Matrix.mul_assoc]
  simp [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec]

theorem matrix_form {h : ℕ} (Hm L M : Matrix (Fin h) (Fin h) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hG : (Mᵀ * Hm * M.map star).map Complex.im = 0)
    (hA : (Lᵀ * Hm * M.map star).map Complex.im = 1)
    (hB : (Lᵀ * Hm * L.map star).map Complex.im = 0) :
    IsUnit M.det ∧ (M⁻¹ * L).IsSymm ∧ ((M⁻¹ * L).map Complex.im).PosDef := by
  set G := Mᵀ * Hm * M.map star with hGdef
  have hGh : G.IsHermitian := by
    have h1 : M.map star = (Mᵀ)ᴴ := by ext i j; simp
    rw [hGdef, h1]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hH
  set R := G.map Complex.re with hR
  have hRs : Rᵀ = R := by
    ext i j
    have := congrArg Complex.re (hGh.apply i j)
    simpa [hR] using this
  have hGR : G = R.map Complex.ofReal := by
    ext i j
    have := congrFun (congrFun hG i) j
    apply Complex.ext
    · simp [hR]
    · simpa [hR] using this
  have hRp : R.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hRs) fun x hx => ?_
    set xc : Fin h → ℂ := fun i => (x i : ℂ) with hxc
    have hst : star (M.mulVec xc) = (M.map star).mulVec xc := by
      funext i
      simp [Matrix.mulVec, dotProduct, hxc]
    have hne : M.mulVec xc ≠ 0 := by
      intro h0
      apply hx
      have h1 : (Lᵀ * Hm * M.map star).mulVec xc = 0 := by
        rw [← Matrix.mulVec_mulVec, ← hst, h0]; simp
      have h2 : ((Lᵀ * Hm * M.map star).map Complex.im).mulVec x = 0 := by
        funext i
        have := congrArg Complex.im (congrFun h1 i)
        simpa [Matrix.mulVec, dotProduct, hxc, Complex.im_sum] using this
      rwa [hA, Matrix.one_mulVec] at h2
    have h3 := hpos _ hne
    have h4 : M.mulVec xc ⬝ᵥ Hm.mulVec (star (M.mulVec xc)) = xc ⬝ᵥ G.mulVec xc := by
      rw [hst, hGdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec xc, Matrix.vecMul_transpose]
    rw [h4] at h3
    simpa [Matrix.mulVec, dotProduct, hxc, Complex.re_sum, hR] using h3
  have hRu : IsUnit R.det := hRp.det_pos.ne'.isUnit
  have hMu : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : G.det = 0 := by
      rw [hGdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; simp
    have h2 : G.det = (R.det : ℂ) := by
      rw [hGR]
      exact (Complex.ofRealHom.map_det R).symm
    rw [h1] at h2
    exact hRu.ne_zero (Complex.ofReal_eq_zero.1 h2.symm)
  set τ := M⁻¹ * L with hτ
  have hL : L = M * τ := by rw [hτ, Matrix.mul_nonsing_inv_cancel_left _ _ hMu]
  have hA' : Lᵀ * Hm * M.map star = τᵀ * G := by
    conv_lhs => rw [hL]
    rw [hGdef, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hB' : Lᵀ * Hm * L.map star = τᵀ * G * τ.map star := by
    have : L.map star = M.map star * τ.map star := by
      conv_lhs => rw [hL]
      exact Matrix.map_mul (f := starRingEnd ℂ)
    rw [this, ← Matrix.mul_assoc, hA']
  set X := τ.map Complex.re with hX
  set Y := τ.map Complex.im with hY
  have e1 : τᵀ.map Complex.re = Xᵀ := rfl
  have e2 : τᵀ.map Complex.im = Yᵀ := rfl
  have e3 : (τ.map star).map Complex.re = X := by ext i j; simp [hX]
  have e4 : (τ.map star).map Complex.im = -Y := by ext i j; simp [hY]
  rw [hB', map_im_mul, ← hA', hA, hA', map_re_mul, e1, e2, e3, e4, hG, ← hR] at hB
  rw [hA', map_im_mul, e1, e2, hG, ← hR, Matrix.mul_zero, zero_add] at hA
  have hRY : R * Y = 1 := by
    have := congrArg Matrix.transpose hA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.transpose_one] at this
  have hYi : R⁻¹ = Y := Matrix.inv_eq_right_inv hRY
  have hYi' : R⁻¹ = Yᵀ := Matrix.inv_eq_left_inv hA
  have hXs : Xᵀ = X := by
    rw [Matrix.mul_zero, sub_zero, Matrix.mul_neg, Matrix.mul_assoc, hRY, Matrix.mul_one, Matrix.one_mul] at hB
    exact (neg_add_eq_zero.1 hB)
  refine ⟨hMu, ?_, hYi ▸ hRp.inv⟩
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun hXs i) j
  · exact congrFun (congrFun (hYi'.symm.trans hYi) i) j

theorem exists_siegel_of_symplectic : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  intro h Hm v hH hpos hv
  let L : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inl i) k
  let M : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inr i) k
  obtain ⟨hM, hs, hp⟩ := matrix_form Hm L M hH hpos
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inr i) (.inr j)).trans ?_
      simp [omegaStd])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inr j)).trans ?_
      simp [omegaStd, Pi.single_apply, Matrix.one_apply, eq_comm])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inl j)).trans ?_
      simp [omegaStd])
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hM
  refine ⟨M⁻¹ * L, M.toLinearEquiv' inferInstance, hs, hp, fun a => ?_⟩
  change M.mulVec (per (M⁻¹ * L) a) = _
  rw [per, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hM]
  funext k
  simp [L, M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]

end GlobalTheory.RiemannRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelMod
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymplecticLevelLift

open Matrix Module

theorem omegaStd_single {h : ℕ} (i j : Fin h ⊕ Fin h) :
    omegaStd (Pi.single i 1) (Pi.single j 1) = (-Matrix.J (Fin h) ℤ) i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [omegaStd, Matrix.J, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem gram_eq {h : ℕ} {M : Type} [AddCommGroup M] {Ef : LinearMap.BilinForm ℤ M}
    {b : Basis (Fin h ⊕ Fin h) ℤ M} (hb : IsSymplecticBasis Ef b) (hE : Ef.IsAlt)
    (v : Fin h ⊕ Fin h → M) :
    (Matrix.of fun i j => Ef (v i) (v j)) =
      (b.toMatrix v)ᵀ * (-Matrix.J (Fin h) ℤ) * b.toMatrix v := by
  ext i j
  rw [of_apply, hb.apply_eq_sum hE]
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Basis.toMatrix_apply, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring

theorem exists_symplectic_equiv_congr : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  intro h k M _ _ _ Ef l _ hrk halt hbij hl
  have hE : Ef.IsAlt := halt
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hE hbij hrk
  set v : Fin h ⊕ Fin h → M := fun j => l (Pi.single j 1) with hv
  have hmem : (b.toMatrix v).map (Int.castRingHom (ZMod k)) ∈
      Matrix.symplecticGroup (Fin h) (ZMod k) := by
    rw [SymplecticGroup.mem_iff']
    have h1 : (Matrix.of fun i j => Ef (v i) (v j)).map (Int.castRingHom (ZMod k)) =
        (-Matrix.J (Fin h) ℤ).map (Int.castRingHom (ZMod k)) := by
      ext i j
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).2 (hl (Pi.single i 1) (Pi.single j 1))
      rw [omegaStd_single, Int.cast_sub, sub_eq_zero] at this
      simpa [hv] using this
    rw [gram_eq hb hE, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (map_neg _), map_J,
      transpose_map] at h1
    simpa using h1
  obtain ⟨N, hN, hNT⟩ := symplectic_zmod_lift h k _ hmem
  have hw : b.toMatrix (fun j => ∑ i, N i j • b i) = N := by
    ext i j
    rw [Basis.toMatrix_apply, b.repr_sum_self]
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hE (hw.symm ▸ hN)
  have hcong : ∀ j, ∃ m : M, v j - c j = (k : ℤ) • m := by
    intro j
    have hd : ∀ i, ∃ t : ℤ, b.toMatrix v i j - N i j = k * t := fun i => by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).1 ?_
      have := congrFun (congrFun hNT i) j
      simp only [Matrix.map_apply, eq_intCast] at this
      rw [Int.cast_sub, this, sub_self]
    choose t ht using hd
    refine ⟨∑ i, t i • b i, ?_⟩
    rw [← b.sum_toMatrix_smul_self v j, hcv, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← sub_smul, ht, mul_smul]
  choose m hm using hcong
  refine ⟨c.equivFun.symm, fun x y => ?_, fun a => ⟨∑ j, a j • m j, ?_⟩⟩
  · have hr : ∀ (z : Fin h ⊕ Fin h → ℤ) i, c.repr (c.equivFun.symm z) i = z i := fun z i => by
      rw [← c.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc.apply_eq_sum hE]
    simp only [hr, omegaStd]
  · have hla : l a = ∑ j, a j • v j := by
      conv_lhs => rw [← Finset.univ_sum_single a]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hv, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hla, c.equivFun_symm_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← smul_sub, hm, smul_comm]

end GlobalTheory.SymplecticLevelLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMatrixOfConjugateTransport
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem exists_torsion_matrix : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ h c₀ c₁ τ₀ τ₁ h₀ h₁ N _
  obtain ⟨a, b, c⟩ := _root_.GlobalTheory.RelTors.main K ι Λ₀ Λ₁ (Tr t) c₀ c₁ τ₀ τ₁
    (_root_.GlobalTheory.WpFam.TrIs.main K ι g t Λ₀ Λ₁ Ω₀ Ω₁ h) h₀ h₁ N
    (fun x y => ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ Tr t k k')
    (fun _ _ => Iff.rfl)
  exact _root_.GlobalTheory.RelLin.main N _ a b c

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMatrixLiftModTauAinf
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.WinLift

theorem isUnit_of_isUnit_theta {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O)
    (z : Ainf p O) (hz : IsUnit (WittVector.fontaineTheta O p z)) : IsUnit z := by
  haveI := GlobalTheory.AinfXi.isLocalRing_ainf (p := p) hv
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  by_contra hn
  obtain ⟨w, hw⟩ := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (↑hz.unit⁻¹ : O)
  have hm : z ∈ IsLocalRing.maximalIdeal (Ainf p O) := (IsLocalRing.mem_maximalIdeal _).2 hn
  have hk : z * w - 1 ∈ IsLocalRing.maximalIdeal (Ainf p O) := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (WittVector.fontaineTheta O p))
    rw [RingHom.mem_ker, map_sub, map_mul, hw, map_one, IsUnit.mul_val_inv, sub_self]
  have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hm) hk
  rw [sub_sub_cancel] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (Ainf p O)).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_unit_lift_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F ι _ _ U hU
  choose x y hxy using fun i j => F.gen (U i j)
  refine ⟨Matrix.of x, ?_, fun i j => ⟨F.a (y i j), by rw [hxy i j]; simp⟩⟩
  have hτ := GlobalTheory.WinLift.theta_tau F hv hε
  have e : F.θ.mapMatrix (F.a.mapMatrix (Matrix.of x)) = F.θ.mapMatrix U :=
    Matrix.ext fun i j => by simp [hxy i j, hτ]
  have hdet : WittVector.fontaineTheta O p (Matrix.of x).det = F.θ U.det := by
    rw [← F.θ_a, RingHom.map_det, RingHom.map_det, e, ← RingHom.map_det]
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_theta hv
  rw [hdet]
  exact ((Matrix.isUnit_iff_isUnit_det U).1 hU).map F.θ

end GlobalTheory.WinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBase
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section FrobInv

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem wittMap_frobeniusEquiv_symm (x : WittVector p k) :
    WittVector.map ((frobeniusEquiv k p).symm : k →+* k) x = (WittVector.frobeniusEquiv p k).symm x := by
  apply (WittVector.frobeniusEquiv p k).injective
  rw [RingEquiv.apply_symm_apply]
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff]

noncomputable def frobInv (G : PDivGroup p k) :
    SemiHom ((frobeniusEquiv k p).symm : k →+* k) G (frobTwist (p_eq_zero p k) G) :=
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  (SemiHom.ofHom (𝟙 G)).liftOver _ fun r => by
    change r = (frobeniusEquiv k p).symm (frobRing (p_eq_zero p k) r)
    rw [frobRing_apply, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

theorem frobInv_frobProj (G : PDivGroup p k) (n : ℕ) (a : G.A n) :
    (frobInv G).app n ((frobProj (p_eq_zero p k) G).app n a) = a := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  refine (SemiHom.liftOver_app _ _ _ n 1 a).trans ?_
  simp

theorem frobInv_app_pow (G : PDivGroup p k) (n : ℕ) (y : (frobTwist (p_eq_zero p k) G).A n) :
    ((frobInv G).app n y) ^ p = (relFrob (p_eq_zero p k) G).app n y := by
  have h0 : (p : G.A n) = 0 := natCast_eq_zero_of_algebra (p_eq_zero p k) _
  induction y using frobTwist_induction (p_eq_zero p k) n with
  | h0 => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | h1 r a =>
    rw [(frobInv G).app n |>.smul_map, frobInv_frobProj, map_smul, relFrob_app_frobProj, smul_pow]
    congr 1
    exact frobeniusEquiv_symm_pow_p k p r
  | h2 x y hx hy =>
    rw [map_add (f := _), map_add (f := _), ← hx, ← hy]
    simpa using map_add (frobRing h0) ((frobInv G).app n x) ((frobInv G).app n y)


omit [CharP k p] [PerfectRing k p] in
theorem Base.smap_ofHom_nsmul_id {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
    [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (n : ℕ) (m : B.M G h) :
    B.smap h h (SemiHom.ofHom (n • 𝟙 G)) m = n • m := by
  induction n with
  | zero =>
    have e := B.smap_add h h 0 0 m
    rw [add_zero] at e
    rw [zero_smul, zero_smul]
    simpa using e
  | succ n ih => rw [succ_nsmul, B.smap_add, ih, B.smap_id, succ_nsmul]

noncomputable def Base.verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) :
    B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      B.M G trivial where
  toFun m := B.smap trivial trivial (frobInv G) (B.map trivial trivial (verschiebung (p_eq_zero p k) G) m)
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]
  map_smul' a m := by
    rw [LinearMap.map_smul, B.smap_smul, wittMap_frobeniusEquiv_symm]
    rfl

theorem Base.F_verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.F G trivial (B.verOp G m) = p • m := by
  change B.smap trivial trivial (absFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (absFrob (p_eq_zero p k) G) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app, frobInv_app_pow]
    rfl

theorem Base.verOp_F (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.verOp G (B.F G trivial m) = p • m := by
  change B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))
      (B.smap trivial trivial (absFrob (p_eq_zero p k) G) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial (absFrob (p_eq_zero p k) G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app]
    rw [map_pow, map_pow, frobInv_app_pow]
    rfl

end FrobInv

theorem exists_V_of_base : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)),
    ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial,
      (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        B.F G trivial (V G m) = p • m) ∧
      ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        V G (B.F G trivial m) = p • m :=
  fun _ _ B => ⟨fun G => B.verOp G, fun G m => B.F_verOp G m, fun G m => B.verOp_F G m⟩

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_sh_acyclic_twists : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  intro q _ A _ hA _ T _ _ hfin s i hs
  obtain ⟨hH, hsep⟩ := hA
  obtain ⟨ι, hι, F, hF, hAF, e, hHF, hF'⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A T
  exact acycF_of_pi_sh (ZMod q) (tw q i) ι F T ⟨e.toRingEquiv⟩
    (fun j => ⟨hHF j, (hF' j).1⟩) s hs

end GlobalTheory.EtC.GmStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealMulOfIdempotents
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finrank_quot_kerIdeal_mul_of_idem (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0)
    (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) =
      p ^ (n * G.height) := by
  have hdim : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    have h := G.rank_eq n q
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    simpa using h
  have hker := GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents p k G u v huv h1 h2 n
  have hord := finrank_eq_ker_mul_range k (G.A n) (G.A n) (u.app n)
  have hr : Module.finrank k (LinearMap.range ((u.app n : G.A n →ₐ[k] G.A n).toLinearMap)) =
      Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) := by
    rw [← hker]
    exact (((u.app n : G.A n →ₐ[k] G.A n).toLinearMap.quotKerEquivRange).symm.finrank_eq).trans rfl
  rw [← hdim, hord, hr]

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReducedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  first | (exact @GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (exact GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (intros; apply GlobalTheory.fractionRing_away_etale_isArtinian_isReduced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwoStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_invariance_of_rank_one_two : GlobalTheory.LeviCut.RankOne → GlobalTheory.LeviCut.RankTwo → GlobalTheory.LeviCut.GridInv := by
  first | exact @GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | exact GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | (intros; apply GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo <;> assumption)
end

