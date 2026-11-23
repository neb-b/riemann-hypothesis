module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFunEqMinIntLinearFormsOnCones
section
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.PolFan

theorem evalZ_eq_of_nsmul_eq_sum {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {φ : InvFun O} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ}
    (hk : 0 < k) {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) :
    φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem cones_eq_min_linear : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) →
    ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
      (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) →
      (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro O _ bar φ Y _ _ _ p m γ hγ
  have hs : ∀ i, IsStrict bar φ (γ i) := fun i => (hγ i).strict
  unfold IsStrict at hs
  choose N ℓ hN h1 h2 h3 using hs
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hb hp ⟨i, k, cf, hk, he⟩
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_nsmul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem posIndex_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature M p q) : posIndex M = p ∧ posIndex (-M) = q := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix _ _ ℂ).map (starRingEnd ℂ) with hA
  have hAc : A.map (starRingEnd ℂ) = (P : Matrix _ _ ℂ) := by
    ext i j; simp [hA]
  have hdet : A.det ≠ 0 := by
    have hu := Matrix.isUnits_det_units P
    have h2 := RingHom.map_det (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    rw [RingHom.mapMatrix_apply] at h2
    rw [hA, ← h2]
    exact (map_ne_zero _).2 hu.ne_zero
  have hc : A.transpose * M.reindex e e * A.map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    rw [hAc, ← hP]; rfl
  have hcn : A.transpose * (-M).reindex e e * A.map (starRingEnd ℂ) = -Formalism.UG.Jpq p q := by
    rw [← hc]
    have : (-M).reindex e e = -(M.reindex e e) := by ext; simp
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  have hJn : -Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1)) := by
    rw [hJ, Matrix.diagonal_neg]
    congr 1
    ext i; rcases i with i | i <;> simp
  have hre : ∀ N : Matrix n n ℂ, posIndex N = posIndex (N.reindex e e) := fun N =>
    (posIndex_submatrix_equiv N e.symm).symm
  constructor
  · rw [hre, ← posIndex_congr _ hdet, hc, hJ, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp
  · rw [hre, ← posIndex_congr _ hdet, hcn, hJn, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp

theorem hT_coords {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (u : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = ∑ b, ∑ a, star (u a) * S.gram a b * u b := by
  rw [Module.Basis.equivFun_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [starRingEnd_apply]
  ring

end GlobalTheory.IsoNegIdx

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem exists_isotropic_of_negIdx : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  intro D S k hS hk1 hk2 hn
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, star x = FD.cc x := fun _ => rfl

  have hsig : ∀ φ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S.gram.map φ) (S.rank - k) k := by
    intro φ
    obtain ⟨ρ, h | h⟩ := GlobalTheory.MassLink.tauE_or' D φ
    · subst h
      simpa [gramAt] using hS ρ
    · have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hS ρ)
      rw [Matrix.map_map] at h1
      have e : (⇑(starRingEnd ℂ) ∘ ⇑(tauE D ρ)) = ⇑φ := by
        funext x
        rw [Function.comp_apply, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [e] at h1

  set G : Matrix (Fin S.rank) (Fin S.rank) D.host.E := S.gram.transpose with hGdef
  have hG : ∀ a b, FD.cc (G a b) = G b a := fun a b => by
    simp only [hGdef, Matrix.transpose_apply, ← hst]
    exact S.herm.eq _ _
  have hform : ∀ u, S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = FD.herm G u u := fun u => by
    rw [hT_coords, FD.herm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [hGdef, Matrix.transpose_apply, hst]
    ring
  have hGφ : ∀ φ : D.host.E →+* ℂ, G.map φ = S.gram.map (ComplexEmbedding.conjugate φ) := fun φ => by
    ext a b
    simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq]
    rw [← hG b a, GlobalTheory.Published.embedding_cc]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  have key : ∀ u, FD.herm G (P.mulVec u) (P.mulVec u) = FD.herm (Matrix.diagonal d) u u := fun u => by
    rw [GlobalTheory.Published.LandherrSt.herm_mulVec, hPd]
  have hne : ∀ u, u ≠ 0 → S.frame.equivFun.symm (P.mulVec u) ≠ 0 := fun u hu h => by
    apply hu
    apply Matrix.eq_zero_of_mulVec_eq_zero hP
    have h3 := congrArg S.frame.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨_, hne (Pi.single i 1) (by simp), ?_⟩
    rw [hform, key, GlobalTheory.UTrans.herm_diagonal_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Pi.single_apply, hj]
  push_neg at hz

  have hs : ∀ φ : D.host.E →+* ℂ, (∃ i, 0 < (φ (d i)).re) ∧ ∃ j, (φ (d j)).re < 0 := by
    intro φ
    have hc : (P.map φ).transpose * G.map φ * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => φ (d i) := by
      have h1 : (P.map φ).map (starRingEnd ℂ) = (P.map FD.cc).map φ := by
        ext a b
        simp [GlobalTheory.Published.embedding_cc]
      rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd, Matrix.diagonal_map (map_zero φ)]
    have hdet : (P.map φ).det ≠ 0 := by
      have h2 := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h2
      rw [← h2]
      exact (map_ne_zero φ).2 hP
    obtain ⟨hp, hq⟩ := posIndex_of_hasSignature (hGφ φ ▸ hsig (ComplexEmbedding.conjugate φ))
    have hcn : (P.map φ).transpose * (-G.map φ) * (P.map φ).map (starRingEnd ℂ) =
        Matrix.diagonal fun i => -φ (d i) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hc, Matrix.diagonal_neg]
    rw [← posIndex_congr _ hdet, hc, posIndex_diagonal] at hp
    rw [← posIndex_congr _ hdet, hcn, posIndex_diagonal] at hq
    constructor
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hp]; omega)
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hq]; omega)
      refine ⟨i, ?_⟩
      have := (Finset.mem_filter.1 hi).2
      simp only [Complex.neg_re] at this
      linarith
  obtain ⟨z, hz0, hzz⟩ := GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hz hs
  exact ⟨_, hne z hz0, by rw [hform, key, hzz]⟩

end GlobalTheory.IsoNegIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.KeyLieChg

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem lieComb_of_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left)
    (hu'v' : ∀ i, (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left) (i : Fin m) :
    IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i) := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).1 (hu'v' i)

theorem constFn_one {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    Geo.Tor.constFn p U (1 : R) = 1 := by
  simp [Geo.Tor.constFn]

theorem exists_keyPB_det : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  intro κ hκ R _ y x f hxy v' hv' M hM
  obtain ⟨φ, he, w, hg, F, hp, hw, hrig, hsec, hF, hε, hlie⟩ := hxy
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  subst hF'
  haveI := y.P.isAb.comm
  haveI := x.P.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R ℂ f y.P.A x.P.A φ hp y.P.isAb.smooth y.P.g v' hv'
  have hb : IsLieBasis (fun i : Fin x.P.g => u (i.cast hg)) := isLieBasis_cast hg hu
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, fun i => u (i.cast hg), hb⟩,
    ⟨φ, he, w, hg, Chart.dualMapR f, hp, hw, hrig, hsec, hF, hε, fun i => huv (i.cast hg)⟩, ?_⟩
  have hc := lieComb_of_over f hp hg M y.v v' x.v (fun i => u (i.cast hg)) hM hlie (fun i => huv (i.cast hg))
  have k := hκ ℂ x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne (fun i => u (i.cast hg)) hb 1
    (fun i j => f (M (i.cast hg) (j.cast hg))) (fun i => by rw [constFn_one, _root_.one_mul]) hc
  have hd : (Matrix.of fun i j : Fin x.P.g => f (M (i.cast hg) (j.cast hg))).det = (M.map f).det :=
    Matrix.det_submatrix_equiv_self (finCongr hg) (M.map f)
  simp only [Nat.mul_one, one_pow, _root_.one_mul] at k
  rw [k]
  exact congrArg (· ^ 4 * (κ ℂ x : ℂ)) hd

end GlobalTheory.KeyLieChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_keyAtMap_of_isGrpPullback : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (y : KeyIn R)
    (P : PolAV (Sp K)) (φ : P.A.left ⟶ y.P.A.left) (hp : 1 ≤ P.g) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (hr : rig.IsGen), P.g = y.P.g → IsGrpPullback P.A y.P.A (spMap f) φ → LBIso P.L (y.P.L.pull φ) →
    ∃ th hth v hv, KeyAtMap ⟨P, hp, rig, hr, th, hth, v, hv⟩ y f φ := by
  intro R K _ _ f y P φ hp rig hr hg h hI
  obtain ⟨w, hw0⟩ := hI
  have hw := (isGen_iff w).1 hw0
  have he : eSec P.A ≫ φ = spMap f ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  have := P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale y.P.isLB P.isLB hw (p := P.A.hom) (Over.w η[P.A]) he hr y.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down g' y.P.isLB P.isLB y.th
  have := P.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R K f y.P.A P.A φ h y.P.isAb.smooth y.P.g y.v y.basis
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact hb'
  refine ⟨th', SectionBaseChange.fibre_nonzero_of_pull P.isLB hth' h.1 y.th_ne, _, hb hg, he, w', hg,
    Chart.dualMapR f, h, (isGen_iff _).2 g',
    (maps_iff w' _ (fun _ => eSec y.P.A) _ rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2 m',
    KeyPow.appLE_eq_of_stalk _ y.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_keyIn_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W]
    (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  intro W _ _ _ _ P hg
  have hL := GlobalTheory.abelianSchemeLaws_all
  let m : PrimeSpectrum W := IsLocalRing.closedPoint W
  obtain ⟨th, a, ha, -, hth⟩ := _root_.GlobalTheory.TwoPrimeSection.main hL.1 hL.2 W P m m
  have c : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨b, hb, -, v, hv⟩ := _root_.GlobalTheory.LieTwo.lie_free_near_two_primes W P.A P.g P.smoothDim m m
  have hbu : IsUnit b := (IsLocalRing.mem_maximalIdeal b).not.mp hb |> not_not.mp
  let g : Localization.Away b →+* W := IsLocalization.Away.lift (g := RingHom.id W) b hbu
  have hgf : g.comp (algebraMap W (Localization.Away b)) = RingHom.id W := by
    ext x; simp [g]
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap W (Localization.Away b)))
  have hA₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap W (Localization.Away b))) P.A P.isAb
  have c₁ := hA₁.comm
  have e : spMap g ≫ spMap (algebraMap W (Localization.Away b)) = 𝟙 (Sp W) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgf, CommRingCat.ofHom_id, Spec.map_id]
  have w₁ : 𝟙 P.A.left ≫ P.A.hom = (P.A.hom ≫ spMap g) ≫ spMap (algebraMap W (Localization.Away b)) := by
    rw [Category.assoc, e]; simp
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
  have hid : IsGrpPullback P.A P.A (𝟙 _) (𝟙 P.A.left) := isGrpPullback_of_iso (Iso.refl P.A)
  have h₂ : IsGrpPullback P.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (hid.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ W g _ P.A _ h₂ hA₁.smooth P.g v hv
  obtain ⟨rig, hr⟩ := P.rigid
  refine ⟨⟨P, hg, rig, hr, th, fun s => hth s fun h => ?_, v', hb'⟩, rfl⟩
  have hs : s.asIdeal ≤ IsLocalRing.maximalIdeal W := IsLocalRing.le_maximalIdeal s.isPrime.ne_top
  exact ha (hs h)

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyInNf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_keyIn_nf :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → c ≠ 0 → Mx.det ≠ 0 → ∃ (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
  intro g τ a b c Mx hg hs hp ha hb hc hM
  obtain ⟨x, h, u, τ', a', b', e₁, e₂, e₃, -, -, -, -, h₃, h₄, h₅, h₆⟩ :=
    GlobalTheory.KeyOfPeriod.exists_keyIn_classicalFrame g τ a b hg hs hp ha hb
  subst h
  obtain rfl : τ' = τ := e₁
  obtain rfl : a' = a := e₂
  obtain rfl : b' = b := e₃
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hbas⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (Mx i)).exists
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyNormalExists.constMul x.P.A.hom c x.th, fun s => ?_, v,
    (hbas Mx v x.basis hv).2 hM.isUnit⟩, rfl, u, hs, hp, ha, hb, hc, h₃, h₄,
    KeyNormalExists.isFn_constMul u c h₅, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ hc.isUnit _ hz'⟩
  · have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (Mx i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, Mx i j • (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin x.P.g → ℂ) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx i := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, MulZeroClass.mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [e] at h1
    exact h1

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelTangentOfPullbackTangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanPull

theorem one_left_congr {X Z : Scheme.{0}} {G : Over X} [GrpObj G] {f g : Z ⟶ X} (h : f = g) :
    (1 : Over.mk f ⟶ G).left = (1 : Over.mk g ⟶ G).left := by
  subst h; rfl

theorem isTanAtG_comp
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) : IsTanAtG Y.t x (w.left ≫ ψ.φ) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, ψ.cart.1.w, ← Category.assoc, Over.w w]
    rfl
  · rw [← Category.assoc, hw]
    refine (Formalism.L2.Pj.grpPull_one ψ.cart (ptOver V V)).symm.trans (one_left_congr ?_)
    show spMap (algebraMap V V) ≫ x = x
    have : spMap (algebraMap V V) = 𝟙 _ := by
      rw [Algebra.algebraMap_self]; exact Spec.map_id _
    rw [this, Category.id_comp]

theorem exists_tanM_of_isTan
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) :
    ∃ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (Formalism.L2.Pj.ovT (isTanAtG_comp x G ψ w hw)) (Formalism.L2.Pj.smT_zero_ovT _), rfl⟩

end GlobalTheory.TanPull
end
end

