module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0159
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankTangentPELFamilyLeSymmetricDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTan

theorem finrank_derivation_le : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  intro l1 l2 _ hu E _ _ _ H D g J _ a w w' bas _ _ _ _ _ N' o _ b ρ R _ _ _ _ _ t τ hρ hP _ hun
  obtain ⟨t₀, m, u, Hm, χ, κ, hG, ⟨hm, -⟩, hκ, hD⟩ := _root_.GlobalTheory.KS.tangent_injects_symm_antilinear l1 l2 hu o g (N' ^ 2) J b R t hun
  have hx : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨act, act₀, hc, hdet⟩ := GlobalTheory.FibreAct.exists_fibre_act E H D g (N' ^ 2) J a bas o b ρ _ _ t τ _
    (algebraMap o ℂ) t₀.A m hP hx hm
  obtain ⟨F, hF⟩ := (GlobalTheory.KS.exists_linear_lift_action t₀.pol u Hm χ hG).2 (𝓞 E) act₀
  have hle := GlobalTheory.T.finrank_symm_antilinear_comm_CM_le E H t₀.pol.g D.p D.q (algebraMap o ℂ ρ) Hm F (LinearMap.range κ)
    (by rw [← map_pow, hρ]; simp) hG.ah.1 hG.ah.2.1
    (fun σ => by
      split_ifs with h
      · exact _root_.GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).1 h)
      · exact _root_.GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).2 h))
    (by
      rintro _ ⟨d, rfl⟩
      exact ⟨(hD d).1, fun c => (hD d).2 (act.act c) (act₀.act c) (F c) (hc c) (hF c)⟩)
  rw [LinearMap.finrank_range_of_inj hκ] at hle
  exact hle

end GlobalTheory.PelTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbertStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.lbIso_linComb_lam_of_appellHumbert | exact GlobalTheory.lbIso_linComb_lam_of_appellHumbert | (intros; apply GlobalTheory.lbIso_linComb_lam_of_appellHumbert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyLevelQuot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelTower

theorem zeta_eq_pow {n m : ℕ} (hm : 0 < m) (h : n ∣ m) : zeta n = zeta m ^ (m / n) := by
  obtain ⟨c, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c hn, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact (baseKA l₂).ρ.2
  · rw [zeta_eq_pow l₂.A_pos h]
    exact pow_mem (baseKA l₂).ζ.2 _

theorem base_rho (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem base_zeta (l : Level H) : (((baseKA l).ζ : KA l) : ℂ) = zeta l.A := rfl

theorem exists_inclusion' {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    ∃ j : F →+* F', ∀ x, ((j x : F') : ℂ) = ((x : F) : ℂ) :=
  ⟨(IntermediateField.inclusion h).toRingHom, fun x => IntermediateField.coe_inclusion h x⟩

theorem exists_inclusion {l l₂ : Level H} (h : l.A ∣ l₂.A) :
    ∃ j : KA l →+* KA l₂, (∀ x, ((j x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ j (baseKA l).ρ = (baseKA l₂).ρ ∧
      j (baseKA l).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  obtain ⟨j, hj⟩ := exists_inclusion' (KA_le h)
  refine ⟨j, hj, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hj, base_rho, base_rho]
  · rw [hj, IntermediateField.coe_pow, base_zeta, base_zeta]
    exact zeta_eq_pow l₂.A_pos h

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_natCast H.d).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem finite_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : j.Finite := by
  letI := j.toAlgebra
  exact Module.Finite.of_restrictScalars_finite ℚ K K'

theorem etale_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : Etale (spMap j) := by
  letI := j.toAlgebra
  haveI : Module.Finite K K' := finite_of_numberField j
  haveI : Algebra.FormallyEtale K K' := Algebra.FormallyEtale.of_isSeparable K K'
  haveI : Algebra.FinitePresentation K K' := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K K' := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this

end GlobalTheory.LevelTower

namespace GlobalTheory

open LevelTower

theorem nonempty_levelQuot : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  intro hL hL2 hTh E _ _ _ H D l l₂ Xo₂ hpq hdvd
  have hA : l.A ∣ l₂.A := hdvd.2.2
  obtain ⟨jK, hj, hjρ, hjζ⟩ := exists_inclusion hA
  haveI := finiteDimensional_KA l₂
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ :=
    GlobalTheory.LevelGroup.exists_group_action hL hL2 E H D l l₂ Xo₂ jK hpq hdvd hj
  have hq : IsQProjOver (Xo₂.s ≫ spMap jK) :=
    (isQProjOver_baseChange_and_finite_restrict _ _ jK Xo₂.X (Xo₂.s ≫ spMap jK)).2 Xo₂.s
      (finite_of_numberField jK) Xo₂.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    exists_isGaloisCover_of_isQProjOver (KA l) Xo₂.X (Xo₂.s ≫ spMap jK) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := _root_.GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover (KA l) _ Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension D.dim (π ≫ sY) := by
    rw [hπ]
    haveI := Xo₂.smooth
    haveI : Etale (spMap jK) := etale_of_numberField jK
    haveI : SmoothOfRelativeDimension 0 (spMap jK) := inferInstance
    have := smoothOfRelativeDimension_comp D.dim 0 Xo₂.s (spMap jK)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension D.dim sY := _root_.GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover (KA l) _ Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨t', m, hνm, hp, ha, hk⟩ := _root_.GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover hL hL2 hTh E H (KA l) _ Y π sY Ga ρ Xo₂.univ.t _ ν hG hqY
    Xo₂.univ.proper (obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ _ _ _ Xo₂.univ).2.1
    Xo₂.univ.ample Xo₂.univ.ktriv hν1 hνmul
  obtain ⟨ob, m', hη, hηA⟩ := obj_descend_lower_level hL hL2 E H D l l₂ _ _ (baseKA l) (baseKA l₂) jK _ Y π sY
    Xo₂.s Ga ρ Xo₂.univ (fun a => (ν a).φ) t' m hdvd hjρ hjζ
    hπ hG hνm hlow hp ha hk
  refine ⟨⟨Y, sY, hqY, hsY, ob, π, jK, hj, hπ, hG.fin, hG.etale, hG.onto, m', hη, hηA, ?_⟩⟩
  intro K _ _ y y' t mu mu' eM eA h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans K y y' t mu mu' eM eA h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisedIsoCommutesFieldAutomorphismOfTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.SerreTwist

theorem iso_eq_of_torsion (hL : Laws) {C : Type} [Field C] [IsAlgClosed C] (Q Q' : PolAV (Sp C))
    (a b : Q.A ≅ Q'.A) (ha : η[Q.A] ≫ a.hom = η[Q'.A]) (hb : η[Q.A] ≫ b.hom = η[Q'.A])
    (la : LBIso Q.L (Q'.L.pull a.hom.left)) (lb : LBIso Q.L (Q'.L.pull b.hom.left))
    {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0)
    (h : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ a.hom = x ≫ b.hom) : a.hom = b.hom := by
  have hη : η[Q.A] ≫ (a ≪≫ b.symm).hom = η[Q.A] := by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ha, ← hb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hmon : IsMonHom (a ≪≫ b.symm).hom := hL.rigidity _ Q.A Q.A Q.isAb Q.isAb _ hη
  have hpb : LBIso (Q.L.pull (a ≪≫ b.symm).hom.left) (Q'.L.pull a.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso lb _
      (by rw [← Over.comp_left, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨w, hw⟩ : LBIso Q.L (Q.L.pull (a ≪≫ b.symm).hom.left) :=
    LBIso.trans Q.isLB (LB.isLB_pull Q'.isLB _) (LB.isLB_pull Q.isLB _) la (LBIso.symm hpb)
  have hfix : ∀ x : Over.mk (𝟙 (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a ≪≫ b.symm).hom = x := by
    intro x hx
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h x hx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key := GlobalTheory.MatchRigid.aut_eq_id hL Q (𝟙 (Sp C)) hk hkC (a ≪≫ b.symm) w hw hfix
  have := congrArg (· ≫ b.hom) key
  simpa using this

theorem exists_fibre (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (P : PolAV S) (t : S' ⟶ S) :
    ∃ (Q : PolAV S') (e : Q.A.left ≅ (Over.mk t ⊗ P.A).left),
      e.hom ≫ (fst (Over.mk t) P.A).left = Q.A.hom ∧
      LBIso Q.L (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left)) ∧
      ∃ F : (𝟙_ (Over S') ⟶ Q.A) →* (Over.mk t ⟶ P.A),
        ∀ x, x.left ≫ e.hom = (lift (𝟙 (Over.mk t)) (F x)).left := by
  obtain ⟨Q, g, hg, -, hmul, w, hw⟩ := hB S S' t P
  have hpb : IsPullback Q.A.hom g t P.A.hom := hg.flip
  let c : Over.mk t ⟶ Over.mk ((𝟙_ (Over S')).hom ≫ t) := Over.homMk (𝟙 S') (by simp)
  have hsnd : hpb.isoPullback.hom ≫ (snd (Over.mk t) P.A).left = g := by
    rw [Over.snd_left]; exact hpb.isoPullback_hom_snd
  refine ⟨Q, hpb.isoPullback, ?_, ?_,
    MonoidHom.mk' (fun x => c ≫ toBase hg.w x) (fun x y => by simp only [hmul, MonObj.comp_mul]), fun x => ?_⟩
  · rw [Over.fst_left]; exact hpb.isoPullback_hom_fst
  · rw [hsnd]; exact LBIso.symm ⟨w, hw⟩
  · apply pullback.hom_ext
    · simp [c]
    · have hs : hpb.isoPullback.hom ≫ pullback.snd (Over.mk t).hom P.A.hom = g := hpb.isoPullback_hom_snd
      rw [Category.assoc, hs, Over.lift_left]
      erw [pullback.lift_snd]
      simp [c, toBase]

theorem prod_iso_eq (hL : Laws) {S : Scheme.{0}} (P P' : PolAV S) {C : Type} [Field C] [IsAlgClosed C]
    (t : Sp C ⟶ S) {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0) (φ : Fin 2 → (Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A))
    (h1 : ∀ i, (φ i).hom ≫ fst _ _ = fst _ _)
    (h2 : ∀ i, lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ (φ i).hom ≫ snd _ _ = 1)
    (h3 : ∀ i, LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull ((φ i).hom ≫ snd (Over.mk t) P'.A).left))
    (h4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ (φ 0).hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ (φ 1).hom ≫ snd _ _) :
    (φ 0).hom = (φ 1).hom := by
  obtain ⟨Q, e, he1, he2, F, hF⟩ := exists_fibre hL.polBaseChange P t
  obtain ⟨Q', e', he1', he2', F', hF'⟩ := exists_fibre hL.polBaseChange P' t

  have hlift : ∀ i (z : Over.mk t ⟶ P.A), lift (𝟙 (Over.mk t)) z ≫ (φ i).hom =
      lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) z ≫ (φ i).hom ≫ snd _ _) := by
    intro i z
    apply CartesianMonoidalCategory.hom_ext
    · simp [h1 i]
    · simp
  have h1' : ∀ i, (φ i).hom.left ≫ (fst (Over.mk t) P'.A).left = (fst (Over.mk t) P.A).left := by
    intro i
    rw [← Over.comp_left, h1 i]

  let θ : Fin 2 → (Q.A.left ≅ Q'.A.left) := fun i => e ≪≫ (Over.forget S).mapIso (φ i) ≪≫ e'.symm
  have hθ : ∀ i, (θ i).hom = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hw : ∀ i, (θ i).hom ≫ Q'.A.hom = Q.A.hom := by
    intro i
    rw [hθ, ← he1', ← he1, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h1']
  let a : Fin 2 → (Q.A ≅ Q'.A) := fun i => Over.isoMk (θ i) (hw i)
  have ha_left : ∀ i, (a i).hom.left = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hcomp : ∀ i (x : 𝟙_ (Over (Sp C)) ⟶ Q.A), x.left ≫ (a i).hom.left =
      (lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) (F x) ≫ (φ i).hom ≫ snd _ _)).left ≫ e'.inv := by
    intro i x
    rw [ha_left, ← Category.assoc, hF, ← Category.assoc, ← Over.comp_left, hlift]

  have hone : ∀ (R : PolAV (Sp C)), (1 : 𝟙_ (Over (Sp C)) ⟶ R.A) = η[R.A] := by
    intro R
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have ha : ∀ i, η[Q.A] ≫ (a i).hom = η[Q'.A] := by
    intro i
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← hone Q, hcomp, map_one, h2 i, ← map_one F', ← hF', hone Q', Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

  have la : ∀ i, LBIso Q.L (Q'.L.pull (a i).hom.left) := by
    intro i
    have h3e : LBIso (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left))
        (P'.L.pull ((a i).hom.left ≫ e'.hom ≫ (snd (Over.mk t) P'.A).left)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp e.hom rfl
        (by rw [ha_left, Over.comp_left]; simp only [Category.assoc, Iso.inv_hom_id_assoc]) (h3 i)
    have hQ' := GlobalTheory.GenSpread.lbIso_pull_of_lbIso he2' (a i).hom.left rfl
    exact LBIso.trans Q.isLB (LB.isLB_pull P'.isLB _) (LB.isLB_pull Q'.isLB _)
      (LBIso.trans Q.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull P'.isLB _) he2 h3e) (LBIso.symm hQ')

  have htor : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a 0).hom = x ≫ (a 1).hom := by
    intro x hx
    have hFx : F x ^ k = 1 := by rw [← map_pow, hx, map_one]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, hcomp, hcomp, h4 (F x) hFx]
  have key := congrArg Over.Hom.left (iso_eq_of_torsion hL Q Q' (a 0) (a 1) (ha 0) (ha 1) (la 0) (la 1) hk hkC htor)
  rw [ha_left, ha_left] at key
  apply Over.OverMorphism.ext
  simpa using key

end GlobalTheory.SerreTwist

theorem GlobalTheory.SerreTwist.whisker_comp_eq : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  intro hL S P P' C inst1 inst2 t φ h1 h2 h3 k hk hkC s hs
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A := whiskerRightIso s P.A ≪≫ φ ≪≫ whiskerRightIso s.symm P'.A
  have hψ : ψ.hom = s.hom ▷ P.A ≫ φ.hom ≫ s.inv ▷ P'.A := rfl
  have hψs : ψ.hom ≫ snd _ _ = s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ := by
    rw [hψ]; simp

  have hsw : ∀ z : Over.mk t ⟶ P.A,
      lift (𝟙 (Over.mk t)) z ≫ s.hom ▷ P.A = s.hom ≫ lift (𝟙 (Over.mk t)) (s.inv ≫ z) := by
    intro z
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ψ1 : ψ.hom ≫ fst _ _ = fst _ _ := by
    rw [hψ]; simp [reassoc_of% h1]
  have ψ2 : lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ ψ.hom ≫ snd _ _ = 1 := by
    rw [hψs, ← Category.assoc, hsw, MonObj.comp_one, Category.assoc, h2, MonObj.comp_one]
  have ψ3 : LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (ψ.hom ≫ snd (Over.mk t) P'.A).left) := by
    rw [hψs]
    exact GlobalTheory.GenSpread.lbIso_pull_comp (s.hom ▷ P.A).left (by rw [← Over.comp_left, whiskerRight_snd])
      (by rw [Over.comp_left]) h3
  have ψ4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ ψ.hom ≫ snd _ _ := by
    intro x hx
    have hx' : (s.inv ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    conv_rhs => rw [hψs, ← Category.assoc, hsw, Category.assoc]
    rw [← hs _ hx', Iso.hom_inv_id_assoc]
  have key : φ.hom = ψ.hom :=
    GlobalTheory.SerreTwist.prod_iso_eq hL P P' t hk hkC ![φ, ψ] (Fin.forall_fin_two.2 ⟨h1, ψ1⟩)
      (Fin.forall_fin_two.2 ⟨h2, ψ2⟩) (Fin.forall_fin_two.2 ⟨h3, ψ3⟩) ψ4
  rw [← hψs, ← key]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_finite_cover_ample_frames : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  first | exact @GlobalTheory.RaisedAmple.amp_of_raises | exact GlobalTheory.RaisedAmple.amp_of_raises | (intros; apply GlobalTheory.RaisedAmple.amp_of_raises <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_level_one_descends : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  first | exact @GlobalTheory.RaisedDescends.descends_of_raises | exact GlobalTheory.RaisedDescends.descends_of_raises | (intros; apply GlobalTheory.RaisedDescends.descends_of_raises <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothAndGeomConnectedOfVeryDense
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem of_local_near_veryDense (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (P : Set (Ideal R))
    (hP : ∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p)
    (h : ∀ q ∈ P, ∃ f : R, f ∉ q ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))) : Q s := by
  let S : Set R := {f | ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, -, hmp, -⟩ := hP m 1 hm.isPrime ((Ideal.ne_top_iff_one m).1 hm.ne_top)
    obtain ⟨f, hf, hfS⟩ := h p hp
    exact hf (hmp (hle (Ideal.subset_span hfS)))
  have hS' : Ideal.span (Set.range (fun f : S => (f : R))) = ⊤ := by
    rw [Subtype.range_coe]; exact hS
  refine IsZariskiLocalAtTarget.of_openCover (P := Q)
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) (fun f : S => (f : R)) hS').openCover ?_
  intro i
  exact (show S from i).2 (Localization.Away ((show S from i) : R)) (algebraMap R _)
    (IsLocalization.Away.algebraMap_isUnit _)

theorem smooth_and_geomConnected_of_veryDense : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hproj hflat h
  have hsm : SmoothOfRelativeDimension g s := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) := HasRingHomProperty.instIsZariskiLocalAtTarget _
    refine of_local_near_veryDense (@SmoothOfRelativeDimension.{0} g) R Z s P hP ?_
    intro q hq
    obtain ⟨K, _, x, hx, h1, -⟩ := h q hq
    obtain ⟨f, hf, H⟩ := _root_.GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit R Z s g K x (projProper R Z s hproj) hflat h1
    exact ⟨f, by rw [← hx]; exact hf, H⟩
  refine ⟨hsm, ?_⟩
  have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  refine of_local_near_veryDense (@GeometricallyConnected.{0}) R Z s P hP ?_
  intro q hq
  obtain ⟨K, _, x, hx, -, h2⟩ := h q hq
  obtain ⟨f, hf, H⟩ := _root_.GlobalTheory.ConnOpen.geometricallyConnected_near R Z s K x hproj (SmoothOfRelativeDimension.smooth g s) h2
  exact ⟨f, by rw [← hx]; exact hf, H⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AbLaw.CubeAffine

theorem triv_theta_of_isProjBy :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → Triv (Theta A M) :=
  fun hL R _ A _ _ hA hp M hM => CubeProj.exists_gen_theta_of_isProjBy hL.globalFns R A hA hp M hM

end GlobalTheory.AbLaw.CubeAffine
end

