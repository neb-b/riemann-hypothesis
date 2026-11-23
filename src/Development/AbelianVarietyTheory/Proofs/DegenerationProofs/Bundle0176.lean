module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedFibreSplitOfArcDataFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitOverOfHasArcData
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_parAt : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a : u.PtC), ∃ g, u.ParAt S.N a g := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l a
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h1 : 2 ≤ ρ.n ^ ρ.k := le_trans ρ.n_prime.two_le
      (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    nlinarith
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  obtain ⟨k, hk, hint⟩ := _root_.GlobalTheory.ZH.exists_int_pow hL o Ω S ρ p y₀ u a
  obtain ⟨a₁, ⟨c, hc, hca⟩, hpow⟩ := _root_.GlobalTheory.IntDiv.exists_integral_root hL o Ω S ρ p y₀ u (a ^ k) k hk hint
  obtain ⟨g₁, hg₁⟩ := _root_.GlobalTheory.IntegralGt.exists_lev hL o Ω S ρ p y₀ u c hc
  have hpar := (_root_.GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt hL o Ω S ρ p y₀ u c g₁ a₁ hc hca hg₁).2
  have hNk : 1 ≤ S.N * k := Nat.mul_pos (by omega) hk
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.N * k) hNk
  haveI : IsMonHom u.U.gen.hom := u.U.gen_hom
  have hk' : (a₁ ≫ u.U.gen.hom) ^ k = (a ≫ u.U.gen.hom) ^ k := by
    rw [← MonObj.pow_comp, ← MonObj.pow_comp, hpow]
  have hx : ((a ≫ u.U.gen.hom) * (a₁ ≫ u.U.gen.hom)⁻¹) ^ (S.N * k) = 1 := by
    rw [mul_comm S.N k, pow_mul, mul_pow, inv_pow, hk', mul_inv_cancel, one_pow]
  obtain ⟨pk, hpk⟩ := hsurj _ hx
  obtain ⟨g, hg⟩ := (gt_add_iota_sub_exist hL o Ω S ρ p y₀ u).1 pk.g g₁
  refine ⟨g, _root_.GlobalTheory.ParameterRoot.parAt_of_parAt_mul hL o Ω S ρ p y₀ u l S.N k a g hN hk ?_⟩
  exact ParTranslate.parAt_translate hL o Ω S ρ p y₀ u (S.N * k) pk _ a₁ a g₁ g hNk
    ((hf pk _).2 hpk.symm) (by rw [inv_mul_cancel_right]) hg (hpar _ hNk)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem polAt_of_point {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem admissible_maximal_ideal_of_complete_dvr_char_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) :
    admitted V (IsLocalRing.maximalIdeal V) ∧ IsPrincipalIdealRing (V ⧸ IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  exact ⟨⟨⟨inferInstance, inferInstance, inferInstance, h₂⟩, h₂, h₃, inferInstance, inferInstance⟩, inferInstance⟩

theorem cdvr_powerSeries (K : Type) [Field K] [CharZero K] : CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

theorem powerSeries_dvr_admissible_X_ideal (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal O) O) :
    admitted (PowerSeries O) (Ideal.span {PowerSeries.X}) ∧
      IsPrincipalIdealRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) := by
  have hk : Ideal.span {(PowerSeries.X : PowerSeries O)} = RingHom.ker (PowerSeries.constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) ≃+* O :=
    (Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
  refine ⟨⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_,
    charZero_of_injective_ringHom (PowerSeries.C_injective (R := O)), hk ▸ RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv e.symm⟩, IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective⟩
  infer_instance

theorem hasArcData_trait (h₁ : Laws) (h₂ : Laws2) (h₃ : Laws3) (h₄ : Laws4) (h₅ : Laws5) (h₆ : Laws6) (hE : Ega)
    (hU : USt) (hP : PelSt) (hH : HomExtSt) {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    {b : c.V W₀ →+* O'} (a : ArcIn D l (c.V W₀).subtype O' b) (hp : PushInvertible Y.t.G Y.t.PP.L)
    (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X) (hχ : jK _ ≫ χ = y ≫ Y.j)
    (hT : TraitData Y a (RingHom.id _) y) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (φ : PowerSeries O' →+* V) (hφ : Function.Injective φ) (hX : ¬ IsUnit (φ PowerSeries.X))
    (hC : ∀ x, x ≠ 0 → IsUnit (φ (PowerSeries.C x))) :
    Y.HasArcData a (IsLocalRing.maximalIdeal V) (φ.comp (PowerSeries.C (R := O'))) (φ PowerSeries.X) (spMap φ ≫ χ) := by
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp φ) := (IsFractionRing.injective V _).comp hφ
  let gam : FractionRing (PowerSeries O') →+* FractionRing V := IsFractionRing.lift hinj
  have hg : ∀ r, gam (algebraMap _ _ r) = algebraMap V _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : spMap gam ≫ y ≫ Y.j = jK V ≫ spMap φ ≫ χ := by
    rw [← hχ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hg r
  obtain ⟨W, _, _, _, io, hW, hio, hfin, hA⟩ := (hT.2 V hV φ gam hg _ hsq).2 hX
  have hA' : Y.HasArcData a (IsLocalRing.maximalIdeal W) (io.comp (φ.comp (PowerSeries.C (R := O'))))
    (io (φ PowerSeries.X)) (spMap io ≫ spMap φ ≫ χ) := hA
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap φ ≫ χ) Y.t
  have hsq' : (spMap gam ≫ y) ≫ Y.j = jK V ≫ spMap φ ≫ χ := (Category.assoc _ _ _).trans hsq
  have hS := _root_.GlobalTheory.SplitAtTrait.splitOver_of_hasArcData h₁ h₂ h₃ h₄ h₅ h₆ E H D l Xo c W₀ Y O' b a V hV _ _ hC hX _ _ hsq' t m W hW io hio hfin hA'
  obtain ⟨hadm, hpid⟩ := admissible_maximal_ideal_of_complete_dvr_char_zero hV
  obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H V _ hadm hpid t (polAt_of_point Y m _ _ hsq') hS
    (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp V _ t m)
  have := hV.2.2
  have hloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  exact _root_.GlobalTheory.ArcDataDescent.hasArcData_descends h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a V _ _ _ hadm.1
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top (hφ.comp PowerSeries.C_injective) _ _ hsq' t m P hPt W hW io hio
    (IsLocalRing.map_maximalIdeal_le io) (fun h => hX (isUnit_of_map_unit io _ h)) (fun x hx => (hC x hx).map io) hA'

theorem hasArcData_of_traitData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb hp y χ hχ hT
  rcases hb with ⟨hf, -⟩ | ⟨hd, hϖ, hc⟩
  · letI := hf.toField
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT (cdvr_powerSeries O') (RingHom.id _)
      Function.injective_id PowerSeries.X_prime.not_unit (fun x hx => (IsUnit.mk0 x hx).map (PowerSeries.C (R := O')))
    have e : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp, PowerSeries.maximalIdeal_eq_span_X] at h
    exact h
  · have hi := IsFractionRing.injective O' (FractionRing O')
    have hX : ¬ IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) PowerSeries.X) := by
      rw [PowerSeries.map_X]
      exact PowerSeries.X_prime.not_unit
    have hC : ∀ x, x ≠ 0 → IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) (PowerSeries.C x)) := fun x hx => by
      rw [PowerSeries.map_C]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 hx)).map _
    have hV := cdvr_powerSeries (FractionRing O')
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT hV _
      (PowerSeries.map_injective _ hi) hX hC
    obtain ⟨t, ⟨m⟩⟩ := exists_sab χ Y.t
    have hS := GlobalTheory.splitOver_of_hasArcData h₁ h₂ h₃ hH E H D l Xo c W₀ Y O' b a hd χ t m (by
      have e : (PowerSeries.map (algebraMap O' (FractionRing O'))).comp (PowerSeries.C (R := O')) =
          (PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _) := RingHom.ext fun x => PowerSeries.map_C (algebraMap O' (FractionRing O')) x
      rw [e, PowerSeries.map_X] at h
      exact h)
    obtain ⟨hadm, hpid⟩ := powerSeries_dvr_admissible_X_ideal O' (hϖ.maximalIdeal_eq ▸ hc)
    obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H _ _ hadm hpid t (polAt_of_point Y m _ _ hχ.symm) hS
      (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp _ _ t m)
    have := hadm.2.2.1
    refine _root_.GlobalTheory.ArcDataDescent.hasArcData_descends h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a _ _ _ _ hadm.1 hadm.2.2.2.1.ne_top
      PowerSeries.C_injective _ _ hχ.symm t m P hPt _ hV _ (PowerSeries.map_injective _ hi) ?_ hX hC h
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hX

end GlobalTheory.ArcData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogeny
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.Isog

open IsLocalRing

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := GlobalTheory.ModelDescent.spMap_comp_eq rfl

theorem isModel_pullback {K W L W' L' : Type} [Field K] [CommRing W] [Field L] [CommRing W'] [Field L']
    [Algebra K L] [Algebra W L] [Algebra K L'] [Algebra W' L'] (c : W →+* W') (b : L →+* L')
    (e : (algebraMap W' L').comp c = b.comp (algebraMap W L)) (e' : b.comp (algebraMap K L) = algebraMap K L')
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (h : IsModel (L := L) A G) :
    IsModel (L := L') A ((Over.pullback (spMap c)).obj G) := by
  obtain ⟨e₀, he₀⟩ := h
  have hW : spMap (algebraMap W' L') ≫ spMap c = spMap b ≫ spMap (algebraMap W L) := by
    rw [spMap_comp, spMap_comp, e]
  have hK : spMap (algebraMap K L') = spMap b ≫ spMap (algebraMap K L) := by
    rw [spMap_comp, e']
  have key : ∀ (φ : Sp L' ⟶ Sp W) (ψ : Sp L' ⟶ Sp K), φ = spMap b ≫ spMap (algebraMap W L) →
      ψ = spMap b ≫ spMap (algebraMap K L) →
      ∃ f : (Over.pullback φ).obj G ≅ (Over.pullback ψ).obj A, IsMonHom f.hom := by
    rintro φ ψ rfl rfl
    refine ⟨pullCompIso _ _ G ≪≫ (Over.pullback (spMap b)).mapIso e₀ ≪≫ (pullCompIso _ _ A).symm, ?_⟩
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  obtain ⟨f, hf⟩ := key _ _ hW hK
  show ∃ e : _ ≅ _, IsMonHom e.hom
  refine ⟨(pullCompIso _ _ G).symm ≪≫ f, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

theorem pullback_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  simpa using map_pow ((Over.pullback f).homMonoidHom) (𝟙 B) m

theorem exists_model_of_isogeny (K R K' : Type) [Field K] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K']
    [Algebra R K'] [Algebra K K'] (hSH : SH R K') (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ)
    (hA : IsAbelianScheme A) (hP : GlobalTheory.AbLaw.IsProjBy A.hom) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] [IsMonHom r] (hm : 1 ≤ m)
    (hri : r ≫ i = 𝟙 _ ^ m) (G' : Over (Sp R)) [GrpObj G'] (hG' : IsSemiAbelian G') (hmod : IsModel (L := K') B G') :
    ∃ (G : Over (Sp R)) (_ : GrpObj G), SmConn G ∧ IsModel (L := K') A G ∧
      Nonempty (TorusExtension (spFibre G)) := by
  obtain ⟨e, he⟩ := hmod
  haveI := he
  have hbc : ∀ (X : Over (Sp K)), SmoothOfRelativeDimension g X.hom →
      SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj X).hom := fun X hX =>
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap K K'))) hX
  have hA' : IsAbelianScheme ((Over.pullback (spMap (algebraMap K K'))).obj A) := by
    obtain ⟨h1, h2, h3, h4⟩ := hA
    exact ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd A.hom (spMap (algebraMap K K')))),
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) h3,
      inferInstanceAs (GeometricallyConnected (pullback.snd A.hom (spMap (algebraMap K K'))))⟩
  have hP' : GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K K'))).obj A).hom :=
    GlobalTheory.AbLaw.isProjBy_baseChange K K' (algebraMap K K') A.left _ A.hom _ _
      (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) hP
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj A).hom := hbc A hgA
  haveI hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj B).hom := hbc B hgB
  have hgG : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K'))).obj G').hom := by
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    have h : SmoothOfRelativeDimension (0 + g) (e.hom.left ≫ ((Over.pullback (spMap (algebraMap K K'))).obj B).hom) := inferInstance
    rw [zero_add, Over.w e.hom] at h
    exact h
  have hri' : (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) ≫ ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) = 𝟙 _ ^ m := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hri, pullback_map_id_pow, MonObj.pow_comp, MonObj.comp_pow]
    simp
  obtain ⟨G, _, e₂, hsc, he₂, ht⟩ := _root_.GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny R K' hSH ((Over.pullback (spMap (algebraMap K K'))).obj A) G' g m hA' hP' hG' hgA' hgG
    ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) inferInstance inferInstance hm hri'
  exact ⟨G, inferInstance, hsc, show ∃ _, _ from ⟨e₂, he₂⟩, ht⟩

end GlobalTheory.SS.Isog

namespace GlobalTheory.SS


open Isog IsLocalRing in
theorem potModel_semiAbelian_of_isogeny : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ A B _ _ g m hA hP hgA hgB i r hi hr hm hri hB
  haveI := hi
  haveI := hr
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hfin, hloc, hcomp, G, _, hmod, hG⟩ := hB
  have hG' : IsSemiAbelian G := hG
  haveI : IsAdicComplete (maximalIdeal W) W := hcomp
  haveI : CharZero L := (RingHom.charZero_iff (algebraMap K L).injective).1 inferInstance
  haveI : CharZero W := (RingHom.charZero_iff (IsFractionRing.injective W L)).2 inferInstance
  haveI : CharZero V := (RingHom.charZero_iff (IsFractionRing.injective V K)).2 inferInstance
  obtain ⟨R, _, _, _, _, hinj, hint, hac⟩ := GlobalTheory.T.exists_integral_ext_isAlgClosed_residueField' W
  obtain ⟨-, hhen, -⟩ := _root_.GlobalTheory.henselian_and_union_of_isIntegral_complete W R hinj hint
  have hWK : Function.Injective ((algebraMap R (FractionRing R)).comp (algebraMap W R)) :=
    (IsFractionRing.injective R (FractionRing R)).comp hinj
  obtain ⟨b, hbW⟩ : ∃ b : L →+* FractionRing R,
      (algebraMap R (FractionRing R)).comp (algebraMap W R) = b.comp (algebraMap W L) :=
    ⟨IsFractionRing.lift hWK, RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := L) hWK x).symm⟩
  letI : Algebra K (FractionRing R) := (b.comp (algebraMap K L)).toAlgebra
  have hSH : SH R (FractionRing R) := by
    show _ ∧ _ ∧ _ ∧ _
    exact ⟨inferInstance, hhen, hac, inferInstance⟩
  have hmodR : IsModel (L := FractionRing R) B ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    isModel_pullback (algebraMap W R) b hbW rfl B G hmod
  have hsemiR : IsSemiAbelian ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (spMap (algebraMap W R)) G hG'
  obtain ⟨GR, _, hsc, hmodA, ht⟩ := exists_model_of_isogeny K R (FractionRing R) hSH A B g m hA hP hgA hgB
    i r hm hri _ hsemiR hmodR
  letI : Algebra V R := ((algebraMap W R).comp (algebraMap V W)).toAlgebra
  have hVR : (algebraMap R (FractionRing R)).comp (algebraMap V R) =
      (algebraMap K (FractionRing R)).comp (algebraMap V K) := by
    change (algebraMap R (FractionRing R)).comp ((algebraMap W R).comp (algebraMap V W)) =
      (b.comp (algebraMap K L)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, hbW, RingHom.comp_assoc, hc, RingHom.comp_assoc]
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R (FractionRing R) hVR A hA GR hsc hmodA
  have hVW : Function.Injective (algebraMap V W) := by
    have h2 : Function.Injective ((algebraMap K L).comp (algebraMap V K)) :=
      (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    rw [← hc, RingHom.coe_comp] at h2
    exact h2.of_comp
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have hVRi : (algebraMap V R).IsIntegral :=
    RingHom.IsIntegral.trans (f := algebraMap V W) (g := algebraMap W R)
      (fun x => Algebra.IsIntegral.isIntegral (R := V) x) (fun x => hint.isIntegral x)
  have hVRinj : Function.Injective (algebraMap V R) := hinj.comp hVW
  obtain ⟨hlocVR, -, hdescV⟩ := _root_.GlobalTheory.henselian_and_union_of_isIntegral_complete V R hVRinj ⟨fun x => hVRi x⟩
  obtain ⟨W', _, hsW, hcW, hfW, hlW⟩ := hdescV s
  obtain ⟨GW, _, _, ε, hscW, hε, hcompW, hmodW⟩ := hs W' inferInstance hsW hlW
  haveI := hε
  have hlVW : IsLocalHom (algebraMap V W') := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (W'.val.toRingHom (algebraMap V W' x)) := hx.map _
    exact IsLocalHom.map_nonunit (f := algebraMap V R) x h1
  let ρ : W' →+* ResidueField R := (residue R).comp W'.val.toRingHom
  have hker : RingHom.ker ρ = maximalIdeal W' := by
    rw [← RingHom.comap_ker, ker_residue, maximalIdeal_comap]
  have hρi : ρ.IsIntegral :=
    RingHom.IsIntegral.trans (f := W'.val.toRingHom) (g := residue R)
      (RingHom.IsIntegral.tower_top (f := algebraMap V W') (g := W'.val.toRingHom) hVRi)
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  have htor : Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj GW)) := by
    obtain ⟨T⟩ := ht
    have hρ : spMap ρ = spMap (residue R) ≫ spMap W'.val.toRingHom := (Isog.spMap_comp _ _).symm
    rw [hρ]
    let Z := pullCompIso (spMap (residue R)) (spMap W'.val.toRingHom) GW ≪≫ (Over.pullback _).mapIso ε
    haveI : IsMonHom Z.symm.hom := by
      dsimp only [Z, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv]
      infer_instance
    exact ⟨torusExtOfIso Z.symm T⟩
  have hprop : IsProper ((Over.pullback (spMap (algebraMap W' (FractionRing W')))).obj GW).hom := by
    obtain ⟨e, -⟩ := hmodW
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper ((Over.pullback (spMap (algebraMap K (FractionRing W')))).obj A).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K (FractionRing W')))) (inferInstanceAs (IsProper A.hom))
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    rw [← Over.w e.hom]
    infer_instance
  have hsemiW : IsSemiAbelian GW :=
    isSemiAbelian_of_proper_generic_of_torusExtension W' (FractionRing W') GW hscW hprop
      (ResidueField R) ρ hker hρi htor
  unfold PotModel
  exact ⟨W', FractionRing W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcompW, hfW, hlVW, hcW, GW, inferInstance, hmodW, hsemiW⟩

end GlobalTheory.SS
end

