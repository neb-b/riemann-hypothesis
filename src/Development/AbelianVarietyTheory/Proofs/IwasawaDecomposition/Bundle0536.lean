module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.LieRel
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHolds
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.LocM.RootsPrescribe

theorem exists_smul_of_mem_of_coprime {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L] {I J : Ideal R} {r : R}
    (hc : I ⊔ J = ⊤) (hp : I * J = Ideal.span {r}) {x : L} (hI : x ∈ I • (⊤ : Submodule R L))
    (hJ : x ∈ J • (⊤ : Submodule R L)) : ∃ b, x = r • b := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : R) ∈ I ⊔ J from hc ▸ Submodule.mem_top)
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_smul]; exact Submodule.smul_mem_smul hu hJ
  have h2 : v • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_comm, mul_smul]; exact Submodule.smul_mem_smul hv hI
  have h3 : x ∈ (I * J) • (⊤ : Submodule R L) := by
    have := Submodule.add_mem _ h1 h2
    rwa [← add_smul, huv, one_smul] at this
  rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨b, -, hb⟩ := h3
  exact ⟨b, hb.symm⟩

theorem exists_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) (hpq : 1 ≤ Dw.p + Dw.q) {m : ℕ} (hm : 0 < m) {w : kˣ}
    (hw : IsPrimitiveRoot w (l.A * m)) (hA : w ^ m = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, I'.ζ (l.A * m) = w ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  have hN : 0 < l.A * m := Nat.mul_pos l.A_pos hm
  have hM : 0 < l.M := by have := l.three_le; omega
  have : NeZero (l.A * m) := ⟨hN.ne'⟩
  have hζ : IsPrimitiveRoot ((I.ζ (l.A * m) : kˣ) : k) (l.A * m) := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim _ hN)
  obtain ⟨i, -, hi, hiz⟩ := (hζ.isPrimitiveRoot_iff).1 (IsPrimitiveRoot.coe_units_iff.2 hw)
  have hiz' : I.ζ (l.A * m) ^ i = w := Units.ext (by rw [Units.val_pow_eq_pow_val, hiz])
  have hi1 : (l.A : ℤ) ∣ (i : ℤ) - 1 := by
    rw [← (I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, zpow_one, zpow_natCast, mul_inv_eq_one]
    conv_lhs => rw [← I.ζ_pow l.A m l.A_pos hm, ← pow_mul, mul_comm m, pow_mul, hiz', hA]
  obtain ⟨g, hg, -, hgM, hgA⟩ := GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift E H Dw
    l (l.A * m) i hN (Nat.isCoprime_iff_coprime.2 hi) hi1
  refine ⟨GlobalTheory.LevelTwist.twist I g ((GlobalTheory.SimAlg.sim_group E H Dw hpq).1 g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.LevelTwist.twist_ζ, GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, hiz']
  · exact GlobalTheory.LevelTwist.ev_congr I l.A_pos (hgA a)
  · refine GlobalTheory.LevelTwist.ev_congr I hM ?_
    obtain ⟨b, hb⟩ := exists_smul_of_mem_of_coprime l.coprime l.prod (hgM a)
      (Submodule.sub_mem _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) ha)
    exact ⟨b, hb.trans (Nat.cast_smul_eq_nsmul _ _ _)⟩

theorem roots : GlobalTheory.LocM.Cht.RootsSt := by
  intro E _ _ _ H Dw l k _ Q _ act e I z hpq hz hzp hA
  have hM : 0 < l.M := by have := l.three_le; omega
  have key := fun j : ℕ => exists_one l I hpq j.factorial_pos (hz _ (Nat.mul_pos l.A_pos j.factorial_pos))
    ((hzp _ _ l.A_pos j.factorial_pos).trans hA)
  choose J hJ hJA hJM using key
  obtain ⟨I', hI'⟩ := GlobalTheory.Ex.TateLimit.exists_limit E H Dw k Q act e J
  refine ⟨I', fun n hn => ?_, fun a => ?_, fun a ha => ?_⟩
  · obtain ⟨j, hj, -, h⟩ := hI' n hn n
    obtain ⟨t, ht⟩ : n ∣ l.A * j.factorial := (Nat.dvd_factorial hn hj).mul_left _
    have ht0 : 0 < t := Nat.pos_of_mul_pos_left (ht ▸ Nat.mul_pos l.A_pos j.factorial_pos : 0 < n * t)
    rw [h, ← (J j).ζ_pow n t hn ht0, ← hzp n t hn ht0, ← ht, hJ]
  · obtain ⟨j, -, h, -⟩ := hI' l.A l.A_pos 0
    rw [h, hJA]
  · obtain ⟨j, -, h, -⟩ := hI' l.M hM 0
    rw [h, hJM j a ha]

end GlobalTheory.LocM.RootsPrescribe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : P.D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ P.D χ).choose

theorem isQ_qv : QForm.IsQ P.D.toPre ϖ (qv P hϖ) := fun χ => (QForm.exists_QVal hϖ P.D χ).choose_spec

def beF : LinearMap.BilinForm ℤ P.D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D (isQ_qv P hϖ) a b)
    (fun a a' b => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : P.D.toPre.X) : beF P hϖ a b = beF P hϖ b a := QForm.bOf_comm P.D a b

theorem beF_self (a : P.D.toPre.X) : beF P hϖ a a = 2 * qv P hϖ a :=
  (QForm.two_Q_eq hϖ P.D (isQ_qv P hϖ) a).symm

theorem beF_adj (x : 𝓞 E) (a b : P.D.toPre.X) : beF P hϖ (x • a) b = beF P hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ P.D GlobalTheory.abelianSchemeLaws_all.1 P.oD (isQ_qv P hϖ) x a b

theorem beF_w0 (a : P.D.toPre.X) : beF P hϖ a (H.w0 • a) = qv P hϖ a := by
  have h₁ := beF_adj P hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm P hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self P hϖ a
  omega

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

def tF (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b))

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist P.D.toPre H.w0 (tF P hϖ)

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)



end ThetaShiftProofs

end GlobalTheory.ArcBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ValCoord

open GlobalTheory.ShFam.Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ρ : A →+* B) {x' : Sp B ⟶ Z.X} (hx : spMap ρ ≫ x = x') :
    ∃ g : EigFrame Z (ρ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ρ) ≫ fr.v τ i := by
  subst hx
  exact GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A B φ x fr ρ

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) = spMap (dualMap (χ.comp ρ)) := by
  rw [sp_comp]
  congr 1
  ext z <;> simp [dualMap]

theorem tri_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    {fr : EigFrame Z φ x} {ρ : A →+* B} {x₀ : Sp B ⟶ Z.X} (hx₀ : spMap ρ ≫ x = x₀) {g₀ : EigFrame Z (ρ.comp φ) x₀}
    (hg : ∀ τ i, g₀.v τ i = spMap (dualMap ρ) ≫ fr.v τ i) {χ : B →+* C} {φ' : c.F →+* C} {x' : Sp C ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Cˣ} (h : fr.Tri (χ.comp ρ) g t) : g₀.Tri χ g t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, ← hx₀, ← Category.assoc, sp_comp]
  · rw [h2]; rfl
  · obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun k => spMap (dualMap χ) ≫ g₀.v τ k) = fun k => spMap (dualMap (χ.comp ρ)) ≫ fr.v τ k :=
      funext fun k => by rw [hg, ← Category.assoc, spMap_dualMap_comp]
    rw [e]
    exact c3

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

end GlobalTheory.ShFam.ValCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcExt

theorem exists_ramified_ext (T : CDVR) {Ω : Type} [Field Ω] [Algebra T.Fr Ω] [Algebra.IsAlgebraic T.Fr Ω] [IsAlgClosed Ω]
    (M : IntermediateField T.Fr Ω) [FiniteDimensional T.Fr M] (N : ℕ) (hN : 0 < N) (ϖ₀ : T.V) (h₀ : Irreducible ϖ₀) :
    ∃ (T' : CDVR) (g : T.V →+* T'.V) (κ : M →+* T'.Fr) (e : ℕ) (ϖ : T'.V),
      Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧
      (∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap T'.V T'.Fr (g v)) ∧
      N ∣ e ∧ Associated (g ϖ₀) (ϖ ^ e) := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap T.Fr Ω (algebraMap T.V T.Fr ϖ₀)) hN
  let A := IntermediateField.adjoin T.Fr ({α} : Set Ω)
  have : FiniteDimensional T.Fr A := IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let L : IntermediateField T.Fr Ω := M ⊔ A
  have : FiniteDimensional T.Fr L := inferInstance
  obtain ⟨W, _, _, _, _, _, _, _, hc, -, hinj, hloc, -, -⟩ := GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  have : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := fun w =>
    (FractionRing.algEquiv W L).symm.commutes w
  let κ : M →+* FractionRing W := ψ.toRingHom.comp (IntermediateField.inclusion (le_sup_left : M ≤ L)).toRingHom
  have hκ : ∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap W (FractionRing W) (algebraMap T.V W v) := by
    intro v
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr v) = algebraMap W L (algebraMap T.V W v) :=
      (RingHom.congr_fun hc v).symm
    rw [← hψ, ← h1]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg0 : algebraMap T.V W ϖ₀ ≠ 0 := fun h => h₀.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  have hαL : α ∈ L := (le_sup_right : A ≤ L) (IntermediateField.mem_adjoin_simple_self T.Fr α)
  let b : FractionRing W := ψ ⟨α, hαL⟩
  have hb : b ^ N = algebraMap W (FractionRing W) (algebraMap T.V W ϖ₀) := by
    have h1 : (⟨α, hαL⟩ : L) ^ N = algebraMap W L (algebraMap T.V W ϖ₀) := by
      apply Subtype.ext
      have h2 := RingHom.congr_fun hc ϖ₀
      refine hα.trans ?_
      exact (congrArg (L.val) h2.symm)
    rw [← hψ, ← h1, map_pow]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hN.ne'] at hb
    exact hg0 ((IsFractionRing.injective W (FractionRing W)) (by rw [← hb, map_zero]))
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := W) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hxy, map_zero, zero_div])
  obtain ⟨m, v₁, hv₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, v₂, hv₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hW : x ^ N = algebraMap T.V W ϖ₀ * y ^ N := by
    apply IsFractionRing.injective W (FractionRing W)
    have hy' : algebraMap W (FractionRing W) y ≠ 0 := by
      simpa using hy0
    rw [map_pow, map_mul, map_pow, ← hb, ← hxy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hy')]
  have he : m * N = e + n * N := by
    rw [hv₁, hv₂, hu, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hW
    have : ((v₁ ^ N : Wˣ) : W) * ϖ ^ (m * N) = ((u * v₂ ^ N : Wˣ) : W) * ϖ ^ (e + n * N) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hW, pow_add]
      ring
    exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ this
  refine ⟨T', algebraMap T.V W, κ, e, ϖ, hinj, hloc, hϖ, hκ, ?_, ?_⟩
  · have : N ∣ e + n * N := ⟨m, by rw [← he, mul_comm]⟩
    exact (Nat.dvd_add_left (Dvd.intro_left n rfl)).1 this
  · exact ⟨u⁻¹, by
      show algebraMap T.V W ϖ₀ * ((u⁻¹ : Wˣ) : W) = ϖ ^ e
      rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩

section Level

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Level

section Level2

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


end Level2
section Main

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull


end Main

end GlobalTheory.ArcExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open ReciprocityTheory.ChartRestriction.G.PullbackSections (IsEigV)

namespace GlobalTheory.FlagEmb.EigSpread

section Alg

theorem existsUnique_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (v : ι → M) :
    (∀ w, ∃! a : ι → R, ∑ j, a j • v j = w) ↔ LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  exact (Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] (χ : ι → O →+* K)

def Splits : Prop :=
  ∀ (S M : Type) [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M] (ρ : O →+* Module.End S M),
    (∀ m, ∃ mm : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) ∧ ∑ τ, mm τ = m) ∧
    ∀ mm mm' : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) → (∀ τ, IsEigV ρ (χ τ) (mm' τ)) → ∑ τ, mm τ = ∑ τ, mm' τ → mm = mm'

variable {χ} {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}

omit [Fintype ι] in
theorem eig_single [DecidableEq ι] {τ : ι} {w : M} (hw : IsEigV ρ (χ τ) w) (τ' : ι) :
    IsEigV ρ (χ τ') (Pi.single (M := fun _ => M) τ w τ') := by
  by_cases h : τ' = τ
  · subst h; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]; intro a; simp

theorem eig_comb {κ : Type} [Fintype κ] {ψ : O →+* K} {u : κ → M} (hu : ∀ i, IsEigV ρ ψ (u i)) (a : κ → R) :
    IsEigV ρ ψ (∑ i, a i • u i) := fun o => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu, smul_comm]

theorem block_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ w, ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w) (τ : ι) (w : M) (hw : IsEigV ρ (χ τ) w) :
    ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w := by
  classical
  obtain ⟨a, ha, -⟩ := hb w
  have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) (Pi.single τ w)
    (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) (eig_single hw)
    (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← ha, Fintype.sum_sigma])
  have e' := congrFun e τ
  rw [Pi.single_eq_same] at e'
  refine ⟨_, e', fun b hb' => ?_⟩
  have li : LinearIndependent R fun i => u ⟨τ, i⟩ :=
    ((existsUnique_iff u).1 hb).1.comp (Sigma.mk τ) sigma_mk_injective
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 li (hb'.trans e'.symm)

theorem global_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ τ w, IsEigV ρ (χ τ) w → ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w) (w : M) :
    ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w := by
  obtain ⟨mm, h1, h2⟩ := (hs R M ρ).1 w
  choose c hc hc' using fun τ => hb τ _ (h1 τ)
  refine ⟨fun z => c z.1 z.2, ?_, fun a ha => ?_⟩
  · show ∑ z : Σ τ, Fin (m τ), c z.1 z.2 • u z = w
    rw [Fintype.sum_sigma, ← h2]
    exact Finset.sum_congr rfl fun τ _ => hc τ
  · have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) mm
      (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) h1 (by rw [h2, ← ha, Fintype.sum_sigma])
    funext z
    exact congrFun (hc' z.1 (fun i => a ⟨z.1, i⟩) (congrFun e z.1)) z.2

variable {S N : Type} [CommRing S] [Algebra K S] [AddCommGroup N] [Module S N] {ρ' : O →+* Module.End S N}
  {φ : R →+* S} (f : M →ₛₗ[φ] N)


end Alg

section Lift

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] {χ : ι → O →+* K}
  {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}
  {k N : Type} [Field k] [Algebra K k] [AddCommGroup N] [Module k N] {ρ' : O →+* Module.End k N}
  {φ : R →+* k} (f : M →ₛₗ[φ] N)

end Lift

section Geo

open GlobalTheory.FrameTangent MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {x' : Sp S ⟶ X}

theorem splits {l : Level H} (c : Coeff l) : Splits (embK c) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c)
    (fun τ a => embK_coe c τ a)
  intro S M _ _ _ _ ρ
  refine ⟨fun m => ⟨fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ m, fun τ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m), ?_⟩,
    fun mm mm' h h' e => funext fun τ => ?_⟩
  · rw [← LinearMap.sum_apply, ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj ρ _ α hinj]
    rfl
  · rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm h, e, ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm' h']

def lf (m : TanM x t.G) : Tn t R := (tv m).left

theorem lf_inj {m m' : TanM x t.G} (h : lf m = lf m') : m = m' := tv_injective (Over.OverMorphism.ext h)

theorem exists_lf {w : Tn t R} (hw : IsTanAtG t x w) : ∃ m : TanM x t.G, lf m = w :=
  ⟨mkT (FrameTangent.ovT (t := t) hw) (FrameTangent.smT_zero_ovT hw), rfl⟩

theorem comb_lf {n : ℕ} (v : Fin n → TanM x t.G) (a : Fin n → R) (w : TanM x t.G) :
    IsCombAtG t x (fun j => lf (v j)) a (lf w) ↔ ∑ j, a j • v j = w := by
  refine (FrameTangent.isCombAtG_iff t x (fun j => tv (v j)) a (lf w)).trans ⟨fun h => lf_inj ?_, fun h => ?_⟩
  · rw [lf, tv_comb]
    exact h
  · rw [← h, lf, tv_comb]
    rfl


variable {Dw : Datum H} {l : Level H} {c : Coeff l}

end Geo

end GlobalTheory.FlagEmb.EigSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_varieties_components_smooth_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed (Xo := Xo) (c := c) → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  first | exact @GlobalTheory.GenFibreComp.exists_vars | exact GlobalTheory.GenFibreComp.exists_vars | (intros; apply GlobalTheory.GenFibreComp.exists_vars <;> assumption)
end

