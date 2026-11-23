module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.EighthPowerFactor

open CechPic

theorem relAmple_diag_lam {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hN : ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hι : (M.pull ((𝟙 B)⁻¹ : B ⟶ B).left).IsLB := pull_isLB hM _
  have hD1 : (LB.div ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) M).IsLB := LB.isLB_div hN hM
  have hD := LB.isLB_div hD1 hι
  haveI : IsProper B.hom := IsAbelianScheme.proper
  have hI : ((𝟙 B)⁻¹ : B ⟶ B) ≫ (𝟙 B)⁻¹ = 𝟙 B := by
    first
    | rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    | rw [GrpObj.inv_def, Category.id_comp, GrpObj.inv_inv]
    | simp [GrpObj.comp_inv]
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := ⟨⟨_, hI, hI⟩⟩
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left :=
    ⟨⟨((𝟙 B)⁻¹ : B ⟶ B).left, by rw [← Over.comp_left, hI, Over.id_left],
      by rw [← Over.comp_left, hI, Over.id_left]⟩⟩
  have h0 : ∀ (L : LB (Sp k)), L.IsLB → ∃ t : LB.Gen L, t.IsGen := by
    intro L hL
    have hcov : ∀ y : Sp k, ∃ i, y ∈ L.U i := fun y => by
      have hy : y ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hy
    have hs : ∀ y y' : Sp k, y = y' := fun y y' => Subsingleton.elim (α := PrimeSpectrum k) y y'
    obtain ⟨y₀⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    obtain ⟨i₀, hi₀⟩ := hcov y₀
    exact GlobalTheory.DescendedPrincipal.exists_gen_of_chart hL i₀ fun y => by rw [← hs y₀ y]; exact hi₀
  set c := GlobalTheory.CechPic.cls M hM
  have e1 : (1 : B ⟶ B).left = (toUnit B).left ≫ η[B].left := rfl
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left c = 0 := by
    rw [e1, GlobalTheory.CechPic.pull_comp]
    obtain ⟨L, hL, hLc⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull η[B].left c)
    rw [← hLc, (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (h0 L hL), map_zero]
  have e5 : GlobalTheory.CechPic.lam c (𝟙 B)⁻¹ (𝟙 B) = -GlobalTheory.CechPic.pull ((𝟙 B)⁻¹ : B ⟶ B).left c - c := by
    unfold GlobalTheory.CechPic.lam
    rw [inv_mul_cancel, Over.id_left, GlobalTheory.CechPic.pull_id, h1]
    abel
  have e3 := GlobalTheory.CechPic.lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, GlobalTheory.CechPic.lam_one_left, e5] at e3
  have e2 : GlobalTheory.CechPic.cls (abelian₂ B M) (LB.isLB_linComb hM _ _) = GlobalTheory.CechPic.lam c (fst B B) (snd B B) :=
    GlobalTheory.CechPic.cls_cube_two hM _ _ _
  have hc : GlobalTheory.CechPic.cls _ hD = 0 := by
    rw [GlobalTheory.CechPic.cls_div hD1 hι hD, GlobalTheory.CechPic.cls_div hN hM hD1,
      GlobalTheory.CechPic.cls_pull (L := abelian₂ B M) (LB.isLB_linComb hM _ _) _ hN, GlobalTheory.CechPic.cls_pull hM _ hι, e2,
      GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
    rw [eq_comm, ← sub_eq_zero] at e3
    rw [← e3]
    abel
  have H := (GlobalTheory.CechPic.cls_eq_zero_iff hD).1 hc
  have hMa := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hM).1 ha
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 (hMa.tensor (hMa.pull_of_isFinite _) hN H)

theorem weilIs_one_one (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB A.left} (hM : M.IsLB) (T : Over S) : Out.WeilIs A M 1 (1 : T ⟶ A) 1 1 := by
  refine GlobalTheory.DescendedPrincipal.weilIs_one_right hG hA hM fun _ => ⟨⊤, trivial, ?_⟩
  exact match GlobalTheory.DescendedPrincipal.exists_theta_one (A := A) hM _ with
  | ⟨θ, hθ, _⟩ => ⟨θ, hθ.trans (MonObj.comp_one _).symm⟩


open SiegelOfPolarised PrimNorm in
def siegOne (hG : Out.GlobalFnsSt) {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (g : ℕ) :
    SiegPre g 1 ((1 : kˣ) : k) (𝟙 (Sp k)) where
  A := B
  ab := hB
  P := abelian₂ B M
  isLB := LB.isLB_linComb hM _ _
  rig₁ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  symm := lbIso_lam_pull hM _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact weilIs_one_one hG hB (pull_isLB (LB.isLB_linComb hM _ _) _) _

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : (W + W.transpose).det = 1) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  have hu : IsUnit (W + W.transpose).det := by rw [hW]; exact isUnit_one
  refine ⟨fun j => Sum.elim (fun p => Matrix.single p.1 p.2 1)
      (fun b => if b then (W + W.transpose)⁻¹ * W else (W + W.transpose)⁻¹ * W.transpose) j,
    Sum.inr true, Sum.inr false, ?_, ?_, fun u v => ⟨Sum.inl (u, v), rfl⟩⟩
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]

theorem isMonHom_of_coord {S : Scheme.{0}} {A G X : Over S} [GrpObj A] [GrpObj G] [GrpObj X] {n : ℕ}
    {pr : Fin n → (G ⟶ A)} (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) {f : X ⟶ G}
    (hf : ∀ u, IsMonHom (f ≫ pr u)) : IsMonHom f := by
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun x x' h =>
    (hu _ (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  constructor
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

theorem exists_polAV_hypS_retract : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Out.KTriv B M → ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  intro k _ _ B _ g hB hd M hM ha hK
  obtain ⟨hL1, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG : Out.GlobalFnsSt := hL1.globalFns
  letI : IsCommMonObj B := hB.comm
  have hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen := GlobalTheory.exists_gen_theta_of_isAbelianScheme k B hB M hM
  let b : GlobalTheory.ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp [IsPrimitiveRoot.one]⟩
  let c := siegOne hG hB hM g
  have hc : c.Principal :=
    ⟨relAmple_diag_lam hB hM hΘ ha, fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  obtain ⟨t, hsh, hp⟩ := GlobalTheory.exists_isSharp_and_prim hL1 hL2 GlobalTheory.Moduli.cube_of_isLB g (8 * g) W _ a w w' bas
    hW hb hw hw' hs 1 k b (Sp k) (𝟙 _) c (show (1 : kˣ) ^ 1 = 1 from one_pow 1) odd_one hc hd
  obtain ⟨pr, hpr, hu, -, -, -⟩ := hsh
  obtain ⟨i, hi, -⟩ := hu B (fun _ => 𝟙 B)
  letI := t.ab.comm
  refine ⟨t.pol, i, pr 0, ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩, ?_, hpr 0, hi 0⟩
  exact isMonHom_of_coord hpr hu (fun u => by rw [hi u]; exact (inferInstance : IsMonHom (𝟙 B)))

end GlobalTheory.EighthPowerFactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingForm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.PerpCharacter
open GlobalTheory.ZH.TorusPerp GlobalTheory.ZH.PerpTorus

theorem exists_torus_point_eStd : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → (∀ a b, x (a + b) = x a * x b) → (∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a) → ∀ t ∈ S.perp l.yy.ker, ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), pk.y = 0 ∧ IsTor τ pk.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk (x t) ∧ ∀ (a : S.Gam) (α : u.D.toPre.X), l.yy a = QuotientAddGroup.mk α → (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ t a).val))) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l x hx hadd hsurj a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have := ρ.P.isAb.comm
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (PadicAlgCl p)ˣ := Units.map y₀.toMonoidHom c₀
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact Polynomial.IsRoot.map (y₀.comp (algebraMap o S.R)) (hζ.isRoot_cyclotomic hn.pos)

  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))
  have hΦ : ∀ b, Φ (x b) = h ≫ ρ.pt b := fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))
  have weil : ∀ b b', WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd S.g _ b b').val)) :=
    fun b b' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil b b' (c₀ ^ (eStd S.g _ b b').val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← hΦ, ← hΦ] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _
      (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => x a.toAdd) fun _ _ => hadd _ _
  have pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = x b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha'⟩ := hsurj (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [ha', hq'] at w₁
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a' b) w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (hx b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q, τ, hq, hqτ, (f₁ _ _).2 ha'.symm, fun b α e => ?_⟩
  rw [hτ, hm b α e, Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]

end GlobalTheory.ZH.PerpCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitValue
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.SecValue
open GlobalTheory.UT.CoefBasic

theorem exists_pow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ} (n : ℕ)
    (h : ε' = fun i => (n : ℤ) * ε i) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε'), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val t' r z J = val t r z J ^ n := by
  subst h
  exact ⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩

theorem line_exp (k : ℕ) : DegPre.lineε k = fun i => (k : ℤ) * DegPre.lineε 1 i := by
  funext i
  fin_cases i <;> simp [DegPre.lineε]

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)
  rwa [sub_add_cancel] at this

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}
  {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)}

theorem genV_pow {ε ε' : K → ℤ} (n : ℕ) (h : ε' = fun i => (n : ℤ) * ε i) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ ε')} (ht : GenV hϖ hv t 0)
    (e : ∀ z J, Good L z J → val t' (𝟙 _) z J = val t (𝟙 _) z J ^ n) : GenV hϖ hv t' 0 := by
  obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩ := ht
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_pow n h t₀ ht₀
  refine ⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩
  · rw [v.map_pow, hx]; simp
  · rw [e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]

end

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

abbrev kon (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kon_surj : Function.Surjective (kon R F) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2

theorem isComb_iff {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) :
    IsComb t b σ ↔ SecM.ofSec A.A σ = ∑ l, kon R F (b l) • SecM.ofSec A.A (t l) := by
  rw [Subtype.ext_iff, funext_iff, Submodule.coe_sum]
  refine forall_congr' fun j => ?_
  rw [Finset.sum_apply]
  rfl

def ValM (σ : SecM A.A A.L k (TFK (R := R) F)) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ValAt (SecM.toSec A.A σ) x e c

theorem ValM.add {σ σ' : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ' x e c') :
    ValM (σ + σ') x e (c + c') := fun z J hJ => by
  refine (ThetaAct.sv_add σ σ' _ z hJ).trans ((congrArg₂ (· + ·) (h z J hJ) (h' z J hJ)).trans ?_)
  simp only [id, cst_eq, map_add (f := _)]
  exact (add_mul (R := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

theorem ValM.smul {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c : F} (h : ValM σ x e c) (b : F) :
    ValM (kon R F b • σ) x e (b * c) := fun z J hJ => by
  refine (ThetaAct.sv_smul _ σ _ z hJ).trans ?_
  rw [ThetaPtMove.ptSecT_fst]
  refine (congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z b) * ·) (h z J hJ)).trans ?_
  simp only [id, cst_eq, map_mul]
  exact (_root_.mul_assoc (G := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

theorem ValM.unique {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ x e c') :
    c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem ValM.exists (hL : Laws) (σ : SecM A.A A.L k (TFK (R := R) F)) {x} {e : FrAt x} (he : e.IsGen) :
    ∃ c, ValM σ x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he (SecM.toSec A.A σ)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem ValM.sum (hL : Laws) {x} {e : FrAt x} (he : e.IsGen) {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨c, hc⟩ := ValM.exists hL (0 : SecM A.A A.L k (TFK (R := R) F)) he
    have := hc.smul 0
    rw [smul_zero, zero_mul] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

end

theorem val_sum_eq_zero {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (i₀ : Ix) (h₀ : v (x i₀) = 0) {q : ℚ} (hq : 0 < q)
    (hx : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  obtain ⟨S, hS⟩ := h q
  have a := hS (insert i₀ S) (Finset.subset_insert _ _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at a
  have b := v.map_le_add a (v.map_le_sum (s := (insert i₀ S).erase i₀) fun i hi => hx i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - (x i₀ + ∑ i ∈ (insert i₀ S).erase i₀, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by ring
  rw [e, v.map_add_eq_of_lt_left, h₀]
  rw [h₀]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hq) b

theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n k : ℕ), 1 ≤ n → 4 ≤ k → ∀ (p : QkPt D.toPre F n) x, p.y = 0 → QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ k • z) → ∀ j, (s.s β).f j = 0) ∧ ∀ (t : SecA A F k) (c : F), U.ExpandsF F k w₀ t s → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.UT.TorsionValue.value_at_torsion hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv
    A G hG U w₀ ρ hN n hn p x hx e he
  rw [hy, QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at hv₁
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g
  obtain ⟨w, hw, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have b0 : ∀ χ, QForm.bOf D.toPre Q p.y χ = 0 := fun χ => by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  have hg := hqk n hn p
  obtain ⟨s, hν, hsupp, hc₀⟩ := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k hk
    p.g w _ 0 hw hg hw0 0
  refine ⟨s, hν, fun β hβ => hsupp β fun z => by simpa using hβ z, fun t c ht hc => ?_⟩
  have hS : SumV v (coef s p.g w) c := hsum k hk1 w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c ht hc
  have hk0 : (0 : ℚ) < k := by exact_mod_cast hk1
  refine val_sum_eq_zero hS 0 ?_ (q := 1 / k) (by positivity) fun χ hχ => ?_
  · rw [hc₀, b0, QForm.Q_zero hϖ D hQ]; simp
  · refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk1 w s hw).2 _ 0 0 hg hw0 hν χ)
    rw [b0]
    have : (1 : ℚ) ≤ Q χ := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    simpa using div_le_div_of_nonneg_right this hk0.le

theorem act_fix : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ x, p.y = 0 → IsTor τ p.g → QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) s, U.ExpandsF F N w₀ t s → (∀ β, τ (Multiplicative.ofAdd β) = 1 ∨ ∀ j, (s.s β).f j = 0) → IsActOf A.A A.L N θ t t' → t' = t := by
  intro hL R _ _ _ I hA D A G _ _ hG U F _ _ _ N hN p τ x hy hτ hx θ hθ w₀ hw₀ t t' s hs hsupp hact
  obtain ⟨hb₁, hb₂⟩ := (GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F N hN.pos w₀ hw₀
  obtain ⟨s', hs', -⟩ := hb₁ t'
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN p).1
  have hφ := GlobalTheory.UT.symLift_acts_as_phi hL R I hA D A G hG U F N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have e := ((GlobalTheory.UT.TorusWeight.torus_weight hL R I hA D A G hG U F N hN p τ hy hτ w hw).2 s s').1 hφ
  obtain rfl : s' = s := fam_ext fun α j => by
    rw [e α j]
    rcases hsupp α with h | h
    · rw [h, Units.val_one, DegPre.constBF, map_one, map_one, map_one, _root_.one_mul]
    · rw [h j, mul_zero]
  exact (hb₂ s').unique hs' hs

end GlobalTheory.ZH.SecValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteMulKTriv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.KTrivPoints

theorem finite_mul_kTriv : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // GlobalTheory.MemKL B M x} ∧ (∀ x y : (𝟙_ (Over (Sp k)) ⟶ B), GlobalTheory.MemKL B M x → GlobalTheory.MemKL B M y → GlobalTheory.MemKL B M (x * y)) ∧ ((∀ x : (𝟙_ (Over (Sp k)) ⟶ B), GlobalTheory.MemKL B M x → x = 1) → Out.KTriv B M) := by
  intro k _ _ _ B _ hB M hM hA
  obtain ⟨H, j, hj, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have := hB.comm
  refine ⟨?_, fun x y hx hy => GlobalTheory.UU.InK.mul hM hx hy, fun hx => ?_⟩
  · have : IsFinite (toUnit H).left := hfin
    have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
    refine Finite.of_surjective
      (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} =>
        (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : (𝟙_ (Over (Sp k)) ⟶ B) // GlobalTheory.MemKL B M x})) fun x => ?_
    obtain ⟨z, hz⟩ := (hH _ _).1 x.2
    exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩
  · have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
    have key := GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hH _ _).1 (GlobalTheory.memKL_one hM _))
      (fun T x y => (hH _ _).1 (GlobalTheory.UU.InK.mul hM ((hH _ _).2 ⟨x, rfl⟩)
        (GlobalTheory.UU.InK.inv hM ((hH _ _).2 ⟨y, rfl⟩))))
      k (𝟙 _) (fun x => hx _ ((hH _ _).2 ⟨x, rfl⟩))
    refine GlobalTheory.UU.kTriv_iff_forall.2 fun T x hxK => ?_
    obtain ⟨y, rfl⟩ := (hH T x).1 hxK
    exact key T (toUnit T) y

end GlobalTheory.KTrivPoints
end

