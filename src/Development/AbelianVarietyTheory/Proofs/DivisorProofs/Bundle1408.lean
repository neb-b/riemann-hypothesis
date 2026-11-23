module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  first | exact @GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | exact GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | (intros; apply GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupSchemes
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTorsRep

theorem absNorm_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] (𝔟 : Ideal (𝓞 K))
    (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) : (Ideal.absNorm 𝔟).Coprime p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have h1 : (1 : 𝓞 K) ∈ 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} := h ▸ Submodule.mem_top
  obtain ⟨β, hβ, z, hz, hβz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  by_cases h0 : 𝔟 = ⊥
  · subst h0
    have hβ0 : β = 0 := (Submodule.mem_bot _).1 hβ
    subst hβ0
    rw [zero_add] at hβz
    have hu : IsUnit (p : 𝓞 K) := ⟨⟨(p : 𝓞 K), y, by rw [mul_comm]; exact hβz, hβz⟩, rfl⟩
    have hu' := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
    rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at hu'
    have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := (Module.finrank_pos).ne'
    rw [isUnit_pow_iff hd, Int.isUnit_iff] at hu'
    rcases hu' with h' | h'
    · exact hp.out.one_lt.ne' (by exact_mod_cast h')
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · have hne : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hne hdvd
    have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hne
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have h1' : (Ideal.Quotient.mk 𝔟 y) * (p : 𝓞 K ⧸ 𝔟) = 1 := by
      have := congrArg (Ideal.Quotient.mk 𝔟) hβz
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
    have hx0 : x = 0 := by
      rw [← _root_.one_mul x, ← h1', _root_.mul_assoc, hpx, MulZeroClass.mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx

section Tors

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (n : ℕ)

theorem mono_of_unit {X : Over S} (e : 𝟙_ (Over S) ⟶ X) : Mono e := ⟨fun g h _ => toUnit_unique g h⟩

theorem ι_mulN : torsion.ι A n ≫ mulN A n = toUnit _ ≫ η[A] := by
  exact (pullback.condition (f := mulN A n) (g := (η : 𝟙_ (Over S) ⟶ A))).trans
    (congrArg (· ≫ η[A]) (toUnit_unique _ _))

def torsEta : 𝟙_ (Over S) ⟶ torsion A n :=
  pullback.lift η[A] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

theorem mono_ι : Mono (torsion.ι A n) := by
  have := mono_of_unit η[A]
  exact pullback.fst_of_mono

def torsAct (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) : torsion A n ⟶ torsion A n :=
  pullback.lift (torsion.ι A n ≫ f) (toUnit _) (by
    rw [Category.assoc, hf, ← Category.assoc, ι_mulN, Category.assoc, IsMonHom.one_hom])

@[simp]
theorem torsAct_ι (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) :
    torsAct n f hf ≫ torsion.ι A n = torsion.ι A n ≫ f := pullback.lift_fst _ _ _

theorem exists_openClosed {Ix : Type} [DecidableEq Ix] (act : Ix → (A ⟶ A)) [∀ a, IsMonHom (act a)]
    (hc : ∀ a, act a ≫ mulN A n = mulN A n ≫ act a) [Etale (torsion A n).hom] [IsSeparated (torsion A n).hom]
    (t : Finset Ix) :
    ∃ (Z : Over S) (j : Z ⟶ torsion A n), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ torsion A n), (∃ z, z ≫ j = y) ↔ ∀ a ∈ t, y ≫ torsion.ι A n ≫ act a = 1 := by
  have hEta : torsEta n ≫ torsion.ι A n = η[A] := pullback.lift_fst _ _ _
  have hsec : IsOpenImmersion (torsEta (A := A) n).left ∧ IsClosedImmersion (torsEta (A := A) n).left :=
    GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion A n).hom _ (Over.w (torsEta n))
  have := hsec.1; have := hsec.2
  have := mono_of_unit (torsEta (A := A) n)
  have := mono_ι (A := A) n
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨_, 𝟙 _, inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance, fun W y =>
      ⟨fun _ a ha => absurd ha (Finset.notMem_empty a), fun _ => ⟨y, Category.comp_id y⟩⟩⟩
  | insert a t hat ih =>
    obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := ih
    let g := j ≫ torsAct n (act a) (hc a)
    have hP := (IsPullback.of_hasPullback g (torsEta n)).map (Over.forget S)
    have ho : IsOpenImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1
    have hcl : IsClosedImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2
    refine ⟨pullback g (torsEta n), pullback.fst g (torsEta n) ≫ j, inferInstance, ?_, ?_, fun W y => ?_⟩
    · rw [Over.comp_left]; infer_instance
    · rw [Over.comp_left]; infer_instance
    constructor
    · rintro ⟨z, rfl⟩ b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · have e : j ≫ torsion.ι A n ≫ act b = g ≫ torsion.ι A n := by simp [g]
        simp only [Category.assoc]
        rw [e, ← Category.assoc (pullback.fst g _), pullback.condition]
        simp only [Category.assoc, hEta]
        rw [← Category.assoc, toUnit_unique (z ≫ pullback.snd g (torsEta n)) (toUnit W)]; rfl
      · exact (hpts W _).1 ⟨z ≫ pullback.fst _ _, Category.assoc _ _ _⟩ b hb
    · intro h
      obtain ⟨w, hw⟩ := (hpts W y).2 (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have hwg : w ≫ g = toUnit W ≫ torsEta n := by
        rw [← cancel_mono (torsion.ι A n)]
        simp only [g, Category.assoc, torsAct_ι, hEta]
        rw [← Category.assoc w j, hw, h a (Finset.mem_insert_self a t)]; rfl
      exact ⟨pullback.lift w (toUnit W) hwg, by rw [← Category.assoc, pullback.lift_fst, hw]⟩

end Tors


open GlobalTheory.IwLevel in
theorem exists_finiteEtale_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∃ (K : Over S) (i : K ⟶ o.A), Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o 𝔟 h𝔟
  classical
  set n := Ideal.absNorm 𝔟 with hn_def
  have hcop := absNorm_coprime p 𝔟 h𝔟
  have hnR : IsUnit ((n : ℕ) : R) := b.unit n hcop
  have hnS : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
    have := hnR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hnS
  have hactN : ∀ k : ℕ, o.act.act (k : D.O) = mulN o.A k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one]; rfl
  have hc : ∀ a : D.O, o.act.act a ≫ mulN o.A n = mulN o.A n ≫ o.act.act a := by
    intro a
    rw [← hactN, ← o.act.mul, ← o.act.mul, Nat.cast_comm]
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : IsSeparated (torsion o.A n).hom := inferInstance
  have : Module.Finite ℤ D.O := D.finO
  have : IsNoetherian D.O D.O := isNoetherian_of_tower ℤ inferInstance
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (𝔟.map (algebraMap (𝓞 D.F) D.O))
  obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := exists_openClosed n o.act.act hc t
  have := mono_ι (A := o.A) n
  refine ⟨Z, j ≫ torsion.ι o.A n, inferInstance, ?_, ?_, fun T x => ?_⟩
  · rw [← Over.w j]; infer_instance
  · rw [← Over.w j]; infer_instance
  rw [← ht]
  refine Iff.trans ?_ (killedBy_span (htAct o) (t : Set D.O) x).symm
  simp only [htAct_act]
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simpa only [Category.assoc] using (hpts T (z ≫ j)).1 ⟨z, rfl⟩ a ha
  · intro hx
    have hn𝔟 : ((n : ℕ) : 𝓞 D.F) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
    have hnO : ((n : ℕ) : D.O) ∈ Submodule.span D.O (t : Set D.O) := by
      rw [ht]; simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) hn𝔟
    have hxn : x ≫ mulN o.A n = toUnit T ≫ η[o.A] := by
      rw [← hactN]
      have := (killedBy_span (htAct o) (t : Set D.O) x).2 (by simpa only [htAct_act] using hx) _ hnO
      exact this
    let y : T ⟶ torsion o.A n := pullback.lift x (toUnit T) hxn
    have hy : y ≫ torsion.ι o.A n = x := pullback.lift_fst _ _ _
    obtain ⟨z, hz⟩ := (hpts T y).2 (fun a ha => by rw [← Category.assoc, hy]; exact hx a ha)
    exact ⟨z, by rw [← Category.assoc, hz, hy]⟩

end GlobalTheory.HTTorsRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumnsStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_element_acts_on_frame_columns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  first | exact @GlobalTheory.TorusMat.isTorusElt_mat | exact GlobalTheory.TorusMat.isTorusElt_mat | (intros; apply GlobalTheory.TorusMat.isTorusElt_mat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.LiesOverExt

theorem sumF_algebraMap {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} (x : Ix → FractionRing R) (s : FractionRing R)
    (h : SumF I (FractionRing R) x s) :
    SumF I F (fun i => algebraMap (FractionRing R) F (x i)) (algebraMap (FractionRing R) F s) := by
  letI : Module R (FractionRing R) := Module.compHom (FractionRing R) (algebraMap R (FractionRing R))
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hS⟩ := h
  let φ : FractionRing R →ₗ[R] F :=
    { toFun := algebraMap (FractionRing R) F
      map_add' := map_add _
      map_smul' := fun r y => by
        show algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r • y) =
          algebraMap R (FractionRing R) r • algebraMap (FractionRing R) F y
        rw [smul_eq_mul, map_mul, Algebra.smul_def] }
  refine ⟨N.map φ, hN.map φ, Submodule.mem_map_of_mem hs, fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS n
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := φ) (hS T hT)
  rw [Submodule.map_smul''] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [φ, map_sub, map_sum] using this

theorem exists_frm_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b)
    (hw : w.IsGen) :
    ∃ w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b, w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
        val w' r z J = val w (r ≫ spMap (algebraMap (FractionRing R) F)) z J := by
  have hb := GlobalTheory.TorusExt.gtExt_b (D := D) (algebraMap (FractionRing R) F) (RingHom.comp_id _) g
  have h0 : spMap (algebraMap (FractionRing R) F) ≫ (DegPre.zeroF D (FractionRing R)).left =
      (DegPre.zeroF D F).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A)
      (GlobalTheory.TorusExt.extMap (R := R) (algebraMap (FractionRing R) F) (RingHom.comp_id _)))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB
    (φ' := DegPre.lineφ D F (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b)
    (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) (congrArg (fun q => q.left) hb).symm)
    (LB.pullGen D.P.L _ _ w (spMap (algebraMap (FractionRing R) F))) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_frAt_pull {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x)
    (hfr : fr.IsGen) (x' : TFK (R := R) F ⟶ A.A) (hx : x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left) :
    ∃ fr' : FrAt x', fr'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F).left) (z : Z) (J), Good A.L z J →
      val fr' r z J = val fr (r ≫ spMap (algebraMap (FractionRing R) F)) z J := by
  obtain ⟨fr', hfr', hv⟩ := exists_gen A.isLB (φ' := fun _ : Fin 1 => x'.left) (ε' := fun _ => 1)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hx])
    (LB.pullGen A.L _ _ fr (spMap (algebraMap (FractionRing R) F))) (pullGen_isGen _ _ _ _ hfr _)
  exact ⟨fr', hfr', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val wk r z J = val w r z J ^ k := by
  obtain ⟨wk, hwk, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by fin_cases i <;> simp [DegPre.lineε])
    (GeneratorPullback.powGen D.P.L _ _ w k) (powGen_isGen _ _ _ _ hw k)
  exact ⟨wk, hwk, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pow _ _ _ _ _)⟩


open GlobalTheory.TorsionExt GlobalTheory.FieldBaseChange in
theorem liesOver_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre (FractionRing R)) (w : Frm D.toPre (FractionRing R) 1 g.b) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ g w x fr → ∀ (x' : TFK (R := R) F ⟶ A.A), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → ∃ (w' : Frm D.toPre F 1 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b) (fr' : FrAt x'), w'.IsGen ∧ fr'.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' x' fr' := by
  intro R _ _ _ I hI D A G _ _ hGs U F _ _ _ w₀ hw₀ g w x fr hw hfr hlies x' hx'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨w', hw', hvw'⟩ := exists_frm_pull D.toPre F g w hw
  obtain ⟨fr', hfr', hvfr'⟩ := exists_frAt_pull x fr hfr x' hx'
  refine ⟨w', fr', hw', hfr', ?_⟩
  intro k hk wk' hwk'v hwk' s s'' v hexp hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  obtain ⟨wkF, hwkF, hvwkF⟩ := exists_frm_pull D.toPre F g wk hwk
  have hc : ∀ χ, coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wk' χ =
      coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ := fun χ =>
    GlobalTheory.UT.ThetaSum.coef_congr _ hwkF (fun z J hJ => by
      rw [hwk'v z J hJ, hvw' _ _ z J hJ, hvwkF _ _ z J hJ, hwkv _ _ z J hJ]) s'' χ
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U (FractionRing R) hk w₀ hw₀
  obtain ⟨e', he'⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  have cc : ∀ t, e' (abPull (FractionRing R) F A k t) = famPull D.toPre (FractionRing R) F hG k (e t) := fun t =>
    (he' _ _).1 (expandsF_pull U.toUnifPre hG ((he _ _).2 rfl))
  obtain ⟨n, c, σ, hσ⟩ := (isExtension_famPull D.toPre (FractionRing R) F hG hk).exists_sum s''
  choose a ha using fun i => GlobalTheory.ZH.SecComb.exists_valAt (e.symm (σ i)) hfr
  have sK : ∀ i, SumF I (FractionRing R) (coef (σ i) g wk) (a i) := fun i =>
    hlies k hk wk (fun z J hJ => hwkv _ _ z J hJ) hwk (e.symm (σ i)) (σ i) (a i)
      ((he _ _).2 (e.apply_symm_apply _)) (ha i)
  have comb := GlobalTheory.UT.EvalZero.sumF_comb hI F Finset.univ c _ _ fun i => sumF_algebraMap I F _ _ (sK i)
  have lin := ((GlobalTheory.UT.CoefBasic.coef_basic R D.toPre F k
    (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g)).2.2 wkF hwkF).2.1
  have hcoef : ∀ χ, coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wk' χ =
      ∑ i, c i * algebraMap (FractionRing R) F (coef (σ i) g wk χ) := fun χ => by
    have h0 : coef 0 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ = 0 := by
      have := lin 0 0 1 χ
      rw [smul_zero, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    let Lc : Fam D.toPre F k →ₗ[F] F :=
      { toFun := fun s => coef s (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ
        map_add' := fun s s' => by simpa using lin s s' 1 χ
        map_smul' := fun c s => by simpa [h0] using lin s 0 c χ }
    rw [hc χ, hσ]
    show Lc _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (c i * ·) (_root_.GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac R D.toPre F hG k (σ i) g wk wkF hwk hwkF
      (fun z J hJ => hvwkF _ _ z J hJ) χ)

  let u : Fin n → AbSec A F k := fun i => abPull (FractionRing R) F A k (e.symm (σ i))
  have hs : (s : AbSec A F k) = ∑ i, c i • u i := by
    apply e'.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(he' _ _).1 hexp, map_sum, hσ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, cc, e.apply_symm_apply]
  have hcomb : IsComb u c s := fun j => by
    rw [hs]
    exact (map_sum (chartLin (abelianBase A F) _ j) (fun i => c i • u i) Finset.univ).trans rfl
  have hvu : ∀ i, ValAt (u i) x' fr' (algebraMap (FractionRing R) F (a i)) := fun i =>
    GlobalTheory.T.value_pulledBackSection_eq_image_fieldExtension R A F k _ x fr x' fr' hx' hfr (fun z J hJ => hvfr' _ _ z J hJ) _ (ha i)
  have hval' := ((GlobalTheory.ZH.SecComb.lin_comb_value_act R A F k).2 (Fin n) c u).2 s hcomb |>.1 x' fr' _ hvu
  have hv : v = ∑ i, c i * algebraMap (FractionRing R) F (a i) :=
    ((GlobalTheory.ZH.SecComb.lin_comb_value_act R A F k).1 s x' fr' hfr').unique hval hval'
  rw [hv, funext hcoef]
  exact comb

end GlobalTheory.Poinc.Tors.LiesOverExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNondegenerate
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem mixedTracePairing_nondegenerate_left {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, trP F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same] at this

theorem mixedTracePairing_nondegenerate_right {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) (hy : ∀ x, trP F κ x y = 0) : y = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hy (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this

theorem mixedTracePairing_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (trP F κ).Nondegenerate := by
  intro F _ _ κ _
  refine ⟨fun x hx => mixedTracePairing_nondegenerate_left (F := F) (κ := κ) x hx, fun y hy => mixedTracePairing_nondegenerate_right (F := F) (κ := κ) y hy⟩

end GlobalTheory.ArchSch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTraceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_separation_of_iwahori_trace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → Separation := by
  first | exact @GlobalTheory.TrMultSep.separation_of_iwahoriTrace | exact GlobalTheory.TrMultSep.separation_of_iwahoriTrace | (intros; apply GlobalTheory.TrMultSep.separation_of_iwahoriTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLevelFunctionInertEqLatticStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w (n := m) ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum | exact GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum | (intros; apply GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum <;> assumption)
end

