module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsRelAcyclicPolAVBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadModelFibreAtPointIsGivenVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCore

theorem linComb_hom {S S' : Scheme.{0}} {A T : Over S} {A' T' : Over S'} [GrpObj A] [GrpObj A']
    (f : (T ⟶ A) →* (T' ⟶ A')) {r : ℕ} (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) :
    f (linComb y a) = linComb (fun i => f (y i)) a := by
  have h := map_list_prod f (List.ofFn fun i => y i ^ a i)
  rw [List.map_ofFn] at h
  exact h.trans (congrArg List.prod (congrArg List.ofFn (funext fun i => map_pow f (y i) (a i))))

theorem comp_linComb' {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (U : T' ⟶ T) {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) : U ≫ linComb y a = linComb (fun i => U ≫ y i) a :=
  linComb_hom (MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y) y a

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (M : ℕ) (h : ∀ i, y i ^ M = 1) : linComb y a ^ M = 1 := by
  unfold linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem push_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {T₀ : Over S} (U : T.left ⟶ T₀.left)
    (hU : U ≫ T₀.hom = T.hom ≫ f) {r : ℕ} (x : Fin r → (T ⟶ G')) (y : Fin r → (T₀ ⟶ G))
    (hxy : ∀ i, (x i).left ≫ φ = U ≫ (y i).left) (a : Fin r → ℕ) :
    (linComb x a).left ≫ φ = U ≫ (linComb y a).left := by
  let V : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk U hU
  have e : pushHom h T (linComb x a) = V ≫ linComb y a := by
    rw [linComb_hom, comp_linComb']
    exact congrArg (linComb · a) (funext fun i => Over.OverMorphism.ext (hxy i))
  exact congrArg (fun z => z.left) e

theorem unitOn_zpow {R : Type} [CommRing R] (c : Rˣ) (e : ℤ) : unitOn (c ^ e) = unitOn c ^ e := map_zpow _ c e

theorem final_pf : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A B : PolAV (Sp Ω)) (A₀ : PolAV (Sp F)) (σ : A.A ≅ B.A) (ψ : B.A.left ⟶ A₀.A.left), GlobalTheory.IsPolIso A B σ → IsGrpPullback B.A A₀.A (spMap em) ψ → LBIso B.L (A₀.L.pull ψ) → ∃ a : A.A.left ⟶ A₀.A.left, IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω _ _ em A B A₀ σ ψ hσ h hLB
  haveI := hσ.1
  obtain ⟨w, hw⟩ := hσ.2
  refine ⟨σ.hom.left ≫ ψ, ((isGrpPullback_of_iso σ).comp h).congr (Category.id_comp _) rfl, ?_⟩
  exact LBIso.trans A.isLB (pull_isLB B.isLB _) (pull_isLB A₀.isLB _) (LBIso.symm ⟨w, hw⟩)
    (GlobalTheory.ArcDataDescent.lbIso_pull hLB σ.hom.left rfl)

theorem fibre_descends : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (n J : ℕ), n.Prime → Odd n → 4 ≤ J → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ J → ∀ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (y₀ : Fin (2 * A.g) → (baseOver (Sp T) ⟶ P.A)) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) → (∀ i, (lev.pt i).left ≫ φ = spMap jT ≫ (y₀ i).left) → IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hP hL n J hn ho hJ hb ζ lev y₀ v' hζ hy hv
  obtain ⟨⟨hL1, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have := P.isAb.comm
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  have hgP : P.g = A.g := H1.dim_unique A.A.hom
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hP.1 P.smoothDim) A.smoothDim
    ((1 : baseOver (Sp Ω) ⟶ A.A).left (IsLocalRing.closedPoint Ω))
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    have : n ≠ 2 := by rintro rfl; exact absurd ho (by decide)
    omega
  have hm3 : 3 ≤ n ^ J := hn3.trans (Nat.le_self_pow (by omega) n)
  have hM0 : (n ^ J) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hF0 : (((n ^ J) ^ 2 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hΩ0 : (((n ^ J) ^ 2 : ℕ) : Ω) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hF0
  have hnΩ : (n : Ω) ≠ 0 := by
    rw [← map_natCast em]; exact (map_ne_zero em).2 (Nat.cast_ne_zero.2 hn.ne_zero)
  have hyt : ∀ i, y₀ i ^ ((n ^ J) ^ 2) = 1 := fun i =>
    _root_.GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective Ω T jT hinj A P φ hP (lev.pt i) (y₀ i) _ (hy i) (lev.torsion i)
  let ζT : Tˣ := Units.map (algebraMap F T).toMonoidHom ζ
  have hjζ : Units.map jT.toMonoidHom ζT = Units.map em.toMonoidHom ζ := by
    ext; simp [ζT, ← hcomp]
  have hpair : ∀ i j, WeilIs P.A P.L (((n ^ J) ^ 2 : ℕ) : ℤ) (y₀ i) (y₀ j) (unitOn ζT ^ stdSymp A.g i j) := fun i j => by
    have := _root_.GlobalTheory.MumPair.weilIs_of_spread Ω T jT hinj A P φ hP hL ((n ^ J) ^ 2) (lev.pt i) (lev.pt j) (y₀ i) (y₀ j) (ζT ^ stdSymp A.g i j)
      (Nat.one_le_iff_ne_zero.2 hM0) (hy i) (hy j) (hyt i) (hyt j)
      (by rw [map_zpow, hjζ, unitOn_zpow]; exact lev.pairing i j)
    rwa [unitOn_zpow] at this
  let tR : T →+* F := t.toRingHom
  have htζ : Units.map tR.toMonoidHom ζT = ζ := by ext; simp [ζT, tR]
  let polPull {S : Scheme.{0}} (Q : PolAV S) {R : Type} [CommRing R] (f : Sp R ⟶ S) : PolAV (Sp R) := by
    have h := isGrpPullback_pullback Q.A f
    have hL' := pull_isLB Q.isLB (pullback.fst Q.A.hom f)
    have := Q.isAb.proper
    exact { A := (Over.pullback f).obj Q.A
            isAb := isAbelianScheme_pullback_obj f Q.A Q.isAb
            g := Q.g
            smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
            L := Q.L.pull (pullback.fst Q.A.hom f)
            isLB := hL'
            rigid := PolBaseChange.rigidified_pull h Q.rigid
            sym := PolBaseChange.sym_pull h Q.sym
            ample := AmpleBaseChange.relAmple_of_isPullback Q.isLB Q.ample h.1
            ktriv := by
              obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
              exact kTriv_pull h Q.isLB hL' ((isGen_iff w).1 hw) Q.ktriv }
  let A₀ := polPull P (spMap tR)
  let ψ₀ : A₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap tR)
  have hA₀ : IsGrpPullback A₀.A P.A (spMap tR) ψ₀ := isGrpPullback_pullback P.A (spMap tR)
  have hLA₀ : LBIso A₀.L (P.L.pull ψ₀) := PolBaseChange.lbIso_refl (pull_isLB P.isLB _)
  obtain ⟨levF, hlevF⟩ := _root_.GlobalTheory.Mum.FibLevel.exists_level_of_pullback T F tR P A₀ ψ₀ hA₀ hLA₀ A.g ((n ^ J) ^ 2) hgP ζT ζ hF0 htζ hζ y₀ hyt hpair
  have cover : ∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ (n ^ J) = 1 →
      ∃ a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2),
      ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
        linComb y₀ (fun i => (a i).val)) ^ (n ^ J) = z := by
    intro z hz
    obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hA₀ (𝟙 (Sp F)) (spMap tR) (Category.id_comp _).symm
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_levelPoint_pow_eq F A₀ (n ^ J) A.g hgP _ levF (e.symm z) (by omega) (by rw [← map_pow, hz, map_one])
    refine ⟨a, ?_⟩
    have key : e (GlobalTheory.levelPoint levF hgP a) =
        (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
          linComb y₀ (fun i => (a i).val) := by
      apply Over.OverMorphism.ext
      refine (he _).trans ((congrArg (fun z => z.left ≫ ψ₀) (GlobalTheory.ThetaPtDet.levelPoint_eq levF hgP a)).trans ?_)
      exact push_linComb hA₀ (T := baseOver (Sp F)) (T₀ := baseOver (Sp T)) (spMap tR) (by simp) _ _ hlevF _
    rw [← key, ← map_pow, ha, MulEquiv.apply_symm_apply]
  have hxF : ∀ a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2), (GlobalTheory.levelPoint lev rfl a).left ≫ φ =
      spMap jT ≫ (linComb y₀ (fun i => (a i).val)).left := fun a =>
    (congrArg (fun z => z.left ≫ φ) (GlobalTheory.ThetaPtDet.levelPoint_eq lev rfl a)).trans
      (push_linComb hP (T := baseOver (Sp Ω)) (T₀ := baseOver (Sp T)) (spMap jT) (by simp) _ _ hy _)
  have thF : IsThetaPt P (n ^ J)
      (fun a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2) =>
        (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
          linComb y₀ (fun i => (a i).val))
      (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v' a)) :=
    _root_.GlobalTheory.Mum.isThetaPt_fibre F Ω T em jT t hft hinj hcomp A P φ hP hL (n ^ J) (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2))
      (GlobalTheory.levelPoint lev rfl) (fun a => linComb y₀ (fun i => (a i).val)) v' ho.pow hm3 hxF
      (fun a => linComb_pow_eq_one _ _ _ hyt) cover hv
  let B := polPull A₀ (spMap em)
  let ψ₁ : B.A.left ⟶ A₀.A.left := pullback.fst A₀.A.hom (spMap em)
  have hB₁ : IsGrpPullback B.A A₀.A (spMap em) ψ₁ := isGrpPullback_pullback A₀.A (spMap em)
  have hLB₁ : LBIso B.L (A₀.L.pull ψ₁) := PolBaseChange.lbIso_refl (pull_isLB A₀.isLB _)
  have hsp : spMap em ≫ spMap tR = spMap (em.comp tR) := by simp [spMap, ← Spec.map_comp]
  have hB : IsGrpPullback B.A P.A (spMap em ≫ spMap tR) (ψ₁ ≫ ψ₀) := hB₁.comp hA₀
  have hLB : LBIso B.L (P.L.pull (ψ₁ ≫ ψ₀)) := GlobalTheory.ArcDataDescent.lbIso_pull_pull P.isLB ψ₀ ψ₁ rfl
  have hBζ : Units.map (em.comp tR).toMonoidHom ζT = Units.map em.toMonoidHom ζ := by ext; simp [ζT, tR]
  obtain ⟨levB, hlevB⟩ := _root_.GlobalTheory.Mum.FibLevel.exists_level_of_pullback T Ω (em.comp tR) P B (ψ₁ ≫ ψ₀) (hB.congr hsp rfl) hLB A.g ((n ^ J) ^ 2) hgP ζT _
    hΩ0 hBζ (hζ.map_of_injective (Units.map_injective (f := em.toMonoidHom) em.injective)) y₀ hyt hpair
  have thΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P em (x := spMap em ≫ spMap tR) rfl thF
  have key : ∀ (s : Sp Ω ⟶ Sp T) (_ : s = (baseOver (Sp Ω)).hom ≫ (spMap em ≫ spMap tR))
      (x₀ : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → (Over.mk s ⟶ P.A))
      (v : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → Γ(Sp Ω, ⊤)),
      (∀ a, (x₀ a).left = (GlobalTheory.levelPoint levB hgP a).left ≫ (ψ₁ ≫ ψ₀)) → IsThetaPt P (n ^ J) x₀ v →
      IsThetaPt B (n ^ J) (GlobalTheory.levelPoint levB hgP) v := by
    rintro s rfl x₀ v hx h
    have := B.isAb.comm
    exact (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) hB hLB hx
      (fun a => (congrArg (· ^ ((n ^ J) ^ 2)) (GlobalTheory.ThetaPtDet.levelPoint_eq levB hgP a)).trans
        (linComb_pow_eq_one _ _ _ fun i => levB.torsion _)) v).2 h
  have thB := key _ (Category.id_comp _).symm _ _ (fun a => by
    refine Eq.symm ((congrArg (fun z => z.left ≫ (ψ₁ ≫ ψ₀)) (GlobalTheory.ThetaPtDet.levelPoint_eq levB hgP a)).trans ?_)
    refine (push_linComb hB (T := baseOver (Sp Ω)) (T₀ := baseOver (Sp T)) (spMap em ≫ spMap tR) (by simp) _ _
      (fun i => (hlevB i).trans (by rw [hsp])) _).trans ?_
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]) thΩ
  have hN' : n ^ J = n ^ (J - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.thetaPt_determines hL1 A.g n 2 (J - 4) ((n ^ 2) ^ 2) (n ^ J) hn ho le_rfl rfl hN' hb Ω hnΩ
    A B rfl hgP _ lev levB _ hv thB
  exact ⟨A₀, final_pf F Ω em A B A₀ σ ψ₁ hσ hB₁ hLB₁⟩

end GlobalTheory.MumCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadOfTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SpreadTrait

theorem pull_cancel {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over S'} [GrpObj G₁] {f : S' ⟶ S}
    {m₁ : G₁.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f m₁) (u : S'' ⟶ S') {Gl : Over S''} [GrpObj Gl]
    {φl : Gl.left ⟶ G.left} (hGl : IsGrpPullback Gl G (u ≫ f) φl) :
    ∃ φ : Gl.left ⟶ G₁.left, IsGrpPullback Gl G₁ u φ ∧ φ ≫ m₁ = φl :=
  ⟨h₁.1.lift φl (Gl.hom ≫ u) (by rw [hGl.1.w, Category.assoc]),
    h₁.cancel (hGl.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _), h₁.1.lift_fst _ _ _⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C) :
    spMap v ≫ spMap u = spMap (v.comp u) := (Spec.map_comp _ _).symm

theorem spread_of_trait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁] (ψ : R →+* V₁) (hψ : IsLocalHom ψ)
    (Ω : Type) [Field Ω] (α : V₁ →+* Ω) (hα : Function.Injective α) (b : V →+* Ω)
    (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0) (eα : α.comp ψ = b.comp g)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ)).obj G).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ)).obj G) (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n')
    (hnn : n ≫ pullback.fst G.hom (spMap ψ) = n' ≫ β)
    (j : splitTorus (Sp V₁) D'.toPre.X ⟶ (Over.pullback (spMap ψ)).obj G) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :
    ∃ ρ, Spread U U' g β ρ := by
  haveI := hψ
  haveI := hj
  have hm₁ := isGrpPullback_pullback G (spMap ψ)
  have hm₀ := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap (residue V₁))
  have hm₀' := (hm₀.comp hm₁).congr (spMap_comp' ψ (residue V₁)) rfl
  have h₀ : ∀ x ∈ maximalIdeal R, (residue V₁).comp ψ x = 0 := GlobalTheory.TorusPart.map_eq_zero_of_isLocalHom _
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀)
    hm₀').2 _ (GlobalTheory.TorusPart.pullTorus hm₀ j) inferInstance
  exact ⟨ρ, V₁, inferInstance, inferInstance, inferInstance, ψ, (Over.pullback (spMap ψ)).obj G, inferInstance,
    inferInstance, pullback.fst G.hom (spMap ψ), Ω, inferInstance, α, b, hb, GΩ, inferInstance, n, hn, n', hn', j, _,
    inferInstance, _, hm₀, GlobalTheory.TorusPart.map_pow_one_eq_zero h₀, hm₀', hψ, hm₁, hj, hα, eα, hnn, ej, hρ⟩

theorem exists_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∃ ρ, Spread U U' g β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hβ
  haveI : IsNoetherianRing R := hR.1.1
  by_cases hl : IsLocalHom g
  · haveI := hl
    let κ := ResidueField V
    have hC : IsLocalHom (PowerSeries.C (R := κ)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ))⟩
    let c : V →+* PowerSeries κ := (PowerSeries.C (R := κ)).comp (residue V)
    have hcl : IsLocalHom c := RingHom.isLocalHom_comp _ _
    let ψ : R →+* PowerSeries κ := c.comp g
    have hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ) (FractionRing (PowerSeries κ))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b : V →+* FractionRing (PowerSeries κ) := α.comp c
    have hc0 : ∀ x ∈ maximalIdeal V, c x = 0 := fun x hx => by
      simp [c, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V ^ (0 + 1), c x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := fun x hx => by
      simp [b, hc x hx]
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    obtain ⟨mc, hmc, hmcβ⟩ := pull_cancel hβ (spMap c) (hm₁.congr (spMap_comp' g c).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap α)
    have hn' : IsGrpPullback _ G' (spMap b) _ := (hn.comp hmc).congr (spMap_comp' c α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ pullback.fst G.hom (spMap ψ) =
        (pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ mc) ≫ β := by
      rw [Category.assoc, hmcβ]
    exact spread_of_trait U U' g β (PowerSeries κ) ψ hψ _ α hα b hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U'.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨V₁, _, _, _, ψ, Ω, _, αK, b, hψ, hb, eα, hT⟩ := _root_.GlobalTheory.exists_trait_nonlocal_torusExtension R G hG V g hl
    haveI := hψ
    let alg := algebraMap V₁ (FractionRing V₁)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective V₁ (FractionRing V₁))
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    have hG₁ : IsSemiAbelian ((Over.pullback (spMap ψ)).obj G) := IsSemiAbelian.pullback _ G hG
    obtain ⟨φ₁, hφ₁, -⟩ := pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback G (spMap (alg.comp ψ))).congr (spMap_comp' ψ alg).symm rfl)
    have hn' := isGrpPullback_pullback G' (spMap b)
    obtain ⟨n, hn, hnm⟩ := pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ).congr ((spMap_comp' g b).trans ((congrArg spMap eα.symm).trans
        (spMap_comp' ψ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := _root_.GlobalTheory.TorusPart.extend_torus_hom_dvr V₁ ((Over.pullback (spMap ψ)).obj G) hG₁ _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb' hn') inferInstance
    exact spread_of_trait U U' g β V₁ ψ hψ Ω (αK.comp alg) hα b hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.SpreadTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNoetherianPadicImageFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem stalk_noetherian_and_finite_image :
    ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  intro X U hU x hx hft p _ φ
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℤ Γ(X, U)
  refine ⟨IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ this, ?_⟩
  let ψ : X.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ
  let f : Γ(X, U) →+* PadicAlgCl p := ψ.comp (algebraMap Γ(X, U) (X.presheaf.stalk x))
  obtain ⟨s, hs⟩ := hft.out
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    IntermediateField.adjoin ℚ_[p] ((s.image f : Finset (PadicAlgCl p)) : Set (PadicAlgCl p))
  refine ⟨K, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin (fun y _ => Algebra.IsIntegral.isIntegral y)
  · have hgen : ∀ r : Γ(X, U), f r ∈ K := by
      intro r
      have hr : r ∈ Algebra.adjoin ℤ (s : Set Γ(X, U)) := by rw [hs]; trivial
      induction hr using Algebra.adjoin_induction with
      | mem y hy =>
        apply IntermediateField.subset_adjoin
        simp only [Finset.coe_image]
        exact Set.mem_image_of_mem f hy
      | algebraMap n =>
        have : f (algebraMap ℤ Γ(X, U) n) = (n : PadicAlgCl p) := by simp
        rw [this]; exact K.intCast_mem n
      | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
    intro a
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl a
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk x) r t
    have hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) t) := IsLocalization.map_units _ t
    have hne : f t ≠ 0 := (hunit.map ψ).ne_zero
    have heq : ψ (IsLocalization.mk' (X.presheaf.stalk x) r t) =
        f r * (f t)⁻¹ := by
      have h2 := congrArg ψ hspec
      rw [map_mul] at h2
      change ψ _ * f t = f r at h2
      rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hne, _root_.mul_one]
    change ψ _ ∈ K
    rw [heq]
    exact K.mul_mem (hgen r) (K.inv_mem (hgen t))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def stalkOf {W : Type} [CommRing W] (z : Sp W) : W →+* (Sp W).presheaf.stalk z :=
  ((Sp W).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom

theorem stalkOf_injective {W : Type} [CommRing W] [IsDomain W] (z : Sp W) : Function.Injective (stalkOf z) :=
  (germ_injective_of_isIntegral (Sp W) (U := ⊤) z trivial).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1

abbrev unitW {W : Type} [CommRing W] (G : Over (Sp W)) [GrpObj G] : Sp W ⟶ G.left := eSec G

abbrev idW (W : Type) [CommRing W] : Sp W ⟶ (𝟙_ (Over (Sp W))).left := 𝟙 (Sp W)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_over_lift_of_range_subset {T : Scheme.{0}} {Z H V : Over T} (e : V ⟶ H) [IsOpenImmersion e.left]
    (f : Z ⟶ H) (h : Set.range f.left ⊆ Set.range e.left) : ∃ a : Z ⟶ V, a ≫ e = f := by
  refine ⟨Over.homMk (IsOpenImmersion.lift e.left f.left h) ?_, ?_⟩
  · rw [← Over.w e, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w f]
  · ext
    simp

theorem surjective_mul_of_open_of_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hV hirr
  refine ⟨fun x => ?_⟩
  let t : Spec (CommRingCat.of (H.left.residueField x)) ⟶ T := H.left.fromSpecResidueField x ≫ H.hom
  let g : Over.mk t ⟶ H := Over.homMk (H.left.fromSpecResidueField x) rfl
  have hI := hirr (H.left.residueField x) t
  let X : Over T := Over.mk (pullback.snd H.hom t ≫ t)
  let p : X ⟶ H := Over.homMk (pullback.fst H.hom t) pullback.condition
  let c : X ⟶ Over.mk t := Over.homMk (pullback.snd H.hom t) rfl
  let φ : X ⟶ H := (c ≫ g) * p⁻¹
  let Y : Over T := Over.mk (pullback.snd V.hom t ≫ t)
  let q : Y ⟶ V := Over.homMk (pullback.fst V.hom t) pullback.condition
  let d : Y ⟶ Over.mk t := Over.homMk (pullback.snd V.hom t) rfl
  have hl : ∀ h : Y ⟶ H, ∃ l : Y ⟶ X, l ≫ p = h ∧ l ≫ c = d := by
    intro h
    refine ⟨Over.homMk (pullback.lift h.left (pullback.snd V.hom t) (Over.w h)) ?_, ?_, ?_⟩
    · exact pullback.lift_snd_assoc _ _ _ _
    · ext; exact pullback.lift_fst _ _ _
    · ext; exact pullback.lift_snd _ _ _
  have hY : Nonempty Y.left := by
    have : Surjective (pullback.snd V.hom t) := inferInstance
    obtain ⟨y, -⟩ := (pullback.snd V.hom t).surjective (closedPoint _)
    exact ⟨y⟩
  obtain ⟨y⟩ := hY
  have hopen : IsOpen (Set.range e.left) := e.left.isOpenEmbedding.isOpen_range
  have hne : ∀ (l : Y ⟶ X) (ψ : X ⟶ H), l ≫ ψ = q ≫ e → (ψ.left ⁻¹' Set.range e.left).Nonempty := by
    intro l ψ h
    refine ⟨l.left y, q.left y, ?_⟩
    change (q ≫ e).left y = (l ≫ ψ).left y
    rw [h]
  have h1 : (p.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, -⟩ := hl (q ≫ e)
    exact hne l p hlp
  have h2 : (φ.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, hlc⟩ := hl ((q ≫ e)⁻¹ * (d ≫ g))
    refine hne l φ ?_
    simp only [φ]
    rw [MonObj.comp_mul, GrpObj.comp_inv, hlp, ← Category.assoc, hlc]
    group
  have hI' : IrreducibleSpace X.left := hI
  have ho1 : IsOpen (p.left ⁻¹' Set.range e.left) := hopen.preimage p.left.continuous
  have ho2 : IsOpen (φ.left ⁻¹' Set.range e.left) := hopen.preimage φ.left.continuous
  obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter ho1 ho2 h1 h2
  let U : X.left.Opens := ⟨_, ho1.inter ho2⟩
  let Z : Over T := Over.mk (U.ι ≫ X.hom)
  let j : Z ⟶ X := Over.homMk U.ι rfl
  obtain ⟨a, ha⟩ := exists_over_lift_of_range_subset e (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.2)
  obtain ⟨b, hb⟩ := exists_over_lift_of_range_subset e (j ≫ p) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.1)
  have key : lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e)) = j ≫ c ≫ g := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, hb, ← MonObj.comp_mul]
    simp only [φ, inv_mul_cancel_right]
  let u : Z.left := (⟨z, hz1, hz2⟩ : U)
  refine ⟨(lift a b).left u, ?_⟩
  change (lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e))).left u = x
  rw [key]
  exact H.left.fromSpecResidueField_apply x _

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.tangentVector_section_value_eq_expansion_sum : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_at_tangent | exact GlobalTheory.MBLow.TanExp.value_at_tangent | (intros; apply GlobalTheory.MBLow.TanExp.value_at_tangent <;> assumption) | exact @GlobalTheory.MBLow.TanExp.ds_sum | exact GlobalTheory.MBLow.TanExp.ds_sum | (intros; apply GlobalTheory.MBLow.TanExp.ds_sum <;> assumption)
end

