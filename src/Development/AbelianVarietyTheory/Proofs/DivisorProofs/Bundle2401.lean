module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gtCoord_overPoint_ext {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a a' : Z ⟶ thickObj R I e G)
    (hp : a.left ≫ g.pG.left = a'.left ≫ g.pG.left)
    (hv : ∀ (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      ∀ χ : D.X, val (g.t χ) a.left z J = val (g.t χ) a'.left z J) : a = a' := by
  have := g.i_hom
  have := g.q_hom
  have hq : a ≫ g.q = a' ≫ g.q := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
  have hd : (a' * a⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, mul_inv_cancel]
    rfl
  let τ := g.isKernel.lift (a' * a⁻¹) (toUnit _) hd
  have hτ : τ ≫ g.i = a' * a⁻¹ := g.isKernel.lift_fst _ _ _
  have h1 : τ = 1 := by
    refine TorusPts.torusPt_ext fun χ => ?_
    refine congrArg Units.val (show pullU τ.left ⊤ (charUnit _ D.X χ) =
      pullU (1 : Z ⟶ splitTorus _ D.X).left ⊤ (charUnit _ D.X χ) from unit_ext fun z _ => ?_)
    choose J hJ using fun ψ : Z.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
    have k := (TorusCoord.val_torus_point_and_translate R I D e G g Z τ a z J hJ χ).2
    have k' := (TorusCoord.val_torus_point_and_translate R I D e G g Z 1 a z J hJ χ).2
    rw [hτ, inv_mul_cancel_right] at k
    rw [MonObj.one_comp, _root_.one_mul] at k'
    have k2 := mul_right_cancel (k.symm.trans ((hv z J hJ χ).symm.trans k'))
    exact (gm_pull (𝟙 Z.left) τ.left z ⊤ trivial _).trans (k2.trans
      (gm_pull (𝟙 Z.left) (1 : Z ⟶ splitTorus _ D.X).left z ⊤ trivial _).symm)
  rw [h1, MonObj.one_comp] at hτ
  exact (mul_inv_eq_one.1 hτ.symm).symm

theorem gtCoord_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  intro R _ _ I D e G _ _ g Z r r' hb hp hv
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  exact congrArg (fun φ => φ.left) (gtCoord_overPoint_ext g (Z := FinalForm) (Over.homMk r rfl) (Over.homMk r' hb.symm) hp hv)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerCechH1Uniform
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg.TowerH1
variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

theorem cst_eq_zero (e : ℕ) (V : (Y e).left.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst ((Y e).hom ≫ thick R I e) V a = 0 := by
  have h : (thick R I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = 0 := by
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simp only [AbLaw.cst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem mul_eq_zero_of_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = 0 := by
  have h : x * y ∈ towerIdeal Y e (I ^ (e + 1)) V := by
    have h0 := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h0 ⊢
    rw [← Ideal.map_mul, ← pow_succ'] at h0
    exact h0
  have hb : towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    unfold towerIdeal
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact cst_eq_zero e V ha
  rw [hb] at h
  exact h

theorem mul_eq_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = x' * y := by
  have := mul_eq_zero_of_mem e V hx hy
  rw [sub_mul] at this
  exact sub_eq_zero.1 this

theorem pow_mul_eq_pow_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) :
    x ^ m * y = x' ^ m * y :=
  mul_eq_mul_of_sub_mem e V (Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow x x' m) hx) hy

theorem pow_mul_eq_of_sub_one_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x - 1 ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) : x ^ m * y = y := by
  rw [pow_mul_eq_pow_mul_of_sub_mem e V hx hy m, one_pow, one_mul]

theorem rs_mem (e : ℕ) (J : Ideal R) {U V : (Y e).left.Opens} (h : V ≤ U) {x : Γ((Y e).left, U)}
    (hx : x ∈ towerIdeal Y e J U) : rs (Y e).left h x ∈ towerIdeal Y e J V := by
  unfold towerIdeal at hx ⊢
  have h1 := Ideal.mem_map_of_mem (rs (Y e).left h) hx
  rw [Ideal.map_map] at h1
  have h2 : (rs (Y e).left h).comp (AbLaw.cst ((Y e).hom ≫ thick R I e) U) = AbLaw.cst ((Y e).hom ≫ thick R I e) V :=
    RingHom.ext fun r => rs_cst _ h r
  rwa [h2] at h1

theorem isUnit_rs_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U))
    (hb : V ≤ X.basicOpen f) : IsUnit (rs X h f) := by
  have hu : IsUnit (rs X (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  have := hu.map (rs X hb)
  rwa [rs_rs] at this

end GlobalTheory.FormalAlg.TowerH1

namespace GlobalTheory.FormalAlg.TowerH1

theorem ev_X {R : Type} [CommRing R] {I : Ideal R}
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ} (C : Charts I Y β n) (e : ℕ) (i m : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X m) = C.ρ e i m := by
  simp only [Charts.ev, MvPolynomial.eval₂Hom_X']

end GlobalTheory.FormalAlg.TowerH1


open GlobalTheory.FormalAlg.TowerH1 in
theorem GlobalTheory.FormalAlg.towerCech_h1_uniform : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ e : ℕ, (∀ c : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j), (∀ i j, c i j ∈ towerIdeal Y e (I ^ e) _) → (∀ i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j) (c i j) + rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l) (c j l) = rs (Y e).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l) (c i l)) → ∃ a : ∀ i, Γ((Y e).left, C.D e i), (∀ i, a i ∈ towerIdeal Y e (I ^ e) _) ∧ ∀ i j, c i j = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (a i) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (a j)) := by
  intro R _ _ I Y β hβ n C
  classical
  let J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R) := fun e => ⨅ i, RingHom.ker (C.ev e i)
  have hJ : ∀ e F, F ∈ J e ↔ ∀ i, C.ev e i F = 0 := by
    intro e F
    simp only [J, Ideal.mem_iInf, RingHom.mem_ker]
  obtain ⟨d₀, hd₀⟩ := _root_.GlobalTheory.uniformSerre_cocycle R I n J (fun e t a F ha _ _ hF =>
    (hJ _ _).2 fun i => _root_.GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero R I Y β hβ n C e a F i ha ((hJ e F).1 hF i))
  refine ⟨d₀, fun k hk e c hc hcoc => ?_⟩
  have lev := _root_.GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod R I Y β hβ n C
  choose N₀ hN₀ using fun i j => _root_.GlobalTheory.FormalAlg.JFrac.exists_form R I Y β hβ n C e i j (c i j) (hc i j)
  let N := Finset.univ.sup (fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2)
  have hN : ∀ i j, N₀ i j ≤ N := fun i j =>
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose F hFh hFc hFe using fun i j => hN₀ i j N (hN i j) k
  have hFm : ∀ i j, F i j ∈ Ideal.map MvPolynomial.C (I ^ e) := fun i j =>
    MvPolynomial.mem_map_C_iff.2 (hFc i j)

  have htri : ∀ i j l, ∃ L : ℕ, ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j * MvPolynomial.X l) ^ L *
      (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l) ∈ J e := by
    intro i j l
    have hH : (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l :
        MvPolynomial (Fin (n + 1)) R).IsHomogeneous (N + (k + 2 * N)) :=
      (((MvPolynomial.isHomogeneous_X_pow l N).mul (hFh i j)).add
        ((MvPolynomial.isHomogeneous_X_pow i N).mul (hFh j l))).sub
        ((MvPolynomial.isHomogeneous_X_pow j N).mul (hFh i l))
    have hHc : ∀ m, AddMonoidAlgebra.coeff (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l : MvPolynomial (Fin (n + 1)) R) m ∈ I ^ e :=
      MvPolynomial.mem_map_C_iff.1 (sub_mem (add_mem (Ideal.mul_mem_left _ _ (hFm i j))
        (Ideal.mul_mem_left _ _ (hFm j l))) (Ideal.mul_mem_left _ _ (hFm i l)))

    have hTij : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j := inf_le_left
    have hTil : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTjl : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTi : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i := inf_le_left.trans inf_le_left
    have hTj : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j := inf_le_left.trans inf_le_right
    have h1 : rs (Y e).left hTi (C.ev e i (F i j)) =
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTij (c i j) := by
      have := congrArg (rs (Y e).left hTij) (hFe i j)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h3 : rs (Y e).left hTi (C.ev e i (F i l)) =
        rs (Y e).left hTi (C.ρ e i l) ^ N * rs (Y e).left hTil (c i l) := by
      have := congrArg (rs (Y e).left hTil) (hFe i l)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h2 : rs (Y e).left hTi (C.ev e i (F j l)) =
        rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * (rs (Y e).left hTj (C.ρ e j l) ^ N *
          rs (Y e).left hTjl (c j l)) := by
      have t1 := congrArg (rs (Y e).left hTij)
        (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + 2 * N) (F j l) (hFh j l) (hFc j l) i j).2.2
      have t2 := congrArg (rs (Y e).left hTjl) (hFe j l)
      simp only [rs_rs, map_mul, map_pow] at t1 t2
      rw [t1, t2]
    have hcjl : rs (Y e).left hTjl (c j l) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hTjl (hc j l)
    have hP : rs (Y e).left hTi (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTi (lev.2.1 e i)
      rwa [map_sub, map_one] at this
    have hB : rs (Y e).left hTi (C.ρ e i l) - rs (Y e).left hTi (C.ρ e i j) * rs (Y e).left hTj (C.ρ e j l)
        ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTij (lev.2.2 e i j l)
      simpa only [map_sub, map_mul, rs_rs] using this
    have e1 := pow_mul_eq_of_sub_one_mem e _ hP hcjl N
    have e2 := pow_mul_eq_pow_mul_of_sub_mem e _ hB hcjl N
    have hyp := hcoc i j l
    have hz : rs (Y e).left hTi (C.ev e i (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l)) = 0 := by
      simp only [map_add (f := _), map_sub, map_mul, map_pow, ev_X]
      rw [h1, h2, h3]
      linear_combination (rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * rs (Y e).left hTj (C.ρ e j l) ^ N) * e1 -
        rs (Y e).left hTi (C.ρ e i j) ^ (k + N) * e2 +
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTi (C.ρ e i l) ^ N * hyp
    obtain ⟨L, hL⟩ := _root_.GlobalTheory.FormalAlg.TripleKill.ev_triple_kill R I Y β hβ n C e _ _ hH hHc i j l hz
    exact ⟨L, (hJ _ _).2 hL⟩

  obtain ⟨N', G, hGh, hGc, hrel⟩ := hd₀ k hk e N F hFh hFc htri
  have tr := fun i j => GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + N') (G j) (hGh j) (hGc j) i j
  refine ⟨fun i => C.ev e i (G i), fun i => (tr i i).1, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := hrel i j
  have hl : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hr : C.D e i ⊓ C.D e j ≤ C.D e j := inf_le_right
  have h0 := congrArg (rs (Y e).left hl) ((hJ _ _).1 hL i)
  simp only [map_mul, map_sub, map_pow, ev_X, map_zero] at h0
  rw [hFe i j, (tr i j).2.2] at h0
  have hci := hc i j
  have hai : rs (Y e).left hl (C.ev e i (G i)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hl (tr i i).1
  have haj : rs (Y e).left hr (C.ev e j (G j)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hr (tr j j).1
  have hP : rs (Y e).left hl (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
    have := rs_mem e I hl (lev.2.1 e i)
    rwa [map_sub, map_one] at this
  have ec := pow_mul_eq_of_sub_one_mem e _ hP hci (L + N')
  have ea := pow_mul_eq_of_sub_one_mem e _ hP hai (L + N)
  have eb := pow_mul_eq_of_sub_one_mem e _ hP haj (L + N + N')
  have hu : IsUnit (rs (Y e).left hl (C.ρ e i j) ^ (L + N + N')) :=
    (isUnit_rs_of_le_basicOpen hl _ (lev.1 e i j).ge).pow _
  have hw : rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * (c i j - (rs (Y e).left hl (C.ev e i (G i)) -
      rs (Y e).left hl (C.ρ e i j) ^ k * rs (Y e).left hr (C.ev e j (G j)))) = 0 := by
    linear_combination h0 - rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ec +
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ea -
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N' + k) * eb
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hw)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullOfSval
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem toProj_secPull_of_gs {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} [Subsingleton Z] {A : LB Y} {A' : LB Y'}
    {N : ℕ} (σ : Fin (N + 1) → A.Sec) (τ : Fin (N + 1) → A'.Sec) (s : Y' ⟶ Sp R)
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Z ⟶ Y) (y : Z ⟶ Y')
    (H : ∀ z : Z, ∃ (a : A.ι) (a' : A'.ι) (c : (Z.presheaf.stalk z)ˣ), p z ∈ A.U a ∧ y z ∈ A'.U a' ∧
      ∀ i, gs p z _ ((σ i).f a) = c.val * gs y z _ ((τ i).f a')) :
    (∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧
      ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  have h1 : ∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i) := by
    intro i z
    obtain ⟨a, a', c, ha, ha', e⟩ := H z
    rw [GlobalTheory.mem_nonzeroLocus_iff_pull (σ i) p z ha, GlobalTheory.mem_nonzeroLocus_iff_pull (τ i) y z ha', e i,
      IsUnit.mul_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.isUnit, h⟩⟩
  have hs : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) p) = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y z)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (GlobalTheory.nonzeroLocus_secPull (σ i) p).ge ((h1 i z).2 hi)⟩
  refine ⟨h1, hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hτ y hs fun z => ?_⟩
  obtain ⟨a, a', c, ha, ha', e⟩ := H z
  obtain ⟨W, hW, u, hu⟩ := Z.presheaf.exists_germ_eq c.val
  have hall : ∀ {U : Z.Opens}, z ∈ U → W ≤ U := fun hU x _ => (Subsingleton.elim z x) ▸ hU
  have hl : z ∈ (A.pull p).U fun _ => a := Set.mem_iInter.2 fun _ => ha
  refine ⟨W, hW, a', hall ha', fun _ => a, hall hl, u, fun j => fn_ext fun x hx => ?_⟩
  obtain rfl : z = x := Subsingleton.elim _ _
  have e₁ : gs (𝟙 Z) z W (resG Z (hall hl) ((GlobalTheory.secPull (σ j) p).f fun _ => a)) = gs p z _ ((σ j).f a) :=
    (gs_res (𝟙 Z) z (hall hl) hW _).trans
      ((GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull A p) (σ j) (𝟙 Z) z (fun _ => a) hl).trans (by rw [Category.id_comp]; rfl))
  have e₂ : gs (𝟙 Z) z W u = c.val := (gs_eq (𝟙 Z) z W hW u).trans hu
  have e₃ : gs (𝟙 Z) z W ((y.appLE _ W (hall ha')).hom ((τ j).f a')) = gs y z _ ((τ j).f a') :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE y _ _ _ (𝟙 Z) z hW _).trans (by rw [Category.id_comp])
  rw [e₁, gs_mul (𝟙 Z) z W hW, e₂, e₃, e j]

theorem toProj_secPull_of_sval : ∀ (R Ω : Type) [CommRing R] [Field Ω] (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (h : Y ⟶ X) (h' : Y' ⟶ X') (k N : ℕ) (σ : Fin (N + 1) → SecK L h k) (τ : Fin (N + 1) → SecK L' h' k) (s : Y' ⟶ Sp R) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Sp Ω ⟶ Y) (y : Sp Ω ⟶ Y'), L.IsLB → L'.IsLB → (∀ z J J', Good L z J → Good L' z J' → ∃ c : ((Sp Ω).presheaf.stalk z)ˣ, ∀ i, sval (σ i) p z J = c.val * sval (τ i) y z J') → (∀ i (z : Sp Ω), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧ ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  intro R Ω _ _ X X' Y Y' L L' h h' k N σ τ s hτ p y hL hL' H
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  refine toProj_secPull_of_gs σ τ s hτ p y fun z => ?_
  choose J hJ using fun χ : Sp Ω ⟶ X => exists_chart hL (χ z)
  choose J' hJ' using fun χ : Sp Ω ⟶ X' => exists_chart hL' (χ z)
  obtain ⟨c, hc⟩ := H z J J' hJ hJ'
  exact ⟨_, _, c, Good.mem hJ _ p, Good.mem hJ' _ y, hc⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjFormulaTop

theorem topSelf_pull_eq_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  intro k _ X Y _ _ p q _ D hp hq hD π hπ hgen hdeg B hB
  obtain ⟨U, hU, hgU, hU', -, hfin, hfree, hrank⟩ :=
    GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hp hq π hπ hgen hdeg
  subst hπ
  letI := GlobalTheory.algebraΓOfHom p
  letI := GlobalTheory.algebraΓOfHom (π ≫ p)
  rw [topSelf_def, topSelf_def]
  letI := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  exact GlobalTheory.FieldProj.interNum_pull_eq_mul k Y X p π hq hp U _ hgU hU hU'
    ⟨hfree, hfin', hrank⟩ D hD (fun _ => B) (fun _ => hB)

end GlobalTheory.ProjFormulaTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem torMatch_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (g₂ : V →+* V₂) (β₂ : G₂.left ⟶ G'.left), Function.Injective g₂ → (∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V)) → ∀ ρ ρ₂, TorMatch U U' g β ρ → TorMatch U' U₂ g₂ β₂ ρ₂ → TorMatch U U₂ (g₂.comp g) (β₂ ≫ β) (ρ₂.comp ρ) := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ hVb G' _ _ hG' D' A' U' g β V₂ _ _ _ hV₂b G₂ _ _ hG₂ D₂ A₂ U₂ g₂ β₂
    hg₂ hkV ρ ρ₂ h₁ h₂
  intro F _ _ _ _ hF k hk τ τ₂ q q₂ a a₂ hτ₂ hττ hqy hqt hq₂y hq₂t ha ha₂
  have hinj : Function.Injective ((algebraMap (FractionRing V₂) F).comp ((algebraMap V₂ (FractionRing V₂)).comp g₂)) :=
    (algebraMap (FractionRing V₂) F).injective.comp ((IsFractionRing.injective V₂ (FractionRing V₂)).comp hg₂)
  letI : Algebra (FractionRing V) F := (IsFractionRing.lift hinj).toAlgebra
  have hV : ∀ v, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) v) =
      algebraMap (FractionRing V₂) F (algebraMap V₂ (FractionRing V₂) (g₂ v)) := fun v =>
    IsFractionRing.lift_algebraMap hinj v
  have hk' : IsUnit (k : V) := hkV k hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  let τ' : Multiplicative D'.toPre.X →* Fˣ := τ₂.comp (AddMonoidHom.toMultiplicative ρ₂)
  have hτ' : τ' ^ k = 1 := MonoidHom.ext fun χ => DFunLike.congr_fun hτ₂ _
  obtain ⟨q', hq'y, hq't⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (k := k) τ' hτ'
  obtain ⟨hV', _⟩ := hVb
  obtain ⟨f', ⟨i', -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV' D' A' G' hG' U' F k hk1
  have e₁ := h₁ F (fun r => by rw [hF, hV]; rfl) k hk τ τ' q q' a (f' q') hτ' hττ hqy hqt hq'y hq't ha ((i' _ _).2 rfl)
  have e₂ := h₂ F hV k hk' τ' τ₂ q' q₂ (f' q') a₂ hτ₂ (fun _ => rfl) hq'y hq't hq₂y hq₂t ((i' _ _).2 rfl) ha₂
  rw [e₁, reassoc_of% e₂]

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc

theorem qk_lattice_oAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  intro E _ _ _ H V _ _ _ hV t P K _ _ _ m a pk pk' x x' hm hx hx' hxx'
  obtain ⟨h1, h2, h3⟩ := hV
  have hT : P.TorsionIso := GlobalTheory.GeneratorsCompare.torsionIso P
  obtain ⟨f, hf, -, heq, -, hact, -⟩ := hT K m hm
  letI := H.starRing
  obtain ⟨p'', hp''⟩ := qkAct_exists GlobalTheory.lawsAndExpansions.1.1.globalFns P.D.tau_bimult P.oD a pk
  have e1 : f p'' = x' := by
    rw [hact a pk p'' hp'', ← (hf pk x).1 hx, hxx']
  have e2 : f p'' = f pk' := by rw [e1, ← (hf pk' x').1 hx']
  obtain ⟨z₂, hz₂, -⟩ := (heq p'' pk').1 e2
  obtain ⟨q, hq, -, z₁, hz₁, -⟩ := hp''
  exact ⟨z₁ + z₂, by rw [hz₂, hz₁, hq, smul_add, add_assoc]⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMaps
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem val_eq_of_maps_pullAlong {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (F : X ⟶ X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (W : LB.Iso (LB.LinComb L φ ε) (LB.LinComb (L.pull F) φ ε)) (a t : LB.Gen (LB.LinComb L φ ε))
    (f f' : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k) (hψ' : ∀ k, φ k ≫ F = f' ≫ φ k)
    (h : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f φ ε φ hψ t)) (h' : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f' φ ε φ hψ' t))
    (z : Y) (J : (Y ⟶ X) → L.ι) (hJ : Good L z J) : val t f z J = val t f' z J := by
  let jj : K → (L.pull F).ι := fun k _ => J (φ k ≫ F)
  let q : K → L.ι := fun k => J (φ k)
  have m₁ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ (φ k ≫ F)
  have m₂ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L φ q := Set.mem_iInter.2 fun k => hJ (φ k)
  have m : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q := ⟨m₁, m₂⟩
  have key : ∀ (f : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k),
      val t f z J = gm (𝟙 Y) z _ (res (inf_le_left : LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q ≤ _)
        ((GeneratorPullback.pullAlong L F f φ ε φ hψ t).s jj)) := by
    intro f hψ
    rw [val_of t f z J (fun k => J (φ k ≫ F)) (fun k => by rw [hψ k])]
    exact ((gm_res (𝟙 Y) z _ m _).trans ((gm_res (𝟙 Y) z _ m₁ _).trans
      (gm_pull (𝟙 Y) f z _ (@GeneratorPullback.pullAlong_le _ _ _ _ L _ _ F f φ φ hψ jj z m₁) _))).symm
  rw [key f hψ, key f' hψ']
  exact congrArg (gm (𝟙 Y) z _) ((h (jj, q)).trans (h' (jj, q)).symm)

theorem gtCoord_val_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J :=
  fun g F _ f f' x hψ hψ' h h' z J hJ => val_eq_of_maps_pullAlong F _ Oinvε _ (g.t x) (g.t x) f f' hψ hψ' h h' z J hJ

end GlobalTheory.Mum
end
end

