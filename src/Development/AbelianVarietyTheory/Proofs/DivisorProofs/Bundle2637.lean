module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoordinatesFormsAndFibreNormBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDegreeGeHalfDetLieDefinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Data
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFGData

theorem data : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (P₀ : LB (A₀ ⊗ A₀).left) (lv₀ : Std g n → (𝟙_ (Over (Sp R₀)) ⟶ A₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ IsSymmetricPair g A₀ P₀ ∧ (∀ a b, lv₀ (a + b) = lv₀ a * lv₀ b) ∧ Out.RelAmple A₀ (diagPull A₀ P₀) ∧ IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ lv₀ (spMap R₀.subtype) := by
  intro g n hn _ R _ β c hc
  have h0 : n ≠ 0 := by omega
  obtain ⟨R₁, β₁, A₁, _, P₁, lv₁, hfg, hβ, hA₁, hd₁, hP₁, htr⟩ := _root_.GlobalTheory.SiegFg.siegPre_data_descends_fg g n hn R β c
  have htr' := htr
  obtain ⟨φ, φ₂, hφ, sq₁, sq₂, iso, hl⟩ := htr
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have hsym : IsSymmetricPair g c.A c.P := isSymmetricPair (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hlev : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := (cycBase h0).ζ) c
  obtain ⟨hAb, hdim, hPlb, hr1, hr2, hsy⟩ := hsym
  obtain ⟨F₅, H₅⟩ := _root_.GlobalTheory.rigSym_descends_to_subring_containing_finset R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hr1 hr2 hsy
  obtain ⟨F₂, H₂⟩ := _root_.GlobalTheory.AmpleDiagSubring.relAmple_diag_subring R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hc.1
  classical
  let S : Subalgebra R₁ R := Algebra.adjoin R₁ ((F₅ ∪ F₂ : Finset R) : Set R)
  let R₂ : Subring R := S.toSubring
  have h12 : R₁ ≤ R₂ := fun x hx => S.algebraMap_mem ⟨x, hx⟩
  have hF : ((F₅ ∪ F₂ : Finset R) : Set R) ⊆ R₂ := Algebra.subset_adjoin
  have hfg₂ : Algebra.FiniteType ℤ R₂ := GlobalTheory.SpreadGroup.finiteType_of_fg hfg (Subalgebra.fg_adjoin_finset _)
  obtain ⟨A₂, _, lv₂, π, π₂, hA₂, hd₂, hπ, sqπ, htr₂⟩ :=
    _root_.GlobalTheory.SiegBaseChange.pullbackTriple_of_le R R₁ R₂ h12 g n c.A c.P (lvOf c) A₁ P₁ lv₁ hA₁ hd₁ hPlb hP₁ htr'
  obtain ⟨t1, t2, t3⟩ := H₅ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  have am := H₂ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  refine ⟨R₂, (Subring.inclusion h12).comp β₁, A₂, inferInstance, P₁.pull π₂, lv₂, hfg₂, ?_,
    ⟨hA₂, hd₂, pull_isLB hP₁ _, t1, t2, t3⟩, ?_, am, htr₂⟩
  · rw [← hβ]
    rfl
  · intro a b
    obtain ⟨ψ, ψ₂, hψ, -, -, -, hl₂⟩ := htr₂
    have : IsSeparated A₂.hom := by have := hA₂.proper; infer_instance
    refine Over.OverMorphism.ext (_root_.GlobalTheory.sections_eq_of_spMap_subtype_comp_eq R R₂ A₂.left A₂.hom _ _ ?_ ?_)
    · exact (Over.w (lv₂ (a + b))).trans (Over.w (lv₂ a * lv₂ b)).symm
    · let f := spMap R₂.subtype
      let u : Over.mk ((𝟙_ (Over (Sp R))).hom ≫ f) ⟶ 𝟙_ (Over (Sp R₂)) := toUnit _
      have hu : u.left = (𝟙_ (Over (Sp R))).hom ≫ f := Over.toUnit_left
      have hid : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
      have m := hψ.2 (𝟙_ (Over (Sp R))) (lvOf c a) (lvOf c b) (u ≫ lv₂ a) (u ≫ lv₂ b)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ a).symm)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ b).symm)
      rw [← MonObj.comp_mul, Over.comp_left, hu, hid, Category.id_comp, ← hlev.1] at m
      exact (hl₂ (a + b)).symm.trans m.symm

end GlobalTheory.SiegFGData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiff
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem trace_mul_mul_eq_sum_entries {R : Type} [CommRing R] {r : Type} [Fintype r] (P M Q : Matrix r r R) :
    (P * M * Q).trace = ∑ p, ∑ q, (Q * P) q p * M p q := by
  rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm (f := fun p q => (Q * P) q p * M p q)]
  exact Finset.sum_congr rfl fun q _ => Matrix.mul_apply

theorem dbarAt_transAt (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n)
    (hG : MContDiffAt ∞ G v) (hGu : IsUnit (G v).det) (hG' : MContDiffAt ∞ G' v)
    (hG'u : IsUnit (G' v).det) (k : ℕ) :
    dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  obtain ⟨_, hsum, hsmul, _, hleib⟩ := _root_.GlobalTheory.CxForm.dbarAt_local_calculus n v
  obtain ⟨sconst, ssum, ssmul, smul⟩ := _root_.GlobalTheory.ChernCalc.smooth_coeff_closure n v
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_of_eq (by simp)
  have hdiff : ∀ α : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v :=
    fun α h S => (h S).differentiableAt (by simp)
  obtain ⟨W, hW⟩ : ∃ W : ℕ → V n → Matrix r r (Ev n),
      W = fun i x => curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : r → r → V n → Alt n, β = fun p q x =>
      (∑ a, conn G x (coordVec a) p q • dz a) - ∑ a, conn G' x (coordVec a) p q • dz a := ⟨_, rfl⟩

  have hWs : ∀ i p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((W i x q p : Ev n) : Alt n) S) v := by
    intro i p q; subst hW; exact (_root_.GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1
  have hWc : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n)) v = 0 := by
    intro i p q; subst hW; exact (_root_.GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).2

  have hcs : ∀ (H : V n → Matrix r r ℂ), MContDiffAt ∞ H v → IsUnit (H v).det → ∀ p q,
      ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ a, conn H x (coordVec a) p q • dz a) S) v := by
    intro H hH hHu p q
    exact ssum (Fin n) Finset.univ (fun a x => conn H x (coordVec a) p q • dz a) fun a _ =>
      ssmul (fun x => conn H x (coordVec a) p q) (fun _ => dz a)
        (hH.conn hHu hinf (coordVec a) p q) (sconst (dz a))
  have hβs : ∀ p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β p q x) S) v := by
    intro p q S; subst hβ
    simpa only [map_sub, Finsupp.sub_apply] using (hcs G hG hGu p q S).sub (hcs G' hG' hG'u p q S)
  have dsub : ∀ α γ : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (γ x) S) v) →
      dbarAt (fun x => α x - γ x) v = dbarAt α v - dbarAt γ v := by
    intro α γ hα hγ
    have e : (fun x => α x - γ x) =
        fun x => ∑ j ∈ (Finset.univ : Finset (Fin 2)), (![α, fun y => (-1 : ℂ) • γ y] j) x := by
      funext x; simp [Fin.sum_univ_two, sub_eq_add_neg]
    rw [e, hsum (Fin 2) Finset.univ _ ?_]
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsmul (-1) γ hγ]
      simp [sub_eq_add_neg]
    · intro j _ S
      fin_cases j
      · exact hα S
      · simpa [map_smul] using (hγ S).const_smul (-1 : ℂ)
  have hdβ : ∀ p q, dbarAt (β p q) v = (curvEv G v p q : Alt n) - curvEv G' v p q := by
    intro p q; subst hβ
    refine (dsub _ _ (hdiff _ (hcs G hG hGu p q)) (hdiff _ (hcs G' hG' hG'u p q))).trans ?_
    rw [_root_.GlobalTheory.ChernCalc.dbarAt_conn n r G v hG hGu p q, _root_.GlobalTheory.ChernCalc.dbarAt_conn n r G' v hG' hG'u p q]
  have step : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n) * β p q x) v =
      (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i p q
    rw [hleib (fun x => W i x q p) (β p q) (hdiff _ (hWs i p q)) (hdiff _ (hβs p q)), hWc, zero_mul,
      zero_add, hdβ]

  have key : (fun x => transAt G G' x k) =
      fun x => ∑ i ∈ Finset.range k, ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x := by
    funext x
    subst hW hβ
    simp only [transAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trace_mul_mul_eq_sum_entries, Matrix.map_apply, Matrix.sub_apply, map_sub,
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, sub_mul, Subalgebra.coe_sub]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Algebra.smul_def, mul_assoc, mul_sub, sub_mul]

  have alg : ∑ i ∈ Finset.range k, ∑ p, ∑ q, W i v q p * (curvEv G v p q - curvEv G' v p q) =
      powAt G v k - powAt G' v k := by
    refine Eq.trans ?_ (_root_.GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow (Ev n) r (curvEv G v) (curvEv G' v) k)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm, hW]
    exact Finset.sum_congr rfl fun q _ => by rw [Matrix.diag_apply, Matrix.mul_apply]; rfl
  rw [key]
  refine (hsum _ _ _ ?_).trans ?_
  · intro i _
    exact hdiff _ (ssum r Finset.univ _ fun p _ => ssum r Finset.univ _ fun q _ =>
      smul _ _ (hWs i p q) (hβs p q))
  have inner : ∀ i, dbarAt (fun x => ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x) v =
      ∑ p, ∑ q, (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun p _ => ?_)
    · intro p _
      exact hdiff _ (ssum r Finset.univ _ fun q _ => smul _ _ (hWs i p q) (hβs p q))
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun q _ => step i p q)
    intro q _
    exact hdiff _ (smul _ _ (hWs i p q) (hβs p q))
  rw [Finset.sum_congr rfl fun i _ => inner i]
  have := congrArg (fun w : Ev n => (w : Alt n)) alg
  simpa only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_sub] using this

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRam

open GlobalTheory.WeilParts

variable {D : D7}

theorem unramAt_mul {e : AF D.host.F} {a b : (AE D)ˣ →* Circle} (ha : UnramAt e a) (hb : UnramAt e b) : UnramAt e (a * b) := by
  intro x h1 h2 h3
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem unramAt_pow {e : AF D.host.F} {a : (AE D)ˣ →* Circle} (ha : UnramAt e a) (n : ℕ) : UnramAt e (a ^ n) := by
  intro x h1 h2 h3
  rw [MonoidHom.pow_apply, ha x h1 h2 h3, one_pow]

theorem bottom_ram : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hr T Lc μ₀ hμ G => ?_⟩⟩
  intro W i j A A' WW X _ t v e he
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    rw [mul_div_mul_right_eq_div]
    rcases hS with hS | ⟨PP, hPP, hPv⟩
    · refine ⟨_root_.GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt G μ₀ hμ t v e he hS, ?_, ?_⟩
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · exact _root_.GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent G μ₀ hμ t v e he h0 i j
        · exact _root_.GlobalTheory.RamifiedOnLargePlaces.not_unramAt G μ₀ hμ t v e he h1 i j
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · subst h0; exact _root_.GlobalTheory.DifferentAtBasePlace.not_dvd_different G
        · exact _root_.GlobalTheory.DiffSOne.not_dvd_differentIdeal large₂ hr v h1
    · refine ⟨_root_.GlobalTheory.SplitTwistPlaces.not_nonSplitAt G μ₀ hμ t v e he PP hPP hPv, ?_, hPv ▸ _root_.GlobalTheory.TwistPlDiff.under_not_dvd_differentIdeal Lc μ₀ hμ t PP hPP⟩
      by_cases h0 : v ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h0 with h0 | h1
        · exact _root_.GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent G μ₀ hμ t v e he h0 i j
        · exact _root_.GlobalTheory.RamifiedOnLargePlaces.not_unramAt G μ₀ hμ t v e he h1 i j
      · exact _root_.GlobalTheory.SqTop.not_unramAt_twist G μ₀ hμ t v e he h0 PP hPP hPv i j
  · left
    push_neg at hS
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.GridUnr.chi_eta_unramAt G μ₀ hμ t v e he hS.1 i
    exact ⟨unramAt_mul (_root_.GlobalTheory.BotTripleUnr.unramAt_mu G μ₀ hμ t v e he hS.1 hS.2 j) (unramAt_pow h2 _), unramAt_mul h1 (unramAt_pow h2 _)⟩

end GlobalTheory.BotRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCaseCuspFormFibreSlopeGeBound
section
noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefFibre

theorem vAdd_pow' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) (n : ℕ) :
    vAdd w (x ^ n) = n * vAdd w x := by
  simp [vAdd, map_pow, WithZero.log_pow]

theorem vAdd_one' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : vAdd w (1 : K) = 0 := by
  simp [vAdd]

theorem subsingleton_idx : ∀ (N : ℕ) (la : Fin N → ℕ), N = 0 → Subsingleton (Idx la) := by
  rintro N la rfl
  constructor
  rintro ⟨m, -⟩ ⟨m', -⟩
  congr 1
  ext ⟨i, _⟩
  exact i.elim0

theorem dim_eq_one_of_zero {N : ℕ} (la : Fin N → ℕ) (hla : Antitone la) (h : N = 0) : dim la = 1 := by
  haveI := subsingleton_idx N la h
  have h1 := dim_pos hla
  have h2 : dim la ≤ 1 := by rw [dim_eq_card]; exact Fintype.card_le_one_iff_subsingleton.2 inferInstance
  omega

theorem fibreAt_defCase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ →
      ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  intro E _ _ _ H Dw l Xo c r U ξ a n c₁ hD hDom hFl Z
  obtain ⟨P⟩ := _root_.GlobalTheory.DefPt.PtExist.main E H Dw l Xo c r U ξ hD Z
  haveI hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hanti : ∀ τ, Antitone (part Dw a τ) := fun τ i j hij => hDom.1 τ (show (i : ℕ) ≤ j from hij)
  obtain ⟨φ, hinj, hrange, hreads⟩ := _root_.GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hconj, hint⟩ := _root_.GlobalTheory.DefPt.IntNorm.integral_and_norm_le E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hlie, -⟩ := _root_.GlobalTheory.DefPt.degLie_eq_neg_deg_flat E H Dw l Xo c r U ξ hD Z P
  have hth := _root_.GlobalTheory.DefPt.ThetaDeg.main E H Dw l Xo c r U ξ hD Z P
  have hIntOne : ∀ (w : HeightOneSpectrum (𝓞 c.F)) (m : ℕ), IntAt w (1 : Matrix (Fin m) (Fin m) c.F) :=
    fun w m i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hBad : ∀ τ, IsAdelic fun w => P.B w τ := fun τ => by
    refine ⟨fun w => (P.loc w).2.1 τ, P.fin.subset fun w hw h => hw ?_⟩
    show IntAt w (P.B w τ) ∧ IntAt w (P.B w τ)⁻¹
    have hB : P.B w τ = 1 := by rw [h.2]; rfl
    rw [hB, inv_one]
    exact ⟨hIntOne w _, hIntOne w _⟩
  have ha0 : ∀ w, P.a w ^ n ≠ 0 := fun w => pow_ne_zero _ (P.loc w).1
  have hsupp1 : (Function.support fun w => vAdd w (P.a w)).Finite :=
    P.fin.subset fun w hw h => hw (by simp only; rw [h.1, vAdd_one'])
  have hsupp : (Function.support fun w => vAdd w (P.a w ^ n)).Finite :=
    hsupp1.subset fun w hw h => hw (by simp only at h ⊢; rw [vAdd_pow', h, mul_zero])
  have hspos : ∀ σ, 0 < (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ =>
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 (P.arch σ).1)) n
  have hsconj : ∀ σ, (Real.sqrt (P.N ((starRingEnd ℂ).comp σ)))⁻¹ ^ n = (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ => by
    rw [(hconj σ).1]
  obtain ⟨hdet, hslope⟩ := _root_.GlobalTheory.FibSlope.slope_fibre_ge c.F (E →+* ℂ) Dw.mult (part Dw a) hanti (fun w => P.a w ^ n) P.B
    (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) P.X ha0 hsupp hBad hspos (fun σ τ => (P.arch σ).2.1 τ) hsconj
    (fun σ τ => (hconj σ).2 τ)
  have hlat : IsAdelic fun w => fibA (part Dw a) (P.a w ^ n) (P.B w) :=
    _root_.GlobalTheory.FibAdel.fibA_isAdelic c.F (E →+* ℂ) Dw.mult (part Dw a) (fun w => P.a w ^ n) P.B ha0 hsupp hBad
  have hsec : ∀ x, φ x ∈ sec Xo c a n := fun x => by
    have h1 : φ x ∈ cuspOn U Z (wtZ a n) := hrange ▸ ⟨x, rfl⟩
    have h2 := cuspOn_le U Z (wtZ a n) h1
    rw [cuspW_wtZ] at h2
    exact cusp_le_sec Xo c U a n h2
  have hne : ∀ τ, Nonempty (Idx (part Dw a τ)) := fun τ =>
    Fintype.card_pos_iff.1 ((dim_eq_card _) ▸ dim_pos (hanti τ))

  have hline : lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) (fun w => (vAdd w (P.a w ^ n) : ℝ)) = n * P.degTh := by
    simp only [PtData.degTh, lineDeg, vAdd_pow', Int.cast_mul, Int.cast_natCast, Real.log_pow]
    have hf := fin_mul (ρ := fun w => (vAdd w (P.a w) : ℝ)) (hsupp1.subset fun w hw => by simpa [Function.mem_support] using hw) (lw c.F)
    simp only [mul_assoc]
    rw [← mul_finsum, ← Finset.mul_sum]
    ring

  have hterm : ∀ τ : E →+* ℂ, ¬ τ (H.rt : E) = H.rt0 →
      (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2 = 0 := fun τ hτ => by
    have hm : Dw.mult τ = 0 := by simp [Datum.mult, hτ, hD.q]
    have hm' : (Dw.mult τ : ℝ) = 0 := by rw [hm]; simp
    rw [dim_eq_one_of_zero _ (hanti τ) hm, hm', div_zero, zero_mul]
    simp
  have hpsi : ∀ τ : Psi H,
      (size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) * detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) -
        Real.log (dim (part Dw a τ.1)) / 2 =
      (size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2 := fun τ => by
    have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
    have hl : P.degLie τ.1 = c₁ := by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]
    have hm' : (Dw.mult τ.1 : ℝ) = Dw.p := by rw [hm]
    rw [hm', show detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) = P.degLie τ.1 from rfl, hl]
  have hsum := (Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
    (fun τ => (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2)).symm
  have h0 : ∑ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) = 0 :=
    Finset.sum_eq_zero fun τ _ => hterm τ.1 τ.2
  rw [h0, add_zero] at hsum
  have hsum' : ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) :=
    Finset.sum_congr rfl fun τ _ => hpsi τ
  have hlieSum : ∑ τ : Psi H, P.degLie τ.1 = (Fintype.card (Psi H) : ℝ) * c₁ := by
    rw [Finset.sum_congr rfl fun τ _ => (show P.degLie τ.1 = c₁ by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbound : defBound Dw a n c₁ = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
      Real.log (dim (part Dw a τ.1)) / 2) + (Fintype.card (Psi H) : ℝ) * ((n : ℝ) / 2 * c₁) +
      (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) := by
    have hS : ∑ τ : Psi H, ((((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) + (n : ℝ) / 2) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2)) = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2) + ∑ _τ : Psi H, ((n : ℝ) / 2 * c₁) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [defBound, hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hth hn
  rw [hlieSum] at hmul
  refine ⟨TIdx (part Dw a), inferInstance, inferInstance, ⟨fun τ => (hne τ).some⟩, locLat (P.matA a n), P.matY a n, φ,
    GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily c.F _ (P.matA a n) hlat, hdet, ?_, hinj, hrange, fun x hx w v hv =>
      (hint x (φ x) (hsec x) (hreads x)).1 hx w v hv, fun σ x z hz => (hint x (φ x) (hsec x) (hreads x)).2 σ z hz⟩
  refine le_trans ?_ hslope
  have htot : ∑ t : E →+* ℂ, ((size (part Dw a t) : ℝ) / (Dw.mult t : ℝ) *
      detDeg (fun w => P.B w t) (fun σ => P.X σ t) - Real.log (dim (part Dw a t)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) := by
    rw [hsum]
    convert hsum' using 3
  rw [hline, htot, hbound]
  nlinarith [hmul]

end GlobalTheory.DefFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' : ∀ (k Ω V : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (F : Polynomial k), algebraMap k Ω (LinearMap.det (Polynomial.aeval φ F)) = ((φ.charpoly.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  first | (exact @GlobalTheory.det_aeval_eq_prod_aroots_charpoly) | (exact GlobalTheory.det_aeval_eq_prod_aroots_charpoly) | (intros; apply GlobalTheory.det_aeval_eq_prod_aroots_charpoly  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.DomSurj

open CategoryTheory.Limits

theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem surjective_cxPts_map : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  intro k _ X _ p D hX Y _ q E hY π hπ hgen σ x
  have := isProper_of_projOver hX.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ isProper_of_projOver hY.isProjOver
  have : IsProper π := IsProper.of_comp π p

  have hsurj : Function.Surjective π := by
    have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hall : Set.range π = Set.univ := by
      rw [← Set.univ_subset_iff, ← genericPoint_closure X, hcl.closure_subset_iff]
      exact Set.singleton_subset_iff.2 ⟨_, hgen⟩
    exact Set.range_eq_univ.1 hall
  obtain ⟨y, hy⟩ := hsurj (x.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x.1) y
    (IsLocalRing.closedPoint ℂ) hy
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x.1)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback π x.1)))
    ⟨z, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨⟨pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hπ, ← Category.assoc, Category.assoc _ _ π, pullback.condition,
      ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp, x.2]
  · show (pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1) ≫ π = x.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.DomSurj
end

