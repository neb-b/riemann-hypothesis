module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesOddRankGap
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section
namespace GlobalTheory.ParamMatch

theorem lamAt_anti_fin {Rk : Ranks} (h : HCParam Rk) {n : ℕ} (hn : n ≤ Rk.r) :
    StrictAnti fun a : Fin n => Formalism.L2.NTheta.lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have h1 := Formalism.L2.NTheta.lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at h1
  have h2 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ (b : ℕ) - a)
  show Formalism.L2.NTheta.lamAt h b < Formalism.L2.NTheta.lamAt h a
  linarith

theorem enum_fst {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum S lam ε)
    (f : Fin n → ℚ) (hf : StrictAnti f) (hS : S.image Prod.fst = Finset.univ.image f) (a : Fin n) :
    lam a = f a := by
  obtain ⟨h1, q, hq, rfl⟩ := he
  have h3 : StrictAnti q := fun a b hab => by
    have := h1 hab
    rw [hq, hq] at this
    exact_mod_cast this
  have h4 : Finset.univ.image q = Finset.univ.image f := by
    rw [← hS, Finset.image_image]; rfl
  have h5 : q = f := by
    refine (h3.range_inj hf).1 ?_
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) h4
    simpa [Finset.coe_image] using this
  rw [hq, h5]

theorem lamAt_b' {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + j) = -h.b j := by
  have hc : ∀ (x y : ℕ) (hx : x < Rk.m) (hy : y < Rk.m), x = y → h.b ⟨x, hx⟩ = h.b ⟨y, hy⟩ := by
    rintro x _ _ _ rfl; rfl
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  rw [hc _ _ _ j.2 (by omega)]

theorem lamAt_v' {Rk : Ranks} (h : HCParam Rk) (j : Fin (Rk.k - 1)) :
    Formalism.L2.NTheta.lamAt h j = h.v j := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_left j.2]

theorem parA_fst (D : D7) (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parA (Ptw D) 0 ρ).image Prod.fst = Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  have hk := D.R.m_add_three_le_k
  have hv : (Ptw D).v ρ = (D.hc ρ).v := rfl
  have hb : (Ptw D).b ρ = (D.hc ρ).b := rfl
  ext x
  simp [parA, TPar.Dpar]
  rw [hv, hb]
  constructor
  · rintro (⟨a, rfl, -⟩ | ⟨a, rfl⟩ | ⟨a, rfl, -⟩)
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
    · exact ⟨⟨a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_v' _ a⟩
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    unfold Ranks.r at ha
    by_cases h1 : (a : ℕ) < D.R.k - 1
    · exact Or.inr (Or.inl ⟨⟨a, h1⟩, (lamAt_v' _ ⟨a, h1⟩).symm⟩)
    · let c : Fin D.R.m := ⟨a - (D.R.k - 1), by omega⟩
      have hc : Formalism.L2.NTheta.lamAt (D.hc ρ) a = -(D.hc ρ).b c := by
        rw [← lamAt_b' _ c]; congr 1; simp only [c]; omega
      rw [hc]
      by_cases h2 : (c : ℕ) = 0 ∨ Even (c : ℕ)
      · exact Or.inr (Or.inr ⟨c, rfl, h2⟩)
      · push_neg at h2
        exact Or.inl ⟨c, rfl, h2.1, h2.2⟩

theorem tauE_inj {D : D7} {τ ρ : D.what₂.Tau} (h : tauE D τ = tauE D ρ) : τ = ρ :=
  D.eTau.injective (Subtype.ext (Formalism.IndefR.Conj.emb_injective h))

open Formalism.FrobeniusOrbits in
theorem tauE_ne_conj' {D : D7} (τ ρ : D.what₂.Tau) : tauE D τ ≠ (starRingEnd ℂ).comp (tauE D ρ) := by
  intro h
  unfold tauE at h
  rw [Formalism.IndefR.Conj.conj_comp_emb] at h
  have e1 : (D.eTau τ).1.1.2 = ((D.eTau ρ).1 * D.R.cc).1.2 :=
    congrArg (fun g : D.R.GG => g.1.2) (Formalism.IndefR.Conj.emb_injective h)
  have hc := Formalism.IndefR.Conj.snd_side (D := D) false
  simp only [Bool.false_eq_true, if_false] at hc
  rw [show ((D.eTau ρ).1 * D.R.cc).1.2 = (D.eTau ρ).1.1.2 * (D.R.cc).1.2 from rfl] at e1
  rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2, one_mul, hc] at e1
  exact absurd e1 (by decide)

theorem lab_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (ρ : D.what₂.Tau) :
    lab (sg0 D A) ρ = ρ ∧ labE (sg0 D A) ρ = tauE D ρ := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hb : ∀ τ, labE D.what₂.embLL τ = tauE D τ := fun τ => Formalism.IndefR.Conj.labE_base τ
  rw [hs]
  refine ⟨?_, hb ρ⟩
  have hex : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (hb ρ)⟩
  unfold lab
  rw [dite_eq_left hex]
  rcases hex.choose_spec with h | h
  · rw [hb] at h; exact tauE_inj h
  · rw [hb] at h; exact absurd h (tauE_ne_conj' _ _)

theorem parAt_fst {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parAt (Wc D i) (sg0 D A) ρ).image Prod.fst =
      Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  obtain ⟨h1, h2⟩ := lab_base R ρ
  have hpq : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    have hk := D.R.m_add_three_le_k
    have hi := i.2
    rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2]
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [parAt, if_pos (by rw [h1]; exact h2), kapAt, h1]
  generalize ((Wc D i).sig (tauE D ρ)).1 = p at hpq ⊢
  generalize ((Wc D i).sig (tauE D ρ)).2 = q at hpq ⊢
  have ho : Odd (p + q) := hpq ▸ Formalism.L2.NTheta.odd_r D.R
  ext x
  simp only [Formalism.L2.NTheta.holPar, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp_def, Formalism.L2.NTheta.holEnt_kapW _ _ _ ho]
  constructor
  · rintro ⟨(a | c), rfl⟩
    · exact ⟨⟨a, by omega⟩, rfl⟩
    · exact ⟨⟨p + c, by omega⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    by_cases hap : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hap⟩, rfl⟩
    · refine ⟨Sum.inr ⟨a - p, by omega⟩, ?_⟩
      simp only [Sum.elim_inr]
      congr 1
      omega

end GlobalTheory.ParamMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors
open GlobalTheory.TorusExt

private theorem sumF_mul_left {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x y : Ix → F} {s t : F} (a : F) (h : SumF I F x s)
    (hy : ∀ i, y i = a * x i) (ht : t = a * s) : SumF I F y t := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, happ⟩ := h
  let f : F →ₗ[R] F :=
    { toFun := fun u => a * u
      map_add' := fun u v => mul_add a u v
      map_smul' := fun r u => by
        change a * ((algebraMap R (FractionRing R) r) • u) = (algebraMap R (FractionRing R) r) • (a * u)
        rw [Algebra.smul_def, Algebra.smul_def]
        ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, ht.symm⟩, fun i => ⟨x i, hx i, (hy i).symm⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := happ n
  refine ⟨S, fun T hT => ?_⟩
  have hm := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at hm
  have e : f (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i := by
    change a * (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i
    rw [mul_sub, Finset.mul_sum, ht]
    simp only [hy]
  rw [e] at hm
  exact hm


attribute [local instance] gtGroup in
theorem exhaust_of_labels : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (C : Type) (g : C → GtPtF D.toPre (FractionRing R)) (x : C → (TFK (R := R) (FractionRing R) ⟶ A.A)), (∀ c, ∃ o, GtPtF.IsNsmul N (g c) o ∧ o.IsZero) → (∀ c c', g c = g c' → x c = x c') → (∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) N) (y : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) N p y → ∃ c, y.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left) → ∀ b : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ D.toPre.P.A, b ^ N = 1 → ∃ c, b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (g c).b.left := by
  intro hLL R _ _ _ I hI D A G _ _ hSA U N hN C g x htor hfun hcov b hb
  have hB : D.toPre.TauBimult := D.tau_bimult
  have hN0 : N ≠ 0 := by omega
  have hf : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap (FractionRing R) (FractionRing R)) = (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) :=
    RingHom.ext fun _ => rfl
  obtain ⟨fT, hT⟩ := GlobalTheory.TorsionIso.torsion_eq hLL R I hI D A G hSA U (AlgebraicClosure (FractionRing R)) N hN
  obtain ⟨hT1, -, hT3, -⟩ := hT
  have hi : GtPtF.IsIota 0 (0 : GtPtF D.toPre (AlgebraicClosure (FractionRing R))) := by
    have hz : (0 : GtPtF D.toPre (AlgebraicClosure (FractionRing R))).IsZero := (isZero_iff_eq _).2 rfl
    obtain ⟨hb, hv⟩ := (isZero_iff_val _).1 hz
    refine (isIota_iff_val _ _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (th D.toPre (T := TF (R := R) (AlgebraicClosure (FractionRing R))) y J) := isCub_cubV D.toPre.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) (AlgebraicClosure (FractionRing R)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm
  let P : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → QkPt D.toPre (AlgebraicClosure (FractionRing R)) N :=
    fun h => ⟨0, h.1, N • h.1, (isNsmul_iff_eq _ _ _).2 rfl,
      h.2.symm ▸ hi⟩
  have hPy : ∀ h, (P h).y = 0 := fun _ => rfl
  have hPg : ∀ h, (P h).g = h.1 := fun _ => rfl
  have hEq : ∀ h h', QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (P h) (P h') → h = h' := by
    intro h h' e
    obtain ⟨z, hy, t, ht, hg⟩ := e
    change 0 = 0 + N • z at hy
    simp only [zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : N = 0) hN0
      · exact h3
    have ht0 : t = 0 := isIota_unique (hz ▸ ht) hi
    have hg := (isAdd_iff_eq _ _ _).1 hg
    rw [hPg, hPg, ht0, add_zero] at hg
    exact Subtype.ext hg.symm
  haveI : Finite {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} := by
    have hc := GlobalTheory.UT.card_qk hLL R I hI D (AlgebraicClosure (FractionRing R)) N hN
    haveI : Finite (Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N))) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hN0)
    refine Finite.of_injective (β := Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)))
      (fun h => Quot.mk (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)) (P h)) fun h h' e => hEq h h' ?_
    exact (equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact e)
  have hcx : ∀ h, ∃ c, (fT (P h)).left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left :=
    fun h => hcov (P h) (fT (P h)) (hPy h) ((hT1 _ _).2 rfl)
  choose c hc using hcx
  have hgc : ∀ c, N • g c = 0 := by
    intro c
    obtain ⟨o, ho, hz⟩ := htor c
    rw [isNsmul_iff_eq] at ho
    rw [isZero_iff_eq] at hz
    rw [← ho, hz]
  let Φ : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} :=
    fun h => ⟨gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)), by rw [← map_nsmul, hgc, map_zero]⟩
  have hΦ : Function.Injective Φ := by
    intro h h' e
    have e1 : g (c h) = g (c h') := GlobalTheory.Balanced.gtExt_injective _ hf D.toPre (congrArg Subtype.val e)
    have e2 := hfun _ _ e1
    apply hEq
    apply (hT3 _ _).1
    apply Over.OverMorphism.ext
    rw [hc h, hc h', e2]
  obtain ⟨g', hg'b, hg'N⟩ :=
    exists_nsmul_eq_of_pow_eq (D := D.toPre) (F := (AlgebraicClosure (FractionRing R))) hN0 0 (hb.trans zero_b.symm)
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hΦ) ⟨g', hg'N⟩
  refine ⟨c h, ?_⟩
  have e1 : g' = gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)) := (congrArg Subtype.val hh).symm
  rw [← hg'b, e1, gtExt_b, Over.comp_left, extMap_left]

section Scale
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem exists_scale {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) {c : F} (hc : c ≠ 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ z J, Good L z J →
      (val t' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val t (𝟙 _) z J).val := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom : F →* Γ(Spec (CommRingCat.of F), ⊤)) (Units.mk0 c hc)
  refine ⟨GlobalTheory.UU.scaleGen u t, GlobalTheory.UU.scaleGen_isGen u ht, fun z J hJ => ?_⟩
  rw [GlobalTheory.UU.val_scaleGen u t (𝟙 _) hJ, Units.val_mul, ← gs_unit (𝟙 _) z ⊤ trivial u, ← CoefBasic.cst_eq]
  rfl

theorem coef_scale {D : DegPre R} {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen) {c : F}
    (h : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val w (𝟙 _) z J).val)
    (s : Fam D F k) (χ : D.X) : coef s g w' χ = c * coef s g w χ := by
  apply CoefBasic.coef_eq
  intro z J hJ
  have hx := CoefBasic.isCoef_coef g hw χ s z J hJ
  rw [h z J hJ]
  rw [CoefBasic.cst_eq] at hx ⊢
  rw [map_mul]
  linear_combination (CoefBasic.cstH (R := R) z c) * hx

end Scale

theorem liesOver_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → LiesOver U w₀ g w x fr → ∀ c : F, c ≠ 0 → ∃ (w' : Frm D.toPre F 1 g.b) (fr' : FrAt x), w'.IsGen ∧ fr'.IsGen ∧ LiesOver U w₀ g w' x fr' ∧ (∀ (s : Fam D.toPre F 1) χ, c * coef s g w' χ = coef s g w χ) ∧ ∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val fr (𝟙 _) z J).val := by
  intro R _ _ I _ D A G _ _ U F _ _ w₀ g w x fr hw hfr hL c hc
  obtain ⟨w', hw', hw'v⟩ := exists_scale (R := R) (F := F) w hw (inv_ne_zero hc)
  obtain ⟨fr', hfr', hfr'v⟩ := exists_scale (R := R) (F := F) fr hfr hc
  refine ⟨w', fr', hw', hfr', ?_, ?_, ?_⟩
  · intro k hk wk hwk hwkg s s' v hexp hval
    have hck : c ^ k ≠ 0 := pow_ne_zero k hc
    obtain ⟨wk0, hwk0g, hwk0v⟩ := exists_scale (R := R) (F := F) wk hwkg hck
    have h1 : SumF I F (coef s' g wk0) (c ^ k * v) := by
      refine hL k hk wk0 ?_ hwk0g s s' (c ^ k * v) hexp ?_
      · intro z J hJ
        apply Units.ext
        have e : CoefBasic.cstH (R := R) z (c ^ k) * (CoefBasic.cstH (R := R) z c⁻¹) ^ k = 1 := by
          rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc, one_pow, map_one]
        rw [hwk0v z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw'v z J hJ]
        linear_combination ((val w (𝟙 _) z J).val) ^ k * e
      · intro z J hJ
        have hv := hval z J hJ
        rw [hv, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
          Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
          show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
            @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
        simp only [id, CoefBasic.cst_eq, map_mul, map_pow]
        ring
    have h2 : ∀ χ, coef s' g wk0 χ = c ^ k * coef s' g wk χ := fun χ => coef_scale g hwkg hwk0v s' χ
    exact sumF_mul_left (c ^ k)⁻¹ h1
      (fun χ => by rw [h2, ← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
      (by rw [← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
  · intro s χ
    rw [coef_scale g hw hw'v s χ, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul]
  · intro z J hJ
    rw [show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
    simp only [CoefBasic.cst_eq, id]

end GlobalTheory.Poinc.Tors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhdStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_finite_free_nbhd : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  first | exact @GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | exact GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | (intros; apply GlobalTheory.GenFinEtField.exists_affine_finite_etale_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliarySplitPlaceNotMemFinsetAlt
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AuxiliarySplitPlace

theorem exists_auxiliarySplitPlace_notMem_finset : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ U : AuxiliaryPlaceHermitianSpace V, U.u ∉ S := fun D V S =>
  exists_auxiliaryPlace_not_mem_finset (isCMExt_host D) (isHermND_gram V) (SelfDual.isSelfDualAt_frameLat D V) S

end GlobalTheory.AuxiliarySplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellUAbsorbUnip
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.WeylUnipotentShell

section BlockKeep

variable {R : Type} [CommRing R] {n : ℕ}

def blockKeep (a b : Fin n) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (a ≤ i ∧ i ≤ b) ∧ (a ≤ j ∧ j ≤ b) then A i j else (1 : Matrix (Fin n) (Fin n) R) i j

theorem blockKeep_one (a b : Fin n) : blockKeep a b (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j; unfold blockKeep; split_ifs <;> rfl

theorem blockKeep_mul (a b : Fin n) (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : blockKeep a b (A * B) = blockKeep a b A * blockKeep a b B := by
  ext i j
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hj : a ≤ j ∧ j ≤ b
    · simp only [blockKeep, Matrix.mul_apply, if_pos (And.intro hi hj)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : a ≤ k ∧ k ≤ b
      · rw [if_pos ⟨hi, hk⟩, if_pos ⟨hk, hj⟩]
      · rw [if_neg (fun h => hk h.2), Matrix.one_apply_ne (by rintro rfl; exact hk hi), zero_mul]
        rcases not_and_or.1 hk with h | h
        · rw [hA i k (lt_of_lt_of_le (not_le.1 h) hi.1), zero_mul]
        · rw [hB k j (lt_of_le_of_lt hj.2 (not_le.1 h)), mul_zero]
    · have hcol : ∀ k, blockKeep a b B k j = (1 : Matrix (Fin n) (Fin n) R) k j := fun k => if_neg (fun h => hj h.2)
      rw [Matrix.mul_apply]
      simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [blockKeep, hi, hj, and_false, if_false, true_and, Matrix.one_apply]
  · have hrow : ∀ k, blockKeep a b A i k = (1 : Matrix (Fin n) (Fin n) R) i k := fun k => if_neg (fun h => hi h.1)
    rw [Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [blockKeep, hi, false_and, if_false, Matrix.one_apply]

end BlockKeep

section Keep

variable {L : Type} [Field L] {n : ℕ}

def blockKeepGL (a b : Fin n) (g : GL (Fin n) L) (hg : g ∈ unipB L (Fin n)) : GL (Fin n) L where
  val := blockKeep a b (g : Matrix (Fin n) (Fin n) L)
  inv := blockKeep a b ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  val_inv := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 hg).1 ((mem_unipB L).1 (inv_mem hg)).1, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, blockKeep_one]
  inv_val := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 (inv_mem hg)).1 ((mem_unipB L).1 hg).1, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, blockKeep_one]

theorem blockKeepGL_mem_GU [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (a : Fin n) (g : GL (Fin n) L)
    (hg : g ∈ unipB L (Fin n)) (hG : g ∈ GU σ n) : blockKeepGL a a.rev g hg ∈ GU σ n := by
  rw [LGrp.mem_GU_iff] at hG ⊢
  intro i j
  show blockKeep a a.rev ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
    σ (blockKeep a a.rev (g : Matrix (Fin n) (Fin n) L) j.rev i.rev)
  have key : ∀ i : Fin n, (a ≤ i.rev ∧ i.rev ≤ a.rev) ↔ (a ≤ i ∧ i ≤ a.rev) := by
    intro i
    have := i.isLt
    have := a.isLt
    simp only [Fin.le_iff_val_le_val, Fin.val_rev]
    omega
  unfold blockKeep
  simp only [key]
  by_cases h : (a ≤ i ∧ i ≤ a.rev) ∧ (a ≤ j ∧ j ≤ a.rev)
  · rw [if_pos h, if_pos h.symm, hG]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), Matrix.one_apply, Matrix.one_apply, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, eq_comm (a := j)]

theorem blockKeep_eq_self (a b : Fin n) (A : Matrix (Fin n) (Fin n) L) (h1 : ∀ i j, j < i → A i j = 0)
    (h2 : ∀ i, A i i = 1) (h3 : ∀ i j, i < j → (i < a ∨ b < j) → A i j = 0) : blockKeep a b A = A := by
  ext i j
  unfold blockKeep
  split_ifs with h
  · rfl
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h3 i j hij]
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact h ⟨⟨hc.1, hij.le.trans hc.2⟩, hc.1.trans hij.le, hc.2⟩
    · rw [Matrix.one_apply_eq, h2]
    · rw [Matrix.one_apply_ne hij.ne', h1 i j hij]

end Keep

end GlobalTheory.WeylCell.WeylUnipotentShell
end
end

