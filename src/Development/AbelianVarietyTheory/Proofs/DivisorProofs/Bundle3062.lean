module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3053
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTrivialisationEqUnitMulMonomial
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem Taut.exists_ext_normBl : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  intro g _ φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ y α₁ hC
  obtain ⟨hsa, hab, hgen, hmum, hy⟩ := hC
  obtain ⟨J, -, -, hval, hbl, -, -, hji, hpre, -, -⟩ := hB
  obtain ⟨hreg, hchar, -, -, hpar, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  haveI : IsOpenImmersion i := hM.isThetaCompact.1.2.2.1
  haveI : IsCommMonObj G₁ := hsa.comm
  haveI : IsNoetherianRing C.R := C.compl.1
  haveI : IsIntegrallyClosed C.R := hmum.1.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.MinExt.exists_ext_of_minAt5 g n F Z z i OZ hM C.R G₁ hsa y α₁ hgen C.b hy
  have hon : IsPolFanOn id φ C.Q.X := hφ C.Q.X hrk
  have he : ∀ k, ∃ e : ℕ, (e : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := by
    intro k
    have hmem : (n : ℤ) • C.δ k ∈ balForms (id : ℤ → ℤ) C.Q.X := Submodule.smul_mem _ _ (hcone.mem k)
    have hnn : ∀ w, 0 ≤ ((n : ℤ) • C.δ k) w w := fun w => by
      simpa using mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
    obtain ⟨c, hc⟩ := hon.integral _ hmem hnn
    have hc0 : 0 ≤ c := by
      have hne : (n : ℤ) • C.δ k ≠ 0 := by
        refine fun h => hcone.basis.linearIndependent.ne_zero k (Subtype.ext ?_)
        exact (smul_eq_zero.1 h).resolve_left (by omega)
      have := hon.pos _ hmem hnn hne
      rw [hc] at this
      exact_mod_cast this.le
    lift c to ℕ using hc0
    exact ⟨d * c, by rw [hc]; push_cast; rfl⟩
  choose e he using he
  have hJ := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F Z i φ hφ d J hval C.R C.compl.2.1 C.b a C.Q G₁ y α₁ hsa hgen ha
    hmum C.m C.t C.δ e hpar hab hcone hdef hmono he
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.NormBlLift.lift_normBl g n F Z S i π j J hbl hji hpre C.R a y ha _
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hJ
  refine ⟨ξ, ?_⟩
  have hπ : (jK C.R ≫ ξ) ≫ π = y ≫ i := by rw [Category.assoc, hξ, ha]
  have hr : Set.range (jK C.R ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [← hpre]
    exact ⟨y p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ]⟩
  have hl := IsOpenImmersion.lift_fac j (jK C.R ≫ ξ) hr
  have : IsOpenImmersion.lift j (jK C.R ≫ ξ) hr = y := by
    rw [← cancel_mono i, ← hπ, ← hji, ← Category.assoc, hl]
  rw [← this, hl]

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantLocalFramesUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_lb_frames_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact
  have key : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · exact _root_.GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
    · exact _root_.GlobalTheory.Mum.exists_carried_frame_off_closed R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  choose V hV T hT hI using key
  refine ⟨V, T, hV, hT, ?_⟩
  intro y y' r hr σ h
  obtain ⟨hh, bc, hf, hP, hPO⟩ := a.unif σ
  have i₁ := hI y σ hh bc hf hP hPO
  have i₂ := hI y' σ hh bc hf hP hPO
  revert h
  rw [← hf]
  intro h
  exact FrameCarried.ratio_fixed U'.LG.isLB i₁ i₂ (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.1)
    (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.2) r hr h

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltration
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twistI {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} (hB : D₀.TauBimult) [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (I : TateIsoQ D D₀ oa F) (g : ℕ → D.La ≃ₗ[𝓞 E] D.La) (hiso : ∀ n a b, D.EF (g n a) (g n b) = D.EF a b)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) : TateIsoQ D D₀ oa F where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := I.ev n (g n a)
  add n hn a b := by rw [map_add (f := _)]; exact I.add n hn _ _
  lin n hn x a := by rw [map_smul]; exact I.lin n hn x _
  ker n hn a b := (I.ker n hn _ _).trans
    ⟨fun ⟨e, he⟩ => ⟨(g n).symm e, by
        have := congrArg (g n).symm he
        rwa [LinearEquiv.symm_apply_apply, map_add, LinearEquiv.symm_apply_apply, map_nsmul] at this⟩,
     fun ⟨e, he⟩ => ⟨g n e, by rw [he, map_add (f := _), map_nsmul]⟩⟩
  onto n hn p := by
    obtain ⟨b, hb⟩ := I.onto n hn p
    exact ⟨(g n).symm b, by rw [LinearEquiv.apply_symm_apply]; exact hb⟩
  tower n m hn hm a := by
    obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm (g (n * m) a)
    exact ⟨q, h₁, h₂, GlobalTheory.TorusExt.equiv_trans hB h₃ ((I.ker n hn _ _).2 (htow n m hn hm a))⟩
  isom n hn a b := by rw [← hiso n a b]; exact I.isom n hn _ _

end GlobalTheory.LowFilt

open GlobalTheory.LowFilt GlobalTheory.LowDat in
theorem GlobalTheory.LowFilt.exists_filt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
  1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ Z : Submodule (𝓞 E) Dw.La, GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨tK, ⟨m1⟩, ⟨m2⟩⟩ := C.gen
  haveI : CharZero R := hR.2
  letI := H.starRing
  have hB := C.P.D.tau_bimult
  have hT : C.P.TorsionIso := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  haveI : IsNoetherianRing R := hR.1.1
  let F₀ := AlgebraicClosure (FractionRing R)
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F₀).injective
  obtain ⟨I₀, hI₀⟩ := GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart Xo c R hR C tK m1 m2 F₀
  obtain ⟨y, hy, hcois⟩ := GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel Dw R C.P.D.toPre C.P.oD C.P.D.psi_even hB F₀ I₀
  have htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e := by
    intro n m hn hm a
    obtain ⟨q, h₁, -, z, h₃, -⟩ := I₀.tower n m hn hm a
    obtain ⟨e₁, he₁⟩ := hy (n * m) (Nat.mul_pos hn hm) a
    obtain ⟨e₂, he₂⟩ := hy n hn a
    have e₃ : (q.y : C.P.D.toPre.X) = (I₀.ev (n * m) a).y := h₁
    have e₄ : q.y = (I₀.ev n a).y - n • z := by rw [h₃]; abel
    refine ⟨m • e₁ - e₂ - z, ?_⟩
    rw [he₁, he₂, ← e₃, e₄]
    simp only [smul_sub, smul_smul]
    abel
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨Z, hZ, hZr, g, hgi, hgt, hgN, hker⟩ := _root_.GlobalTheory.LowFilt.exists_compatible_isometries Dw y hcois htow (_root_.GlobalTheory.UChart.Fam.finrank_le_min Xo c R hR C) l.M' hM
  refine ⟨Z, hZ, hZr, tK, m1, m2, fun F _ _ _ => ?_⟩
  let I₁ := twistI hB I₀ g hgi hgt
  have hI₁ : XFLevel C tK m1 m2 F₀ I₁ := by
    refine ⟨hI₀.1, fun k a σ hk x hx => hI₀.2 k a σ hk x ?_⟩
    have hk1 : 1 ≤ k ∧ k ∣ l.M' := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨l.A_pos, Nat.dvd_lcm_right _ _⟩
      · exact ⟨by have := l.three_le; omega, Nat.dvd_lcm_left _ _⟩
    obtain ⟨f, f₁, -, f₃, -⟩ := hT F₀ k hk1.1
    rw [f₁] at hx ⊢
    rw [hx]
    refine (f₃ _ _).2 ((I₀.ker k hk1.1 _ _).2 ?_)
    obtain ⟨e, he⟩ := hgN k a
    obtain ⟨j, hj⟩ := hk1.2
    exact ⟨j • e, by rw [smul_smul, ← hj]; exact he⟩
  obtain ⟨I, hIl, hIy⟩ := GlobalTheory.T.exists_levelIsometry_extension_algClosed Xo c R hR C tK m1 m2 I₁ hI₁ F
  refine ⟨I, hIl, fun n hn a => ?_⟩
  rw [_root_.GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff R _ hB F n hn, hIy, ← hker n hn a]
  obtain ⟨e, he⟩ := hy n hn (g n a)
  change (∃ e, (I₀.ev n (g n a)).y = n • e) ↔ _
  constructor
  · rintro ⟨e', he'⟩; exact ⟨e + e', by rw [he, he', smul_add, add_comm]⟩
  · rintro ⟨e', he'⟩; exact ⟨e' - e, by rw [smul_sub, ← he', he, add_sub_cancel_right]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_lowBase_of_trait : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn ho V _ _ _ hV hd b PB r c hc
  obtain ⟨F, V₁, _, _, _, f₁, v, hs, hV₁, hd₁, hi₁, hf₁, hl₁, β₁, β₁₂, hp₁, hq₁, hL₁, hc₁⟩ :=
    _root_.GlobalTheory.LowChart.exists_fibrePow_point_of_polAV n hn ho V hV hd b PB r c hc
  obtain ⟨L, V', _, _, _, f, κ, e, hh, hV', hd', hi, hf, hl, hκ, hb, B', _, β', β'', β₂, β₂', hp, hp', hq, hq', hL, hx⟩ :=
    _root_.GlobalTheory.LowLift.main n hn ho PB.g F r V₁ hV₁ hd₁ (f₁.comp b) v hs
  have es : spMap (f.comp f₁) = spMap f ≫ spMap f₁ := by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hl' : IsLocalHom (f.comp f₁) := RingHom.isLocalHom_comp f f₁
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f.comp f₁, κ, e, hh, hV', hd', hi.comp hi₁,
    hf.comp hf₁, hl', hκ, ?_, B', inferInstance, β' ≫ β₁, β'', β₂ ≫ β₁₂, β₂', ?_, hp', isSquare_comp hq hq₁, hq', ?_, ?_⟩
  · rw [hb, RingHom.comp_assoc]
  · rw [es]
    exact hp.comp hp₁
  · have h1 : LBIso ((LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ PB.A PB.L).pull (β₂ ≫ β₁₂)) :=
      lbIso_pull_comp hL₁ β₂ rfl
    exact LBIso.trans (pull_isLB (LB.isLB_linComb PB.isLB _ _) _) (pull_isLB (LowChart.siegAt F v _ hs).isLB _)
      (pull_isLB (LB.isLB_linComb L.T.M.isLB _ _) _) h1.symm hL
  · intro a
    obtain ⟨x, h1, h2, h3⟩ := hx a
    refine ⟨x, h1, ?_, h3⟩
    rw [← Category.assoc, h2, Category.assoc, hc₁, es, Category.assoc]

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_monomialFamily_coords_over_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  first | exact @GlobalTheory.UCanon.Periods.exists_divFrom | exact GlobalTheory.UCanon.Periods.exists_divFrom | (intros; apply GlobalTheory.UCanon.Periods.exists_divFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkPointExtensionOfDividedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivTorsRat

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_char_descend {X K F : Type} [Group X] [Field K] [Field F] (f : K →+* F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (t : X →* Fˣ) (ht : t ^ k = 1) :
    ∃ t₀ : X →* Kˣ, (Units.map f.toMonoidHom).comp t₀ = t := by
  have hinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : NeZero k := ⟨hk⟩
  have hr : ∀ x, t x ∈ (Units.map f.toMonoidHom).range := fun x => by
    have h1 : ((t x : Fˣ) : F) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ht]; rfl
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective f.injective).eq_pow_of_pow_eq_one h1
    exact ⟨(hζ.isUnit hk).unit ^ i, Units.ext (by simpa using hi)⟩
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (t.codRestrict _ hr), MonoidHom.ext fun x => ?_⟩
  exact MonoidHom.apply_ofInjective_symm hinj _

theorem exists_qkExt_of_b {V : Type} [CommRing V] [IsDomain V] {Q : DegPre V} (hB : Q.TauBimult) {K F : Type} [Field K]
    [Field F] [Algebra (FractionRing V) K] [Algebra (FractionRing V) F] (f : K →+* F)
    (hf : f.comp (algebraMap (FractionRing V) K) = algebraMap (FractionRing V) F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (p : QkPt Q F k) (hp : p.y = 0) (q : QkPt Q K k) (hq : q.y = 0)
    (hb : p.g.b.left = spMap f ≫ q.g.b.left) : ∃ p₀ : QkPt Q K k, QkExt f p₀ p := by
  have hb' : p.g.b = (gtExt Q f hf q.g).b := (Over.OverMorphism.ext hb).trans (gtExt_b f hf _).symm
  have np : k • p.g = 0 := by rw [qk_nsmul hB, hp, map_zero]
  have nq : k • q.g = 0 := by rw [qk_nsmul hB, hq, map_zero]
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := p.g + -(gtExt Q f hf q.g)) (by rw [add_b, neg_b, hb', mul_inv_cancel])
  have tk : t ^ k = 1 := by
    have : torusPt Q F (Additive.ofMul (t ^ k)) = torusPt Q F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← ht, nsmul_add, smul_neg, ← map_nsmul, np, nq, ofMul_one, map_zero, map_zero, neg_zero,
        add_zero]
    exact torusPt_injective this
  obtain ⟨t₀, rfl⟩ := exists_char_descend f hk hζ t tk
  have t0 : t₀ ^ k = 1 := MonoidHom.ext fun x => Units.map_injective (f := f.toMonoidHom) f.injective (by
    have := DFunLike.congr_fun tk x
    rw [MonoidHom.pow_apply, map_pow, MonoidHom.one_apply, map_one]
    exact this)
  refine ⟨qkMk hB 0 (q.g + torusPt Q K (Additive.ofMul t₀)) ?_, (qkExt_iff hB f hf _ _).2 (qk_ext hp ?_)⟩
  · simp only [nsmul_add, nq, ← map_nsmul, ← ofMul_pow, t0, ofMul_one, map_zero, zero_add]
  · show p.g = gtExt Q f hf (q.g + torusPt Q K (Additive.ofMul t₀))
    rw [map_add (f := _), GlobalTheory.QkNumberField.gtExt_torusPt, ← ht]
    abel

theorem exists_ptEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) (T : Over S') (b : T.left ⟶ S) (hb : b = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  refine ⟨MulEquiv.ofBijective (pushHom gp T) ⟨fun x y e => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (gp.1.lift y.left T.hom (Over.w y)) (gp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩

theorem exists_etaA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B W : Type} [CommRing B] [CommRing W] {b : Geo.Tor.Base l B} {σ : B →+* W} (o : Obj D l b (spMap σ)) {F : Type} [Field F]
    [IsAlgClosed F] (j : W →+* F) (x : Over.mk (spMap j) ⟶ o.t.G) (hx : x ^ l.A = 1) :
    ∃ a, x.left = spMap j ≫ (o.etaA a).left := by
  obtain ⟨-, I, -, h, -⟩ := o.geom F (spMap j) (j.comp σ) (by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos x).1 hx
  refine ⟨a, ?_⟩
  rw [← ha, ← h]
  simp

theorem exists_qkExt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  intro E _ _ _ H D' l c L R _ _ _ _ t P iw I _ s ε e hε hs ⟨g, hD, hdiv⟩ p hp
  have hB := P.D.tau_bimult
  have hM : 0 < l.M' := (LowDat.lowLevel l).A_pos
  let K := FractionRing R
  let F := AlgebraicClosure K
  let j : L.W →+* F := (algebraMap K F).comp ((algebraMap R K).comp iw)
  have hj : spMap j = (TF (R := R) F).hom ≫ spMap iw := by
    show _ = (jFK (R := R) F ≫ jK R) ≫ spMap iw
    simp only [j, jFK, jK, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have gp : IsGrpPullback P.D.toPre.P.A L.D.P.A (spMap iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    pull_grp hD
  obtain ⟨ρ₁, h₁⟩ := exists_ptEquiv gp (TF (R := R) F) (spMap j) hj
  obtain ⟨ρ₂, h₂⟩ := exists_ptEquiv L.ab.1 (Over.mk (spMap j)) (spMap j) (Category.comp_id _).symm
  have hbk : p.g.b ^ l.M' = 1 := by rw [← nsmul_b, qk_nsmul hB, hp, map_zero, zero_b]
  obtain ⟨a, ha⟩ := exists_etaA L.o j (ρ₂.symm (ρ₁ p.g.b)) (by
    show _ ^ l.M' = 1
    rw [← map_pow, ← map_pow, hbk, map_one, map_one])
  obtain ⟨q, hq, hqb⟩ := GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate L P.D.toPre P.oD iw s ε e g hD hε hs hdiv a
  have hζ : IsPrimitiveRoot (⟨zeta l.M', c.zeta_mem⟩ : c.F) l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M' hM.ne')
      Subtype.val_injective
  refine exists_qkExt_of_b hB (algebraMap K F) (RingHom.comp_id _) hM.ne'
    (hζ.map_of_injective ((algebraMap R K).comp (iw.comp L.b)).injective) p hp q hq ?_
  have e₂ := h₂ (ρ₂.symm (ρ₁ p.g.b))
  rw [ρ₂.apply_symm_apply, ha, h₁] at e₂
  refine gp.1.hom_ext (e₂.trans (Eq.symm ((Category.assoc _ _ _).trans
    ((congrArg (spMap (algebraMap K F) ≫ ·) hqb).trans ?_)))) ?_
  · rw [hj]
    show _ = (((spMap (algebraMap K F) ≫ jK R) ≫ _) ≫ _) ≫ _
    simp only [Category.assoc]
  · exact (Over.w p.g.b).trans ((Over.w (extMap (R := R) (algebraMap K F) (RingHom.comp_id _) ≫ q.g.b)).symm)

end GlobalTheory.DivTorsRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTranslatesConvergentLiftDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem exists_translates_lift : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
      translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨z, hz, h1, hJ⟩ := _root_.GlobalTheory.ZConv.zconv hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨hI, h2⟩ := _root_.GlobalTheory.SmallRoute.zdeg_mul_liftT hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  exact ⟨z, hz, Filter.Eventually.of_forall h1, h2.trans (_root_.GlobalTheory.SmallRoute.sum_integral_translates_outer_eq hL W t i j M hM Θ' F hB g₁ z hI hJ)⟩

end GlobalTheory.SmallRoute

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.Poinc.Sep.MkMember

theorem exists_uMem : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → Q.IsMonomialTau t δ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ 𝔪 : UMem X₁ z₁ act V₁ ev Q.X (fun k => ρ (t k)) δ, SharpRef W Q ρ 𝔪.D.toPre 𝔪.e₈ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact V _ _ _ Q m t δ ht hsym hnn hmono V₁ _ _ _ ρ hCN hρi hρf D₀ e₀ href G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb ev hloc hreg hcomm
  obtain ⟨yK, hyK, hy⟩ := _root_.GlobalTheory.Poinc.Sep.valPt_lies_over g n F Z i W X₁ z₁ V₁ ev y hreg hcomm
  subst hy
  obtain ⟨A, φ, -, cart, hlbA⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds yK X₁.ρ.P
  obtain ⟨wl, hwl⟩ := LBIso.symm hlbA
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hactc⟩ := hact
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hlift⟩ := GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback g n (cycAway n) (zetaAway n) F W _ _ X₁.ρ.P A X₁.u (spMap yK) φ c hc pr hpr huniv hbun cart (LBIso.symm hlbA)
  have hsharp : SharpOver F W A (spMap yK ≫ X₁.u) := ⟨c', hc', pr', hpr', huniv', hbun'⟩
  obtain ⟨D, ⟨U⟩⟩ := _root_.GlobalTheory.PowE8.exists_unif_pow8 g n (cycAway n) (zetaAway n) F W hW V₁ hCN D₀ G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A hsharp
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨e, hsr, heq⟩ := GlobalTheory.T.uniformisation_eighthPower_data_equivariant g n (cycAway n) (zetaAway n) F W hW V Q V₁ ρ hCN hρi hρf D₀ e₀ href G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A c' hc' pr' hpr' huniv' hbun' (powObj G₀ 8) hS8 D U
  refine ⟨{ cn := hCN, loc := hloc, reg := hreg, yK := yK, yK_eq := hyK, D := D, e₈ := e, G := powObj G₀ 8, semi := hS8, A := A, U := U, φ := φ, cart := cart, wl := wl, wl_gen := hwl, equiv := ?_, psi := ?_ }, hsr⟩
  · intro a a' h
    obtain ⟨aA, h1, h2⟩ := hlift (act a) (fun u v => a u v) (hactc a)
    obtain ⟨E, hE, hE2⟩ := heq a a' h aA h1
    exact ⟨E, hE ▸ h2, hE2⟩
  · exact _root_.GlobalTheory.Poinc.Sep.psi_unit_mono W X₁.posW V V₁ Q ρ hρi m t δ hsym hnn ht hmono D.toPre e hsr

end GlobalTheory.Poinc.Sep.MkMember
end
end

