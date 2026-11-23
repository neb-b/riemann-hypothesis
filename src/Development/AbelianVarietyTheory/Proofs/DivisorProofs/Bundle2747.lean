module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapEighthPowerSiegelModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_thMap_of_affine_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    IsReduced X → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U)) →
    ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hmu hn hred hP hA
  have hloc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3, h4⟩ := hA x
    exact _root_.GlobalTheory.UMin.exists_nbhd_thetaMap S G L ρ hL hρ g m n o X s q hmo hm3 hmu hn hP U h1 h2 h3 h4 x hxU
  choose W h hxW hs hT using hloc
  have hag : ∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ h i = y' ≫ h j := by
    intro i j K _ _ y y' e
    have hPK := hP K (y ≫ (W i).ι)
    obtain ⟨⟨θ, hθ⟩, -⟩ := gen_of_polFib S G L hL g K _ hPK
    have hmK : (m : K) ≠ 0 := by
      have := hmu.map (Spec.preimage (y ≫ (W i).ι ≫ s)).hom
      rw [map_natCast] at this
      exact this.ne_zero
    obtain ⟨pt, c, hc⟩ := _root_.GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m (n + 1) K _ θ hmo hmK hn hPK
    have hH : HasTh G L ρ m ((y ≫ (W i).ι) ≫ q) c := ⟨θ, pt, hθ, hc⟩
    have h1 := hT i K y c (by rw [Category.assoc] at hH; exact hH)
    have h2 := hT j K y' c (by rw [e, Category.assoc] at hH; exact hH)
    refine CrdUniq.eq_of_pCrd ?_ h1 h2
    rw [Category.assoc, Category.assoc, hs, hs, ← Category.assoc, e, Category.assoc]
  have hcov : (⨆ x, W x) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfi⟩ := GlobalTheory.ThetaGlue.glue_geom o n X s X W h hcov hs hag
  refine ⟨f, hf, fun K _ x c hH => ?_⟩
  let z : X := x.base (IsLocalRing.closedPoint K)
  have hr : Set.range x.base ⊆ Set.range (W z).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact hxW z
  let x' : Sp K ⟶ (W z).toScheme := IsOpenImmersion.lift (W z).ι x hr
  have hx : x' ≫ (W z).ι = x := IsOpenImmersion.lift_fac _ _ _
  have h1 := hT z K x' c (by rw [← Category.assoc, hx]; exact hH)
  rw [← hx, Category.assoc, hfi]
  exact h1

theorem exists_thAt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  intro g n hg hn hno F W hW P rig m hPg hSh hrig hmo hm3 hmu
  obtain ⟨hI, hN, hLN⟩ := _root_.GlobalTheory.SiegelIntegral.integral_normal_noetherian g n hg hn hno F
  letI := P.isAb.comm
  have hpos : 0 < m ^ (4 * (8 * g)) := pow_pos (by omega) _
  have hA : ∀ x : F.X, ∃ U : F.X.affineOpens, x ∈ (U : F.X.Opens) ∧ IsDomain Γ(F.X, U) ∧ IsNoetherianRing Γ(F.X, U) ∧
      IsIntegrallyClosed Γ(F.X, U) ∧ CharZero Γ(F.X, U) := fun x => by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.X.isBasis_affineOpens)
      (show x ∈ (⊤ : F.X.Opens) from trivial)
    have hne : (U : F.X.Opens) ≠ ⊥ := fun h => by simp [h] at hxU
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.affineOpen_ring_isDomain_noetherian_integrallyClosed F.X hI hN hLN ⟨U, hU⟩ hne
    exact ⟨⟨U, hU⟩, hxU, h1, h2, h3, GlobalTheory.SiegelTor.sFam_charZero_affineOpen g n F ⟨U, hU⟩ inferInstance⟩
  obtain ⟨f, hf, hT⟩ := exists_thMap_of_affine_cover F.X P.A P.L rig P.isLB hrig P.g m (m ^ (4 * (8 * g)) - 1) (cycAway n) F.X F.s (𝟙 F.X)
    hmo hm3 hmu (by rw [hPg]; omega) inferInstance (fun R _ x => by simpa using GlobalTheory.UMin.FibExist.polFib_of_point F.X P R x) hA
  exact ⟨_, f, hPg, hSh, hrig, hmo, hm3, hmu, by omega, hf, hT, hW⟩

end GlobalTheory.SiegTh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupLevelCoverEveryPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.SetupCov
open GlobalTheory.PoincChart

theorem chartAt : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := _root_.GlobalTheory.Poinc.ChartAt.exists_chart_at

theorem modelAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := _root_.GlobalTheory.Poinc.ModelAt.exists_map_model

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))


set_option maxHeartbeats 1000000 in
theorem exists_setup_cov : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro g hg n hn ho F Z z i _ hproj hZn hiz hden W hW hT l hl hln j₀
  have hlo : Odd l := Odd.of_dvd_nat ho hln
  obtain ⟨k, j₁, hk, -, hj₁, big⟩ := exists_big_ge (8 * g) l hl.two_le 0
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n l (2 * (j₀ + j₁ + k)) F hg hn ho hl hln (by omega)
  refine ⟨j₀ + j₁ + k, F'.X, q, by omega, hqfin, hqsurj, fun K _ y' => ?_⟩
  have hl3 : 3 ≤ l := by
    have h2 := hl.two_le
    have : l ≠ 2 := fun e => by rw [e] at hlo; exact absurd hlo (by decide)
    omega
  have hk3 : 3 ≤ (l ^ (2 * (j₀ + j₁ + k))) ^ 2 :=
    le_trans (le_trans hl3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := hlo.pow.pow
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, x, yR, V, f, hRfg, hfrac, hRic, hxs, hyR, hgen, hst, hV, hf, hfV⟩ :=
    chartAt n (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2) F.X F'.X Z F.s F'.s q i inferInstance (by omega)
      (Nat.mul_pos (by omega) (pow_pos (pow_pos hl.pos _) _)) inferInstance inferInstance hqfin hqet hqsurj K y'
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) x t' hxs
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ x t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (x ≫ q) := sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q x ψ hsh' hψ hψL
  have := t.ab.comm
  have hS : ZH.HypS t.A t.L := ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩
  have hu : IsUnit (l : cycAway (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    ((dvd_pow_self l (by omega : 2 * (j₀ + j₁ + k) ≠ 0)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  haveI : NeZero ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := ⟨by have := hl.pos; positivity⟩
  obtain ⟨lev₀, -⟩ := GlobalTheory.ThetaSysOfObj.exists_level R t
  have e : (l ^ (2 * (j₀ + j₁ + k))) ^ 2 = (l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2 := by ring
  obtain ⟨lev, -⟩ : ∃ lev : Out.Level t.pol ((l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2)
      (unitOn (Units.map (algebraMap _ R).toMonoidHom b.ζ)), True := by
    rw [← e]; exact ⟨lev₀, trivial⟩
  obtain ⟨S, ρ, hR, φ, hreg, -, hNS, hrS, hgS, hpb, hL, -⟩ :=
    _root_.GlobalTheory.ThetaRealAt.exists_thetaSys_real_at _ Ω R hRfg hfrac (yR (IsLocalRing.closedPoint K)).asIdeal (yR (IsLocalRing.closedPoint K)).isPrime t.pol l k (2 * (j₀ + j₁))
      b.ζ hl hlo hk (by omega) hu hS lev
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hbase : spMap R.val.toRingHom ≫ x ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ) := by
    rw [hqs, ← Category.assoc x, hxs]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hp0 : (spMap R.val.toRingHom ≫ x ≫ q ≫ i) ≫ z = spMap ((algebraMap _ Ω).comp κ) := by
    simp only [Category.assoc, hiz]
    exact hbase
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := _root_.GlobalTheory.Poinc.exists_ratModel_normalization (cycAway n) _ Ω κ ((IsFinite.SpecMap_iff _).1 hfin) Z z
    inferInstance inferInstance inferInstance _ hp0 hst
  obtain ⟨φM, hφπ, hφreg⟩ := modelAt _ Ω M Z π hMn hπ R hfrac hRic V f hV hf (by rw [hcomp, hfV])
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hsharp : SharpOver F W ρ.P (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) :=
    sharpOver_pullback _ _ _ _ F W _ _ t.pol ρ.P (x ≫ q) _ φ hsh hpb hL
  refine ⟨Setup.mk _ Ω S ρ (big (2 * (j₀ + j₁)) (by omega) _ Ω S (hgS.trans ?_) hNS hrS)
    (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) hsharp
    (fun w => by rw [← Category.assoc, ef]; exact hgen w) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ
    (by rw [hcomp]; simp only [Category.assoc]; rw [← Category.assoc (spMap S.R.val.toRingHom), ef]) hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) inferInstance hiz hden
    hW hT κ (by rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]; exact hbase),
    yR ≫ φM, ?_, ?_, ?_⟩
  · rfl
  · show S.r * S.N = _
    rw [hrS, hNS]; ring
  · show (yR ≫ φM) ≫ π = _
    rw [Category.assoc, hφπ, hfV, ← Category.assoc, hyR]
  · intro a ha
    change a ∈ S.R at ha
    obtain ⟨a', b', hb', e⟩ := hreg a ha
    change a ∈ M.O ((yR ≫ φM) (IsLocalRing.closedPoint K))
    rw [e]
    exact hφreg _ a' b' hb'

end GlobalTheory.Poinc.SetupCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TraitUnif

theorem exists_generic_fibre_pull : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), Function.Injective φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (AW : PolAV (Sp (FractionRing W))) (genW : ((Over.pullback (jK W)).obj ((Over.pullback (spMap φ)).obj G)) ≅ AW.A) (κ₁ : pullback ((Over.pullback (spMap φ)).obj G).hom (jK W) ⟶ pullback G.hom (jK R)), IsMonHom genW.hom ∧ κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst ((Over.pullback (spMap φ)).obj G).hom (jK W) ≫ pullback.fst G.hom (spMap φ) ∧ LBIso (AW.L.pull genW.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ A gen hgen
  haveI : IsMonHom gen.hom := hgen
  set gφ := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ with hgφ
  have hsq : jK W ≫ spMap φ = spMap gφ ≫ jK R := by
    simp only [hgφ, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  let GV := (Over.pullback (spMap φ)).obj G
  have hβ := isGrpPullback_pullback G (spMap φ)
  let κ₁ : pullback GV.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ)) (pullback.snd GV.hom (jK W) ≫ spMap gφ)
      (by rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ) :=
    pullback.lift_fst _ _ _
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GV).hom ≫ spMap gφ :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GV) ((Over.pullback (jK R)).obj G) (spMap gφ) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GV (jK W)).comp hβ).congr hsq hκf.symm) w
  have hκA : IsGrpPullback ((Over.pullback (jK W)).obj GV) A.A (spMap gφ) (κ₁ ≫ gen.hom.left) :=
    (hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨P', g, hg, -, hmul, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap gφ) A
  have hP' : IsGrpPullback P'.A A.A (spMap gφ) g := by
    refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
    have ex : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]
    rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hκA hP'
  refine ⟨P', e, κ₁, he, hκf, ?_⟩
  have h1 : LBIso (P'.L.pull e.hom.left) ((A.L.pull g).pull e.hom.left) :=
    GlobalTheory.FamRep.lbIso_pull (LBIso.symm ⟨t, ht⟩) _
  have h2 : LBIso ((A.L.pull g).pull e.hom.left) (A.L.pull (e.hom.left ≫ g)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB g e.hom.left
  have h3 : LBIso ((A.L.pull gen.hom.left).pull κ₁) (A.L.pull (κ₁ ≫ gen.hom.left)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB gen.hom.left κ₁
  rw [heq] at h2
  exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB (pull_isLB A.isLB _) _) h1
    (LBIso.trans (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) h2 h3.symm)

theorem extLam_pull_square : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)), IsGrpPullback G₁ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst G₁.hom (jK R') ≫ β → ∀ (L : LB ((Over.pullback (jK R)).obj G).left) (N : LB ((Over.pullback (jK R')).obj G₁).left) (PP : LB (G2 G).left), L.IsLB → N.IsLB → LBIso N (L.pull κ₁) → ExtLam G L PP → ExtLam G₁ N (PP.pull β₂) := by
  intro R R' _ _ _ _ _ _ ρ hρ G _ _ G₁ _ _ β β₂ κ₁ hβ hsqβ hκf L N PP hL hN hNL hExt
  have hsq : jK R' ≫ spMap ρ =
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  have hκ : IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have H1 := Hκ L N _ PP g₂ hL hN hExt.1 hNL (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  have := hR.1.1
  have := hR.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨AV, genV, κ₁, hgenV, hκ, hLV⟩ := exists_generic_fibre_pull R V φ hφ G A gen hgen
  obtain ⟨βV₂, hsqV, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G _ _ (isGrpPullback_pullback G (spMap φ))
  have hExtV := extLam_pull_square R V φ hφ G _ _ βV₂ κ₁ (isGrpPullback_pullback G (spMap φ)) hsqV hκ _ _ PP
    (pull_isLB A.isLB _) (pull_isLB AV.isLB _) hLV hPP
  have hGV : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hsq, hLam⟩ :=
    _root_.GlobalTheory.Mum.exists_unif_finExt_lam V hV _ hGV AV genV hgenV _ hExtV
  have hρloc : IsLocalHom ρ := RingHom.IsIntegral.isLocalHom hρ.2.2.to_isIntegral hρ.2.1
  refine ⟨R', _, _, _, ρ.comp φ, G₁, _, _, β ≫ pullback.fst G.hom (spMap φ), β₂ ≫ βV₂, D₁, A₁, U₁, hR',
    hρ.2.1.comp hφ, ?_, ?_, ?_, ?_⟩
  · exact RingHom.isLocalHom_comp ρ φ
  · refine (hβ.comp (isGrpPullback_pullback G (spMap φ))).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsqV.1, ← Category.assoc, hsq.1, Category.assoc]
    · rw [Category.assoc, hsqV.2, ← Category.assoc, hsq.2, Category.assoc]
  · exact LBIso.trans (DVR.linComb_isLB _ U₁.LG.isLB _ _) (pull_isLB (pull_isLB hPP.1 _) _) (pull_isLB hPP.1 _) hLam
      (GlobalTheory.FamRep.lbIso_pull_pull hPP.1 βV₂ β₂)
end GlobalTheory.Mum.TraitUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtFrac

theorem thList_pull_of_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {m N : ℕ} {K K' : Type} [Field K] [Field K']
    (i : K →+* K') {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') {θ : SecAt G L x}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x θ pt c) :
    ∃ pt' : Fin N → (Over.mk x' ⟶ G),
      ThList G L ρ m x' (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) θ) pt'
        (fun a => i (c a)) := by
  subst h
  obtain ⟨pt', -, H'⟩ := ThPull.thList_pull S G L ρ hL hρ m N K K' i x θ pt c H
  exact ⟨pt', H'⟩

theorem ext_any_frac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R K) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R K) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R K (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R K)) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ K _ _ _ χ θ pt c hm h3 hu hP hT hc
  let φ : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let i : K →+* FractionRing R := φ.symm.toRingEquiv.toRingHom
  let j : FractionRing R →+* K := φ.toRingEquiv.toRingHom
  have hi : ∀ r, i (algebraMap R K r) = algebraMap R (FractionRing R) r := fun r => φ.symm.commutes r
  have hi' : i.comp (algebraMap R K) = algebraMap R (FractionRing R) := RingHom.ext hi
  have hj' : j.comp (algebraMap R (FractionRing R)) = algebraMap R K := RingHom.ext fun r => φ.commutes r
  have hji : j.comp i = RingHom.id K := RingHom.ext fun r => φ.apply_symm_apply r
  have e₁ : spMap i ≫ spMap (algebraMap R K) ≫ χ = spMap (algebraMap R (FractionRing R)) ≫ χ := by
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hi']
  have e₂ : spMap j ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap R K) ≫ χ := by
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hj']
  have hp : IsGrpPullback t.G t.G (𝟙 _) (𝟙 t.G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  have hLL : LBIso t.PP.L (t.PP.L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl t.PP.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  have hP' := (FibMove.polFib_move S S t.G t.PP.L t.G t.PP.L (𝟙 _) (𝟙 _) t.PP.isLB t.PP.isLB hp hLL g K _).2 _ i hP
  rw [e₁] at hP'
  obtain ⟨pt', hT'⟩ := thList_pull_of_eq t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen i e₁ hT
  simp only [hi] at hT'
  obtain ⟨σ, hσ, hz⟩ := _root_.GlobalTheory.UMin.OmExt.om_ext E H S t g m N R χ _ pt' c hm h3 hu hP' hT' hc
  refine ⟨σ, ?_, hz⟩
  let β : Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) :=
    Over.homMk (spMap j) e₂
  have q := congrArg (VVRank.pullM t.G t.PP.L _ β) hσ
  have a₁ : β ≫ (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) = Over.homMk (spMap (algebraMap R K)) rfl := by
    ext
    change spMap j ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R K)
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hj']
  have a₂ : β ≫ (Over.homMk (spMap i) e₁ : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶
      Over.mk (spMap (algebraMap R K) ≫ χ)) = 𝟙 _ := by
    ext
    change spMap j ≫ spMap i = 𝟙 _
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hji]
    exact Spec.map_id _
  have b₁ := VVRank.pullM_comp t.G t.PP.isLB ((1 : ℕ) : ℤ) β (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) (SecM.ofSec t.G σ)
  have b₂ := VVRank.pullM_comp t.G t.PP.isLB ((1 : ℕ) : ℤ) β (Over.homMk (spMap i) e₁ :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk (spMap (algebraMap R K) ≫ χ)) (SecM.ofSec t.G θ)
  rw [a₁] at b₁
  rw [a₂, VVRank.pullM_id t.G t.PP.isLB] at b₂
  exact b₁.symm.trans (q.trans b₂)

end GlobalTheory.UMin.ExtFrac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_quot_kerIdeal_succ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G Q : PDivGroup p k)
    (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (h : q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G) (hmn : m ≤ n) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (q.app (n + 1))) =
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) := by
  have h1 : Hom.app (q ≫ q') (n + 1) = mulBy k (G.A (n + 1)) (p ^ m) := by
    rw [h, ← Nat.cast_pow, natCast_smul_id_app]
  have h2 : torsionIdeal (R := k) (A := G.A (n + 1)) (p ^ m) ≤ kerIdeal (q.app (n + 1)) := by
    rw [torsionIdeal, ← h1, comp_app, kerIdeal_comp]
    refine Ideal.map_mono ((kerIdeal_le_ker_iff _ (counitAlgHom k _)).2 fun c => ?_)
    simp
  have h3 : RingHom.ker (G.res n : G.A (n + 1) →ₐ[k] G.A n) ≤ kerIdeal (q.app (n + 1)) :=
    (G.ker_res n).le.trans ((torsionIdeal_le_of_dvd (pow_dvd_pow p hmn)).trans h2)
  have h4 : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app (n + 1))) =
      kerIdeal (q.app n) := by
    rw [← kerIdeal_comp, q.comm n, kerIdeal_comp_of_surjective _ (Q.res_surjective n)]
  have hs : Function.Surjective (G.res n : G.A (n + 1) →ₐ[k] G.A n) := G.res_surjective n
  have hc : Ideal.comap (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app n)) =
      kerIdeal (q.app (n + 1)) := by
    rw [← h4, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 h3
  let e := Ideal.quotientMapₐ (kerIdeal (q.app n)) (G.res n : G.A (n + 1) →ₐ[k] G.A n) hc.ge
  have he : Function.Bijective e :=
    ⟨Ideal.quotientMap_injective' (H := hc.ge) hc.le, Ideal.quotientMap_surjective (H := hc.ge) hs⟩
  exact (AlgEquiv.ofBijective e he).toLinearEquiv.finrank_eq

theorem finrank_quot_kerIdeal_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n →
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  intro p _ k _ _ G Q m n q q' h hmn
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => exact (finrank_quot_kerIdeal_succ p k G Q m n q q' h hmn).trans ih

end GlobalTheory.Dieu
end

