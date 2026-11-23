module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatQuotientOfEquivCokerDualMapOfExactFibres
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeckeOperatorMultiplicativeOnSectionProducts
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PhiMul

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frm_pow {D : DegPre R} {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) (hw : w.IsGen)
    (n N : ℕ) (hN : N = k * n) : ∃ w' : Frm D F N b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J ^ n := by
  obtain ⟨w', h₁, h₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 1
      subst hN
      fin_cases i <;> simp [DegPre.lineε, mul_comm])
    (GeneratorPullback.powGen D.P.L _ _ w n) (powGen_isGen _ _ _ _ hw n)
  exact ⟨w', h₁, fun z J hJ => (h₂ _ _ z J hJ).trans (map_pow _ _ _)⟩


omit [IsDomain R] in
theorem exists_secA_mul {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {a b c : ℕ} (hc : c = a + b)
    (t : SecA A F a) (t' : SecA A F b) : ∃ u : SecA A F c,
      ∀ z J, Good A.L z J → sA u (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  obtain ⟨u, hu⟩ := exists_sec A.isLB (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (ε' := fun _ => (c : ℤ)) (fun U _ h => by
      subst hc
      simp [Fintype.prod_sum_type, zpow_add])
    (H1.SectionArithmetic.mulSec (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (a : ℤ))
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (b : ℤ)) t t')
  exact ⟨u, fun z J hJ => (hu _ _ z J hJ).trans (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ)⟩

theorem phi_mul : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (n : Fin 3 → ℕ) (N : Fin 3 → ℕ), (∀ i, 1 ≤ n i ∧ N i = k * n i) → n 2 = n 0 + n 1 → ∀ (q : ∀ i, QkPt D.toPre F (N i)) (ω : ∀ i, Frm D.toPre F (N i) (q i).g.b), (∀ i, (q i).y = n i • p.y ∧ (q i).g = p.g ∧ ((ω i).IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val (ω i) (𝟙 _) z J = val w (𝟙 _) z J ^ n i)) → ∀ (t t' : ∀ i, SecA A F (N i)) (s s' : ∀ i, Fam D.toPre F (N i)), (∀ i, U.ExpandsF F (N i) w₀ (t i) (s i) ∧ U.ExpandsF F (N i) w₀ (t' i) (s' i) ∧ PhiRel D.toPre F (N i) (q i) (ω i) (s i) (s' i)) → (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (t' 2) (𝟙 _) z J = sA (t' 0) (𝟙 _) z J * sA (t' 1) (𝟙 _) z J := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ w₀ hw₀ k hk p w hw n N hn hn2 q ω hq t t' s s' hs ht
  have hN1 : ∀ i, 1 ≤ N i := fun i => by rw [(hn i).2]; exact Nat.mul_pos hk (hn i).1
  have hN2 : N 2 = N 0 + N 1 := by rw [(hn 0).2, (hn 1).2, (hn 2).2, hn2, mul_add]
  have hB := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F (N 2) (hN1 2) w₀ hw₀
  obtain ⟨u, hu⟩ := exists_secA_mul hN2 (t' 0) (t' 1)
  obtain ⟨r, hr, -⟩ := hB.1 u
  have hrs : r = s' 2 := by
    refine CoefDet.fam_eq_of_coef_eq hL R I hI D F (N 2) r (s' 2) fun g₀ => ?_
    letI := GlobalTheory.TorusExt.gtGroup D.toPre F
    have hadd : g₀.IsAdd p.g (g₀ + p.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
    obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen :=
      exists_gen_of_local (V := F) D.toPre.P.L D.toPre.P.isLB _ _
    obtain ⟨ω₁, hω₁, -, hφ⟩ := CoefPhi.coef_phi hL R I hI D F k hk p w hw g₀ _ hadd ω₀ hω₀
    choose a ha using fun i => exists_frm_pow ω₀ hω₀ (n i) (N i) (hn i).2
    choose b hb using fun i => exists_frm_pow ω₁ hω₁ (n i) (N i) (hn i).2
    have hc : ∀ i α, coef (s' i) g₀ (a i) (α + (q i).y) = coef (s i) (g₀ + p.g) (b i) α := fun i =>
      hφ (n i) (N i) (hn i).1 (hn i).2 (q i) (hq i).1 (hq i).2.1 (ω i) (a i) (b i) (hq i).2.2 (ha i) (hb i)
        (s i) (s' i) (hs i).2.2
    refine ⟨a 2, (ha 2).1, fun χ => ?_⟩
    have S₀ := _root_.GlobalTheory.UT.ProdConv.main hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t' 0) (t' 1) u
      (s' 0) (s' 1) r (hs 0).2.1 (hs 1).2.1 hr hu g₀ (a 0) (a 1) (a 2) (ha 0).1 (ha 1).1 (ha 2).1
      (fun z J hJ => by rw [(ha 0).2 z J hJ, (ha 1).2 z J hJ, (ha 2).2 z J hJ, hn2, pow_add]) χ
    have S₁ := _root_.GlobalTheory.UT.ProdConv.main hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t 0) (t 1) (t 2)
      (s 0) (s 1) (s 2) (hs 0).1 (hs 1).1 (hs 2).1 ht (g₀ + p.g) (b 0) (b 1) (b 2) (hb 0).1 (hb 1).1 (hb 2).1
      (fun z J hJ => by rw [(hb 0).2 z J hJ, (hb 1).2 z J hJ, (hb 2).2 z J hJ, hn2, pow_add]) (χ - (q 2).y)
    have hy : (q 2).y = (q 0).y + (q 1).y := by rw [(hq 0).1, (hq 1).1, (hq 2).1, hn2, add_smul]
    have S₂ := ((GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ 0).2.2 _ (fun ψ => ψ + (q 0).y)
      (add_left_injective _) (fun i hi => absurd ⟨i - (q 0).y, sub_add_cancel _ _⟩ hi)).2 S₀
    have e : ((fun ψ => coef (s' 0) g₀ (a 0) ψ * coef (s' 1) g₀ (a 1) (χ - ψ)) ∘ fun ψ => ψ + (q 0).y) =
        fun ψ => coef (s 0) (g₀ + p.g) (b 0) ψ * coef (s 1) (g₀ + p.g) (b 1) (χ - (q 2).y - ψ) := by
      funext ψ
      rw [← hc 0, ← hc 1, hy]
      have e' : χ - ((q 0).y + (q 1).y) - ψ + (q 1).y = χ - (ψ + (q 0).y) := by abel
      rw [e']
      rfl
    rw [e] at S₂
    rw [(GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ _).1 S₂ S₁, ← hc 2, sub_add_cancel]
  obtain rfl : u = t' 2 := (hB.2 (s' 2)).unique (hrs ▸ hr) (hs 2).2.1
  exact hu

end GlobalTheory.UT.PhiMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivOfGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivGeneric

theorem dominant_field (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] :
    IsSchemeTheoreticallyDominant (TF (R := V) F).hom := by
  have h₁ : IsDominant (jK V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have h₂ : IsDominant (jFK (R := V) F) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (FractionRing V) F).injective).le.trans bot_le)⟩
  have h₃ : IsDominant (TF (R := V) F).hom := inferInstanceAs (IsDominant (jFK (R := V) F ≫ jK V))
  have h₄ : IsReduced (Spec (CommRingCat.of V)) := inferInstance
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem kTriv_of_generic : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L), RelAmple B L.L → (∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ B, InK B L.L x → x = 1) → KTriv B L.L := by
  intro hG V _ _ _ _ B _ _ hB L c hL hx
  have hLB : L.L.IsLB := L.isLB
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L.L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L.L hLB
  obtain ⟨H, j, hj, hH⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG V B hB hP L.L (pw L.L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L.L (pw L.L 0) hLB hO hL H j hj hH
  have hflat : Flat H.hom := _root_.GlobalTheory.StabFlat.flat_of_isFinite hG V B hB hP L c (pw L.L 0) hO hu H j hj hH hfin
  have hrep : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), InK B L.L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have hchar : CharZero (AlgebraicClosure (FractionRing V)) := inferInstance
  have key := GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hrep _ _).1 (inK_one hLB _))
    (fun T x y => (hrep _ _).1 (InK.mul hLB ((hrep _ _).2 ⟨x, rfl⟩) (InK.inv hLB ((hrep _ _).2 ⟨y, rfl⟩))))
    (AlgebraicClosure (FractionRing V)) (TF (R := V) (AlgebraicClosure (FractionRing V))).hom
    (fun x => hx _ ((hrep _ _).2 ⟨x, rfl⟩))
  have hd := dominant_field V (AlgebraicClosure (FractionRing V))
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have hj1 : j = 1 := by
    let T := TF (R := V) (AlgebraicClosure (FractionRing V))
    have h1 : fst H T ≫ j = fst H T ≫ 1 := by
      rw [MonObj.comp_one]
      exact key (H ⊗ T) (snd H T) (fst H T)
    have h0 : QuasiCompact T.hom :=
      inferInstanceAs (QuasiCompact (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V))
    have h2 : IsSchemeTheoreticallyDominant (fst H T).left :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback H.hom T.hom).flip
    exact GlobalTheory.over_ext_of_schemeTheoreticallyDominant (fst H T).left (congrArg (fun q => q.left) h1)
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.StabFlatLocal
open GlobalTheory.CechPic GlobalTheory.StabFlat

theorem exists_ideal (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (σ : V →+* A) (hσ : IsLocalHom σ) (h₁ : σ.Flat)
    (h₂ : IsRegularLocalRing (A ⧸ (IsLocalRing.maximalIdeal V).map σ))
    (h₃ : ringKrullDim (A ⧸ (IsLocalRing.maximalIdeal V).map σ) = g)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a)
    (hE : ∀ (K : Type) [Field K] (φ : A →+* K), (IsLocalRing.maximalIdeal V).map σ ≤ RingHom.ker φ →
      (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
      RingHom.ker φ = IsLocalRing.maximalIdeal A) :
    ∃ I : Ideal A, ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
        I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := _root_.GlobalTheory.AbLaw.exists_free_complex_of_primitive A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, ?_, fun R _ _ φ => (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans
    (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  letI : Algebra V A := σ.toAlgebra
  haveI : IsLocalHom (algebraMap V A) := hσ
  haveI : Module.Flat V A := h₁
  have key : Module.Flat V (A ⧸ I) → ((Ideal.Quotient.mk I).comp σ).Flat := fun h =>
    RingHom.flat_algebraMap_iff.2 h
  refine key (_root_.GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres V A g h₂ h₃ C c₁ c₂ (fun p hϖ => ?_) I ⟨eC.trans eI⟩)
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let φ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  have hk : RingHom.ker φ = p.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField K).injective,
      Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · refine Or.inr fun ht => hi (hk.symm.trans (hE K φ ?_ ((test K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)))
    exact hϖ.trans hk.ge
  · exact Or.inl hi

theorem flat_of_isFinite : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ H j hj hH hf
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hL
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine _root_.GlobalTheory.StabFlat.flat_of_isFinite_of_ideals V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := _root_.GlobalTheory.StabFlat.stalk_of_smooth_local V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L (pw L 0) hL hO hΘ hu H j
    (fun T x => (hK _ rfl T x).symm.trans (hH T x))
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.StabFlatLocal
end
end

