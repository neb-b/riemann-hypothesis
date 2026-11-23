module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionOfFunctionalEquation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecBEqEverywhereOfGenericAgreeConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBGenericAgree

variable {R : Type} [CommRing R] [IsDomain R]

theorem isUnit_jK_app (c : R) (hc : c ≠ 0) :
    IsUnit ((jK R).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have h := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hu : IsUnit (algebraMap R (FractionRing R) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  rw [h] at this
  exact this

theorem isUnit_gs (Q : DegPre R) (c : R) (hc : c ≠ 0) (z : (DegPre.BF Q (FractionRing R)).left) :
    IsUnit (gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e1 : (DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom =
      ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Over.w (DegPre.prB Q (FractionRing R)), Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)).symm
  rw [e1, ← gs_pull ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) (jK R) z ⊤ trivial,
    gs_eq _ z (jK R ⁻¹ᵁ ⊤) trivial]
  exact ((isUnit_jK_app c hc).map _).map _

theorem f_eq (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R) (hc : c ≠ 0)
    (H : ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J →
      gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s (DegPre.prB Q (FractionRing R)).left z J =
        gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s' (DegPre.prB Q (FractionRing R)).left z J)
    (j : Fin 4 → Q.P.L.ι) : s.f j = s'.f j := by
  set p := (DegPre.prB Q (FractionRing R)).left
  have H' : ∀ z J, Good Q.P.L z J → sval s p z J = sval s' p z J := fun z J hJ =>
    (isUnit_gs Q c hc z).mul_left_cancel (H z J hJ)
  refine GlobalTheory.IntegralExpansion.prB_app_injective Q _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ y)
  have hI' : Good Q.P.L y I := hI
  have m := hI'.mem (DegPre.famφB Q β) p
  rw [gs_pull (𝟙 _) p y _ hy, gs_pull (𝟙 _) p y _ hy, Category.id_comp]
  exact (sec_trans s p y hy m).trans ((congrArg _ (H' y I hI')).trans (sec_trans s' p y hy m).symm)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  intro R _ _ Q k β s s' c hc H Z x z J _
  have hf : s.f = s'.f := funext (f_eq Q k β s s' c hc H)
  show gs x z _ (s.f _) = gs x z _ (s'.f _)
  rw [hf]

end GlobalTheory.SecBGenericAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem selfInter_canWeight_le : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u →
      (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  intro hC k _ X _ p D hX P hA e x hG
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  have hf : 0 < Module.finrank ℤ k := Module.finrank_pos
  have he : 0 < e := hG.pos
  obtain ⟨hPI, -, -, -, -, -, -⟩ := _root_.GlobalTheory.HSAmp.toProj_gens k X p D hX P hA e x hG
  obtain ⟨hPV, -, -⟩ := _root_.GlobalTheory.PSpaceDeg.main k D

  obtain ⟨Φ₀, hΦ₀⟩ := ((hC.arExists k (PSpace k D) (PSpace.str k D) D hPV).2 Unit
    fun _ => ProjSpace.hermitianTwistingSheaf k D).1
  have hH := ((hC.arIso k (PSpace k D) (PSpace.str k D) D hPV).2 Unit _ Φ₀ hΦ₀).1 ()
  set H := Φ₀ (MvPolynomial.X () ^ (D + 1)) with hHdef
  set g := gdeg P.L D
  refine ⟨|g * H| / ((Module.finrank ℤ k : ℝ) * e), fun n u a hn hu ha => ?_⟩
  obtain ⟨-, -, -, hG', hu'⟩ := _root_.GlobalTheory.HSAmp.canNorms k X p D hX P e x hG n u hn hu
  obtain ⟨hPI', π, hπ, hgen, hd, hdf, hiso⟩ := _root_.GlobalTheory.HSAmp.toProj_gens k X p D hX P hA (e * n) _ hG'
  have hdeg := _root_.GlobalTheory.HSAmp.finrank_ratF_eq_gdeg hC k X p D hX P hA (e * n) _ hG'
  have hpow := (_root_.GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow hC k X p D hX).2 (up P.L u) (e * n) a ha
  have hpull := ((hC.arProj k (PSpace k D) X (PSpace.str k D) p D hPV hX π hπ hgen hd).1 _ H hH)

  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => (up P.L u).pow (e * n)).1
  have hI := hC.arIso k X p D hX
  have h₁ := (hI.2 Unit _ Φ hΦ).1 ()
  have hΦ' := (hI.2 Unit _ Φ hΦ).2.1 (fun _ => (ProjSpace.hermitianTwistingSheaf k D).pull π hπ) fun _ => hiso u hu'
  have h₂ := (hI.2 Unit _ Φ hΦ').1 ()
  have e₁ := HermLB.IsSelfInter.unique hX hpow h₁
  have e₂ := HermLB.IsSelfInter.unique hX hpull h₂

  set d : ℝ := ((π.residueDegree (genericPoint X) : ℕ) : ℝ)
  set f : ℝ := ((Module.finrank ℤ k : ℕ) : ℝ)
  set E : ℝ := ((e * n : ℕ) : ℝ)
  have hE : 0 < E := by positivity
  have hfpos : (0 : ℝ) < f := Nat.cast_pos.mpr hf
  have key1 : E ^ (D + 1) * a = d * H := e₁.trans e₂.symm
  have key2 : d * f = E ^ D * g := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hdf
    simp only [Nat.cast_mul] at this
    rw [← hdeg]; exact this
  have ha' : a = g * H / (f * E) := by
    field_simp
    have : E ^ (D + 1) * a * f = E ^ D * g * H := by rw [key1, ← key2]; ring
    have hED : E ^ D ≠ 0 := pow_ne_zero _ hE.ne'
    apply mul_left_cancel₀ hED
    linear_combination this
  rw [ha', abs_div, abs_of_pos (by positivity : (0:ℝ) < f * E)]
  have : f * E = (f * e) * n := by simp [E, f]; ring
  rw [this, div_div]

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbedding
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' E hθ
  have : IsNoetherianRing R := hR.1
  have : IsIntegrallyClosed R := hR.2.2.1
  have hs : Surjective M.π := (Modif.appTop_bijective_surjective R M).2
  obtain ⟨N, fU, l, hl, hf⟩ := _root_.GlobalTheory.Mum.exists_near R hR M G' hG' E
  have hN : N.Law := _root_.GlobalTheory.Mum.Near.law_of_emb R hR M G' hG' E N fU l hl hf
  obtain ⟨G, i1, i2, β, i, hG, hβ, hi, hu⟩ := _root_.GlobalTheory.Mum.descend_of_near R hR M.S M.π M.proper hs M.integral G' hG' N hN
  obtain ⟨θ, O, hO, hθO⟩ := _root_.GlobalTheory.Mum.exists_open_theta_descent R M.S M.π hs G' E N fU l hl hf P'.L.L hθ G β i hβ.1.w hi hu
  obtain ⟨L, hL, hLi⟩ := _root_.GlobalTheory.Mum.CubeDesc.cubicalBundle_descends R hR M G' hG' P' G β hG hβ θ O hO hθO
  obtain ⟨P, rfl⟩ := _root_.GlobalTheory.Mum.exists_cp_descent R hR M G' hG' P' G β hG hβ L hL hLi
  exact ⟨G, i1, i2, P, β, hG, hβ, hLi⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.USep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

def IsCov (C : UCompact Xo c) {M : Scheme.{0}} (g : M ⟶ C.Z) (z₁ : M)
    (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) : Prop :=
  IsNormalScheme M ∧
    (∃ (U : C.Z.Opens) (g' : M ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = g ∧
      Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧
    ζ ≫ pullback.fst _ _ = M.fromSpecStalk z₁ ≫ g ∧
    ∀ p : Sp (M.presheaf.stalk z₁), p.asIdeal = ⊥ → ζ p ∈ Set.range C.iF

section

variable {A : Type} [CommRing A] [IsLocalRing A] (ζ : Sp A ⟶ pullback C.z (spMap C.b)) {N₁ : ℕ}
  (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ A)

def HasTraits : Prop :=
  ∀ (T : UTrait Xo c) (ev : A →+* T.V), IsLocalHom ev → jK T.V ≫ spMap ev ≫ ζ = T.y ≫ C.iF →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b)

def IsMember {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (ξ : Sp V ⟶ pullback C.z (spMap C.b)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X)
    (h : Fin (Φ.m y) ≃ Fin Cm.m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ ζ = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k ^ 2 = ρ (Cm.s (h k)) ∧ ∀ a b, Φ.δ y k a b = ((l.M' : ℤ) • Cm.δ (h k)) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (p : IsPullDeg ρ Cm.P.D.toPre D), GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ p.xe.symm
      fun mu c => Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) fun _ => e.symm mu

end

def DescAt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a

theorem sepAtB_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {m N : ℕ}
    (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) :
    GlobalTheory.UChart.SepAtB Q τ₀ s ev k₀ ↔ (∀ i, ev (s (.inl i)) = 0) ∧ DescAt Q ev k₀ ∧
      ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
        ∀ i, ev (s (.inr i)) ∈ k₀ := Iff.rfl

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkDerivationMemSpanInvariantSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerSpan

open GlobalTheory.TangentOrigin

theorem stalk_derivation_span : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  intro R _ _ _ _ G _ _ hsa n v dd hinv p _ D hD δ hadd hmul hbase
  haveI : Smooth G.hom := hsa.smooth
  have hv := GlobalTheory.VertCoeffRing.isLieBasis_tvE v
  have hdd := fun (B : Type) [CommRing B] [Algebra R B] e he z O h =>
    GlobalTheory.VertCoeffRing.evalPt_lieExp (fun a => v a) dd hinv B e he z O h

  let ψ : ∀ (V : G.left.Opens), p ∈ V → Γ(G.left, V) →+* ResidueField (G.left.presheaf.stalk p) :=
    fun V hpV => (residue _).comp (G.left.presheaf.germ V p hpV).hom
  have germ_res : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (f : Γ(G.left, V)),
      G.left.presheaf.germ V' p hpV' (resG G.left e f) = G.left.presheaf.germ V p hpV f := by
    intro V V' e hpV hpV' f
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE e) p hpV' f

  have loc : ∀ (V : G.left.Opens) (hpV : p ∈ V), IsAffineOpen V →
      ∃! c : Fin n → ResidueField (G.left.presheaf.stalk p),
        ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V hpV hV
    obtain ⟨t, ht, et⟩ := exists_evalPt_eq hV (ψ V hpV)
    letI : Algebra R (ResidueField (G.left.presheaf.stalk p)) := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
    let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ResidueField (G.left.presheaf.stalk p)) ⟶ G :=
      Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
    have h : ⊤ ≤ y.left ⁻¹ᵁ V := ht
    have ev : ∀ s, evalPt y.left V h s = ψ V hpV s := fun s => by
      change evalPt t V ht s = _
      rw [et]
    have hconst : ∀ r, G.left.presheaf.germ V p hpV (constFn G.hom V r) =
        (G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      intro r
      have e1 : constFn G.hom V r = resG G.left (le_top : V ≤ ⊤)
          ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
        unfold constFn
        first
          | rfl
          | (rw [Scheme.Hom.appLE_eq_app_comp_map] ; rfl)
          | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; rfl)
      rw [e1]
      exact germ_res ⊤ V le_top trivial hpV _
    have := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg hv hdd y hV h
      (fun f => δ (G.left.presheaf.germ V p hpV f))
      (fun f f' => by simp only [map_add (f := _), hadd])
      (fun f f' => by simp only [map_mul, hmul, ev]; rfl)
      (fun r => by rw [hconst]; exact hbase r)
    simpa only [ev] using this

  have down : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V')
      (c : Fin n → ResidueField (G.left.presheaf.stalk p)),
      (∀ f, δ (G.left.presheaf.germ V' p hpV' f) = ∑ a, c a * ψ V' hpV' (dd a V' f)) →
      ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V V' e hpV hpV' c hc f
    rw [← germ_res V V' e hpV hpV' f, hc]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    change residue _ (G.left.presheaf.germ V' p hpV' (dd a V' (resG G.left e f))) =
      residue _ (G.left.presheaf.germ V p hpV (dd a V f))
    rw [(hinv a).1.2.2 V V' e le_top f, germ_res]
  obtain ⟨V₀, hV₀, hpV₀, -⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : G.left.Opens) from trivial)
  obtain ⟨c₀, hc₀, hu₀⟩ := loc V₀ hpV₀ hV₀
  choose c hc using fun a => residue_surjective (R := G.left.presheaf.stalk p) (c₀ a)
  refine ⟨c, fun y => ?_⟩
  obtain ⟨W, hpW, g, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  obtain ⟨V', hV', hpV', hle⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ V₀ ⊓ W from ⟨hpV₀, hpW⟩)
  obtain ⟨c', hc', -⟩ := loc V' hpV' hV'
  have hcc : c' = c₀ := hu₀ c' (down V₀ V' (hle.trans inf_le_left) hpV₀ hpV' c' hc')
  subst hcc
  have eW : V' ≤ W := hle.trans inf_le_right
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← germ_res W V' eW hpW hpV' g, hc', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hc, hD]
  rfl

end GlobalTheory.StalkDerSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBundleLevelOdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_bundle_level_odd : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.WeilOpenLocus.weil_open) | (exact GlobalTheory.WeilOpenLocus.weil_open) | (intros; apply GlobalTheory.WeilOpenLocus.weil_open  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomain
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem tateIso_spread : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : Sp R ⟶ Sp o) (z : o) (k : ℕ), 0 < k →
  Module.finrank ℤ D.La = 2 * P.g → ∀ (pt : D.La → (𝟙_ (Over (Sp R)) ⟶ P.A))
  (F : Type) [Field F] [CharZero F] (x₀ : Sp F ⟶ Sp R) (β₀ : o →+* F), DenseRange x₀ → x₀ ≫ s = spMap β₀ →
  ∀ I₀ : TateIso D F (Over.mk x₀ ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
  (I₀.ζ k : F) = β₀ z → (∀ a, toUnit _ ≫ pt a = I₀.ev k a) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ Sp R) (β : o →+* K), x ≫ s = spMap β →
  ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
    (I.ζ k : K) = β z ∧ ∀ a, toUnit _ ≫ pt a = I.ev k a := by
  intro E _ _ _ H D R _ _ _ P act o _ s z k hk hrk pt F _ _ x₀ β₀ hd hx₀ I₀ hζ₀ hev₀ K _ _ _ x β hx
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have hu : ∀ {L : Type} [Field L] (y : Sp L ⟶ Sp R),
      (Over.homMk y (by simp) : Over.mk y ⟶ Out.baseOver (Sp R)) = toUnit (Over.mk y) := fun y =>
    Over.OverMorphism.ext ((Over.w (toUnit (Over.mk y))).symm.trans (Category.comp_id _))
  have hcard : ∀ n, 0 < n → Nat.card {w : Over.mk x ⟶ P.A // w ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [hrk]
    exact (hL.mulN _ P n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ P.A) (fun c w => w ≫ act c)
    (fun n w w' c => Out.WeilIs P.A P.L n w w' (unitOn c)) k (β z) _ (fun a : D.La => a)
    (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ pt a) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m w w' c hn hm hw hw' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact PELFamily.weilIs_lower P hL.weil hm u' hw hw' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.exists_levelIsometry_of_dense hL E H D (Sp R) P act o s z _
        (fun a : D.La => a) pt (k * m) m hn (Dense.mono (fun p hp =>
          ⟨F, inferInstance, x₀, β₀, I₀.ζ (k * m), I₀.ev (k * m), Nat.cast_ne_zero.2 hn.ne', hp, hx₀,
            I₀.ζ_prim _ hn, I₀.add _, fun v => (I₀.onto _ hn _).2 ⟨v, rfl⟩, I₀.lin _, I₀.isom _ hn,
            by rw [← hζ₀, ← I₀.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I₀.tower k m hk hm _).trans ((hev₀ i).symm.trans (by rw [hu]))⟩) hd)
        K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.TorsIsometry.ker_and_onto E H D K (Over.mk x ⟶ P.A)
        (fun w w' c => Out.WeilIs P.A P.L (k * m : ℕ) w w' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => PELFamily.eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨I, hI, fun a => Eq.trans (by rw [hu]) (hA a).symm⟩

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatements
section
theorem GlobalTheory.JoinFun.joinOut_of_lat : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hHT hRam hUnr hLatAlg hLatConj
  have hZD := GlobalTheory.ZetaDenom.zetaDenominators hSKDR
  have hField := GlobalTheory.SqTop.fieldDat
  have hAbs := GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT
  have hLNe := GlobalTheory.SqTop.lNe_of_functionalEquation hAbs GlobalTheory.HeckeStrip.completedLBoundedInStrips hField
  exact ⟨GlobalTheory.ToricDenomRow.toricDenominator hZD hRam hUnr,
    GlobalTheory.TransportProof.transport_of hHCF hLatAlg hLatConj,
    GlobalTheory.TwistedTransportProof.main (GlobalTheory.LatVal.periodEx_of_mainTheorem hEM) hLatAlg hLatConj, hZD,
    GlobalTheory.SqTop.refl_of_functionalEquation hHT hField hLNe⟩
end

