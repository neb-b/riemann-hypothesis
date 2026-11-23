module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem psi_zero_rig_const : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  intro V _ _ D
  obtain ⟨z⟩ := GlobalTheory.UT.CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.UT.CoefBasic.cstH_surj z
    ((@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J')).val * (rigV D (TF (R := V) (FractionRing V)).hom z J').val)
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    rw [← Units.val_mul] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := GlobalTheory.UT.CoefBasic.pt_eq z z'
    have a₁ := GlobalTheory.UT.CoefBasic.val_tr (D.psi_gen 0) (jFK (R := V) (FractionRing V)) hJ hJ'
    have a₂ : rigV D (TF (R := V) (FractionRing V)).hom z J =
        GlobalTheory.UT.CoefBasic.trU D.P.L z J J' ((TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A) *
        rigV D (TF (R := V) (FractionRing V)).hom z J' := by
      refine (GlobalTheory.UT.CoefBasic.val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
        (TF (R := V) (FractionRing V)).hom hJ hJ').trans ?_
      rw [Fintype.prod_unique, zpow_one]; rfl
    have e : jFK (R := V) (FractionRing V) ≫ ptK (D.c 0) = (TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A := by
      rw [GlobalTheory.Poinc.ThetaOne.c_zero]
      rfl
    simp only [e] at a₁
    rw [GlobalTheory.UT.CoefBasic.cst_eq, hc]
    show (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J).val * _ = _
    rw [a₁, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [Fintype.prod_unique, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one, zpow_neg,
      zpow_one, id]
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.Poinc.IntTerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAevalSym
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem pull_aeval_sym : ∀ (n n' : ℕ) (L : V n' →L[ℂ] V n) (P : MvPolynomial (Fin n × Fin n) ℂ), pull L ((aeval sym P : Ev n) : Alt n) = ((aeval sym (aeval (fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)) P) : Ev n') : Alt n') := by
  intro n n' L P
  rw [MvPolynomial.comp_aeval_apply]
  have key : (pull L).comp ((Subalgebra.center ℂ (Alt n)).val.comp (aeval sym)) = (Subalgebra.center ℂ (Alt n')).val.comp
      (aeval fun x : Fin n × Fin n => aeval sym (∑ c, ∑ d,
        C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ))) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, Subalgebra.coe_val, sym, (pull_dz L _).1,
      (pull_dz L _).2, Finset.sum_mul_sum, AlgHom.commutes, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Algebra.smul_def, map_mul]
  exact congrArg (fun f => f P) key

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDataRefines
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pullData_refines : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (Q' : Data V) (e : Q'.X ≃+ Q.X) (D : DegPre V) (hB : D.TauBimult) (e' : D.X ≃+ Q'.X), PullData Q θ Q' e → Refines Q' (RingHom.id V) D e' → PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D hB) (e'.trans e) := by
  intro R V _ _ _ _ θ Q Q' e D hB e' hP hR
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, ht⟩ := hP
  obtain ⟨β', β'₂, w', hpb', hsq', hw', hc', ht'⟩ := hR
  have hs : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  letI := D.P.isAb.comm
  obtain ⟨w'', hw'', hv⟩ := _root_.GlobalTheory.LamComp.lam_comp _ _ _ D.P.A Q'.B Q.B D.P.L Q'.M.L Q.M.L
    D.P.isLB Q'.M.isLB Q.M.isLB β'₂ β₂ _ rfl w hw w' hw'
  refine ⟨β' ≫ β, β'₂ ≫ β₂, w'', ?_, ?_, hw'', fun a => ?_, fun a b => ?_⟩
  · exact (hpb'.comp hpb).congr (by rw [hs, Category.id_comp]) rfl
  · refine ⟨?_, ?_⟩
    · erw [Category.assoc, hsq.1, ← Category.assoc, hsq'.1, Category.assoc]
    · erw [Category.assoc, hsq.2, ← Category.assoc, hsq'.2, Category.assoc]
  · have h₁ : (D.c a).left ≫ β' = (Q'.c (e' a)).left := (hc' a).trans (by rw [hs, Category.id_comp])
    show (D.c a).left ≫ β' ≫ β = _
    rw [← Category.assoc, h₁]
    exact hc (e' a)
  · obtain ⟨u, x, y, k, k', hu, hy, hk, hk', h1, h2⟩ := ht (e' a) (e' b)
    refine ⟨u, x, y, k, k', hu, hy, hk, hk', h1, fun z J J' hJ hJ' => ?_⟩
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' Q'.M.isLB z
    have hκ : 𝟙 (TK V).left ≫ jK V = jK V ≫ spMap (RingHom.id V) := by rw [hs, Category.id_comp, Category.comp_id]
    have hca : ∀ a, (D.c a).left ≫ β' = (Q'.c (e' a)).left := fun a => (hc' a).trans (by rw [hs, Category.id_comp])
    have t1 := ht' (𝟙 _) hκ a b z I J' hI hJ'
    have hp : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β'₂ =
        (lift (toUnit (TK V) ≫ Q'.c (e' a)) (toUnit (TK V) ≫ Q'.c (e' b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q'.B Q'.B).left = _ ≫ (fst Q'.B Q'.B).left
        rw [Category.assoc, hsq'.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
      · show _ ≫ (snd Q'.B Q'.B).left = _ ≫ (snd Q'.B Q'.B).left
        rw [Category.assoc, hsq'.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
    have t2 := h2 z J I hJ hI
    have t3 := hv _ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J' I J hJ' hI hJ
    rw [hp] at t3
    have t0 := (Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ'
    show val (Wit.exists_tau D a b).choose (𝟙 _) z J' = _
    rw [t0, t1, t2]
    erw [t3]
    exact (mul_left_comm _ _ _).trans (congrArg _ (_root_.mul_assoc _ _ _).symm)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFields
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem algHom_aeval_ev {m m' : ℕ} {ι : Type} (φ : Alt m →ₐ[ℂ] Alt m') (u : ι → Ev m) (u' : ι → Ev m')
    (h : ∀ i, φ (u i : Alt m) = (u' i : Alt m')) (P : MvPolynomial ι ℝ) :
    φ ((aeval u (P.map (algebraMap ℝ ℂ)) : Ev m) : Alt m) = ((aeval u' (P.map (algebraMap ℝ ℂ)) : Ev m') : Alt m') := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact φ.commutes _
  | add p q hp hq =>
    simp only [map_add (f := _), Subalgebra.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, Subalgebra.coe_mul, hp, h]

theorem pullback_evalF : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  intro M M' _ _ n n' A A' g ι w w' hw P
  funext x
  exact algHom_aeval_ev _ _ _ (fun i => congrFun (hw i) x) P

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUniformisationCharacterMapConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.EndPullChar

theorem pull_char_eq : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' → ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G') (bc : G' ≅ (Over.pullback (spMap φ)).obj G), IsMonHom bc.hom → IsPullUnif φ hD bc U U' → ∀ (E : EndU U.toUnifPre) (E' : EndU U'.toUnifPre), E'.aG.left ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = bc.hom.left ≫ pullback.fst G.hom (spMap φ) ≫ E.aG.left → ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ) := by
  intro R R' _ _ _ _ I I' hR hR' φ _hφ _hI D D' hD A A' G _ _ G' _ _ _hG _hG' U U' bc _hbc hU E E' hE
  have hG : E'.aG ≫ bc.hom = bc.hom ≫ (Over.pullback (spMap φ)).map E.aG := by
    refine GlobalTheory.PullLinear.ext_of_pullback (spMap φ) ?_
    rw [Over.comp_left, Over.comp_left, Category.assoc, hE, Category.assoc,
      GlobalTheory.PullLinear.map_left_fst]
  have := E'.homG
  obtain ⟨E'', h₁, h₂, -⟩ := GlobalTheory.UT.EndBaseChange.exists_end hD hU E E'.aG hG
  have h₃ := (GlobalTheory.EndCalc.congr_data hR' E'' E' h₁).2
  intro χ
  rw [← h₂ χ, h₃]

end GlobalTheory.EndPullChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrame
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

section Pull

variable {F : Type} [Field F] {σ : F →+* ℂ} {X Y : Var F}

theorem ratVal_eq_val_ratOf (y : CxPts X.str σ) {x : X.Fn} (hx : x ∈ (ratOf X).O (under y)) :
    ratVal x y = (ratOf X).val y.1 x := by
  obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 hx).exists_fnOf
  rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
  refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
  rintro _ ⟨w, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]

theorem under_ptMap (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) :
    under (ptMap σ f hf z) = f (under z) := rfl

theorem ratVal_pull {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hφ : (ratOf X).IsHom (ratOf Y) φ f)
    (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) {g : X.Fn} (hg : g ∈ (ratOf X).O (f (under z))) :
    ratVal (φ g) z = ratVal g (ptMap σ f hf z) := by
  rw [ratVal_eq_val_ratOf z (hφ.map_mem_O hg), ratVal_eq_val_ratOf (ptMap σ f hf z) hg]
  exact (hφ.val_comp z.1 _ hg).symm

end Pull

theorem pullGram_eq_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  intro F _ σ X Y ι m E E' φ f hf hR H hH z
  refine ⟨under_ptMap f hf z, ?_⟩
  intro A hA B hB τ
  have hA' : A ∈ E.S (under (ptMap σ f hf z)) := hA
  have hA₀ : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (f (under z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have hA₀' : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (under (ptMap σ f hf z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have htr := hH.trans (ptMap σ f hf z) mem_ptsIn_top A hA' _ hA₀' τ
  unfold pullGram
  rw [htr]
  generalize (E.nonempty (under (ptMap σ f hf z))).choose = A₀ at hA₀ hA₀'

  have hg : Par 0 ((ratOf Y).O (under z)).toSubring (B * (A₀.map φ)⁻¹) := hR.sub (under z) B hB A₀ hA₀
  have hc : Par 0 ((ratOf X).O (f (under z))).toSubring (A₀ * A⁻¹) := (Fr.mem_iff hA).1 hA₀
  have hh : Par 0 ((ratOf Y).O (under z)).toSubring ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)) :=
    hc.map (φ : X.Fn →+* Y.Fn) fun x hx => hR.hom.map_mem_O hx
  have hprod : B * (A₀.map φ)⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map φ)⁻¹ := by
    change B * (A₀.map (φ : X.Fn →+* Y.Fn))⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map (φ : X.Fn →+* Y.Fn))⁻¹
    rw [Mat.map_mul, ← Mat.map_inv, mul_assoc, ← mul_assoc (A₀⁻¹.map _), ← Mat.map_mul,
      Mat.inv_mul (Fr.det_ne hA₀), Mat.map_one, one_mul, Mat.map_inv]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have hmul := hg.map_mul_of hh (ratVal · z) ψ hψ
  rw [hprod] at hmul
  have hval : ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)).map (ratVal · z) = (A₀ * A⁻¹).map (ratVal · (ptMap σ f hf z)) := by
    funext τ'
    ext i j
    exact ratVal_pull hR.hom hf z ((hc τ').1 i j)
  rw [hval] at hmul
  rw [hmul, Pi.mul_apply, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsDiagMemMaximal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPos

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (z : Sp B) (u : Aˣ) :
    gm (spMap g) z ⊤ (unitOn u) = gm (𝟙 _) z ⊤ (unitOn (Units.map g.toMonoidHom u)) := by
  refine (congrArg (fun f => gm f z ⊤ (unitOn u)) (Category.id_comp (spMap g)).symm).trans ?_
  refine (gm_pull (𝟙 _) (spMap g) z ⊤ trivial _).symm.trans ?_
  show gm (𝟙 _) z ⊤ (Units.map (spMap g).appTop.hom (unitOn u)) = _
  congr 1
  apply Units.ext
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact e.symm

theorem gm_unitOn_injective (R : Type) [CommRing R] [IsDomain R] (z : (TK R).left) (a b : (FractionRing R)ˣ)
    (h : gm (𝟙 _) z ⊤ (unitOn a) = gm (𝟙 _) z ⊤ (unitOn b)) : a = b := by
  have e := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at e
  let φ : FractionRing R →+* (TK R).left.presheaf.stalk z :=
    ((TK R).left.presheaf.germ (𝟙 (TK R).left ⁻¹ᵁ ⊤) z trivial).hom.comp
      ((Scheme.Hom.app (𝟙 (TK R).left) ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  exact Units.ext (φ.injective e)

theorem gm_generic_of_closed {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)ˣ) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (h : Sp R ⟶ X) (z : (TK R).left) (hc : h (closedPoint R) ∈ U) :
    ∃ v : Rˣ, gm (jK R ≫ h) z U a =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : h ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem h hc
  have hz : h (jK R z) ∈ U := by
    show jK R z ∈ h ⁻¹ᵁ U
    rw [htop]; trivial
  let b : Γ(Sp R, ⊤)ˣ := res htop.ge (pullU h U a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  rw [← gm_pull (jK R) h z U hz a, ← gm_res (jK R) z htop.ge trivial (pullU h U a)]
  have hb : b = unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) := by
    apply Units.ext
    exact ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _).symm
  change gm (jK R) z ⊤ b = _
  exact (congrArg (gm (jK R) z ⊤) hb).trans (gm_spMap_unitOn (algebraMap R (FractionRing R)) z _)

theorem exists_good_closed {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] {K : Type} (h : K → (Sp R ⟶ X)) (z : (TK R).left)
    (hinj : ∀ a b, jK R ≫ h a = jK R ≫ h b → h a = h b) :
    ∃ J, Good L z J ∧ ∀ k, h k (closedPoint R) ∈ L.U (J (jK R ≫ h k)) := by
  choose ch hch using fun g : Sp R ⟶ X => exists_chart hL (g (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => jK R ≫ h k) (fun k => ch (h k))
    (fun a b hab => by rw [hinj a b hab]) (fun k => by
      rw [Scheme.Hom.comp_apply]
      show jK R z ∈ h k ⁻¹ᵁ L.U (ch (h k))
      rw [Scheme.preimage_eq_top_of_closedPoint_mem (h k) (hch (h k))]; trivial)
  exact ⟨J, hJ, fun k => by rw [e k]; exact hch (h k)⟩

theorem ext_generic {X : Scheme.{0}} {W : Type} [CommRing W] (s : X ⟶ Sp W) [IsSeparated s] (R : Type) [CommRing R]
    [IsDomain R] (f g : Sp R ⟶ X) (h : jK R ≫ f = jK R ≫ g) : f = g := by
  have hs : f ≫ s = g ≫ s := by
    have e : jK R ≫ (f ≫ s) = jK R ≫ (g ≫ s) := by rw [← Category.assoc, h, Category.assoc]
    rw [← Spec.map_preimage (f ≫ s), ← Spec.map_preimage (g ≫ s)] at e ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    congr 1
    have e' := Spec.map_injective e
    ext x
    exact IsFractionRing.injective R (FractionRing R) (congrArg (fun φ => φ.hom x) e')
  have : IsDominant (jK R) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p⟩ : Nonempty (TK R).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    let y : PrimeSpectrum R := (jK R).base p
    have hy : y.asIdeal = ⊥ := by
      ext r
      refine ⟨fun hr => ?_, fun hr => by rw [Ideal.mem_bot.1 hr]; exact zero_mem _⟩
      have h1 : algebraMap R (FractionRing R) r ∈ p.asIdeal := hr
      have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ p.isPrime
      rw [hp, Ideal.mem_bot] at h1
      exact Ideal.mem_bot.2 ((IsFractionRing.injective R (FractionRing R)).eq_iff.1 (h1.trans (map_zero _).symm))
    have hcl : closure ({y} : Set (PrimeSpectrum R)) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton, hy]; exact PrimeSpectrum.zeroLocus_bot
    have key : (x : PrimeSpectrum R) ∈ closure ({y} : Set (PrimeSpectrum R)) := hcl ▸ Set.mem_univ _
    have sub : ({y} : Set (PrimeSpectrum R)) ⊆ Set.range (jK R).base := Set.singleton_subset_iff.2 ⟨p, rfl⟩
    exact closure_mono sub key
  exact ext_of_isDominant_of_isSeparated s hs (jK R) h

theorem exists_fracMap (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁)
    (hf : Function.Injective f₁) : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ ∧
      ∀ (z : (TK V₁).left) (r : V) (k : (FractionRing V)ˣ), (k : FractionRing V) = algebraMap V _ r →
        ∃ k' : (FractionRing V₁)ˣ, (k' : FractionRing V₁) = algebraMap V₁ _ (f₁ r) ∧
          gm κK z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn k') := by
  let fK : FractionRing V →+* FractionRing V₁ := IsLocalization.map (FractionRing V₁) f₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f₁ hf)
  have hfK : ∀ x, fK (algebraMap V _ x) = algebraMap V₁ _ (f₁ x) := fun x => IsLocalization.map_eq _ _
  refine ⟨spMap fK, ?_, fun z r k hk => ⟨Units.map fK.toMonoidHom k, ?_, gm_spMap_unitOn fK z k⟩⟩
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hfK x
  · rw [Units.coe_map, ← hfK, ← hk]; rfl

theorem periods_pos_diag : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ hf₁ _ hloc _ _ _ _ _ x _ w₁ q _ hP a ha
  classical
  set c := e.trans e₀ with hc
  have hy : c a ≠ 0 := (AddEquiv.map_ne_zero_iff c).2 ha
  obtain ⟨r₀, hr₀, k, hk, u, hu⟩ := _root_.GlobalTheory.DataPos.tau_diag_pos V D (c a) hy
  obtain ⟨κK, hκ, hfr⟩ := exists_fracMap V V₁ f₁ hf₁
  obtain ⟨z⟩ : Nonempty (TK V₁).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let P : Sp V₁ ⟶ (G2 B').left := (lift (x a) (x a)).left
  have : IsProper L.T.B.hom := L.T.isAb.proper
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨J, hJ, hJc⟩ := exists_good_closed L.T.M.L L.T.M.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂' ≫ (psum L.T.B (x2 L.T.B) I.down).left)
      (fun k : Fin 4 => spMap κ₁ ≫ lamPts (L.T.c₀ ((n : ℤ) • a)) (L.T.c₀ ((n : ℤ) • a)) k)) z
    (fun _ _ h => ext_generic L.T.B.hom V₁ _ _ h)
  obtain ⟨J', hJ', hJc'⟩ := exists_good_closed D.toPre.P.L D.toPre.P.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂ ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)
      (fun k : Fin 4 => spMap f₁ ≫ lamPts (D.toPre.c (c a)) (D.toPre.c (c a)) k)) z
    (fun _ _ h => ext_generic D.toPre.P.A.hom V₁ _ _ h)
  have key := hP κK hκ a a z J J' hJ hJ'
  rw [hu _ κK z J' hJ'] at key
  obtain ⟨v₁, hv₁⟩ : ∃ v : V₁ˣ, val u (κK ≫ jK V) z J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    rw [hκ]
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap f₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc' (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₂, hv₂⟩ : ∃ v : V₁ˣ, isoVal w₁ (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left z J J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    have hp : (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left = jK V₁ ≫ P := by
      rw [← comp_lift]; rfl
    unfold isoVal
    rw [hp]
    refine gm_generic_of_closed _ _ V₁ P z ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_,
      Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_⟩
    · have := hJc (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
    · have := hJc' (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₃, hv₃⟩ : ∃ v : V₁ˣ, val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • a)) ((TK V₁).hom ≫ spMap κ₁) z J =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap κ₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨k', hk', hkk⟩ := hfr z r₀ k hk
  rw [hkk, hv₁, hv₂, hv₃] at key
  have hmul : ∀ s t : (FractionRing V₁)ˣ,
      gm (𝟙 _) z ⊤ (unitOn (s * t)) = gm (𝟙 _) z ⊤ (unitOn s) * gm (𝟙 _) z ⊤ (unitOn t) := fun s t => by
    rw [← map_mul]; congr 1; exact map_mul _ _ _
  rw [← hmul, ← hmul, ← hmul] at key
  have e' := gm_unitOn_injective V₁ z _ _ key

  have hq : q a a = k' * Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v₁ * (v₂ * v₃)⁻¹) := by
    rw [map_mul, map_inv, map_mul]
    exact (eq_mul_inv_of_mul_eq e'.symm).trans (_root_.mul_assoc _ _ _)
  have hv : ((q a a : (FractionRing V₁)ˣ) : FractionRing V₁) = algebraMap V₁ _ (f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹)) := by
    rw [hq, Units.val_mul, hk', Units.coe_map, map_mul]
    rfl
  refine ⟨f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹), Ideal.mul_mem_right _ _ (map_nonunit f₁ r₀ hr₀), ?_, hv⟩
  intro hw
  apply (q a a).ne_zero
  rw [hv, hw, map_zero]

end GlobalTheory.PeriodPos
end
end

