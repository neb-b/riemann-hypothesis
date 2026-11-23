module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsNsmulOfCommon
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.AmpleTwist

theorem cls_nsmul_of_common {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ)
    (a : Λ) : cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

theorem ampleAt_of_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (A : LB TF.Y.X), A.IsLB → ∀ (ρ χ : AllWt.Weight Dw) (n m : ℕ), IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) → ∀ (y : Y₀ TF.X Z) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), y ∈ nonzeroLocus s → AmpleAt (L₀ TF.X Z (m • χ - ρ)) y := by
  intro E _ _ _ H Dw l Xo c TF Z A hA ρ χ n m hamp y s hs
  have hAg : (A.pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hA _
  have hP : (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n).IsLB := isLB_lbPow hAg n
  have hρ := isLB_L₀ TF.X Z ρ
  have hB : (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)).IsLB := hamp.isLB
  have hN := isLB_L₀ TF.X Z (m • χ - ρ)
  have hN1 := isLB_lbPow hN 1
  have hD := LB.isLB_div hN1 hB
  have hχ := isLB_L₀ TF.X Z χ
  have hχm := isLB_lbPow hχ m
  have hAn := isLB_lbPow hA n
  have hAng : ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hAn _
  have hT := LB.isLB_div hχm hAng
  have hiso : LBIso (LB.div (lbPow (L₀ TF.X Z (m • χ - ρ)) 1)
      (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)))
      (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))) := by
    refine (cls_eq_iff hD hT).1 ?_
    have e := cls_common_add (common₀ TF.X Z) (m • χ - ρ) ρ
    rw [sub_add_cancel] at e
    have e2 := cls_nsmul_of_common (common₀ TF.X Z) m χ
    rw [cls_div hN1 hB hD, cls_div hP hρ hB, cls_lbPow hN 1 hN1, cls_lbPow hAg n hP, cls_pull hA _ hAg,
      cls_div hχm hAng hT, cls_pull hAn _ hAng, cls_lbPow hA n hAn, cls_lbPow hχ m hχm, map_nsmul]
    have e3 : cls (L₀ TF.X Z (m • χ - ρ)) hN = m • cls (L₀ TF.X Z χ) hχ - cls (L₀ TF.X Z ρ) hρ := by
      rw [← e2, e, add_sub_cancel_right]
    rw [e3]
    abel
  obtain ⟨s', hs'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hT hiso s
  refine ⟨1, LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ), s', one_pos, hB, hamp, ?_⟩
  rw [hs']
  exact hs

end GlobalTheory.HSApp.AmpleTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.PureLift GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.GrpTangent
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

theorem eq_epsScale_of_isLieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {c : Fin 1 → R}
    {v : Fin 1 → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb c v w) : w = epsScale (c 0) ≫ v 0 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : (List.ofFn u).prod = u 0 := by simp
  rw [h1]
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact hu 0

theorem push_sub_smul_mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : LieExact A)
    {v : Fin 1 → (epsR R ⟶ A)} (hv : IsLieBasis v) (W : A ⟶ A) [IsMonHom W] {s : Fin 1 → R}
    (e : IsLieComb s v (v 0 ≫ W)) (y : HdR A) : push (dp0 R) (𝟙 _) W y - s 0 • y ∈ Fil A := by
  obtain ⟨u, hu⟩ := (hA.1 y).exists
  obtain ⟨c, hc, -⟩ := hv.2 u hu.1
  have hu' : u = epsScale (c 0) ≫ v 0 := eq_epsScale_of_isLieComb hc
  have hW : v 0 ≫ W = epsScale (s 0) ≫ v 0 := eq_epsScale_of_isLieComb e
  have key : u ≫ W = epsScale (s 0) ≫ u := by
    rw [hu', Category.assoc, hW, epsScale_mul_assoc, epsScale_mul_assoc, mul_comm]
  have h1 := hu.push W
  rw [key] at h1
  exact h1.sub_mem (hu.smul (s 0))

theorem exists_isPolForm (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨hall, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨z, hz⟩ : ∃ z, IsChern (dp0 R) (A.hom ≫ 𝟙 (Sp R)) L z :=
    GlobalTheory.Cris.ChernExists.exists_isChern L hL
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hmem : ∀ x, x ∈ prim (dp0 R) (𝟙 (Sp R)) A := fun x => by
    rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hall]
    exact Submodule.mem_top
  refine ⟨_, n, fun k => ⟨a k, hmem _⟩, fun k => ⟨b k, hmem _⟩, ?_, rfl⟩
  have hz' : z = ∑ k, cup _ (a k) (b k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.apply_symm_apply z, ← hab, map_sum]
    exact Finset.sum_congr rfl fun k _ => he _ _
  rw [hz'] at hz
  exact hz

private theorem pGen_pull_refl {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (F : Y ⟶ X) :
    PGen (⟨fun p => (L.pull F).g p.1 p.2⟩ : LB.Iso (L.pull F) (L.pull F)) := by
  intro Z f y j j' k k' h1 h2 h3 h4
  unfold gw
  dsimp only
  have e1 : (f ≫ F) y ∈ L.U j := h1
  have e2 : (f ≫ F) y ∈ L.U j' := h2
  have e3' : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 h3
  have e3 : (f ≫ F) y ∈ L.U (k PUnit.unit) := e3'
  have e4' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 h4
  have e4 : (f ≫ F) y ∈ L.U (k' PUnit.unit) := e4'
  rw [gm_pull_g L F f y (fun _ => j) k (mem_pull.2 h1) h3, gm_pull_g L F f y k k' h3 h4,
    gm_pull_g L F f y (fun _ => j') k' (mem_pull.2 h2) h4]
  have c1 := gm_cocycle hL (f ≫ F) y e1 e2 e4
  have c2 := gm_cocycle hL (f ≫ F) y e1 e4 e3
  have c3 := gm_cocycle hL (f ≫ F) y e3 e4 e3
  have c4 := gm_cocycle hL (f ≫ F) y e3 e3 e3
  have hkk : (gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit))) (L.g (k PUnit.unit) (k PUnit.unit)) = 1 := by
    have h := congrArg (· * ((gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit)))
      (L.g (k PUnit.unit) (k PUnit.unit)))⁻¹) c4
    simpa using h
  have hinv := eq_inv_of_mul_eq_one_right (c3.trans hkk)
  rw [← c2, ← c1, hinv, mul_right_comm]

theorem isPureBC_ell : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω),
    IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  intro hP E _ _ _ H S _ ω C
  unfold IsPureBC
  intro R _ f A _ φ hpb W' _ hW'

  haveI : IsCommMonObj A := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb
  have hA : IsAbelianScheme A := by
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hpb.1 C.P.isAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hpb.1 C.P.isAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 C.P.isAb.geomConnected⟩
  have hgG : SmoothOfRelativeDimension 1 C.P.A.hom := by
    have h := C.P.smoothDim
    rw [C.dim] at h
    exact h
  have hgA : SmoothOfRelativeDimension 1 A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hpb.1 hgG
  have hLie : LieExact A := (hP.2.1 R A 1 hA hgA).1

  haveI := hgG
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange S R f C.P.A A φ hpb
    (SmoothOfRelativeDimension.smooth 1 C.P.A.hom) 1 ![C.v] C.basis
  have hu : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (![C.v] i).left := hv'φ
  have hw : (v' 0 ≫ W').left ≫ φ = spMap (Chart.dualMapR f) ≫ (C.v ≫ C.act.act (GlobalTheory.CM.wK H)).left := by
    rw [Over.comp_left, Category.assoc, hW', ← Category.assoc, hu 0, Over.comp_left, Category.assoc]
    rfl
  have e : IsLieComb (fun i => f (![ω] i)) v' (v' 0 ≫ W') := by
    have he := eq_epsScale_of_isLieComb C.eig
    have hs : spMap (epsScaleR (f ω)) ≫ spMap (Chart.dualMapR f) =
        spMap (Chart.dualMapR f) ≫ spMap (epsScaleR ω) := by
      rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
      congr 1
      ext r <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    have heq : v' 0 ≫ W' = epsScale (f ω) ≫ v' 0 := by
      apply Over.OverMorphism.ext
      apply hpb.1.hom_ext
      · rw [hw, he, Over.comp_left, Over.comp_left, Category.assoc, hu 0]
        change (spMap (Chart.dualMapR f) ≫ spMap (epsScaleR ω)) ≫ C.v.left =
          spMap (epsScaleR (f ω)) ≫ (spMap (Chart.dualMapR f) ≫ C.v.left)
        rw [← hs, Category.assoc]
      · rw [Over.w, Over.w]
    refine ⟨fun _ => epsScale (f ω) ≫ v' 0, ?_, ?_⟩
    · intro i
      fin_cases i
      rfl
    · simpa using heq
  have hquot : ∀ y : HdR A, push (dp0 R) (𝟙 _) W' y - f ω • y ∈ Fil A :=
    fun y => push_sub_smul_mem_Fil hLie hv' W' e y

  have hL' : (C.P.L.pull φ).IsLB := pull_isLB C.P.isLB φ
  obtain ⟨ψ, hψ⟩ := exists_isPolForm hP.1 hA hgA hL'
  obtain ⟨hiso, hperf⟩ := hP.2.2.2.2 R A 1 hA hgA (C.P.L.pull φ) hL' ψ hψ
  have hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A (C.P.L.pull φ) :=
    kTriv_pull hpb C.P.isLB hL' (pGen_pull_refl C.P.L C.P.isLB φ) C.P.ktriv
  haveI := hperf hK

  obtain ⟨o', ho'⟩ := GlobalTheory.CM.ellPull_exists_oAct hpb C.act
  haveI := o'.hom (GlobalTheory.CM.wK H)
  haveI := o'.hom (1 - GlobalTheory.CM.wK H)
  have hWo : o'.act (GlobalTheory.CM.wK H) = W' := by
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [ho', hW']
    · rw [Over.w, Over.w]

  have hb : ((1 - GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.bar ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) := by
    rw [show ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.w0 from rfl, GlobalTheory.CM.kform_bar_w0]
    push_cast
    rfl
  have HG : LBIso (cubeLB C.P.A ![fst C.P.A C.P.A ≫ C.act.act (GlobalTheory.CM.wK H), snd C.P.A C.P.A] C.P.L)
      (cubeLB C.P.A ![fst C.P.A C.P.A, snd C.P.A C.P.A ≫ C.act.act (1 - GlobalTheory.CM.wK H)] C.P.L) := by
    have h := C.adj (GlobalTheory.CM.wK H) (1 - GlobalTheory.CM.wK H) hb
    unfold GlobalTheory.CM.LamEq at h
    simpa only [Category.comp_id] using h
  have HA := GlobalTheory.PolAdjoint.lbIso_cube hpb C.P.L hW' (ho' (1 - GlobalTheory.CM.wK H)) HG
  have hadj : ∀ x y : HdR A, ψ (push (dp0 R) (𝟙 _) W' x) y =
      ψ x (push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y) :=
    GlobalTheory.PolAdjoint.adjoint_of_lbIso hP.1 hA hgA hL' hψ W' (o'.act (1 - GlobalTheory.CM.wK H)) HA
  have hpushb : ∀ y : HdR A, push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y = y - push (dp0 R) (𝟙 _) W' y := by
    intro y
    have h1 : GlobalTheory.DeRham.act (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H) = 1 - push (dp0 R) (𝟙 _) W' := by
      set_option synthInstance.maxHeartbeats 200000 in
       rw [map_sub, map_one, GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (GlobalTheory.CM.wK H),
        push_congr (dp0 R) (𝟙 _) hWo]
    rw [← GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H), h1]
    rfl

  have hfil : ∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W' x = f (1 - ω) • x := by
    intro x hx
    have hlie : ∀ y : HdR A, ψ x (push (dp0 R) (𝟙 _) W' y) = f ω * ψ x y := by
      intro y
      have h0 := hiso x hx _ (hquot y)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have key : ψ (push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x) = 0 := by
      ext y
      rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hadj, hpushb, map_sub, hlie, map_sub, map_one,
        smul_eq_mul, LinearMap.zero_apply]
      ring
    have hinj := (LinearMap.IsPerfPair.bijective_left ψ).1
    have h0 : push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x = 0 := hinj (by rw [key, map_zero])
    exact sub_eq_zero.mp h0
  exact ⟨hfil, hquot⟩

end GlobalTheory.PureLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CnormMapConjMulVec
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.GramFrame

open Matrix Module
open scoped ComplexOrder InnerProductSpace

variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def gramOf {n : ℕ} (w : Fin n → Hs) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => ⟪w i, w j⟫_ℂ

theorem norm_sum_sq {n : ℕ} (w : Fin n → Hs) (c : Fin n → ℂ) :
    ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ (gramOf w *ᵥ c) := by
  have h1 : ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = ⟪∑ i, c i • w i, ∑ i, c i • w i⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, dotProduct, mulVec, gramOf, of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem gramOf_posDef {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) : (gramOf w).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun c hc => ?_⟩
  · ext i j
    simp [gramOf, conjTranspose_apply]
  · rw [← norm_sum_sq]
    have h0 : ∑ i, c i • w i ≠ 0 := fun h => hc (funext fun i => Fintype.linearIndependent_iff.1 hw c h i)
    exact Complex.zero_lt_real.2 (by positivity)

theorem exists_frame {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ ∀ c, Formalism.HermitianLatticesTheory.cnorm (B *ᵥ c) = ‖∑ i, c i • w i‖ := by
  obtain ⟨B, hB, hG⟩ := exists_unit_factor (gramOf_posDef hw)
  refine ⟨B, hB, fun c => ?_⟩
  have key : star (B *ᵥ c) ⬝ᵥ (B *ᵥ c) = star c ⬝ᵥ ((Bᴴ * B) *ᵥ c) := by
    have e0 : star c ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ c)) = (star c ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ c) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ((∑ i, ‖(B *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_norm_sq_eq, norm_sum_sq, hG, key]
  simp only [Formalism.HermitianLatticesTheory.cnorm, Complex.ofReal_injective e, Real.sqrt_sq (norm_nonneg _)]

theorem cnorm_map_conj_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (B.map (starRingEnd ℂ) *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ star u) := by
  have e : B.map (starRingEnd ℂ) *ᵥ u = star (B *ᵥ star u) := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [e]
  simp [Formalism.HermitianLatticesTheory.cnorm]

end GlobalTheory.HSApp.GramFrame


open GlobalTheory.HSApp.GramFrame Matrix Module in
theorem GlobalTheory.HSApp.hasGram_of_inner : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ), (∀ v : InfinitePlace K, ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (Φ : V →+ Hs), ((∀ (a : K) (x : V), Φ (a • x) = v.embedding a • Φ x) ∨ (∀ (a : K) (x : V), Φ (a • x) = starRingEnd ℂ (v.embedding a) • Φ x)) ∧ (∀ x, N v.embedding x = ‖Φ x‖) ∧ ∀ (n : ℕ) (e : Fin n → V), LinearIndependent K e → LinearIndependent ℂ (fun i => Φ (e i))) → GlobalTheory.AllWt.HasGram N := by
  intro K V _ _ _ _ _ N h
  classical
  let b := Module.finBasis K V
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K V)) (Fin (finrank K V)) ℂ, IsUnit Y.det ∧
      ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x) = N v.embedding x := by
    intro v
    obtain ⟨Hs, i1, i2, Φ, hlin, hN, hli⟩ := h v
    obtain ⟨B, hB, hBn⟩ := exists_frame (hli _ b b.linearIndependent)
    have hsum : ∀ x, Φ x = ∑ i, Φ (b.repr x i • b i) := fun x => by
      conv_lhs => rw [← b.sum_repr x]
      exact map_sum Φ _ _
    rcases hlin with hl | hl
    · refine ⟨B, hB, fun x => ?_⟩
      rw [hN, hBn, hsum]
      simp only [hl]
      rfl
    · refine ⟨B.map (starRingEnd ℂ), ?_, fun x => ?_⟩
      · have e := RingHom.map_det (starRingEnd ℂ) B
        change IsUnit ((starRingEnd ℂ).mapMatrix B).det
        rw [← e]
        exact hB.map _
      · rw [cnorm_map_conj_mulVec, hN, hBn, hsum]
        simp only [hl]
        rfl
  choose Y hY hYn using key
  refine GlobalTheory.AllWt.IsGram.hasGram (b := b) (X := fun v => (Y v)⁻¹) fun v => ⟨isUnit_nonsing_inv_det _ (hY v), fun x => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
  rw [nonsing_inv_nonsing_inv _ (hY v)]
  exact hYn v x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.CoefIndepProof

theorem coefIndep : GlobalTheory.BaseCmp.CoefIndep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i c0L hc h w hw
  obtain ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩ := hw
  obtain ⟨gramR, c0R, hT⟩ := hc
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := (R.B.L i A.μ0).pres.reps (fin (Vc D i) h)
  have hst : Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D i)) : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) :=
    Formalism.L2.DIV.parLev_St k.2.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl _ _ hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP ⊢
  obtain ⟨P', hP', rfl⟩ := hP
  obtain ⟨e', -, h2', -, h4', -⟩ := hT'.coefL i A.μ0
  obtain ⟨e1, -, h2, -, h4, -⟩ := hT.coefL i A.μ0
  rw [← h4' c] at hP'
  obtain ⟨y, hy, rfl⟩ := hP'
  refine ⟨rhoVr (labLL D) (lamV D i) γE (e1 y), ⟨e1 y, ?_, rfl⟩, ?_⟩
  · rw [← h4 c]; exact ⟨y, hy, rfl⟩
  · have a1 := (hT'.mapL i).1 γ γE hγ (e' y)
    have a2 := (hT.mapL i).1 γ γE hγ (e1 y)
    change c0L' i (rhoVr (labLL D) (lamV D i) γE (e' y)) = c0L i (rhoVr (labLL D) (lamV D i) γE (e1 y))
    rw [a1, ← h2', h2]
    exact a2.symm

end GlobalTheory.CoefIndepProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedPairLatticeDilationMemOfInteger
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BaseCmp

theorem dil_mem_latP (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ϖ : 𝓞 D.host.E) : ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  intro y hy
  have hint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := by
    have e : finPart D (incA D (ϖ : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (ϖ : D.host.E) := rfl
    rw [e]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simpa using (one_mem (v.adicCompletionIntegers D.host.F)), ϖ, rfl⟩
  have h := GlobalTheory.LatticeStable.smul_mem_latO D (Vc D i) (Wc D i) _ _ _ (incA D (ϖ : D.host.E)) hint y hy
  exact h

end GlobalTheory.BaseCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsRatioOnComponentOfBirational
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

set_option synthInstance.maxHeartbeats 1000000 in
theorem ratioOn_of_birOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), ∀ (Z : Comp Xo c) (G : WTZ E), BirOn U Z G → RatioOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U Z G hB τ t _
  exact _root_.GlobalTheory.DegVal.isRatio_of_genRatios _ _ _ _ hB τ _

end GlobalTheory.DegVal

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedPartsStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  first | exact @GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep | exact GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep | (intros; apply GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep <;> assumption)
end

