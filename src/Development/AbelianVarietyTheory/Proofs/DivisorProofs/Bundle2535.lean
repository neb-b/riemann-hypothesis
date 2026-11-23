module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem genFibre_endo_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∃ (A₀ : Over (Sp Ω)) (_ : GrpObj A₀) (a₀ : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ FinalForm.G.left), IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a₀ ∧ IsGrpPullback A₀ FinalForm.G M.pt ψ ∧ (∀ e : ρ.P.A ⟶ ρ.P.A, IsMonHom e → ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₀ = a₀ ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left) ∧ ∀ b : S.Gam, ∃ gγ : Over.mk M.pt ⟶ FinalForm.G, gγ ^ (S.r * S.N) = 1 ∧ (∀ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap S.R.val.toRingHom ≫ (ρ.pt b).left → w ≫ ψ = gγ.left) ∧ ∀ z, b ∈ S.HH M z → ExtNear gγ z := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hU
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gA := isGrpPullback_pullback FinalForm.G M.pt
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    gA.congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  have gψ' : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) ρ.P.A (spMap S.R.val.toRingHom)
      (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := gψ.congr (FinalForm.u₀_gen x hx) rfl
  refine ⟨(Over.pullback M.pt).obj FinalForm.G, inferInstance, ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀,
    pullback.fst FinalForm.G.hom M.pt, gψ', gA, ?_, ?_⟩
  · intro e he
    haveI := he
    obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ' e
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    refine ⟨F, hF, fun e₀ he₀ => ?_⟩
    have hw'l : w'.left ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ e.left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    have he₀w : e₀ = w' := hom_ext_of_pullback gψ' (he₀.trans hw'l.symm)
    rw [he₀w, ← hFw]
    simp only [Over.pullback_map_left, pullback.lift_fst]
  · intro b
    have hb : (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) ≫ ρ.P.A.hom = 𝟙 _ ≫ spMap S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (ρ.pt b)]; simp
    let w₀ := gψ'.1.lift _ _ hb
    have hw₁ : w₀ ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = spMap S.R.val.toRingHom ≫ (ρ.pt b).left :=
      gψ'.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ pullback.snd FinalForm.G.hom M.pt = 𝟙 _ := gψ'.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G := Over.homMk w₀ hw₂
    let V : Over.mk M.pt ⟶ Over.mk (𝟙 (Sp Ω) ≫ M.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk M.pt ⟶ FinalForm.G := V ≫ pushPt gA.1.w sec0
    have hgl : gγ.left = w₀ ≫ pullback.fst FinalForm.G.hom M.pt := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : ρ.pt 0 = 1 := by
        have := ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (ρ.pt b) ^ n = ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← ρ.pt_add, succ_nsmul]
      have hrN : (S.r * S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp Ω) ≫ spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) :=
        Over.homMk (spMap S.R.val.toRingHom) (by simp)
      have hs : pushPt gψ'.1.w sec0 = U ≫ ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (S.r * S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective gψ'
        have e1 : pushPt gψ'.1.w (sec0 ^ (S.r * S.N)) = (pushPt gψ'.1.w sec0) ^ (S.r * S.N) :=
          map_pow (pushHom gψ' _) sec0 _
        have e2 : pushPt gψ'.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
          map_one (pushHom gψ' _)
        have e3 : (U ≫ ρ.pt b) ^ (S.r * S.N) = U ≫ (ρ.pt b) ^ (S.r * S.N) :=
          (map_pow (preHom U) (ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp S.R) ⟶ ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (S.r * S.N) = V ≫ (pushPt gA.1.w sec0) ^ (S.r * S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gA.1.w sec0) ^ (S.r * S.N) = pushPt gA.1.w (sec0 ^ (S.r * S.N)) :=
        (map_pow (pushHom gA _) sec0 _).symm
      have f3 : pushPt gA.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
        map_one (pushHom gA _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp Ω) ≫ M.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := gψ'.1.hom_ext (by rw [h2, hw₁]) (by
        show w ≫ pullback.snd FinalForm.G.hom M.pt = w₀ ≫ pullback.snd FinalForm.G.hom M.pt
        rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro z hz
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec z b hz
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_, Category.assoc, hν₁]
      · rw [Category.assoc, ← Category.assoc ν, hν₁, pullback.condition, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc]; exact hw₁

end GlobalTheory.Poinc.FibLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZe
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem torsion_lies_under : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V →
    ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N →
      ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 →
      ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧
        (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧
        ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 →
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  intro V _ _ _ hCN D A G _ _ hG U N hN β hβ
  haveI : CharZero V := hCN.2.2.2
  have hA := GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  obtain ⟨p, hpy, hpb⟩ := GlobalTheory.TorusExt.exists_qkPt_of_torsion (F := AlgebraicClosure (FractionRing V))
    D.tau_bimult (n := N) (by omega) hβ
  refine ⟨f p, ?_, ⟨p, hpy, (hf.1 p (f p)).2 rfl⟩, fun p' hp'y hp' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · have e : f p = f p' := (hf.1 p' (f p)).1 hp'
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    obtain ⟨z, hy, w, hw₁, hw₂⟩ := (hf.2.2.1 p p').1 e
    have hg := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hw₂
    rw [hp'y, hpy, zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h | h
      · omega
      · exact h
    subst hz
    have hw : w.b = 1 := by
      exact hw₁.1.trans (cPoint_zero _)
    rw [hg, GlobalTheory.TorusExt.add_b, hw, _root_.mul_one, hpb]

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedSectionGenericValueNonvanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl.Glued

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U W : X.Opens} (h : W ≤ U) (f : Γ(X, U))
    (hy : ⊤ ≤ y ⁻¹ᵁ W) : valF y W (resG X h f) = valF y U f := by
  have hU : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => h (hy ha)
  unfold valF
  rw [dite_eq_left hy, dite_eq_left hU]
  congr 1
  show (X.presheaf.map (homOfLE h).op ≫ y.appLE W ⊤ hy).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem glued : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  intro S G _ L K _ ξ V κ N s s' v hN hsup hres hgen hnz
  refine ⟨fun ⟨k⟩ => ?_, ?_⟩
  · obtain ⟨hξk, hk⟩ := hgen k
    refine ⟨hξk.trans (hN k), ?_⟩
    rw [← hk]
    funext j
    unfold genPull
    rw [← hres k (j 0)]
    show _ = (G.left.presheaf.map _ ≫ (snd (Over.mk ξ) G).left.appLE _ _ _).hom (s' (j 0))
    rw [Scheme.Hom.map_appLE]
  · intro K' _ _ x hx
    obtain ⟨p⟩ : Nonempty (Sp K') := inferInstance
    have hp : x p ∈ (⨆ k, N k : S.Opens) := hsup ▸ hx ⟨p, rfl⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have hxk : Set.range x ⊆ N k := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      exact hk
    obtain ⟨y, i, hyx, hyr, hval⟩ := hnz k K' x hxk
    refine ⟨y, i, hyx, fun z hz => ⟨(hyr hz).1, hN k (hyr hz).2⟩, ?_⟩
    rw [← hres k i] at hval
    convert hval using 1
    exact (valF_resG y _ (s' i) ((GlobalTheory.ZH.top_le_preimage_iff _ _).2 hyr)).symm

end GlobalTheory.UMin.ThBdl.Glued
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmooth
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leadMinor_re_pos_of_posDef {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) :
    0 < (leadMinor G j).re := by
  have hsub : (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).PosDef :=
    hG.submatrix Subtype.val_injective
  have h := hsub.det_pos
  unfold leadMinor
  exact (Complex.pos_iff.mp h).1

theorem contDiffAt_leadMinor {n s : ℕ} {G : V n → Matrix (Fin s) (Fin s) ℂ} {v : V n}
    (h : MContDiffAt ∞ G v) (j : ℕ) : ContDiffAt ℝ ∞ (fun x => leadMinor (G x) j) v :=
  (h.submatrix _ _).det

theorem ldPart_grD_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef →
    MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  intro n s G v hG hp
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have hnum : ContDiffAt ℝ ∞ (fun x => ((G x).submatrix
        (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det) v :=
      (hG.submatrix _ _).det
    have hden := contDiffAt_leadMinor hG (j : ℕ)
    have hne : leadMinor (G v) j ≠ 0 := fun h0 => by
      have := leadMinor_re_pos_of_posDef hp j
      rw [h0] at this; simp at this
    simp only [ldPart, Matrix.of_apply]
    exact hnum.mul (hden.inv hne)
  · have hnum : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) (i + 1)).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    have hden : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) i).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    exact hnum.div hden (leadMinor_re_pos_of_posDef hp i).ne'

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ}

theorem leadMinor_pos_of_posDef (h : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0 := by
  have h1 : 0 < leadMinor G j := (h.submatrix Subtype.val_injective).det_pos
  rw [Complex.lt_def] at h1
  exact ⟨by simpa using h1.1, by simpa using h1.2.symm⟩

theorem ldPart_diag_of_posDef (h : G.PosDef) (i : Fin s) : 0 < grD G i ∧ ldPart G i i = grD G i := by
  obtain ⟨a1, a2⟩ := leadMinor_pos_of_posDef h ((i : ℕ) + 1)
  obtain ⟨b1, b2⟩ := leadMinor_pos_of_posDef h (i : ℕ)
  refine ⟨div_pos a1 b1, ?_⟩
  have e : (fun a : {a : Fin s // (a : ℕ) < (i : ℕ) + 1} => if a.1 = i then i else a.1) = Subtype.val := by
    funext a
    split_ifs with ha
    · exact ha.symm
    · rfl
  have ea : leadMinor G ((i : ℕ) + 1) = ((leadMinor G ((i : ℕ) + 1)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using a2)
  have eb : leadMinor G (i : ℕ) = ((leadMinor G (i : ℕ)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using b2)
  simp only [ldPart, Matrix.of_apply, grD]
  rw [e, Complex.ofReal_div, ← ea, ← eb]
  rfl

theorem ldPart_eq_zero_of_lt (G : Matrix (Fin s) (Fin s) ℂ) {i j : Fin s} (hij : i < j) : ldPart G i j = 0 := by
  have hij' : (i : ℕ) < j := hij
  simp only [ldPart, Matrix.of_apply]
  rw [Matrix.det_zero_of_row_eq (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩), zero_div]
  · intro h
    exact hij.ne (congrArg Subtype.val h)
  · funext b
    simp [Matrix.submatrix_apply]

theorem ldPart_posDef_spec : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  intro s G h
  refine ⟨leadMinor_pos_of_posDef h, ldPart_diag_of_posDef h, fun i j hij => ldPart_eq_zero_of_lt G hij, ?_⟩
  rw [Matrix.det_of_lowerTriangular (ldPart G) (fun i j hij => ldPart_eq_zero_of_lt G (by simpa using hij)),
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  obtain ⟨h1, h2⟩ := ldPart_diag_of_posDef h i
  rw [h2]
  exact_mod_cast h1.ne'

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem inv_pullback_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (G' : Over Y) [GrpObj G'] {T : Over X}
    (z : T ⟶ (Over.pullback f).obj G') :
    (z⁻¹).left ≫ pullback.fst G'.hom f = z.left ≫ pullback.fst G'.hom f ≫ ι[G'].left := by
  show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]

theorem exists_inv_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc
  have hfl : Flat G.hom := inferInstance
  have D := fun (W : Scheme.{0}) => _root_.GlobalTheory.MorDescent.descend R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb
  have epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b := by
    intro W a b hab
    obtain ⟨h₀, -, hu⟩ := D W (β ≫ a) (by rw [pullback.condition_assoc])
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hw : β ≫ G.hom = G'.hom ≫ π := hpb.w
  set a₁ := pullback.fst β β
  set a₂ := pullback.snd β β
  have hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π := by
    simp only [Category.assoc, ← hw]; rw [pullback.condition_assoc]
  let σ : pullback β β ⟶ pullback π π := pullback.lift _ _ hσ
  let x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G' :=
    Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G',
      y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β =
        (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
    intro y; rw [Over.comp_left, Category.assoc, ← hc]
  have h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂ := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hcx x]
      show pullback.lift a₁ σ _ ≫ _ ≫ β = _
      rw [pullback.lift_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]
      exact pullback.lift_snd _ _ _
  have eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β := by
    have := hcx x⁻¹
    rw [GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst,
      reassoc_of% h2] at this
    simp only [x, Over.homMk_left] at this
    rwa [pullback.lift_fst_assoc] at this
  obtain ⟨h₀, hh₀, -⟩ := D G.left (ι[G'].left ≫ β) eq
  have hover : h₀ ≫ G.hom = G.hom := by
    apply epi
    rw [reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]
  refine ⟨Over.homMk h₀ hover, ?_⟩
  intro T x' x₀ hx
  rw [Over.comp_left]
  show x₀.left ≫ h₀ = _
  rw [hx, Category.assoc, hh₀]
  show _ = (x' ≫ ι[G']).left ≫ β
  rw [Over.comp_left, Category.assoc]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pullback_one_left_fst {S P : Scheme.{0}} (f : P ⟶ S) (G' : Over S) [GrpObj G'] :
    (η[(Over.pullback f).obj G'] : _ ⟶ _).left ≫ pullback.fst G'.hom f = f ≫ η[G'].left := by
  simp [Functor.monObjObj]

theorem descend_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R))
    (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom →
    pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β →
    ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S),
      (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hβ φ hφ hc
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_id_snd
  have hfl : Flat (𝟙 (Sp R)) := inferInstance

  have heq : pullback.fst π π ≫ (η[G'].left ≫ β) = pullback.snd π π ≫ (η[G'].left ≫ β) := by
    have h1 := pullback_one_left_fst (pullback.fst π π) G'
    have h2 := pullback_one_left_fst (pullback.snd π π) G'
    have hu : (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left =
        (η : _ ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    calc pullback.fst π π ≫ (η[G'].left ≫ β)
        = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β := by
          rw [reassoc_of% h1]
      _ = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left ≫
            pullback.fst G'.hom (pullback.snd π π) ≫ β := by rw [hc]
      _ = pullback.snd π π ≫ (η[G'].left ≫ β) := by rw [reassoc_of% hu, reassoc_of% h2]
  obtain ⟨h₀, hh₀, -⟩ := _root_.GlobalTheory.MorDescent.descend R S (Sp R) S G.left π (𝟙 _) π (𝟙 S) hP hS hI hfl sq _ heq

  have hepi : ∀ {W : Scheme.{0}} (a b : Sp R ⟶ W), π ≫ a = π ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc'⟩ := _root_.GlobalTheory.MorDescent.descend R S (Sp R) S W π (𝟙 _) π (𝟙 S) hP hS hI hfl sq (π ≫ a)
      (by rw [pullback.condition_assoc])
    exact (hc' a rfl).trans (hc' b hab.symm).symm
  have hsec : h₀ ≫ G.hom = 𝟙 (Sp R) := by
    apply hepi
    rw [reassoc_of% hh₀, hβ.w]
    simp
  refine ⟨Over.homMk h₀ (by simpa using hsec), fun T => ?_⟩
  simp [Hom.one_def]
  rw [hh₀]

end GlobalTheory.Mum
end
end

