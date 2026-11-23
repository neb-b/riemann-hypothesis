module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergenceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  first | exact @GlobalTheory.CuspFrom.exists_arc_secZ | exact GlobalTheory.CuspFrom.exists_arc_secZ | (intros; apply GlobalTheory.CuspFrom.exists_arc_secZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelAfterExt

theorem weilIs_of_ext {O C : Type} [Field O] [Field C] (β : O →+* C) {Q : PolAV (Sp O)}
    {Q' : PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left} (hQ : IsPolFibre β Q Q' ψ)
    (n : ℕ) (x y : 𝟙_ (Over (Sp O)) ⟶ Q.A) (u : Oˣ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hw : WeilIs Q'.A Q'.L n (ObjPull.secPull hQ.2.1 x) (ObjPull.secPull hQ.2.1 y)
      (unitOn (Units.map β.toMonoidHom u))) : WeilIs Q.A Q.L n x y (unitOn u) := by
  have H := hQ.2.1
  have := Q.isAb.comm
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let e : Over.mk (spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (spMap β) (Category.comp_id _)
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hQ.2.2.symm _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (ObjPull.secPull_left H x) (ObjPull.secPull_left H y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (β.injective h₅)
  exact hc

theorem exists_ext_torsion (K : Type) [Field K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (σ : K'' →+* Ω) (Q : PolAV (Sp Ω)) (ψσ : Q.A.left ⟶ P.A.left) (hQ : IsPolFibre σ P Q ψσ),
        ∀ y, y ^ N = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y := by
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points K (torsion P₀.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp K) P₀.A P₀.isAb N hN).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro K'' Ω _ _ i f hf P ψ hP σ Q ψσ hQ y hy
  letI : Algebra K' K'' := i.toAlgebra
  letI : Algebra K K'' := f.toAlgebra
  haveI : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq' hf.symm
  have hPg : IsGrpPullback P.A P₀.A (spMap f) ψ := hP.2.1
  have hQg : IsGrpPullback Q.A P.A (spMap σ) ψσ := hQ.2.1
  let x0 := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
  have hx0 : x0 ^ N = 1 := by simp only [x0, ← map_pow, hy, map_one]
  have hx0l : x0.left = (y.left ≫ ψσ) ≫ ψ := rfl
  have hmul : x0 ≫ mulN P₀.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx0, Hom.one_def]
  let t0 : _ ⟶ torsion P₀.A N := pullback.lift x0 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι P₀.A N = x0 := pullback.lift_fst _ _ _
  have hs : ((𝟙_ (Over (Sp Ω))).hom ≫ spMap σ) ≫ spMap f = spMap (σ.comp f) := by
    rw [Category.assoc, spMap_comp_spMap]
    exact Category.id_comp _
  obtain ⟨w, hw⟩ := H K'' Ω σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion P₀.A N).hom = (𝟙_ (Over (Sp K''))).hom ≫ spMap f := by
    haveI : Epi (spMap σ) := by
      letI := σ.toAlgebra
      haveI : Flat (spMap σ) := by
        rw [HasRingHomProperty.Spec_iff (P := @Flat)]
        exact RingHom.flat_algebraMap_iff.2 inferInstance
      haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
      exact Flat.epi_of_flat_of_surjective _
    apply (cancel_epi (spMap σ)).1
    rw [← Category.assoc, hw, Over.w t0]
    refine hs.trans ?_
    rw [← spMap_comp_spMap]
    exact congrArg (spMap σ ≫ ·) (Category.id_comp _).symm
  let w1 : Over.mk ((𝟙_ (Over (Sp K''))).hom ≫ spMap f) ⟶ P₀.A :=
    Over.homMk (w ≫ (torsion.ι P₀.A N).left) (by rw [Category.assoc, Over.w, hw2]; rfl)
  let x := (ObjPull.pushEquiv hPg (𝟙_ _)).symm w1
  have hxl : x.left ≫ ψ = w ≫ (torsion.ι P₀.A N).left := ObjPull.pushEquiv_symm_left hPg _ w1
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  refine hQg.1.hom_ext ?_ ?_
  · rw [ObjPull.secPull_left]
    refine hPg.1.hom_ext ?_ ?_
    · rw [Category.assoc, hxl, ← Category.assoc, hw, ← Over.comp_left, ht0, hx0l]
    · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem exists_ext_level (K : Type) [Field K] [CharZero K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' : Type) [Field K''] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (g : ℕ), P.g = g → ∀ ze : K''ˣ, IsPrimitiveRoot (ze : K'') N →
      ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp K'')) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
        (∀ x, lev x ^ N = 1) ∧ ∀ x y, WeilIs P.A P.L N (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_torsion K P₀ N hN
  refine ⟨K', inferInstance, inferInstance, hfin, fun K'' _ i f hf P ψ hP g hg ze hze => ?_⟩
  let Ω := AlgebraicClosure K''
  let σ : K'' →+* Ω := algebraMap K'' Ω
  haveI : CharZero Ω := (σ.comp f).charZero_iff (σ.comp f).injective |>.1 inferInstance
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 σ P
  obtain ⟨l, h₁, h₂, h₃⟩ := SiegPt.exists_level (O := Ω) (C := Ω) Q g N (Units.map σ.toMonoidHom ze) (hQ.1.trans hg)
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))) (hze.map_of_injective σ.injective)
  haveI : Epi (spMap σ) := by
    letI := σ.toAlgebra
    haveI : Flat (spMap σ) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext ((cancel_epi (spMap σ)).1 (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H K'' Ω i f hf P ψ hP σ Q φ hQ (l a) (h₂ a)
  have tors : ∀ a, t a ^ N = 1 := fun a => hinj (by rw [map_pow, ht, map_one, h₂])
  refine ⟨t, fun a b => hinj ?_, tors, fun a b => weilIs_of_ext σ hQ N _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, h₁]
  · rw [ht, ht, map_zpow]
    exact h₃ a b


end GlobalTheory.LevelAfterExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponentStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelGroup_transport_uniformisation_components : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  first | exact @GlobalTheory.ShareOn.exists_transport | exact GlobalTheory.ShareOn.exists_transport | (intros; apply GlobalTheory.ShareOn.exists_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOfLabels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.LabelLevel

theorem perV_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (M N M' N' : Fin g → ℤ) :
    perV τ (M + M') (N + N') = perV τ M N + perV τ M' N' := by
  have h : ∀ a b : Fin g → ℤ, cv (a + b) = cv a + cv b := fun a b => funext fun i => by simp [cv]
  simp only [perV, h, Matrix.mulVec_add]
  abel

theorem perV_smul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (M N : Fin g → ℤ) :
    perV τ ((k : ℤ) • M) ((k : ℤ) • N) = (k : ℂ) • perV τ M N := by
  have h : ∀ a : Fin g → ℤ, cv ((k : ℤ) • a) = (k : ℂ) • cv a := fun a => funext fun i => by simp [cv]
  simp only [perV, h, Matrix.mulVec_smul, smul_add]

theorem prod_single {n k : ℕ} [NeZero k] (a : Fin n → ZMod k) :
    (List.ofFn fun i => (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ZMod k)) ^ (a i).val).prod =
      Multiplicative.ofAdd a := by
  rw [List.prod_ofFn]
  simp only [← ofAdd_nsmul, ← ofAdd_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply, -ZMod.natCast_val, ZMod.natCast_zmod_val]

theorem exists_level_of_labels : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (k : ℕ), 0 < k → ∀ (ζ : ℂˣ), IsPrimitiveRoot ζ k → ∀ M Nn : (Fin (2 * g) → ZMod k) → Fin g → ℤ, ((∀ a a', ∃ M' N', M (a + a') = M a + M a' + (k : ℤ) • M' ∧ Nn (a + a') = Nn a + Nn a' + (k : ℤ) • N') ∧ (∀ a a' M' N', M a' = M a + (k : ℤ) • M' → Nn a' = Nn a + (k : ℤ) • N' → a = a') ∧ (∀ M₁ N₁, ∃ a M' N', M₁ = M a + (k : ℤ) • M' ∧ N₁ = Nn a + (k : ℤ) • N') ∧ ∀ i j, Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv (M (Pi.single i 1)) ⬝ᵥ cv (Nn (Pi.single j 1)) - cv (Nn (Pi.single i 1)) ⬝ᵥ cv (M (Pi.single j 1))) / k) = ((ζ ^ stdSymp g i j : ℂˣ) : ℂ)) → ∃ lev : Out.Level x.P k (unitOn ζ), ∀ a, (levelPoint lev hg a).left = (u.ex ((k : ℂ)⁻¹ • perV τ (M a) (Nn a))).left := by
  intro g x hg u τ a b c W hNF k hk ζ hζ M Nn ⟨hadd, _, _, hpair⟩
  subst hg
  obtain ⟨hs, hp, ha, hb, hc, hΛ, -, hfn, -⟩ := hNF
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have : NeZero k := ⟨hk.ne'⟩
  have hper : ∀ M' N', u.ex (perV τ M' N') = 1 := fun M' N' => (u.ker _).2 ((hΛ _).2 ⟨M', N', rfl⟩)
  let e : Multiplicative (Fin (2 * x.P.g) → ZMod k) →* (𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) :=
    MonoidHom.mk' (fun s => u.ex ((k : ℂ)⁻¹ • perV τ (M s.toAdd) (Nn s.toAdd))) (fun s t => by
      obtain ⟨M', N', h1, h2⟩ := hadd s.toAdd t.toAdd
      rw [toAdd_mul, h1, h2, perV_add, perV_add, perV_smul, smul_add, smul_add, inv_smul_smul₀ hk', u.ex_add,
        u.ex_add, hper, _root_.mul_one])
  let f : Multiplicative (Fin (2 * x.P.g) → ZMod k) →* (baseOver (Sp ℂ) ⟶ x.P.A) := e
  have hcv : ∀ M' N' : Fin x.P.g → ℤ, perV τ M' N' = GlobalTheory.KeyFam.per τ (Sum.elim N' M') := fun M' N' => by
    rw [perV, add_comm]; rfl
  obtain ⟨lev, hlev⟩ := GlobalTheory.Ex.FibIso.exists_level GlobalTheory.abelianSchemeLaws_all.1 x.P rfl hk' hζ
    (fun i => f (Multiplicative.ofAdd (Pi.single i 1)))
    (fun i => by
      rw [← map_pow, ← ofAdd_nsmul, ← f.map_one]
      congr 2
      funext j
      simp)
    (fun i j => by
      have h := GlobalTheory.WeilStd.weilIs_per x _ u τ a b c rfl hs hp ⟨ha, hb⟩ hc hΛ hfn k
        (Sum.elim (Nn (Pi.single i 1)) (M (Pi.single i 1))) (Sum.elim (Nn (Pi.single j 1)) (M (Pi.single j 1)))
        (ζ ^ stdSymp x.P.g i j) hk (by
          rw [← hpair i j]
          congr 2
          simp only [omegaStd, cv, dotProduct, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib]
          push_cast
          ring)
      rw [← hcv, ← hcv, show unitOn (ζ ^ stdSymp x.P.g i j) = unitOn ζ ^ stdSymp x.P.g i j from map_zpow _ _ _] at h
      exact h)
  refine ⟨lev, fun s => ?_⟩
  have h : levelPoint lev rfl s = f (Multiplicative.ofAdd s) := by
    rw [levelBasis_rfl] at hlev
    rw [levelPoint_rfl, Level.toPt, hlev, GlobalTheory.Ex.FibIso.linComb_map, prod_single]
  rw [h]
  rfl

end GlobalTheory.MBLow.LabelLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStabilizerAction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def nu (g : LevelAut Dw l) : SABMap Xo.univ.t Xo.univ.t (GlobalTheory.CompLevelStab.mv hpq hA Xo g) :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose

theorem nu_spec (g : LevelAut Dw l) :
    IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g) (nu hpq hA Xo g) (liftLa g) LinearMap.id :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.2

theorem nu_mul (c : Coeff l) (g h : LevelAut Dw l) : (nu hpq hA Xo (g * h)).φ = (nu hpq hA Xo g).φ ≫ (nu hpq hA Xo h).φ := by
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ (nu hpq hA Xo g) (nu hpq hA Xo h)
  have hg := nu_spec hpq hA Xo g
  have hh := nu_spec hpq hA Xo h
  have hc : IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g ≫ GlobalTheory.CompLevelStab.mv hpq hA Xo h) μ (liftLa (g * h))
      LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, hh.1, hg.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub g h a), hμ, ← Category.assoc, hg.2.1,
        Category.assoc, hh.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
          (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, hg.2.2, Category.assoc, hh.2.2, Category.assoc]
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.1
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo h).choose_spec.1
  rw [← hμ]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (g * h) (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo (g * h)).choose_spec.1
    inferInstance (nu_spec hpq hA Xo (g * h)) hc).2

end Moves

section Lift

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem j₀_ι' : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = i₀ TF.Y Z ≫ (TF.Y.jQ ≫ pullback.fst _ _) := j₀_ι TF.Y Z

def toF : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ TF.Y.oF.t.G.left :=
  TF.Y.m.cart.1.lift (pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z) (by
      rw [pullback.condition, Category.assoc]; exact congrArg (_ ≫ ·) (j₀_ι' TF Z))

theorem toF_m : toF TF Z ≫ TF.Y.m.φ = pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) :=
  TF.Y.m.cart.1.lift_fst _ _ _

theorem toF_hom : toF TF Z ≫ TF.Y.oF.t.G.hom =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z :=
  TF.Y.m.cart.1.lift_snd _ _ _

theorem toF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) TF.Y.oF.t.G (i₀ TF.Y Z) (toF TF Z) :=
  IsGrpPullback.cancel TF.Y.m.cart
    ((GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr (j₀_ι' TF Z) (toF_m TF Z).symm) (toF_hom TF Z)

def toU : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ Xo.univ.t.G.left := toF TF Z ≫ TF.Y.m0.toSABMap.φ

theorem toU_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) Xo.univ.t.G (i₀ TF.Y Z ≫ pullback.fst _ _)
    (toU TF Z) :=
  (toF_cart TF Z).comp TF.Y.m0.cart

theorem hom_ext' {T : Scheme.{0}} {u u' : T ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left}
    (h₁ : u ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
      u' ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (h₂ : u ≫ toU TF Z = u' ≫ toU TF Z) : u = u' :=
  (toU_cart TF Z).1.hom_ext h₂ h₁

end Lift

section Move

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem nF_w (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (toU TF Z ≫ (nu hpq hA Xo g).φ) ≫ Xo.univ.t.G.hom =
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) ≫ pullback.fst _ _ := by
  rw [Category.assoc, (nu hpq hA Xo g).cart.1.w, ← Category.assoc, (toU_cart TF Z).1.w, hr,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_fst]
  rfl

def nF (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left :=
  pullback.lift
    (TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) ≫ TF.Y.m.φ)
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r) (by
      rw [Category.assoc, TF.Y.m.cart.1.w, ← Category.assoc, TF.Y.m0.cart.1.lift_snd]
      simp only [Category.assoc]
      exact congrArg (fun x => _ ≫ r ≫ x) (j₀_ι' TF Z).symm)

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem nF_snd : nF hpq hA TF Z g r hr ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r :=
  pullback.lift_snd _ _ _

theorem nF_toF : nF hpq hA TF Z g r hr ≫ toF TF Z = TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, toF_hom, ← Category.assoc, nF_snd, Category.assoc, TF.Y.m0.cart.1.lift_snd]

theorem nF_toU : nF hpq hA TF Z g r hr ≫ toU TF Z = toU TF Z ≫ (nu hpq hA Xo g).φ := by
  rw [toU, ← Category.assoc, nF_toF]
  exact TF.Y.m0.cart.1.lift_fst _ _ _

theorem nF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) r
    (nF hpq hA TF Z g r hr) := by
  refine IsGrpPullback.cancel (toU_cart TF Z) (((toU_cart TF Z).comp (nu hpq hA Xo g).cart).congr ?_ ?_) ?_
  · rw [Category.assoc, ← GlobalTheory.CompLevelStab.mvF_fst, ← Category.assoc, ← hr, Category.assoc]
  · exact (nF_toU hpq hA TF Z g r hr).symm
  · exact nF_snd hpq hA TF Z g r hr

end Move

section Laws

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem act_toF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toF TF Z =
    toF TF Z ≫ (TF.Y.oF.t.act.act a).left := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m, Category.assoc, TF.Y.m.act a, ← Category.assoc, toF_m]
    exact GlobalTheory.EqvAct.pullAct_pullψ TF Z (j₀ TF.Y Z) a
  · rw [Category.assoc, toF_hom, Category.assoc, Over.w (TF.Y.oF.t.act.act a), toF_hom, ← Category.assoc]
    exact congrArg (· ≫ i₀ TF.Y Z) (Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a))

theorem act_toU (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toU TF Z =
    toU TF Z ≫ (Xo.univ.t.act.act a).left := by
  rw [toU, ← Category.assoc, act_toF, Category.assoc, TF.Y.m0.toSABMap.act a, Category.assoc]

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem act_nF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr =
    nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left := by
  apply hom_ext' TF Z
  · rw [Category.assoc, nF_snd, Category.assoc]
    have e := Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a)
    erw [e, ← Category.assoc, e]
    exact (nF_snd hpq hA TF Z g r hr).symm
  · have e1 : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr ≫ toU TF Z =
        toU TF Z ≫ (Xo.univ.t.act.act a).left ≫ (nu hpq hA Xo g).φ := by
      rw [nF_toU, ← Category.assoc, act_toU, Category.assoc]
    have e2 : (nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left) ≫ toU TF Z =
        toU TF Z ≫ (nu hpq hA Xo g).φ ≫ (Xo.univ.t.act.act a).left := by
      rw [Category.assoc, act_toU, ← Category.assoc, nF_toU, Category.assoc]
    rw [Category.assoc, e1, e2, (nu hpq hA Xo g).act a]

theorem sec_toU (b : Dw.La) (w : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left)
    (hw : w ≫ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _)
    (hb : w ≫ GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z) = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) :
    w ≫ toU TF Z = i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left := by
  have hF : w ≫ toF TF Z = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left := by
    apply TF.Y.m.cart.1.hom_ext
    · rw [Category.assoc, toF_m, Category.assoc]
      exact hb
    · rw [Category.assoc, toF_hom, ← Category.assoc]
      erw [hw]
      rw [Category.id_comp, Category.assoc, Over.w (TF.Y.oF.eta b)]
      exact (Category.comp_id _).symm
  rw [toU, ← Category.assoc, hF, Category.assoc, TF.Y.m0.eta b]

end Laws

end GlobalTheory.EqvInterior
end
end

