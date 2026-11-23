module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart sp fB)

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem exists_univChart_pullback {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    ∃ xc : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ (Over.pullback x).obj t.G, IsUnivChart _ n xc ∧
      ∀ cc : Fin n → A, LieLocBasis.vec t x xc cc = (tvec (x := y) cc).left ≫ ψ := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback t.G x)
  refine ⟨fun m => y m ≫ e.hom, gfp_chart_iso e hy, fun cc => ?_⟩
  have key : (tvec (x := fun m => y m ≫ e.hom) cc).left = (tvec (x := y) cc).left ≫ e.hom.left := by
    show (_ ≫ y 1 ≫ e.hom).left = (_ ≫ y 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => y m ≫ e.hom) cc).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ]

theorem isTanBasis_of_chart {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart G₁) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    IsTanBasis t x fun j => (tvec (x := y) (Pi.single j 1)).left ≫ ψ := by
  refine ⟨fun j => ?_, fun S' _ φ w hw => ?_⟩
  · obtain ⟨xc, hx, hv⟩ := exists_univChart_pullback t x h hy
    have h1 := LieLocBasis.vec_tan hx (Pi.single j 1)
    rw [hv] at h1
    exact h1
  let _ : Algebra A S' := φ.toAlgebra
  obtain ⟨y', hy', e'⟩ := LieChart.univChart_baseChange_of_chart (R' := S') G₁ C n y hy
  obtain ⟨xc', hx', hv⟩ := exists_univChart_pullback t (spMap φ ≫ x)
    ((isGrpPullback_pullback G₁ (fB A S')).comp h) hy'
  obtain ⟨cc, rfl⟩ := LieLocBasis.vec_exists hx' w hw
  have hD : (fun j => spMap (dualMap φ) ≫ (tvec (x := y) (Pi.single j 1)).left ≫ ψ) =
      fun j => LieLocBasis.vec t (spMap φ ≫ x) xc' (Pi.single j 1) := by
    funext j
    have h1 : (Pi.single j 1 : Fin n → S') = algebraMap A S' ∘ (Pi.single j 1 : Fin n → A) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    rw [hv, h1, ← Category.assoc (tvec (x := y') _).left, e', Category.assoc]
    rfl
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (LieLocBasis.comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((LieLocBasis.comb_iff hx' _ _ _).1 ha).symm

theorem exists_affine_isTanBasis (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Scheme.{0}) (ρ : S ⟶ X) (z : S) :
    ∃ (V : S.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left)),
      z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e := by
  let G : Over S := (Over.pullback ρ).obj t.G
  have : Smooth G.hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom ρ)
    infer_instance
  obtain ⟨U, hU, V, hV, e, hxU, -, hs, h⟩ :=
    LieChart.exists_isStandardSmooth_section G.hom (η[G]).left (Over.w η[G]) z ⊤ trivial
  let i : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  let G₀ : Over (Spec (CommRingCat.of Γ(S, U))) := (Over.pullback i).obj G
  have hφ₀ : IsGrpPullback G₀ G i (pullback.fst G.hom i) := isGrpPullback_pullback G i
  obtain ⟨C, hC⟩ := LieChart.exists_chart_pullback G hU hV e hs h G₀ _ hφ₀
  obtain ⟨n, y, hy⟩ := LieChart.univChart_of_chart G₀ C hC
  exact ⟨⟨U, hU⟩, n, _, hxU,
    isTanBasis_of_chart t (i ≫ ρ) (hφ₀.comp (isGrpPullback_pullback t.G ρ)) C hy⟩

end GlobalTheory.LineNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.CountableCompletion

open Cardinal IsLocalRing

theorem mk_adicCompletion_le_continuum (R : Type) [CommRing R] [Countable R] (I : Ideal R) :
    #(AdicCompletion I R) ≤ 𝔠 := by
  have hinj : Function.Injective
      (fun x : AdicCompletion I R => (x.1 : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Submodule R R))) :=
    fun x y h => Subtype.ext h
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    (mk_le_of_surjective (Submodule.mkQ_surjective _)).trans mk_le_aleph0).trans ?_
  simp

noncomputable abbrev completionCDVR (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] : CDVR :=
  haveI : CharZero (AdicCompletion (maximalIdeal R) R) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R)
  { V := AdicCompletion (maximalIdeal R) R }

theorem exists_cdvr_mk_le_continuum :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R →
      ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧
        Cardinal.mk T.V ≤ Cardinal.continuum := by
  intro R _ _ _ _ hR
  exact ⟨completionCDVR R, algebraMap R (AdicCompletion (maximalIdeal R) R),
    GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance,
    mk_adicCompletion_le_continuum R (maximalIdeal R)⟩

end GlobalTheory.CountableCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterAllChartsFurtherPlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi


open GlobalTheory.Mem.Col2.ChartLevel in
theorem chi_eq_prod_eval {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (Q : Finset (HeightOneSpectrum (𝓞 F))) (G : Q → Type) [∀ v, Group (G v)]
    (ψv : ∀ v : Q, G v →* ℂˣ) (κ : S.U) (z : ∀ v : Q, G v)
    (hoff : ∀ v, v ∉ Q → bc (prV (E := E) v) κ.1 = 1)
    (h : ∀ v : Q, S.chi (embU S v.1 (cmp S v.1 κ)) = ψv v (z v)) :
    S.chi κ = (∏ v : Q, (ψv v).comp (Pi.evalMonoidHom G v)) z := by
  rw [MonoidHom.finsetProd_apply, chi_eq_prod S Q κ (fun w _ hw => hoff w hw), ← Finset.prod_coe_sort Q]
  exact Finset.prod_congr rfl fun v _ => h v


set_option maxHeartbeats 1000000 in
theorem exists_locChi : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∃ ψv : ↥(⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) →* ℂˣ, ∀ β (x : (K β).lev.Uloc v) (w : ↥(⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1 = x.1 → (K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) = ψv w := by
  intro B X I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v hv
  have hB := GlobalTheory.Mem.Col2.QChi.nearSet_closed I hOk l Z a v
  have hC := GlobalTheory.Mem.Col2.QChi.valV_mul I hOk l Z a v
  let G' : Subgroup (GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) :=
    { carrier := GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v
      one_mem' := hB.1
      mul_mem' := fun {x y} hx hy => hB.2.1 x y hx hy
      inv_mem' := fun {x} hx => hB.2.2 x hx }
  let G'' := G'.comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom
  have hle : (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ≤ G'' :=
    iSup_le fun β' => Subgroup.comap_mono fun x hx => GlobalTheory.T.penultimateChart_localGroup_mem_nearLevelSet I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hU hchi Lb0 hLb v hv β' ⟨x, hx⟩
  let f : G'' →* ℂ :=
    { toFun := fun w => GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1)
      map_one' := by
        show GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ 1) = 1
        rw [map_one]
        exact hC.1
      map_mul' := fun x y => by
        show GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (x.1 * y.1)) = _
        rw [map_mul]
        exact hC.2 _ _ x.2 y.2 }
  refine ⟨(f.toHomUnits)⁻¹.comp (Subgroup.inclusion hle), fun β x w hw => ?_⟩
  have hd := GlobalTheory.T.furtherPlace_penultimateChart_character_inverseValue I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v hv β x
  show _ = (f.toHomUnits (Subgroup.inclusion hle w))⁻¹
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  show (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1) = 1
  exact (congrArg (fun y => (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y) hw).trans hd


set_option maxHeartbeats 1000000 in
theorem exists_chi_further : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ ψ : (∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) →* ℂˣ, ∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z := by
  intro B X I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb
  choose ψv hψv using fun (v : Q) => exists_locChi I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v.1 v.2
  refine ⟨∏ v : Q, (ψv v).comp (Pi.evalMonoidHom (fun v : Q => ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) v), ?_⟩
  intro β κ z hz hoff
  exact chi_eq_prod_eval (K β).lev Q _ ψv κ z hoff (fun v => hψv v β _ (z v) (hz v))

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSection
section
set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

open Topology in
set_option autoImplicit false in
private theorem exists_pos_int_combination_eq_zero_near_of_linearIndependent {g r : ℕ} {l₁ : Fin r → Fin g → ℂ}
    (hl : LinearIndependent ℝ l₁) :
    ∃ δ > 0, ∀ l : Fin r → Fin g → ℂ, ‖l - l₁‖ < δ → ∀ c : Fin r → ℤ,
      ‖∑ j, c j • l j‖ < δ → c = 0 := by
  set L : (Fin r → ℝ) →ₗ[ℝ] (Fin g → ℂ) := Fintype.linearCombination ℝ l₁ with hL
  have hLapp : ∀ x, L x = ∑ j, x j • l₁ j := fun x => by
    simp [hL, Fintype.linearCombination_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hl x (by rw [← hLapp]; exact hx))
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  set k : ℝ := (K : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hbound : ∀ x, ‖x‖ ≤ k * ‖L x‖ := fun x => by
    have h := hK.le_mul_dist x 0
    simp only [map_zero, dist_zero_right] at h
    nlinarith [norm_nonneg (L x)]
  refine ⟨1 / (2 * k * ((r : ℝ) + 1)), by positivity, fun l hl c hc => ?_⟩
  set δ : ℝ := 1 / (2 * k * ((r : ℝ) + 1)) with hδ
  set x : Fin r → ℝ := fun j => (c j : ℝ) with hx
  have hcx : ∑ j, c j • l j = ∑ j, x j • l j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hx, Int.cast_smul_eq_zsmul]
  have hsplit : L x = ∑ j, x j • l j - ∑ j, x j • (l j - l₁ j) := by
    rw [hLapp]
    simp [smul_sub, Finset.sum_sub_distrib]
  have hsum : ‖∑ j, x j • (l j - l₁ j)‖ ≤ r * (‖x‖ * ‖l - l₁‖) := by
    calc ‖∑ j, x j • (l j - l₁ j)‖ ≤ ∑ j, ‖x j • (l j - l₁ j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin r, ‖x‖ * ‖l - l₁‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm x j) (by simpa using norm_le_pi_norm (l - l₁) j)
          (norm_nonneg _) (norm_nonneg _)
      _ = r * (‖x‖ * ‖l - l₁‖) := by simp
  have hLx : ‖L x‖ < δ + r * (‖x‖ * δ) := by
    rw [hsplit]
    calc ‖∑ j, x j • l j - ∑ j, x j • (l j - l₁ j)‖
        ≤ ‖∑ j, x j • l j‖ + ‖∑ j, x j • (l j - l₁ j)‖ := norm_sub_le _ _
      _ < δ + r * (‖x‖ * δ) := by
        have h1 : ‖∑ j, x j • l j‖ < δ := by rw [← hcx]; exact hc
        have h2 : r * (‖x‖ * ‖l - l₁‖) ≤ r * (‖x‖ * δ) := by
          gcongr
        linarith
  have hkδ : k * δ * ((r : ℝ) + 1) = 1 / 2 := by
    rw [hδ]; field_simp
  have hxlt : ‖x‖ < 1 := by
    have hb := hbound x
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hxn := norm_nonneg x
    have hδ0 : 0 < δ := by positivity
    have : ‖x‖ < k * δ + k * δ * r * ‖x‖ := by
      calc ‖x‖ ≤ k * ‖L x‖ := hb
        _ < k * (δ + r * (‖x‖ * δ)) := mul_lt_mul_of_pos_left hLx hk0
        _ = k * δ + k * δ * r * ‖x‖ := by ring
    have hkδ0 : 0 < k * δ := mul_pos hk0 hδ0
    have hkδ' : k * δ * r + k * δ = 1 / 2 := by rw [← hkδ]; ring
    have ha : k * δ * r ≤ 1 / 2 := by linarith
    have ha2 : k * δ ≤ 1 / 2 := by nlinarith
    have hm : k * δ * r * ‖x‖ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right ha hxn
    linarith
  funext j
  have hj : ‖x j‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm x j) hxlt
  have hj' : |(c j : ℝ)| < 1 := by simpa [hx] using hj
  have : |c j| < 1 := by exact_mod_cast hj'
  simpa using Int.abs_lt_one_iff.1 this


open Topology in
set_option autoImplicit false in
theorem _root_.GlobalTheory.ShFam.Hor.LogCh.exists_const_coords (n g r : ℕ) (B : Set (Fin n → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ)
    (hB : IsPreconnected B) (hlam : ContinuousOn lam B) (hζ : ContinuousOn ζ B)
    (hbas : ∀ b ∈ B, _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (K b) (lam b)) (hmem : ∀ b ∈ B, ζ b ∈ K b)
    (hb₀ : b₀ ∈ B) :
    ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  classical
  have hex : ∀ b ∈ B, ∃ m : Fin r → ℤ, ζ b = ∑ j, m j • lam b j :=
    fun b hb => ((hbas b hb).2 (ζ b)).1 (hmem b hb)
  let F : (Fin n → ℂ) → Fin r → ℤ := fun b => if hb : b ∈ B then (hex b hb).choose else 0
  have hF : ∀ b ∈ B, ζ b = ∑ j, F b j • lam b j := by
    intro b hb
    simp only [F, dite_eq_left hb]
    exact (hex b hb).choose_spec
  have hloc : ∀ b₁ ∈ B, ∀ᶠ b in 𝓝[B] b₁, F b = F b₁ := by
    intro b₁ hb₁
    obtain ⟨δ, hδ, hkey⟩ := exists_pos_int_combination_eq_zero_near_of_linearIndependent (hbas b₁ hb₁).1
    have h1 : ∀ᶠ b in 𝓝[B] b₁, ‖lam b - lam b₁‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖lam b - lam b₁‖) B b₁ :=
        ((hlam b₁ hb₁).sub continuousWithinAt_const).norm
      exact hc.eventually (eventually_lt_nhds (by simpa using hδ))
    have hcomb : Continuous (fun l : Fin r → Fin g → ℂ => ∑ j, F b₁ j • l j) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).const_smul (F b₁ j)
    have h2 : ∀ᶠ b in 𝓝[B] b₁, ‖ζ b - ∑ j, F b₁ j • lam b j‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖ζ b - ∑ j, F b₁ j • lam b j‖) B b₁ :=
        ((hζ b₁ hb₁).sub (hcomb.continuousAt.comp_continuousWithinAt (hlam b₁ hb₁))).norm
      refine hc.eventually (eventually_lt_nhds ?_)
      show ‖ζ b₁ - ∑ j, F b₁ j • lam b₁ j‖ < δ
      rw [← hF b₁ hb₁, sub_self, norm_zero]
      exact hδ
    filter_upwards [h1, h2, self_mem_nhdsWithin] with b hb1 hb2 hbB
    have hdiff : ∑ j, (F b - F b₁) j • lam b j = ζ b - ∑ j, F b₁ j • lam b j := by
      rw [hF b hbB]
      simp [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.1 (hkey (lam b) hb1 (F b - F b₁) (by rw [hdiff]; exact hb2))
  have hcont : ContinuousOn F B := fun b₁ hb₁ =>
    continuousWithinAt_const.congr_of_eventuallyEq (hloc b₁ hb₁) rfl
  refine ⟨F b₀, fun b hb => ?_⟩
  rw [← hB.constant hcont hb hb₀]
  exact hF b hb

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartRescaleFrameChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ρ : ℝ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ → Metric.ball 0 ρ ⊆ e0.target → (∀ j, HolAlong e0.source fun x => e0 x j) → IsHolTo e0.target (fun z => (e0.symm z).1) → IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) → (∀ x ∈ e0.source, ‖e0 x‖ < ρ → IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) → DifferentiableOn ℂ A (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (A z).det) → ∃ (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex' : ExpMaps Z σ g), IsExpChart e ex' ∧ e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} ∧ (∀ x ∈ e.source, e x = ρ⁻¹ • e0 x) ∧ ∀ x ∈ e.source, ∀ w, ex' x w = ex x (A (e0 x) *ᵥ w) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e0 ex ρ A hρ hball hhol hsymm hjoint hexp hA hdet
  have hss : ∀ z : Fin n → ℂ, (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ.ne')).symm z = ρ • z := fun z => by
    simp [Homeomorph.smulOfNeZero, Units.smul_def]
  have hnorm : ∀ z : Fin n → ℂ, ‖ρ • z‖ < ρ ↔ ‖z‖ < 1 := fun z => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_lt_iff_lt_one_right hρ
  let e1 := e0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin n → ℂ) ρ) Metric.isOpen_ball)
  let hs : (Fin n → ℂ) ≃ₜ (Fin n → ℂ) := Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ.ne')
  let e := e1.transHomeomorph hs
  have he_app : ∀ x, e x = ρ⁻¹ • e0 x := fun x => rfl
  have he_symm : ∀ z, e.symm z = e0.symm (ρ • z) := fun z => by
    simp [e, e1, hs, Homeomorph.smulOfNeZero, Units.smul_def]
  have he_src : e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} := by
    ext x
    simp [e, e1]
  have hss' : ∀ z, hs.symm z = ρ • z := hss
  have he_tgt : e.target = Metric.ball 0 1 := by
    ext z
    show z ∈ (e1.transHomeomorph hs).target ↔ _
    rw [OpenPartialHomeomorph.transHomeomorph_target, Set.mem_preimage, hss']
    show ρ • z ∈ (e0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin n → ℂ) ρ) Metric.isOpen_ball)).target ↔ _
    rw [OpenPartialHomeomorph.trans_target]
    show ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ρ • z ∈ e0.target ↔ _
    rw [mem_ball_zero_iff, mem_ball_zero_iff]
    constructor
    · rintro ⟨h, -⟩
      exact (hnorm z).1 h
    · intro h
      exact ⟨(hnorm z).2 h, hball (mem_ball_zero_iff.2 ((hnorm z).2 h))⟩
  have hsrc : ∀ x ∈ e.source, x ∈ e0.source ∧ ‖e0 x‖ < ρ := fun x hx => by
    rw [he_src] at hx
    exact hx
  refine ⟨e, fun x w => ex x (A (e0 x) *ᵥ w), ⟨he_tgt, ?_, ?_, ?_, ?_, ?_⟩, he_src, fun x _ => he_app x, fun _ _ _ => rfl⟩
  · intro k V _ _ _ B x hB hx hm
    have hd := hhol k V B x hB hx fun b hb => (hsrc _ (hm hb)).1
    refine (hd.const_mul ((ρ⁻¹ : ℝ) : ℂ)).congr fun b _ => ?_
    simp [he_app, Complex.real_smul]
  · rw [he_tgt]
    refine GlobalTheory.HolPeriods.isHolTo_congr (GlobalTheory.HolPeriods.isHolTo_comp hsymm Metric.isOpen_ball
      (φ := fun z => ρ • z) ?_ ?_) fun z _ => by rw [he_symm]
    · exact differentiableOn_id.const_smul ρ
    · intro z hz
      exact hball (mem_ball_zero_iff.2 ((hnorm z).2 (mem_ball_zero_iff.1 hz)))
  · intro x hx v w
    obtain ⟨h1, h2⟩ := hsrc x hx
    simp only [Matrix.mulVec_add]
    exact (hexp x h1 h2).1 _ _
  · rw [he_tgt]
    have hmaps : Set.MapsTo (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ρ • zw.1, A (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) (Metric.ball 0 ρ ×ˢ Set.univ) := fun zw hzw =>
      ⟨mem_ball_zero_iff.2 ((hnorm _).2 (mem_ball_zero_iff.1 hzw.1)), trivial⟩
    have hdiff : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ρ • zw.1, A (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      have h1 : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => ρ • zw.1) (Metric.ball 0 1 ×ˢ Set.univ) :=
        differentiableOn_fst.const_smul ρ
      refine h1.prodMk (differentiableOn_pi.2 fun i => ?_)
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ => ?_
      have hij : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => A (ρ • zw.1) i j)
          (Metric.ball 0 1 ×ˢ Set.univ) := by
        have hA2 : DifferentiableOn ℂ (fun z => (Matrix.of.symm (A z) : Fin g → Fin g → ℂ)) (Metric.ball 0 ρ) := hA
        have hL : DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 ρ) :=
          differentiableOn_pi.1 (differentiableOn_pi.1 hA2 i) j
        exact hL.comp h1
          fun zw hzw => (hmaps hzw).1
      exact hij.mul (differentiableOn_pi.1 differentiableOn_snd j)
    refine GlobalTheory.HolPeriods.isHolTo_congr (GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ)
      hdiff hmaps) fun zw hzw => ?_
    have hz : ρ • zw.1 ∈ e0.target := hball (hmaps hzw).1
    simp only [he_symm, e0.right_inv hz]
    rw [he_symm]
  · intro x hx
    obtain ⟨h1, h2⟩ := hsrc x hx
    have hU : IsUnit (A (e0 x)).det := hdet _ (mem_ball_zero_iff.2 h2)
    let k := Matrix.toLinearEquiv' (A (e0 x)) (Matrix.invertibleOfIsUnitDet _ hU)
    have hk : ∀ w, k w = A (e0 x) *ᵥ w := fun _ => rfl
    have hD : ∀ w v, IsDerivAt0 (fun u => (ex x (A (e0 x) *ᵥ u)).left) w v ↔
        IsDerivAt0 (fun u => (ex x u).left) (A (e0 x) *ᵥ w) v := fun w v => by
      simpa only [hk] using GlobalTheory.HolPeriods.isDerivAt0_comp_equiv (fun u => (ex x u).left) k w v
    obtain ⟨-, hT1, hT2⟩ := hexp x h1 h2
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · simp only [hD]
      exact hT1 _
    · obtain ⟨w', hw', hu⟩ := hT2 v hv
      refine ⟨k.symm w', ?_, fun w hw => ?_⟩
      · beta_reduce
        rw [hD, ← hk, k.apply_symm_apply]
        exact hw'
      · beta_reduce at hw
        rw [hD, ← hk] at hw
        rw [← hu _ hw, k.symm_apply_apply]

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem exists_matches : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ), x ≫ genStr Z = spMap φ → ψ.comp φ = σ → (∀ s, (spMap ψ ≫ x) s ∉ genBd Z) → ∃ y : FrPt Xo c (CAt σ), Matches fr ψ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ hx hψ hb
  subst hψ
  have := Z.jQ_open
  have : IsLocalRing (CAt (ψ.comp φ)) := inferInstanceAs (IsLocalRing ℂ)
  let ψ' : A →+* CAt (ψ.comp φ) := ψ
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A (CAt (ψ.comp φ)) φ (x ≫ genι Z) fr ψ'
  have hr : Set.range (spMap ψ' ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact not_not.1 (hb s)
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap ψ' ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt (ψ.comp φ))) := by
    rw [← Z.jQ_over, ← Category.assoc, hxF, Category.assoc]
    exact (congrArg (spMap ψ' ≫ ·) hx).trans (OpenReg.spMap_comp _ _)
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (R := CAt (ψ.comp φ)) xF hs
    (x := spMap ψ' ≫ x ≫ genι Z) (by rw [← Category.assoc, hxF, Category.assoc]) g
  have hp : GlobalTheory.AllWt.ptF y = xF := by
    apply pullback.hom_ext
    · rw [← hy]; exact pullback.lift_fst _ _ _
    · rw [hs]; exact pullback.lift_snd _ _ _
  refine ⟨y, by rw [hp]; exact hxF, fun τ i => ⟨w τ i, by rw [hp]; exact (hw τ i).1, (hw τ i).2.1, ?_⟩⟩
  exact (hw τ i).2.2.trans (hg τ i)

end GlobalTheory.ShFam.BdArc
end

