module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CompHS GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.FlagHodge

attribute [local instance] Over.cartesianMonoidalCategory

theorem ev_cocycle {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {S : Type} [CommRing S] (z : Sp S ⟶ Z) (i j k : L.ι)
    (hij : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j)) (hjk : ⊤ ≤ z ⁻¹ᵁ (L.U j ⊓ L.U k)) (hik : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    ev z _ hij (L.g i j).val * ev z _ hjk (L.g j k).val = ev z _ hik (L.g i k).val := by
  have h3 : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_preimage_inf hij (le_preimage_mono inf_le_right hjk)
  have e := congrArg (fun u => ev z _ h3 u.val) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (ev_res z _ h3 hij _).symm (ev_res z _ h3 hjk _).symm).trans
    ((map_mul (ev z _ h3) _ _).symm.trans (e.trans (ev_res z _ h3 hik _)))

theorem lbIso_of_coboundary {Z : Scheme.{0}} {J : Type} {U : J → Z.Opens} {g g' : ∀ i j, Γ(Z, U i ⊓ U j)ˣ}
    (hA : (⟨J, U, g⟩ : LB Z).IsLB) (d : ∀ k, Γ(Z, U k)ˣ)
    (h : ∀ k k', (g' k k').val * resG Z inf_le_right (d k').val = (g k k').val * resG Z inf_le_left (d k).val) :
    LBIso (⟨J, U, g⟩ : LB Z) ⟨J, U, g'⟩ := by
  refine ⟨⟨fun p => g p.1 p.2 * res inf_le_left (d p.1)⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ U p.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ U q.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ U q.2 := le_preimage_mono inf_le_right hq
  have c₁ := ev_cocycle hA z p.1 p.2 q.2 hp (le_preimage_inf hp2 hq2) (le_preimage_inf hp1 hq2)
  have c₂ := ev_cocycle hA z p.1 q.1 q.2 (le_preimage_inf hp1 hq1) hq (le_preimage_inf hp1 hq2)
  have c₃ := congrArg (ev z _ (le_preimage_inf hp1 hq1)) (h p.1 q.1)
  rw [map_mul, map_mul, ev_res z _ _ hq1, ev_res z _ _ hp1] at c₃
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((map_mul (ev z _ hp) _ _).trans
    (congrArg (_ * ·) (ev_res z _ hp hp1 _)))) (ev_res z _ hz (le_preimage_inf hp2 hq2) _)).trans (Eq.trans ?_
    (congrArg₂ (· * ·) (ev_res z _ hz (le_preimage_inf hp1 hq1) _) ((ev_res z _ hz hq _).trans
      ((map_mul (ev z _ hq) _ _).trans (congrArg (_ * ·) (ev_res z _ hq hq1 _))))).symm)
  have alg : ∀ a b e m n u v w : S, a * b = e → m * n = e → w * v = m * u → a * u * b = w * (n * v) :=
    fun a b e m n u v w h₁ h₂ h₃ => by linear_combination u * (h₁ - h₂) - n * h₃
  exact alg _ _ _ _ _ _ _ _ c₁ c₂ c₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

theorem exists_eigFrame {W : X.YY.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S] (z : Sp S ⟶ X.YY)
    (hzW : ⊤ ≤ z ⁻¹ᵁ W) : ∃ φ : c.F →+* S, ∀ (k : X.F.J) (_ : W ≤ X.F.U k) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
      ∃ f : EigFrame Y φ (z ≫ X.π), ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(X.YY, W) →+* S, spMap ψ ≫ tau hW = z := ⟨_, spMap_ev z hW hzW⟩
  haveI := X.proper
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian X.YY := LocallyOfFiniteType.isLocallyNoetherian (X.π ≫ Y.s)
  obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* Γ(X.YY, W), spMap φ = tau hW ≫ X.π ≫ Y.s :=
    ⟨(Spec.preimage (tau hW ≫ X.π ≫ Y.s)).hom, Spec.map_preimage _⟩
  refine ⟨ψ.comp φ, fun k hk hz => ?_⟩
  obtain ⟨K, _, ρ, hρ, hK⟩ := affineOpen_injects_to_dense X.YY (flagOpen X) (dense_flagOpen X) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have h₀ : ⊤ ≤ tau hW ⁻¹ᵁ X.F.U k := tau_le hW hk
  have hz' : ⊤ ≤ (spMap ρ ≫ tau hW) ⁻¹ᵁ X.F.U k := le_preimage_comp _ h₀
  have hr : Set.range ((spMap ρ ≫ tau hW) ≫ X.π) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift Y.j ((spMap ρ ≫ tau hW) ≫ X.π) hr
  have hyK : yK ≫ Y.j = (spMap ρ ≫ tau hW) ≫ X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap ρ ≫ tau hW) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ tau hW) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (tau hW) k h₀ hz'
    (key _ hyK.symm fun σ => X.top K yK hy _ hyK.symm k hz' σ)
  obtain ⟨f, hf⟩ := f₀.exists_isMap ψ rfl (Category.assoc _ _ _)
  refine ⟨f, fun τ => funext fun i => tan_ext_left ?_⟩
  rw [← X.F.tanPull_vecAt k ψ (tau hW) h₀ hz rfl rfl (Category.assoc _ _ _).symm τ i, tanPull_left, ← hf₀, ← hf]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]

def allDet (k : X.F.J) : Γ(X.YY, X.F.U k) :=
  rdet (Matrix.of fun (j : Fin (X.F.M k).n) (a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) =>
    X.F.u k ((Fintype.equivFin _).symm a).1 j ((Fintype.equivFin _).symm a).2)

theorem ev_allDet (k : X.F.J) {S : Type} [CommRing S] {z : Sp S ⟶ X.YY} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {φ : c.F →+* S}
    {f : EigFrame Y φ (z ≫ X.π)} (hf : ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ) :
    ev z _ hz (allDet X k) = frameDet (X.F.M k).toMChart (X.F.inM hz rfl) f := by
  rw [allDet, map_rdet, frameDet]
  congr 1
  ext j a
  simp [Module.Basis.toMatrix_apply, eigBasisFin, eigBasis_apply, hf, Frames.vecAt, Frames.uAt, vec,
    Finsupp.single_apply]

theorem isUnit_allDet (k : X.F.J) : IsUnit (allDet X k) := by
  refine X.YY.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k) (x := x) hx
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW (tau hW) (tau_le hW le_rfl)
  obtain ⟨f, hf⟩ := hφ k hle (tau_le hW hle)
  have hu := isUnit_frameDet (X.F.M k).toMChart (X.F.inM (tau_le hW hle) rfl) f
  rw [← ev_allDet X k _ hf, ev_tau hW hle] at hu
  have := hu.map (X.YY.presheaf.germ W x hxW).hom
  rwa [show (X.YY.presheaf.germ W x hxW).hom (resG X.YY hle (allDet X k)) = _ from
    X.YY.presheaf.germ_res_apply (homOfLE hle) x hxW _] at this

theorem lbIso_detOm_Llam : LBIso X.detOm (X.Llam (mu0 Dw)) := by
  classical
  rw [FlagCover.Llam, unitaryWeightExponentVector_signatureWeightMuZero]
  refine lbIso_of_coboundary X.F.isLB_detOm (fun k => (isUnit_allDet X k).unit) fun k k' =>
    ext_ev_loc fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k ⊓ X.F.U k') (x := x) hx
  refine ⟨W, hxW, fun S _ z hh hzW => ?_⟩
  have hz := le_preimage_mono inf_le_left hh
  have hz' := le_preimage_mono inf_le_right hh
  have hM := le_preimage_inf (X.F.inM hz rfl) (X.F.inM hz' rfl)
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW z hzW
  obtain ⟨f, hf⟩ := hφ k (fun _ h => (hle h).1) hz
  obtain ⟨f', hf'⟩ := hφ k' (fun _ h => (hle h).2) hz'
  have hco : ∀ τ, f.co f' τ = (X.F.B k k' τ).map (ev z _ hh) := fun τ => by
    ext a i
    have e := f.vec_eq f' τ i
    rw [hf', X.F.vecAt_eq_sum k k' z hz hz' hh rfl τ i, ← hf] at e
    exact ((Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ)) _ _ e a).symm
  have e₁ := (ev_detChg_mul_frameDet (X.F.M k).toMChart (X.F.M k').toMChart (X.F.inM hz rfl) (X.F.inM hz' rfl) hM
    f').trans (frameDet_change _ _ f f')
  have e₂ : ∏ τ, (f.co f' τ).det = (∏ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), X.F.TAt k k' z hh (some p)).val := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hco, Matrix.det_of_upperTriangular (X.F.B_map_tri k k' τ _)]
    rfl
  have e₃ := X.F.ev_LL_g (fun ix => ix.elim 0 fun _ => 1) k k' z hh
  rw [Fintype.prod_option] at e₃
  simp only [Option.elim, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one, Finset.prod_inv_distrib] at e₃
  let a : Sˣ := Units.map (ev (z ≫ X.π) _ hM).toMonoidHom (detChg (X.F.M k).toMChart (X.F.M k').toMChart)
  have e₄ : ev z _ hh (X.F.detOm.g k k').val = (a⁻¹).val :=
    (ev_unit_inv z hh _).trans (congrArg (fun u : Sˣ => (u⁻¹).val) (Units.ext (ev_appLE z X.π _ hh hM _)))
  rw [← ev_allDet X k hz hf, ← ev_allDet X k' hz' hf', e₂] at e₁
  rw [map_mul, map_mul, ev_res z _ hh hz, ev_res z _ hh hz']
  refine (congrArg (· * _) e₃).trans (Eq.trans ?_ (congrArg (· * _) e₄).symm)
  rw [_root_.one_mul, Units.inv_mul_eq_iff_eq_mul, mul_left_comm, Units.eq_inv_mul_iff_mul_eq, _root_.mul_comm (Units.val _) (ev z _ hz _)]
  exact e₁

end GlobalTheory.FlagHodge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinear
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_prod_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ f f' g hg hf hf'
  have key : ∀ y, liftSemi g y =
      (liftSemi f (TensorProduct.prodRight R R' R' M N y).1,
        liftSemi f' (TensorProduct.prodRight R R' R' M N y).2) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul x c => simp [liftSemi_tmul, hg]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]; ext <;> simp
  have e : ⇑(liftSemi g) = Prod.map (liftSemi f) (liftSemi f') ∘ (TensorProduct.prodRight R R' R' M N) :=
    funext key
  rw [e]
  exact (hf.prodMap hf').comp (TensorProduct.prodRight R R' R' M N).bijective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.PinchLift

open TopologicalSpace

theorem sec_eq_of_germ {X : Scheme.{0}} {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx a = X.presheaf.germ U x hx b) : a = b :=
  TopCat.Presheaf.section_ext X.sheaf U a b h

theorem germ_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (a : Γ(X, U)) :
    X.presheaf.germ V x hx (resG X h a) = X.presheaf.germ U x (h hx) a :=
  X.presheaf.germ_res_apply (homOfLE h) x hx a

theorem epi_toPushforward_of_closedImm {X' Z' : Scheme.{0}} (i' : Z' ⟶ X') [IsClosedImmersion i'] {L' : LB X'}
    (hL : L'.IsLB) : Epi (GlobalTheory.LB.toPushforward L' i') := by
  refine GlobalTheory.QCoh.epi_of_locally_app_surjective _ fun W x hx => ?_
  obtain ⟨k, hk⟩ := exists_chart hL x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W ⊓ L'.U k from ⟨hx, hk⟩) (W ⊓ L'.U k).2
  have hVW : V ≤ W ⊓ L'.U k := hle
  have hVk : V ≤ L'.U k := hVW.trans inf_le_right
  refine ⟨V, hxV, hVW.trans inf_le_left, fun t => ?_⟩
  have h' : i' ⁻¹ᵁ V ≤ (L'.pull i').U (fun _ => k) := (i'.preimage_mono hVk).trans (GlobalTheory.LB.pull_U i' (fun _ => k)).ge
  obtain ⟨b, hb⟩ := i'.app_surjective V hV
    (GlobalTheory.LB.chartEquiv (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i') (fun _ => k) h' t)
  refine ⟨(GlobalTheory.LB.chartEquiv hL k hVk).symm b, ?_⟩
  apply (GlobalTheory.LB.chartEquiv (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i') (fun _ => k) h').injective
  rw [← hb]
  exact (GlobalTheory.LB.chartEquiv_pullSec i' hL (fun _ => k) hVk h' _).trans
    (congrArg (i'.app V).hom (LinearEquiv.apply_symm_apply _ _))

theorem lift_section_of_closedImm : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  intro X' Z' i' _ L' hL Y' hY τ hτ
  have hL' := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i'
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL'
  haveI := epi_toPushforward_of_closedImm i' hL
  have hsurj := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (GlobalTheory.LB.toPushforward L' i') hY
  have le1 : ∀ m : (L'.pull i').ι, i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U m ≤ i' ⁻¹ᵁ (L'.U (m PUnit.unit) ⊓ Y') :=
    fun m z hz => ⟨GlobalTheory.LB.pull_U_le i' m hz.2, hz.1⟩
  let c : ∀ m, Γ(Z', i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U m) := fun m => resG Z' (le1 m) (τ (m PUnit.unit))
  have hc : c ∈ secOn (L'.pull i') (i' ⁻¹ᵁ Y') := by
    intro m n
    apply sec_eq_of_germ
    intro z hz
    have hzm : z ∈ i' ⁻¹ᵁ (L'.U (m PUnit.unit) ⊓ Y') := le1 m ⟨hz.1.1, hz.1.2⟩
    have hzn : z ∈ i' ⁻¹ᵁ (L'.U (n PUnit.unit) ⊓ Y') := le1 n ⟨hz.1.1, hz.2⟩
    simp only [c, map_mul, germ_resG]
    rw [hτ (m PUnit.unit) (n PUnit.unit) z hzm hzn]
    congr 1
    have e := GlobalTheory.LB.resG_pull_g (L := L') i' m n (le_refl _)
    rw [GlobalTheory.LB.resG_self] at e
    rw [e, ← GlobalTheory.LB.resG_app, germ_resG]
  obtain ⟨s, hs⟩ := hsurj (GlobalTheory.LB.mkSec c hc)
  have hcoord : ∀ k, (i'.appLE (Y' ⊓ L'.U k) (i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U (fun _ => k))
      (GlobalTheory.LB.pull_inf_le i' Y' (fun _ => k))).hom (GlobalTheory.LB.coord s k) = c (fun _ => k) := fun k => by
    have := congrArg (fun u => GlobalTheory.LB.coord u (fun _ : PUnit => k)) hs
    exact Eq.trans (GlobalTheory.LB.coord_pullSec i' s _).symm this
  refine ⟨fun k => resG X' (le_inf inf_le_right inf_le_left : L'.U k ⊓ Y' ≤ Y' ⊓ L'.U k) (GlobalTheory.LB.coord s k),
    ?_, ?_⟩
  · intro k l x hk hl
    have hx3 : x ∈ Y' ⊓ L'.U k ⊓ L'.U l := ⟨⟨hk.2, hk.1⟩, hl.1⟩
    have e := GlobalTheory.LB.coord_mem s k l
    simp only [germ_resG]
    rw [← germ_resG (inf_le_left : Y' ⊓ L'.U k ⊓ L'.U l ≤ Y' ⊓ L'.U k) x hx3, e, map_mul, germ_resG, germ_resG]
  · intro k
    have h : L'.U k ⊓ Y' ≤ Y' ⊓ L'.U k := le_inf inf_le_right inf_le_left
    apply sec_eq_of_germ
    intro z hz
    have hzB : z ∈ i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U (fun _ => k) :=
      ⟨hz.2, (GlobalTheory.LB.pull_U i' (fun _ => k)).ge hz.1⟩
    have e1 : (i'.app (L'.U k ⊓ Y')).hom (resG X' h (GlobalTheory.LB.coord s k)) =
        (i'.appLE (Y' ⊓ L'.U k) (i' ⁻¹ᵁ (L'.U k ⊓ Y')) (i'.preimage_mono h)).hom (GlobalTheory.LB.coord s k) := by
      rw [← Scheme.Hom.appLE_eq_app, GlobalTheory.LB.appLE_resG]
    show Z'.presheaf.germ _ z hz ((i'.app (L'.U k ⊓ Y')).hom (resG X' h (GlobalTheory.LB.coord s k))) = _
    rw [e1, ← GlobalTheory.LB.resG_app, germ_resG,
      ← germ_resG (GlobalTheory.LB.pull_inf_le i' Y' (fun _ => k)) z hzB, GlobalTheory.LB.resG_app, hcoord k]
    simp only [c, germ_resG]

end GlobalTheory.PinchLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSectionsNextThickeningStandardCharts
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftCech

variable {R : Type} [CommRing R]

theorem map_cst_rs {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) {U V : X.Opens}
    (h : V ≤ U) {x : Γ(X, U)} (hx : x ∈ J.map (cst f U)) : rs X h x ∈ J.map (cst f V) := by
  have h' := Ideal.mem_map_of_mem (rs X h) hx
  rw [Ideal.map_map] at h'
  have e : (rs X h).comp (cst f U) = cst f V := RingHom.ext fun r => rs_cst f h r
  rwa [e] at h'

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs_eq f y U h, map_sub]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split <;> simp

end GlobalTheory.FormalAlg.LiftCech


open GlobalTheory.FormalAlg.LiftCech in
theorem GlobalTheory.FormalAlg.lift_cech : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  intro R _ I Y β hβ n C e k hH g hg hgρ σ hσ
  have hbp := (_root_.GlobalTheory.FormalAlg.towerSquares R I Y β hβ).1 e
  have hk := _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) _ _ _ (β e) (Y e).hom hbp
  have hbas := (_root_.GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod R I Y β hβ n C).1 (e + 1)
  have hz := (_root_.GlobalTheory.FormalAlg.LevSurj.ev_surjective R I Y β hβ n C).1 (e + 1)
  have hA : ∀ i j, IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    hbas i j ▸ (C.aff (e + 1) i).basicOpen _
  have hker : ∀ (V : (Y (e + 1)).left.Opens), IsAffineOpen V → ∀ x,
      ((β e).app V).hom x = 0 ↔ x ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V := fun V hV x => by
    rw [← RingHom.mem_ker, (hk.2.2 V hV).2]; rfl
  have hmem : ∀ (J : Ideal R) {U V : (Y (e + 1)).left.Opens} (h : V ≤ U) {x : Γ((Y (e + 1)).left, U)},
      x ∈ towerIdeal Y (e + 1) J U → rs (Y (e + 1)).left h x ∈ towerIdeal Y (e + 1) J V :=
    fun J _ _ h _ hx => map_cst_rs _ J h hx
  have hmul : ∀ (V : (Y (e + 1)).left.Opens) (x y : Γ((Y (e + 1)).left, V)), x ∈ towerIdeal Y (e + 1) I V →
      y ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V → x * y = 0 := by
    intro V x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h
    rw [← Ideal.map_mul, ← pow_succ'] at h
    have h0 := hz V
    unfold towerIdeal at h0
    rw [h0] at h
    exact (Submodule.mem_bot _).1 h
  choose τ hτ using fun i => (hk.2.2 _ (C.aff (e + 1) i)).1 (σ i)
  have key : ∀ (x : (Y e).left) i, β e x ∈ C.D (e + 1) i →
      gs (β e) x (C.D (e + 1) i) (τ i) = gs (𝟙 _) x _ (σ i) := fun x i hxi => by
    rw [← hτ i, gs_pull (𝟙 _) (β e) x _ hxi, Category.id_comp]
  let c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j)
  have hcdef : ∀ i j, c i j = rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j) := fun _ _ => rfl
  have hc : ∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _ := by
    intro i j
    rw [← hker _ (hA i j)]
    apply fn_ext
    intro x hx
    have hxi : β e x ∈ C.D (e + 1) i := hx.1
    have hxj : β e x ∈ C.D (e + 1) j := hx.2
    rw [gs_pull (𝟙 _) (β e) x _ hx, Category.id_comp, gs_zero',
      hcdef, gs_sub' _ _ _ hx, gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, key x i hxi, key x j hxj,
      hσ x i j hxi hxj, sub_self]
  have hcoc : ∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l) := by
    intro i j l
    have h1 : rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (g i j).val * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) := by
      rw [← sub_eq_zero, ← sub_mul]
      refine hmul _ _ _ ?_ (hmem _ _ (hc j l))
      have h := hmem I (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (hgρ i j)
      rwa [map_sub, map_pow, rs_rs] at h
    have hco := congrArg Units.val (hg.cocycle i j l)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hco
    rw [← h1, hcdef, hcdef, hcdef]
    simp only [map_sub, map_mul, rs_rs]
    linear_combination (-(rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) l) (τ l))) * hco
  obtain ⟨a, ha, hca⟩ := hH c hc hcoc
  refine ⟨⟨fun i => τ i - a i, fun i j => ?_⟩, fun i => ?_⟩
  · have h2 : (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) := by
      rw [← sub_eq_zero, ← sub_mul]
      exact hmul _ _ _ (hgρ i j) (hmem _ _ (ha j))
    have h3 := hca i j
    rw [hcdef] at h3
    change rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i - a i) = (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j - a j)
    rw [map_sub, map_sub]
    linear_combination h3 + h2
  · change ((β e).app (C.D (e + 1) i)).hom (τ i - a i) = σ i
    rw [map_sub, hτ i, (hker _ (C.aff (e + 1) i) (a i)).2 (ha i), sub_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactCokernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_bijective_of_exact_cokernel : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (N : Type) [AddCommGroup N] [Module R N] (Z : Type) [AddCommGroup Z] [Module R Z] (Q : Type) [AddCommGroup Q] [Module R Q] (N' : Type) [AddCommGroup N'] [Module R' N'] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (Q' : Type) [AddCommGroup Q'] [Module R' Q'] (d : N →ₗ[R] Z) (p : Z →ₗ[R] Q) (d' : N' →ₗ[R'] Z') (p' : Z' →ₗ[R'] Q') (fN : N →ₛₗ[algebraMap R R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fQ : Q →ₛₗ[algebraMap R R'] Q'), Function.Exact d p → Function.Surjective p → Function.Exact d' p' → Function.Surjective p' → (∀ x, d' (fN x) = fZ (d x)) → (∀ z, p' (fZ z) = fQ (p z)) → Function.Surjective (liftSemi fN) → Function.Bijective (liftSemi fZ) → Function.Bijective (liftSemi fQ) := by
  intro R R' _ _ _ N _ _ Z _ _ Q _ _ N' _ _ Z' _ _ Q' _ _ d p d' p' fN fZ fQ hdp hp hdp' hp' sN sZ hN hZ
  have sqN : ∀ x, liftSemi fZ (d.lTensor R' x) = d' (liftSemi fN x) := by
    intro x
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sN]
  have sqZ : ∀ z, liftSemi fQ (p.lTensor R' z) = p' (liftSemi fZ z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sZ]
  have ex : Function.Exact (d.lTensor R') (p.lTensor R') := lTensor_exact R' hdp hp
  have ps : Function.Surjective (p.lTensor R') := LinearMap.lTensor_surjective R' hp
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := ps y
    rw [sqZ] at hy
    obtain ⟨x', hx'⟩ := (hdp' (liftSemi fZ z)).1 hy
    obtain ⟨x, rfl⟩ := hN x'
    have : d.lTensor R' x = z := hZ.1 (by rw [sqN, hx'])
    rw [← this]
    exact (ex _).2 ⟨x, rfl⟩
  · intro q'
    obtain ⟨z', rfl⟩ := hp' q'
    obtain ⟨z, rfl⟩ := hZ.2 z'
    exact ⟨p.lTensor R' z, sqZ z⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiPiBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (J : Type) [Finite J] (M M' : J → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) (g : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i)), (∀ x i, g x i = f i (x i)) → (∀ i, Function.Bijective (liftSemi (f i))) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ J _ M M' _ _ _ _ f g hg hf
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ y : R' ⊗[R] (∀ i, M i),
      liftSemi g y = Pi.map (fun i => liftSemi (f i)) (TensorProduct.piRight R R' R' M y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => funext i; simp [Pi.map]
    | tmul x m =>
      funext i
      simp [liftSemi_tmul, hg, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]; funext i; simp
  have : (liftSemi g : R' ⊗[R] (∀ i, M i) → ∀ i, M' i)
      = Pi.map (fun i => liftSemi (f i)) ∘ (TensorProduct.piRight R R' R' M) := funext key
  rw [this]
  exact (Function.Bijective.piMap hf).comp (TensorProduct.piRight R R' R' M).bijective

end GlobalTheory
end

