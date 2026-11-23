module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharBundlePrimitive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ToricRankZero

theorem isProper_of_torusExtension_of_finrank_eq_zero {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (hX : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0) : IsProper G.hom := by
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  haveI := E.q_hom
  have hsub : Subsingleton E.X := Module.finrank_zero_iff.1 hX
  have hp := E.isKernel
  have : Mono E.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ E.q = toUnit _ ≫ η[E.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) E.X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    haveI := E.i_hom
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono E.q.left := inferInstanceAs (Mono ((Over.forget _).map E.q))
  have := E.isAbelian.proper
  have : Flat E.q.left := E.q_flat
  have : Surjective E.q.left := E.q_surjective
  have : QuasiCompact E.q.left := E.q_quasiCompact
  have : IsIso E.q.left := Flat.isIso_of_surjective_of_mono E.q.left
  rw [← Over.w E.q]
  infer_instance

theorem isAbelianScheme_of_finrank_eq_zero : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], IsSemiAbelian G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ E : TorusExtension (GlobalTheory.SS.spFibre G), (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 → IsAbelianScheme G := by
  intro W L _ _ _ _ _ _ G _ hG hgen E hE
  have hS : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, hG.separated, hG.quasiCompact, hG.geomConnected⟩
  have hsp : IsProper (GlobalTheory.SS.spFibre G).hom := isProper_of_torusExtension_of_finrank_eq_zero _ E hE
  exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper _ G hS
    (GlobalTheory.GoodRedProper.isProper_of_proper_fibres W L G hS hgen hsp)

end GlobalTheory.ToricRankZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfInterior
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffOff

theorem isAffineOpen_inf_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, IsAffineOpen (U.1 ⊓ interior Y) := by
  intro E _ _ _ H Dw l Xo c Y h U
  have hs := snc_gen_iff.1 h
  unfold boundary at hs
  set V := interior Y with hVdef
  have key : ∀ y : Y.X, ∃ W : Y.X.Opens, y ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W) := by
    intro y
    obtain ⟨-, W, hy, n, f, J, -, hI⟩ := hs y
    have e : W.1 ⊓ V = Y.X.basicOpen (∏ i ∈ J, f i) := by
      ext z
      constructor
      · rintro ⟨hW, hV⟩
        by_contra hz
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
          exact hz
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact this hV
      · intro hz
        have hW : z ∈ W.1 := Y.X.basicOpen_le _ hz
        refine ⟨hW, by_contra fun hV ↦ ?_⟩
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
          exact hV
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span,
          Scheme.zeroLocus_singleton] at this
        exact this hz
    refine ⟨W.1, hy, W.2, ?_⟩
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm, e]
    exact W.2.basicOpen _
  have : IsAffineHom V.ι := isAffineHom_of_forall_exists_isAffineOpen _ key
  have h2 := U.2.preimage V.ι
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h2
  rwa [inf_comm]

end GlobalTheory.AffOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RayEv

theorem Ray.isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] {oa : D.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv

theorem GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type)
    [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens),
    IsAffineOpen (Y.q.left ⁻¹ᵁ V.1) := by
  intro R _ _ Q O _ _ _ oa Y V
  haveI := Y.isAffineHom_q
  exact V.2.preimage Y.q.left
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

def IsConnK {R : Type} [CommRing R] {k : Type} [Field k] (A : Over (Sp R)) (L : LB A.left) (A₀ : Over (Sp k))
    (m₀ : A₀.left ⟶ A.left) (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (ed : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)) : Prop :=
  GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ D' ⊤ ed ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ L.U (jj i)) ∧
    ∀ i i', ed (V i ⊓ V i') (rsT (L.g (jj i) (jj i')).val (V i ⊓ V i')) =
      pbT m₀ (L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) *
        (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.KSChartRes

theorem isUnit_of_comap_mem {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (s : A)
    (h : ∀ x : PrimeSpectrum S, PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen s) : IsUnit (φ s) := by
  by_contra hn
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hn)
  exact h ⟨m, hm.isPrime⟩ (hsm (Ideal.mem_span_singleton_self _))

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_top_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t m tt n v' D DV Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩

  set s := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i) with hs
  set Wa := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) s with hWa
  have hWV : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ Wa.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hle : Wa.1 ≤ ⊤ := le_top
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, top_inf_eq]
    exact congrArg _ (inf_idem _)
  · have e : ∀ x, (t.G.hom.appLE ⊤ (Wc i) h).hom x =
        (t.G.hom.appLE Wa.1 (Wc i) (hWV i)).hom (((Sp R).presheaf.map (homOfLE hle).op).hom x) := fun x =>
      (congrArg (fun k => k.hom x) (t.G.hom.map_appLE (hWV i) (homOfLE hle).op)).symm
    have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
      Iso.hom_inv_id_apply _ _
    rw [e, e, hcomp i (hWV i)]
    have := hD ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)
    rw [hr] at this
    exact congrArg _ this
  · have hOW : O ≤ t.G.hom ⁻¹ᵁ (Wa.1 ⊓ (Sp R).basicOpen s) :=
      hO.trans (inf_le_left.trans ((le_iSup Wc i).trans hsup.le))
    have hu : IsUnit (φ s) := by
      refine isUnit_of_comap_mem φ s fun x => ?_
      have hx : g₀ x ∈ O := hO' (show x ∈ (⊤ : (Sp S).Opens) from trivial)
      have hV : t.G.hom (g₀ x) ∈ (Sp R).basicOpen s := (hOW hx).2
      have e1 : t.G.hom (g₀ x) = (g₀ ≫ t.G.hom) x := rfl
      rw [e1, hg₀] at hV
      have h2 : (spMap φ) x ∈ (GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ (Sp R).basicOpen s := hV
      change (spMap φ) x ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen s at h2
      rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen s] at h2
      exact h2
    letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, Wa.1) := ((Sp R).presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hl : IsLocalization.Away s Γ(Sp R, Wa.1) :=
      (isAffineOpen_top (Sp R)).isLocalization_of_eq_basicOpen s (homOfLE hle) rfl
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Sp R, Wa.1) →+* S, ψ.comp ((Sp R).presheaf.map (homOfLE hle).op).hom = φ :=
      ⟨IsLocalization.Away.lift s hu, IsLocalization.lift_comp _⟩
    subst hψ
    have hres : spMap ((Sp R).presheaf.map (homOfLE hle).op).hom ≫
        GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) = GlobalTheory.LogKS.chart Wa :=
      (isAffineOpen_top (Sp R)).map_fromSpec Wa.2 (homOfLE hle).op
    have := htest i i' O hO f S ψ g₀ w ?_ hO' ?_
    · exact this
    · rw [hg₀, ← hres, ← Category.assoc, spMap_comp']
    · intro a
      obtain ⟨g', v'', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v'', h₁, ?_, h₃⟩
      rw [h₂]
      dsimp only
      rw [← Category.assoc, ← Category.assoc, spMap_comp']
      erw [spMap_comp']
      erw [dualMap_comp']

end GlobalTheory.KSChartRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermOfIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat.TermDescent

theorem gs_top_appLE {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) = gs φ y U a := by
  have e := gs_appLE φ U ⊤ h (𝟙 Y) y trivial a
  rwa [Category.id_comp] at e

theorem gs_of_valR {S : Type} [CommRing S] {X : Scheme.{0}} (x x' : Sp S ⟶ X) (V : X.Opens) (f : Γ(X, V))
    (c : Sˣ) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x' ⁻¹ᵁ V) (e : valR x' V f = c * valR x V f) (y : Sp S) :
    gs x' y V f = (gm (𝟙 (Sp S)) y ⊤ (unitOn c)).val * gs x y V f := by
  rw [valR, valR, dif_pos h, dif_pos h'] at e
  have e' : (x'.appLE V ⊤ h').hom f = (unitOn c).val * (x.appLE V ⊤ h).hom f := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom e
    rw [map_mul] at this
    simpa [unitOn] using this
  rw [← gs_top_appLE x' y V h', ← gs_top_appLE x y V h, e', gs_mul _ y ⊤ trivial, gs_unit _ y ⊤ trivial]

theorem gen_ratio {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {S : Type} [CommRing S] {K : Type} [Fintype K]
    {φ φ' : K → (Sp S ⟶ X)} (ε : K → ℤ) (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ c : Sˣ, ∀ y J, Good L y J →
      val t' (𝟙 _) y J = gm (𝟙 (Sp S)) y ⊤ (unitOn c) * val t (𝟙 _) y J := by
  subst e
  let u := LB.mulGen L φ ε φ (fun k => - ε k) t' (LB.invGen L φ ε t)
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ ht' (DVR.invGen_isGen _ _ _ _ ht)
  have hF : FormEq (Sum.elim φ φ) (Sum.elim ε fun k => - ε k) (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
      mul_inv_cancel, Fintype.prod_empty]
  obtain ⟨t₀, -, h₀⟩ := exists_gen hL hF u hu
  have le : (⊤ : (Sp S).Opens) ≤ LB.wchart L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let v : Γ(Sp S, ⊤)ˣ := res le (t₀.s PEmpty.elim)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v, fun y J hJ => ?_⟩
  have hv : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v) = v := by
    ext; simp [unitOn]
  have e₀ : gm (𝟙 (Sp S)) y ⊤ v = val t₀ (𝟙 _) y J :=
    (gm_res _ y le trivial _).trans (val_of t₀ _ y J PEmpty.elim fun k => k.elim).symm
  rw [hv, e₀, h₀ _ _ y J hJ, val_mul hJ, val_inv, inv_mul_cancel_right]

end GlobalTheory.Heat.TermDescent

namespace GlobalTheory.Heat
open GlobalTheory.Heat.TermDescent

theorem isTerm_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (τ : SecM Y.q.left Q.P.L k) (J : Type) (V : J → Q.P.A.left.Opens) (j : J → Fin 1 → Q.P.L.ι), ⨆ i, Y.q.left ⁻¹ᵁ V i = ⊤ → (∀ i, Y.q.left ⁻¹ᵁ V i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (j i)) → (∀ i, IsWt Y α (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i))) → ∃ σ' : Q.SecB k α, IsTerm Y k α σ' τ := by
  intro R _ _ Q O _ _ _ oa Y k α τ Jt V j hcov hle hwt
  have hL := Q.P.isLB
  obtain ⟨hs, hqc⟩ := GlobalTheory.T.ray_q_surjective_and_quasiCompact Y
  have := Ray.smooth_q Y
  let t := (Y.Φ Y.H (𝟙 _)).s α
  have ht : t.IsGen := (Y.Φ Y.H (𝟙 _)).isGen α
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Y.q.left) (DegPre.gtφT Q Y.H Y.q α))
      (Sum.elim (fun _ => (k : ℤ)) (fun a => - DegPre.gtε a)) (fun i => Y.q.left ≫ DegPre.famφB Q α i)
      (DegPre.famε k) := by
    intro U _ h
    have e := GlobalTheory.RayEv.formEq_term Y k α U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ (𝟙 _) (LB.invGen Q.P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) J, Good Q.P.L z J →
      sval σ r z J = sval τ r z J * ((val t r z J)⁻¹).val := by
    intro Z r z J hJ
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id]
    exact congrArg (fun u => sval τ r z J * u.val) (val_inv (z := z) (J := J) t r)
  have vt : ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) (y : T.left) J, Good Q.P.L y J →
      val t x.left y J = val ((Y.Φ T x).s α) (𝟙 _) y J := by
    intro T x y J hJ
    obtain ⟨-, h₂⟩ := (GlobalTheory.TorusModel.isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
    have e := h₂ α y J hJ
    rw [Category.comp_id] at e
    exact e.symm
  have hdesc : ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ Y.H.left), g₁ ≫ Y.q.left = g₂ ≫ Y.q.left →
      ∀ J, Good Q.P.L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J := by
    intro S _ _ g₁ g₂ hg J hJ
    have hA : g₂ ≫ Y.H.hom = g₁ ≫ Y.H.hom := by
      rw [← Over.w Y.q, ← Category.assoc, ← Category.assoc, hg]
    obtain ⟨φ, hφ⟩ : ∃ φ : R →+* S, g₁ ≫ Y.H.hom = spMap φ :=
      ⟨(Spec.preimage (g₁ ≫ Y.H.hom)).hom, (Spec.map_preimage _).symm⟩
    let x₁ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₁ hφ
    let x₂ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₂ (hA.trans hφ)
    have hx : x₂ ≫ Y.q = x₁ ≫ Y.q := Over.OverMorphism.ext hg.symm
    have hc : ∀ χ, ∃ c : Sˣ, ∀ y J, Good Q.P.L y J → val ((Y.Φ _ x₂).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn c) * val ((Y.Φ _ x₁).s χ) (𝟙 _) y J := fun χ =>
      gen_ratio Q.P.L hL DegPre.gtε (by rw [Ray.Φ_b, Ray.Φ_b, hx]) _ _ ((Y.Φ _ x₁).isGen χ) ((Y.Φ _ x₂).isGen χ)
    choose c hc using hc
    obtain ⟨i, hi⟩ : ∃ i, g₁ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      have : g₁ (closedPoint S) ∈ (⨆ i, Y.q.left ⁻¹ᵁ V i : Y.H.left.Opens) := by rw [hcov]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hi₂ : g₂ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      show (g₂ ≫ Y.q.left) (closedPoint S) ∈ V i
      rw [← hg]; exact hi
    have h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₁ hi).ge
    have h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₂ hi₂).ge
    have hw := hwt i S φ x₁ x₂ c g₁ g₂ rfl rfl h₁ h₂ hx hc
    have hg' := gs_of_valR g₁ g₂ _ _ (c α) h₁ h₂ hw (closedPoint S)
    have s_i : ∀ g : Sp S ⟶ Y.H.left, g (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i →
        gs g (closedPoint S) (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i)) =
          (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g (closedPoint S) (j i)
            (fun _ => J (g ≫ Y.q.left))).val * sval τ g (closedPoint S) J := by
      intro g hm
      have er : rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i) = resG _ (hle i) (τ.f (j i)) := dif_pos (hle i)
      rw [er]
      exact (gs_res g _ (hle i) hm _).trans (sec_trans τ g _ (hle i hm) (hJ.mem _ g))
    have htr : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₂ (closedPoint S) (j i)
        (fun _ => J (g₂ ≫ Y.q.left)) = trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₁ (closedPoint S) (j i)
        (fun _ => J (g₁ ≫ Y.q.left)) := by
      simp only [trF]
      rw [hg]
    set C : ((Sp S).presheaf.stalk (closedPoint S))ˣ := gm (𝟙 (Sp S)) (closedPoint S) ⊤ (unitOn (c α)) with hC
    have sv : sval τ g₂ (closedPoint S) J = C.val * sval τ g₁ (closedPoint S) J := by
      have e := hg'
      rw [s_i g₂ hi₂, s_i g₁ hi, htr, mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
    have vv : val t g₂ (closedPoint S) J = C * val t g₁ (closedPoint S) J :=
      (vt _ x₂ _ J hJ).trans ((hc α _ J hJ).trans (congrArg (C * ·) (vt _ x₁ _ J hJ).symm))
    rw [vσ _ g₁ _ J hJ, vσ _ g₂ _ J hJ, sv, vv, mul_inv_rev, Units.val_mul]
    linear_combination (-(sval τ g₁ (closedPoint S) J * ((val t g₁ (closedPoint S) J)⁻¹).val)) * C.mul_inv

  obtain ⟨b, hb⟩ := _root_.GlobalTheory.LocDescent.exists_sec_descend Q.P.L hL Y.q.left inferInstance hs hqc (DegPre.famφB Q α) (DegPre.famε k) σ hdesc
  refine ⟨b, fun T x y J hJ => ?_⟩
  have e1 := hb _ x.left y J hJ
  rw [vσ _ _ y J hJ, vt T x y J hJ] at e1
  show sval τ x.left y J = sval b (x.left ≫ Y.q.left) y J * _
  rw [← e1, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.Heat
end
end

