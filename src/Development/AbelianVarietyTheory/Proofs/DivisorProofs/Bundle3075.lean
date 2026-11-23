module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMembersLatticesIsoOfSpecializesDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
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

namespace GlobalTheory.KSOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull_chart {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

theorem proper_ample_kTriv {S S' : Scheme.{0}} [IsAffine S'] {f : S' ⟶ S} {t : SAB H S} {u u' : SAB H S'}
    (m : SABMap u t f) (m' : SABMap u' t f) (hP : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L)
    (hK : Out.KTriv u.G u.PP.L) : IsProper u'.G.hom ∧ Out.RelAmple u'.G u'.PP.L ∧ Out.KTriv u'.G u'.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ m')
  obtain ⟨w, hw, -⟩ := n.lin
  exact ⟨MorphismProperty.of_isPullback n.cart.1 hP,
    relAmple_pull n.cart.1 u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S') (fun _ => trivial) hA,
    kTriv_pull n.cart u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem bijective_appLE {X X' : Scheme.{0}} (j : X' ⟶ X) [IsOpenImmersion j] {U : X.Opens} {U' : X'.Opens}
    (h : j ''ᵁ U' = U) (e : U' ≤ j ⁻¹ᵁ U) : Function.Bijective (j.appLE U U' e).hom := by
  subst h
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.bijective_of_isIso (j.appIso U').hom

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  rw [← Scheme.Hom.appLE_map m h (homOfLE e).op]
  rfl

theorem app_appLE {X X' G G' : Scheme.{0}} {φ : G' ⟶ G} {p' : G' ⟶ X'} {p : G ⟶ X} {j : X' ⟶ X}
    (sq : φ ≫ p = p' ≫ j) {U : X.Opens} {U' : X'.Opens} (e : U' ≤ j ⁻¹ᵁ U) {O : G.Opens} (h : O ≤ p ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ O ≤ p' ⁻¹ᵁ U') (r : Γ(X, U)) :
    (φ.app O).hom ((p.appLE U O h).hom r) = (p'.appLE U' (φ ⁻¹ᵁ O) h').hom ((j.appLE U U' e).hom r) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 3

theorem valR_comp_appLE {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) {O : Z.Opens}
    {O' : Y.Opens} (e : O' ≤ m ⁻¹ᵁ O) (hz : ⊤ ≤ z ⁻¹ᵁ O') (f : Γ(Z, O)) :
    valR (z ≫ m) O f = valR z O' ((m.appLE O O' e).hom f) := by
  rw [GlobalTheory.CechKS.valR_comp_app, ← GlobalTheory.CechKS.valR_resG z e hz]
  rfl

theorem isKS_of_openImmersion {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {j : X' ⟶ X} [IsOpenImmersion j]
    (m : SABMap t' t j) (cp : ChartPull t'.PP.L t.PP.L m.φ) (V : X.Opens) (U : X.affineOpens) (hUV : U.1 ≤ V)
    (U' : X'.affineOpens) (hU : j ''ᵁ U'.1 = U.1) (ψ : Γ(X, U.1) ≃+* Γ(X', U'.1)) (e : U'.1 ≤ j ⁻¹ᵁ U.1)
    (hψ : ∀ r, ψ r = (j.appLE U.1 U'.1 e).hom r) (hch : chart U' ≫ j = spMap ψ.toRingHom ≫ chart U) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left))
    (hv : ∀ i, IsTanAtG t (chart U) (v i)) (hv' : ∀ i, IsTanAtG t' (chart U') (v' i))
    (hvv : ∀ i, v' i ≫ m.φ = spMap (dualMap ψ.toRingHom) ≫ v i)
    (D : Γ(X, U.1) → Γ(X, U.1)) (D' : Γ(X', U'.1) → Γ(X', U'.1)) (hD : ∀ r, D' (ψ r) = ψ (D r))
    (Θ : Matrix (Fin n) (Fin n) Γ(X', U'.1)) (h : IsKS t' ⊤ U' v' D' Θ) : IsKS t V U v D (Θ.map ψ.symm) := by
  obtain ⟨J, W, c, d, hcov, hWc, hd, hl, hr⟩ := h
  obtain ⟨hoi, hrange⟩ := GlobalTheory.sabMap_isOpenImmersion_opensRange E H X X' t t' j m
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  rw [inf_top_eq] at hcov
  have hWU : ∀ i, W i ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun i => hcov ▸ le_iSup W i
  have hpre : t'.G.hom ⁻¹ᵁ U'.1 = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, sq, Scheme.Hom.comp_preimage, ← hU, Scheme.Hom.preimage_image_eq]
  have hle : ∀ i {O : t.G.left.Opens}, O ≤ m.φ ''ᵁ W i → m.φ ⁻¹ᵁ O ≤ W i := fun i O hO =>
    (m.φ.preimage_mono hO).trans (m.φ.preimage_image_eq (W i)).le
  choose d₂ hd₂ hd₂' using fun i => GlobalTheory.LogKS.isField_image _ _ m.φ (W i) (d i) (hd i)
  refine ⟨J, fun i => m.φ ''ᵁ W i, fun i => cp.idx (c i), d₂, ?_, fun i => ?_, hd₂, fun i hW r => ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hcov, hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, inf_eq_left.2 hUV,
      inf_eq_right]
    apply t.G.hom.preimage_mono
    rw [← hU]
    exact j.image_le_opensRange _
  · rintro _ ⟨y, hy, rfl⟩
    exact cp.le _ (hWc i hy)
  · have hinj : Function.Injective (m.φ.app (m.φ ''ᵁ W i)).hom :=
      (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ W i))).1
    apply hinj
    have h1 := hle i le_rfl
    rw [hd₂' i _ le_rfl, app_appLE sq e hW (h1.trans (hWU i)), app_appLE sq e hW (h1.trans (hWU i)), ← hψ, ← hψ,
      ← hD, ← resG_appLE _ _ (hWU i) h1, (hd i).2.2 _ _ h1 le_rfl, hl i (hWU i), resG_appLE]
  · intro i i' O hO f S _ φ g₀ w hg hO₀ hT
    have hOi : O ≤ m.φ ''ᵁ W i := hO.trans inf_le_left
    have hOi' : O ≤ m.φ ''ᵁ W i' := hO.trans inf_le_right
    obtain ⟨g₁, rfl⟩ : ∃ g₁ : Sp S ⟶ t'.G.left, g₁ ≫ m.φ = g₀ :=
      ⟨IsOpenImmersion.lift m.φ g₀ (by
        rintro _ ⟨y, rfl⟩
        obtain ⟨z, -, hz⟩ := hOi (hO₀ (Set.mem_univ y))
        exact ⟨z, hz⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨φ₁, rfl⟩ : ∃ φ₁ : Γ(X', U'.1) →+* S, φ₁.comp ψ.toRingHom = φ :=
      ⟨φ.comp ψ.symm.toRingHom, RingHom.ext fun r => by simp⟩
    have hg₁ : g₁ ≫ t'.G.hom = spMap φ₁ ≫ chart U' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg, Category.assoc, hch, ← Category.assoc]
      congr 1
      exact Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ₁)
    choose w₁ hw₁ hT₁ using fun a => GlobalTheory.TransLift.lift_isTranslate E H X X' t t' j m _ _ ψ.toRingHom (chart U) (chart U') hch
      (v a) (v' a) (hv a) (hv' a) (hvv a) S φ₁ g₁ hg₁ (w a) (hT a)
    obtain rfl : w = fun a => w₁ a ≫ m.φ := funext fun a => (hw₁ a).symm
    have hO₁ : ⊤ ≤ g₁ ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := hO₀
    have key := hr i i' (m.φ ⁻¹ᵁ O) (le_inf (hle i hOi) (hle i' hOi')) ((m.φ.app O).hom f) S φ₁ g₁ w₁ hg₁ hO₁ hT₁
    have hgc : ⊤ ≤ g₁ ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) :=
      hO₁.trans (g₁.preimage_mono (le_inf ((hle i hOi).trans (hWc i)) ((hle i' hOi').trans (hWc i'))))
    have hwc : ∀ b, ⊤ ≤ w₁ b ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) := fun b =>
      GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKS.IsTranslate.fst_comp E H X' t' _ S φ₁ (chart U') g₁ (v' b) (w₁ b) hg₁ (hv' b) (hT₁ b)) hgc
    have hgp := GlobalTheory.chartPull_g_appLE _ _ _ _ m.φ cp (c i) (c i')
    have hgi : ((t'.PP.L.g (c i) (c i'))⁻¹).val = (m.φ.appLE _ _
        (le_inf (inf_le_left.trans (cp.le (c i))) (inf_le_right.trans (cp.le (c i'))))).hom
        ((t.PP.L.g (cp.idx (c i)) (cp.idx (c i')))⁻¹).val :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hgp, ← map_mul, Units.mul_inv, map_one])
    rw [GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂' i O hOi, hd₂' i' O hOi', key]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hgp, hgi]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (by simp) (congrArg₂ (· * ·) (congrArg TrivSqZeroExt.snd ?_) ?_))
      (congrArg TrivSqZeroExt.snd ?_)
    · exact (valR_comp_appLE (w₁ b) m.φ _ (hwc b) _).symm
    · exact (valR_comp_appLE g₁ m.φ _ hgc _).symm
    · exact (GlobalTheory.CechKS.valR_comp_app (w₁ a) m.φ O f).symm

def derivMap {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) : Derivation ℤ B B :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    ((ψ.toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom).comp ψ.symm.toAddMonoidHom)) fun a b => by
      simp

theorem derivMap_apply {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) (r : A) :
    derivMap ψ D (ψ r) = ψ (D r) := by
  simp [derivMap]

theorem exists_isKS_of_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U hUV t' ⟨m'⟩ hP hA hK n v hv hb D
  obtain ⟨u, m, ⟨cp⟩⟩ := exists_pull_chart (chart U) t
  obtain ⟨hP', hA', hK'⟩ := proper_ample_kTriv m' m hP hA hK
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let U' : (Sp Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : chart U ''ᵁ U'.1 = U.1 := by
    show chart U ''ᵁ ⊤ = U.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have e : U'.1 ≤ chart U ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  let ψ : Γ(X, U.1) ≃+* Γ(Sp Γ(X, U.1), U'.1) := RingEquiv.ofBijective _ (bijective_appLE (chart U) hU e)
  have hch : chart U' ≫ chart U = spMap ψ.toRingHom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (chart U) U.2 U'.2 e).symm
  obtain ⟨v', hvv, hv', hb'⟩ := GlobalTheory.SabTan.tanBasis_sabMap E H X _ t u (chart U) m _ _ ψ.toRingHom (chart U) (chart U') hch n v hv hb
  obtain ⟨Θ, hΘ⟩ := _root_.GlobalTheory.KSExists.exists_isKS E H _ u hP' hA' hK' U' n v' hv' hb' (derivMap ψ D)
  exact ⟨_, isKS_of_openImmersion m cp V U hUV U' hU ψ e (fun _ => rfl) hch v v' hv hv' hvv D _
    (derivMap_apply ψ D) Θ hΘ⟩

end GlobalTheory.KSOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelPreservingLatticeIsoOfMembers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.GMem

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem LatTo.trans
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {t₀ : X₀ → V₀} {δ₀ : I → X₀ → X₀}
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁}
    {Y₁ : Type} [AddCommGroup Y₁] {t₁ : Y₁ → V₁} {δ₁ : I → Y₁ → Y₁}
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂}
    {Y₂ : Type} [AddCommGroup Y₂] {t₂ : Y₂ → V₂} {δ₂ : I → Y₂ → Y₂}
    {𝔪₀ : GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪₁ : GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁} {𝔪₂ : GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂}
    (h₁ : 𝔪₀.LatTo 𝔪₁) (h₂ : 𝔪₁.LatTo 𝔪₂) : 𝔪₀.LatTo 𝔪₂ := by
  obtain ⟨K₁, hK₁, hl₁⟩ := h₁
  obtain ⟨K₂, hK₂, hl₂⟩ := h₂
  refine ⟨K₁.trans K₂, fun a mu => ?_, fun a mu h => hl₂ a _ (hl₁ a mu h)⟩
  simp only [AddEquiv.trans_apply, hK₁, hK₂]

theorem LatTo.symm
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {t₀ : X₀ → V₀} {δ₀ : I → X₀ → X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    {𝔪₀ : GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪 : GMem X₁ z₁ act V ev X t δ} (h : 𝔪₀.LatTo 𝔪) : 𝔪.LatTo 𝔪₀ := by
  obtain ⟨K, hK, hl⟩ := h
  have y₀ := _root_.GlobalTheory.GSep.Labels.yy_hom I X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀ 𝔪₀
  have y₁ := _root_.GlobalTheory.GSep.Labels.yy_hom I X₁ z₁ act V ev X t δ 𝔪
  refine ⟨K.symm, fun a mu => K.injective ?_, fun a mu' h => ?_⟩
  · rw [K.apply_symm_apply, hK, K.apply_symm_apply]
  · obtain ⟨mu, hmu⟩ := y₀.1 a
    obtain ⟨w, hw⟩ := (y₁.2.2.1 a (K mu) mu' (hl a mu hmu)).1 h
    refine (y₀.2.2.1 a mu (K.symm mu') hmu).2 ⟨K.symm w, ?_⟩
    rw [hw, map_add (f := _), K.symm_apply_apply, map_nsmul]

end GlobalTheory.GSep.GMem

namespace GlobalTheory.GSep.Cmp

open GlobalTheory.GSep GlobalTheory.GSep.GMem

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem closed_over {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    [IsLocalHom ev] {Y : Scheme.{0}} {πY : Y ⟶ X₁.M.Z} {ξ : Sp V ⟶ Y}
    (h : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) : πY (ξ (closedPoint V)) = z₁ := by
  change (ξ ≫ πY) (closedPoint V) = z₁
  rw [h]
  change X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
  rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
  exact Scheme.fromSpecStalk_closedPoint

theorem latTo_all (hact : IsAct X₁ act)
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {t₀ : X₀ → V₀} {δ₀ : I → X₀ → X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪₀ : GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : GMem X₁ z₁ act V ev X t δ) : 𝔪₀.LatTo 𝔪 := by
  obtain ⟨Y, πY, hY⟩ := _root_.GlobalTheory.GSep.exists_zhAbove X₁
  have lift : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
      {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
      (𝔪 : GMem X₁ z₁ act V ev X t δ), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
        (_ : IsDiscreteValuationRing V') (ev' : X₁.M.Z.presheaf.stalk z₁ →+* V') (t' : X → V')
        (𝔫 : GMem X₁ z₁ act V' ev' X t' δ) (ξ : Sp V' ⟶ Y.Z),
        ξ ≫ πY = spMap ev' ≫ X₁.M.Z.fromSpecStalk z₁ ∧ 𝔪.LatTo 𝔫 := by
    intro V _ _ _ ev X _ t δ 𝔪
    obtain ⟨V₁, _, _, _, _, j₁, hcn₁, hj₁, hl₁⟩ := GlobalTheory.CompleteNormalDvr.exists_dvr_isCN V 𝔪.cn
    haveI := 𝔪.loc
    haveI := hl₁
    obtain ⟨V₂, _, _, _, _, j₂, ξ, hcn₂, hj₂, hl₂, hξ⟩ :=
      _root_.GlobalTheory.GSep.TraitLift.exists_lift X₁ z₁ Y πY hY V₁ (j₁.comp ev) inferInstance hcn₁
    haveI := hl₂
    have hj : Function.Injective (j₂.comp j₁) := hj₂.comp hj₁
    obtain ⟨𝔫, -, hyy⟩ := _root_.GlobalTheory.GSep.MemBC.gMem_baseChange I X₁ z₁ act V ev X t δ 𝔪 V₂ (j₂.comp j₁)
      (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₂) hj) hcn₂ hj inferInstance
      (fun v => IsLocalization.map_eq _ v)
    refine ⟨V₂, inferInstance, inferInstance, inferInstance, inferInstance, (j₂.comp j₁).comp ev, _, 𝔫, ξ, ?_,
      AddEquiv.refl _, fun _ _ => rfl, hyy⟩
    rw [hξ, RingHom.comp_assoc]
  obtain ⟨W₀, _, _, _, _, e₀, s₀, 𝔫₀, ξ₀, hξ₀, a₀⟩ := lift 𝔪₀
  obtain ⟨W₁, _, _, _, _, e₁, s₁, 𝔫₁, ξ₁, hξ₁, a₁⟩ := lift 𝔪
  let P : Y.Z → Prop := fun y => ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X)
    (𝔠 : GMem X₁ z₁ act V ev X t δ) (ξc : Sp V ⟶ Y.Z),
    ξc ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → ξc (closedPoint V) = y → 𝔫₀.LatTo 𝔠
  have step : ∀ a b : Y.Z, πY a = z₁ → πY b = z₁ → a ⤳ b → (P a ↔ P b) := by
    intro a b ha hb hab
    obtain ⟨Va, _, _, _, _, eva, Xa, _, ta, δa, 𝔠a, ξa, hξa, hca, -⟩ := _root_.GlobalTheory.GSep.Thru.exists_gMem_thru I X₁ z₁ act hact Y πY hY a ha
    obtain ⟨Vb, _, _, _, _, evb, Xb, _, tb, δb, 𝔠b, ξb, hξb, hcb, -⟩ := _root_.GlobalTheory.GSep.Thru.exists_gMem_thru I X₁ z₁ act hact Y πY hY b hb
    constructor
    · intro hP V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc
      have h1 := hP Va eva Xa ta δa 𝔠a ξa hξa hca
      have h2 := _root_.GlobalTheory.GSep.Spz.latTo_of_specializes I X₁ z₁ act hact Y πY hY Va eva Xa ta δa 𝔠a ξa V ev X t δ 𝔠 ξc hξa hξc
        (by rw [hca, hc]; exact hab)
      exact h1.trans h2
    · intro hP V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc
      have h1 := hP Vb evb Xb tb δb 𝔠b ξb hξb hcb
      have h2 := _root_.GlobalTheory.GSep.Spz.latTo_of_specializes I X₁ z₁ act hact Y πY hY V ev X t δ 𝔠 ξc Vb evb Xb tb δb 𝔠b ξb hξc hξb
        (by rw [hc, hcb]; exact hab)
      exact h1.trans h2.symm
  have key : ∀ y y' : Y.Z, Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' → (P y ↔ P y') := by
    intro y y' h
    induction h with
    | rel a b hr => exact step a b hr.1 hr.2.1 hr.2.2
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  haveI := 𝔫₀.loc
  haveI := 𝔫₁.loc
  have c₀ : πY (ξ₀ (closedPoint W₀)) = z₁ := closed_over hξ₀
  have c₁ : πY (ξ₁ (closedPoint W₁)) = z₁ := closed_over hξ₁
  have P0 : P (ξ₀ (closedPoint W₀)) := by
    intro V _ _ _ _ ev X _ t δ 𝔠 ξc hξc hc
    exact _root_.GlobalTheory.GSep.Spz.latTo_of_specializes I X₁ z₁ act hact Y πY hY W₀ e₀ X₀ s₀ δ₀ 𝔫₀ ξ₀ V ev X t δ 𝔠 ξc hξ₀ hξc (by rw [hc])
  have P1 := (key _ _ (_root_.GlobalTheory.GSep.fibre_chain X₁ z₁ Y πY hY _ _ c₀ c₁)).1 P0
  exact a₀.trans ((P1 W₁ e₁ X s₁ δ 𝔫₁ ξ₁ hξ₁ rfl).trans a₁.symm)

theorem exists_latTo_of_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (t₀ : X₀ → V₀) (δ₀ : I → X₀ → X₀) (𝔪₀ : GlobalTheory.GSep.GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔪₀.LatTo 𝔪 := by
  intro I X₁ z₁ act hact V₀ _ _ _ ev₀ X₀ _ t₀ δ₀ 𝔪₀ V _ _ _ ev X _ t δ 𝔪
  exact latTo_all hact 𝔪₀ 𝔪

end GlobalTheory.GSep.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeEquivTwoMembersSamePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp

section Glue

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem LatTo.symm' {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    {𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪 : UMem X₁ z₁ act V ev X t δ} (h : LatTo 𝔪₀ 𝔪) : LatTo 𝔪 𝔪₀ := by
  obtain ⟨K, hK, hl⟩ := h
  have y₀ := _root_.GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₀ ev₀ X₀ m₀ t₀ δ₀ 𝔪₀
  have y₁ := _root_.GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  refine ⟨K.symm, fun a mu => K.injective ?_, fun a mu' h => ?_⟩
  · rw [K.apply_symm_apply, hK]
    simp only [K.apply_symm_apply]
  · obtain ⟨mu, hmu⟩ := y₀.1 a
    have hc := (y₁.2.2.1 a (K mu) mu' (hl a mu hmu)).1 h
    refine (y₀.2.2.1 a mu (K.symm mu') hmu).2 fun v => ?_
    choose w hw using hc
    have e : mu' = K mu + (X₁.S.r * X₁.S.N) • w := funext fun u => by simpa using hw u
    refine ⟨K.symm w v, ?_⟩
    have e' : K.symm mu' = mu + (X₁.S.r * X₁.S.N) • K.symm w := by
      rw [e, map_add (f := _), K.symm_apply_apply, map_nsmul]
    exact congrFun e' v

theorem closed_over {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    [IsLocalHom ev] {Y : Scheme.{0}} {πY : Y ⟶ X₁.M.Z} {ξ : Sp V ⟶ Y}
    (h : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) : πY (ξ (closedPoint V)) = z₁ := by
  change (ξ ≫ πY) (closedPoint V) = z₁
  rw [h]
  change X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
  rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
  exact Scheme.fromSpecStalk_closedPoint

end Glue

section Main

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem latTo_all (hact : IsAct X₁ act)
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : UMem X₁ z₁ act V ev X t δ) : LatTo 𝔪₀ 𝔪 := by
  obtain ⟨Y, πY, hY⟩ := _root_.GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove g n F W Z i X₁
  have lift : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
      {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
      (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
        (_ : IsDiscreteValuationRing V') (ev' : X₁.M.Z.presheaf.stalk z₁ →+* V') (m' : ℕ) (t' : Fin m' → V')
        (δ' : Fin m' → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V' ev' X t' δ') (ξ : Sp V' ⟶ Y.Z),
        ξ ≫ πY = spMap ev' ≫ X₁.M.Z.fromSpecStalk z₁ ∧ LatTo 𝔪 𝔫 := by
    intro V _ _ _ ev X _ m t δ 𝔪
    obtain ⟨V₁, _, _, _, _, j₁, hcn₁, hj₁, hl₁⟩ := _root_.GlobalTheory.CompleteNormalDvr.exists_dvr_isCN V 𝔪.cn
    haveI := 𝔪.loc
    haveI := hl₁
    obtain ⟨V₂, _, _, _, _, j₂, ξ, hcn₂, hj₂, hl₂, hξ⟩ :=
      _root_.GlobalTheory.Poinc.Sep.TraitLift.exists_lift g n F W Z i X₁ z₁ Y πY hY V₁ (j₁.comp ev) inferInstance hcn₁
    haveI := hl₂
    obtain ⟨m', t', δ', 𝔫, hyy⟩ :=
      _root_.GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange g n F W Z i X₁ z₁ act hact V ev X m t δ 𝔪 V₂ (j₂.comp j₁) hcn₂ (hj₂.comp hj₁) inferInstance
    exact ⟨V₂, inferInstance, inferInstance, inferInstance, inferInstance, (j₂.comp j₁).comp ev, m', t', δ', 𝔫, ξ, hξ,
      AddEquiv.refl _, fun _ _ => rfl, hyy⟩
  obtain ⟨W₀, _, _, _, _, e₀, n₀, s₀, d₀, 𝔫₀, ξ₀, hξ₀, a₀⟩ := lift 𝔪₀
  obtain ⟨W₁, _, _, _, _, e₁, n₁, s₁, d₁, 𝔫₁, ξ₁, hξ₁, a₁⟩ := lift 𝔪
  let P : Y.Z → Prop := fun y => ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔠 : UMem X₁ z₁ act V ev X t δ) (ξc : Sp V ⟶ Y.Z),
    ξc ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → ξc (closedPoint V) = y → LatTo 𝔫₀ 𝔠
  have step : ∀ a b : Y.Z, πY a = z₁ → πY b = z₁ → a ⤳ b → (P a ↔ P b) := by
    intro a b ha hb hab
    obtain ⟨Va, _, _, _, _, eva, Xa, _, ma, ta, δa, 𝔠a, ξa, hξa, hca⟩ :=
      _root_.GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru g n F W Z i X₁ z₁ act hact Y πY hY a ha
    obtain ⟨Vb, _, _, _, _, evb, Xb, _, mb, tb, δb, 𝔠b, ξb, hξb, hcb⟩ :=
      _root_.GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru g n F W Z i X₁ z₁ act hact Y πY hY b hb
    constructor
    · intro hP V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
      have h1 := hP Va eva Xa ma ta δa 𝔠a ξa hξa hca
      have h2 := _root_.GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes g n F W Z i X₁ z₁ act hact Y πY hY Va eva Xa ma ta δa 𝔠a ξa V ev X m t δ 𝔠 ξc hξa hξc
        (by rw [hca, hc]; exact hab)
      exact h1.trans h2
    · intro hP V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
      have h1 := hP Vb evb Xb mb tb δb 𝔠b ξb hξb hcb
      have h2 := _root_.GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes g n F W Z i X₁ z₁ act hact Y πY hY V ev X m t δ 𝔠 ξc Vb evb Xb mb tb δb 𝔠b ξb hξc hξb
        (by rw [hc, hcb]; exact hab)
      exact h1.trans h2.symm'
  have key : ∀ y y' : Y.Z, Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' → (P y ↔ P y') := by
    intro y y' h
    induction h with
    | rel a b hr => exact step a b hr.1 hr.2.1 hr.2.2
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  haveI := 𝔫₀.loc
  haveI := 𝔫₁.loc
  have c₀ : πY (ξ₀ (closedPoint W₀)) = z₁ := closed_over hξ₀
  have c₁ : πY (ξ₁ (closedPoint W₁)) = z₁ := closed_over hξ₁
  have P0 : P (ξ₀ (closedPoint W₀)) := by
    intro V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
    exact _root_.GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes g n F W Z i X₁ z₁ act hact Y πY hY W₀ e₀ X₀ n₀ s₀ d₀ 𝔫₀ ξ₀ V ev X m t δ 𝔠 ξc hξ₀ hξc
      (by rw [hc])
  have P1 := (key _ _ (_root_.GlobalTheory.SpecChain.fibre_chain g n F W Z i X₁ z₁ Y πY hY _ _ c₀ c₁)).1 P0
  exact a₀.trans ((P1 W₁ e₁ X n₁ s₁ d₁ 𝔫₁ ξ₁ hξ₁ rfl).trans a₁.symm')

end Main

theorem exists_latEquiv_of_members : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (m₀ : ℕ) (t₀ : Fin m₀ → V₀) (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu) := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act hact V₀ _ _ _ ev₀ X₀ _ m₀ t₀ δ₀ 𝔪₀ V _ _ _ ev X _ m t δ 𝔪
  exact latTo_all hact 𝔪₀ 𝔪

end GlobalTheory.Poinc.Sep.Cmp
end
end

