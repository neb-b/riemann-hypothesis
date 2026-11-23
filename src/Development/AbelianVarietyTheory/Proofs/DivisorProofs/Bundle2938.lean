module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowNormValLeUnitaryThetaFiniteModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ValBound

theorem exists_maximalIdeal_pow_le_map_stalkMap (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    ∃ e : ℕ, maximalIdeal (X.presheaf.stalk x) ^ e ≤
      (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro P ⟨hP, hPp⟩
  let q : Sp (X.presheaf.stalk x) := ⟨P, hPp⟩
  have hcomap : P.comap (f.stalkMap x).hom = maximalIdeal _ :=
    ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.1 hP)).symm
  have h1 : Spec.map (f.stalkMap x) q = closedPoint (Y.presheaf.stalk (f x)) := by
    exact PrimeSpectrum.ext hcomap
  have e₁ := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  have hy : f (X.fromSpecStalk x q) = f x := by
    have := congrArg (fun g => g q) e₁
    simp only [Scheme.Hom.comp_apply, h1, Scheme.fromSpecStalk_closedPoint] at this
    exact this.symm
  have hs : X.fromSpecStalk x q ⤳ x := by
    have : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨_, hy⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr hs
  have h3 : X.fromSpecStalk x q = X.fromSpecStalk x (closedPoint _) :=
    (congrArg Subtype.val h2.eq).trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 : q = closedPoint _ := (X.fromSpecStalk x).isEmbedding.injective h3
  exact (congrArg PrimeSpectrum.asIdeal h4).ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem exists_valHom {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    ∃ φ : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p, (∀ a, t.val a = φ a) ∧ ∀ a, ‖φ a‖ ≤ 1 :=
  ⟨(OO p).subtype.comp ((RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom),
    fun a => by
      show X₁.M.val _ ((X₁.M.stalkEquiv z₁ a : X₁.Ω₁)) = _
      rw [RatModel.val_gPt t.cen]
      rfl,
    fun a => (mem_OO_iff _).1 (Subtype.prop _)⟩

theorem val_germ {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (t : UCTrait X p z) {V : X.M.Z.Opens}
    (hz : z ∈ V) (g : Γ(X.M.Z, V)) :
    t.val (X.M.Z.presheaf.germ V z hz g) = valF (gPt p ≫ t.y) V g := by
  rw [UCTrait.val, RatModel.stalkHom_germ]
  refine RatModel.val_valF ?_ g
  rintro _ ⟨w, rfl⟩
  exact (RatModel.gPt_specializes t.cen w).mem_open V.isOpen hz

theorem val_stalkMap_germ {X₁ X' : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {z' : X'.M.Z}
    (t : UCTrait X₁ p z₁) (t' : UCTrait X' p z') (hc : t.y ≫ X₁.π = t'.y ≫ X'.π)
    {U : C.Z.Opens} (hU' : X'.π z' ∈ U) (hU₁ : X₁.π z₁ ∈ U) (s : Γ(C.Z, U)) :
    t'.val (X'.π.stalkMap z' (C.Z.presheaf.germ U _ hU' s)) =
      t.val (X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s)) := by
  rw [Scheme.Hom.germ_stalkMap_apply, val_germ t' (V := X'.π ⁻¹ᵁ U) hU', val_germ t hU₁]
  have e1 := GlobalTheory.Points.valR_comp (gPt p ≫ t'.y) X'.π U s
  have e2 := GlobalTheory.Points.valR_comp (gPt p ≫ t.y) X₁.π U s
  rw [Category.assoc, ← hc, ← Category.assoc] at e1
  exact e1.symm.trans e2

theorem exists_pow_norm_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ X' : USetup C) (z₁ : X₁.M.Z), ∃ e : ℕ, 1 ≤ e ∧ ∀ (p : ℕ) [Fact p.Prime] (t : UCTrait X₁ p z₁) (z' : X'.M.Z) (t' : UCTrait X' p z'), t.y ≫ X₁.π = t'.y ≫ X'.π → ∀ h' ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t'.val h'‖ ^ e ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ X' z₁
  have hnoeth : ∀ z' : X'.M.Z, IsNoetherianRing (X'.M.Z.presheaf.stalk z') := fun z' => by
    have : IsDedekindDomain X'.o₁ := ArithBase.ded (Ω := X'.Ω₁)
    have := X'.M.lft
    have : IsLocallyNoetherian X'.M.Z := LocallyOfFiniteType.isLocallyNoetherian X'.M.s
    infer_instance
  haveI := X'.fin
  have hfin := X'.π.finite_preimage_singleton (X₁.π z₁)
  choose e he using fun z' : X'.M.Z => haveI := hnoeth z'; exists_maximalIdeal_pow_le_map_stalkMap X'.M.Z C.Z X'.π z'
  refine ⟨hfin.toFinset.sup e + 1, by omega, ?_⟩
  intro p _ t z' t' hc h' hh'
  have hz' : X'.π z' = X₁.π z₁ := by
    have := congrArg (fun g : Sp (OO p) ⟶ C.Z => g (cPt p)) hc
    simp only [Scheme.Hom.comp_apply, t.cen, t'.cen] at this
    exact this.symm
  have hmem : z' ∈ hfin.toFinset := by simp [hz']
  have hle : e z' ≤ hfin.toFinset.sup e + 1 := (Finset.le_sup hmem).trans (Nat.le_succ _)
  have hpow : h' ^ (hfin.toFinset.sup e + 1) ∈ (maximalIdeal _).map (X'.π.stalkMap z').hom :=
    he z' (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hh' _))
  obtain ⟨φ', hφ', hφ'1⟩ := exists_valHom t'
  obtain ⟨φ₁, hφ₁, -⟩ := exists_valHom t
  have key : ∀ x ∈ (maximalIdeal (C.Z.presheaf.stalk (X'.π z'))).map (X'.π.stalkMap z').hom,
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖φ' x‖ ≤ ‖φ₁ h‖ := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨U, hU, s, rfl⟩ := C.Z.presheaf.germ_exist g
      have hU₁ : X₁.π z₁ ∈ U := hz' ▸ hU
      refine ⟨X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s), ?_, ?_⟩
      · rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have h1 : z₁ ∈ X₁.M.Z.basicOpen (X₁.π.app U s) := (X₁.M.Z.mem_basicOpen _ z₁ hU₁).2 hu
        rw [← Scheme.preimage_basicOpen] at h1
        have h2 : X₁.π z₁ ∈ C.Z.basicOpen s := h1
        rw [← hz'] at h2
        exact (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hg)) ((C.Z.mem_basicOpen s _ hU).1 h2)
      · rw [← hφ', ← hφ₁, val_stalkMap_germ t t' hc hU hU₁ s]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      rcases le_total ‖φ₁ a‖ ‖φ₁ b‖ with hab | hab
      · exact ⟨b, hb, by
          rw [map_add (f := _)]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hxa.trans hab) hyb)⟩
      · exact ⟨a, ha, by
          rw [map_add (f := _)]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hxa (hyb.trans hab))⟩
    | smul b x _ hx =>
      obtain ⟨a, ha, hxa⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖φ' b‖ * ‖φ' x‖ ≤ 1 * ‖φ' x‖ := mul_le_mul_of_nonneg_right (hφ'1 b) (norm_nonneg _)
        _ = ‖φ' x‖ := one_mul _
        _ ≤ ‖φ₁ a‖ := hxa
  obtain ⟨h, hh, hnorm⟩ := key _ hpow
  refine ⟨h, hh, ?_⟩
  rw [hφ', hφ₁, ← norm_pow, ← map_pow]
  exact hnorm

end GlobalTheory.UPoinc.ValBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  intro R _ _ _ hR M G' _ _ hG E
  have hRn : IsNoetherianRing R := hR.1
  have hRi : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hΓ, hsurj⟩ := _root_.GlobalTheory.Mum.Modif.appTop_bijective_surjective R M
  obtain ⟨P', b, X, a, hPn, hbs, hbl, hap, -, hab, hcomm, hX, hlift⟩ := _root_.GlobalTheory.Mum.closedFibre_chart R hR M G' hG E
  have hsq : a ≫ b ≫ PSpace.str R E.N = (X.ι ≫ E.H.ι ≫ G'.hom) ≫ M.π := by
    rw [← Category.assoc, hcomm, Category.assoc, E.f_over]; simp only [Category.assoc]
  have hpt : ∀ w : X.toScheme, (b ≫ PSpace.str R E.N) (a w) = M.π (G'.hom (E.H.ι (X.ι w))) := by
    intro w
    have := congrArg (fun f => f w) hsq
    simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ c : {x : P' // IsClosed ({x} : Set P') ∧ (b ≫ PSpace.str R E.N) x = closedPoint R},
      ∃ V : P'.Opens, c.1 ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧
        IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
    rintro ⟨x, hx1, hx2⟩
    refine _root_.GlobalTheory.Mum.etale_chart_at_closed_point R hR M G' hG E P' b X a hbs hbl hap hab hcomm hΓ hsurj x hx1 hx2 ?_ (hlift x hx1 hx2)
    intro Ω _ p p' hr he hs
    have hc : ∀ t, M.π (G'.hom (E.H.ι ((p ≫ X.ι) t))) = closedPoint R := by
      intro t
      have ht : (p ≫ a) t = x := by
        have : (p ≫ a) t ∈ Set.range (p ≫ a) := ⟨t, rfl⟩
        rw [hr] at this; exact this
      have := hpt (p t)
      rw [Scheme.Hom.comp_apply] at ht
      rw [ht, hx2] at this
      rw [Scheme.Hom.comp_apply]; exact this.symm
    have hf : (p ≫ X.ι) ≫ E.f = (p' ≫ X.ι) ≫ E.f := by
      rw [Category.assoc, Category.assoc, ← hcomm, ← Category.assoc, he, Category.assoc]
    have := _root_.GlobalTheory.Mum.Emb.eq_of_closedFibre R M G' E Ω (p ≫ X.ι) (p' ≫ X.ι) hc (by simpa only [Category.assoc] using hs) hf
    exact (cancel_mono X.ι).1 this
  choose V hxV hVs hVp using key
  set U : P'.Opens := ⨆ c, V c with hUdef
  have hUp : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (U.ι ≫ b ≫ PSpace.str R E.N) M.π :=
    _root_.GlobalTheory.Mum.isPullback_iSup_of_forall _ _ _ _ a _ _ _ hsq _ V hVp
  have hUs : Smooth (U.ι ≫ b ≫ PSpace.str R E.N) := GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth _ _ _ _ V hVs
  have hlft : LocallyOfFiniteType (b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hU0 : ∀ y : P', (b ≫ PSpace.str R E.N) y = closedPoint R → y ∈ U := by
    refine _root_.GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem R P' (b ≫ PSpace.str R E.N) hlft U ?_
    intro y hy1 hy2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy1, hy2⟩, hxV _⟩
  have hsep : IsSeparated (U.ι ≫ b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hqc : QuasiCompact (U.ι ≫ b ≫ PSpace.str R E.N) := by
    haveI := hPn
    have : CompactSpace U := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set P'))
    exact (quasiCompact_iff_compactSpace _).2 this
  let e := hUp.isoPullback
  refine ⟨Near.mk (Over.mk (U.ι ≫ b ≫ PSpace.str R E.N)) hUs hsep hqc
      (e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι) inferInstance ?_ ?_,
    U.ι ≫ b, e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι, ?_, ?_⟩
  · have := hUp.isoPullback_inv_snd
    exact this
  · intro g hg
    obtain ⟨z, rfl⟩ : g ∈ Set.range E.H.ι := by rw [Scheme.Opens.range_ι]; exact E.H_all g hg
    obtain ⟨w, rfl⟩ : z ∈ Set.range X.ι := by rw [Scheme.Opens.range_ι]; exact hX z hg
    have hw : a w ∈ U := hU0 _ (by rw [hpt]; exact hg)
    obtain ⟨w', rfl⟩ : w ∈ Set.range (a ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hw
    refine ⟨e.hom w', ?_⟩
    rw [← Scheme.Hom.comp_apply e.hom, Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.comp_apply]
  · simp only [Category.assoc]
  · show e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.f = pullback.fst (U.ι ≫ b ≫ PSpace.str R E.N) M.π ≫ U.ι ≫ b
    rw [← hcomm, ← Category.assoc ((a ⁻¹ᵁ U).ι), ← morphismRestrict_ι,
      ← Category.assoc e.inv]
    simp only [Category.assoc]
    rw [← Category.assoc e.inv (a ∣_ U), hUp.isoPullback_inv_fst]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricSecondOrderOperatorOfCharacterFor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod.TorTensor

theorem quad_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {κ : Type} [Fintype κ] {n : ℕ}
    (d : Fin n → S → S) (c : κ → Fin n → R) (w : κ → κ → R) (F : κ → S → S)
    (hF : ∀ s f, F s f = ∑ a, φ (c s a) * d a f) (hadd : ∀ s f g, F s (f + g) = F s f + F s g)
    (hmul : ∀ s r f, F s (φ r * f) = φ r * F s f) (f : S) :
    ∑ a, ∑ b, φ (∑ s, ∑ t, w s t * c s a * c t b) * d a (d b f) = ∑ s, ∑ t, φ (w s t) * F s (F t f) := by
  have h : ∀ s t, F s (F t f) = ∑ a, ∑ b, φ (c s a) * φ (c t b) * d a (d b f) := by
    intro s t
    have hs := map_sum (AddMonoidHom.mk' (F s) (hadd s)) (fun b => φ (c t b) * d b f) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hs
    rw [hF t f, hs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hmul, hF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ s, ∑ b, ∑ t, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ b, ∑ t, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) := Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ t, ∑ b, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ a, ∑ b, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by simp only [_root_.mul_assoc]

theorem form_eq {R X : Type} [CommRing R] [AddCommGroup X] {κ : Type} [Fintype κ] (b : Module.Basis κ ℤ X)
    (w : X → X →+ R) (hw : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (α : X) :
    ∑ s, ∑ t, w (b s) (b t) * ((b.repr α t : ℤ) : R) * ((b.repr α s : ℤ) : R) = w α α := by
  have h1 : ∀ (g : X →+ R), g α = ∑ s, g (b s) * ((b.repr α s : ℤ) : R) := by
    intro g
    conv_lhs => rw [← b.sum_repr α]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  have h2 := h1 (AddMonoidHom.mk' (fun mu => w mu α) fun mu mu' => hw mu mu' α)
  simp only [AddMonoidHom.mk'_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h1 (w (b s)), Finset.sum_mul]

def twoPullConstantsRingHom {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) (W : Z.Opens) : R →+* Γ(Z, W) :=
  (s.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem base_constant_function_eq_torTensorConstantsRingHom {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) (W : Z.Opens) (r : R) :
    constFn s W r = twoPullConstantsRingHom s W r := rfl

theorem exists_quad : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ w : Dd.toPre.X → Dd.toPre.X →+ R, (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → ∃ M : Matrix (Fin n) (Fin n) R, Mᵀ = M ∧ (∀ (α : Dd.toPre.X) (W : Y.H.left.Opens), (∃ V : Dd.toPre.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f → GlobalTheory.HeatMod.quadF Y.H.hom dd M W f = constFn Y.H.hom W (w α α) * f) ∧ ∀ (U : Dd.toPre.P.A.left.Opens) (g : Γ(Dd.toPre.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)), W ≤ Y.q.left ⁻¹ᵁ U → GlobalTheory.HeatMod.quadF Y.H.hom dd M W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * GlobalTheory.HeatMod.quadF Y.H.hom dd M W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd w hw hsymm
  let b := Module.Free.chooseBasis ℤ Dd.toPre.X
  let ℓ : Module.Free.ChooseBasisIndex ℤ Dd.toPre.X → Dd.toPre.X →+ R := fun s =>
    (Int.castAddHom R).comp (b.coord s).toAddMonoidHom
  have hℓ : ∀ s α, ℓ s α = ((b.repr α s : ℤ) : R) := fun s α => rfl
  have hex : ∀ s : Module.Free.ChooseBasisIndex ℤ Dd.toPre.X, ∃ c : Fin n → R,
      GlobalTheory.HeatMod.IsTorField Y (GlobalTheory.HeatMod.combF Y.H.hom dd c) (ℓ s) :=
    fun s => _root_.GlobalTheory.HeatMod.TorField.exists_isTorField R Dd O oa Y n v dd hdd (ℓ s)
  choose c hc using hex
  have hmul : ∀ s W r f, combF Y.H.hom dd (c s) W (twoPullConstantsRingHom Y.H.hom W r * f) =
      twoPullConstantsRingHom Y.H.hom W r * combF Y.H.hom dd (c s) W f := by
    intro s W r f
    rw [(hc s).1.2.1 W le_top, ← base_constant_function_eq_torTensorConstantsRingHom, (hc s).2.1 W r, mul_zero, add_zero]
  have key : ∀ W f, quadF Y.H.hom dd (Matrix.of fun a a' => ∑ s, ∑ t, w (b s) (b t) * c s a * c t a') W f =
      ∑ s, ∑ t, twoPullConstantsRingHom Y.H.hom W (w (b s) (b t)) * combF Y.H.hom dd (c s) W (combF Y.H.hom dd (c t) W f) :=
    fun W f => quad_eq (twoPullConstantsRingHom Y.H.hom W) (fun a => dd a W) c (fun s t => w (b s) (b t))
      (fun s => combF Y.H.hom dd (c s) W) (fun _ _ => rfl) (fun s => (hc s).1.1 W le_top) (fun s => hmul s W) f
  refine ⟨Matrix.of fun a a' => ∑ s, ∑ t, w (b s) (b t) * c s a * c t a', ?_, ?_, ?_⟩
  · ext a a'
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hsymm (b t) (b s)]
    ring
  · intro α W hW f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [key, base_constant_function_eq_torTensorConstantsRingHom, ← form_eq b w hw α, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hc t).2.2.1 α W hW f hf, base_constant_function_eq_torTensorConstantsRingHom, hmul, (hc s).2.2.1 α W hW f hf, base_constant_function_eq_torTensorConstantsRingHom, hℓ, hℓ, map_mul,
      map_mul]
    ring
  · intro U g W k f hW
    rw [key, key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hc t).2.2.2 U g W k f hW, (hc s).2.2.2 U g W k _ hW]
    ring

end GlobalTheory.HeatMod.TorTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnit
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

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)

theorem exists_torTan_of_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  intro R _ _ Q O _ _ _ oa Y p hp hq
  have hmono : ∀ {T : Over (Sp R)} (a b : T ⟶ splitTorus (Sp R) (RayEv.Chr Q)), a ≫ Y.i = b ≫ Y.i → a = b :=
    fun a b h => Y.isKernel.hom_ext h (toUnit_unique _ _)
  have hw : p ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by rw [hq, Hom.one_def]
  let t := Y.isKernel.lift p (toUnit _) hw
  have ht : t ≫ Y.i = p := Y.isKernel.lift_fst _ _ _
  have := Y.i_linear.isMonHom
  have htan : Chart.spMap (Chart.fstD R) ≫ t = 1 := hmono _ _ (by
    rw [Category.assoc, ht, MonObj.one_comp]; exact (Chart.isTan_iff p).2 hp)
  let a : RayEv.Chr Q → DualNumber R := fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))
  have hfst : ∀ χ, (a χ).fst = 1 := fun χ => by
    have e := congrArg (fun f => (coord f).hom (AddMonoidAlgebra.single χ 1)) htan
    simp only at e
    rw [coord_comp, Diag.coord_one, CommRingCat.hom_comp, RingHom.comp_apply, Chart.spMap_left] at e
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Chart.fstD R).toRingHom)
    have k := congrArg (fun f => f.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
    rw [e, map_one] at k
    exact k.symm
  have h0 : a 0 = 1 := by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single 0 1)) = 1
    rw [Diag.coord_single_zero, map_one]
  have hadd : ∀ x y, a (x + y) = a x * a y := fun x y => by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single (x + y) 1)) = _
    rw [Diag.coord_single_add, map_mul]
  have hform : ∀ χ, a χ = 1 + inr (a χ).snd := fun χ => by
    ext
    · rw [hfst χ]; simp
    · simp
  let ℓ : Q.X →+ R :=
    { toFun := fun χ => (a χ).snd
      map_zero' := (congrArg TrivSqZeroExt.snd h0).trans TrivSqZeroExt.snd_one
      map_add' := fun x y => (congrArg TrivSqZeroExt.snd (hadd x y)).trans (by
        rw [hform x, hform y]
        simp only [mul_add, add_mul, _root_.one_mul, _root_.mul_one, TrivSqZeroExt.inr_mul_inr, add_zero,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add]) }
  refine ⟨ℓ, ?_⟩
  rw [← ht]
  refine congrArg (· ≫ Y.i) (Diag.hom_ext fun χ => ?_)
  rw [torTan, Diag.coord_ofChar]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + inr (a χ).snd)
  rw [← hform χ]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1)))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end GlobalTheory.HeatMod.TorField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pelOK_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D hX
  obtain ⟨E, _, _, _, ⟨H⟩⟩ := GlobalTheory.Mum.exists_host
  obtain ⟨r, W, ρ, hr, hpos, hdet, hadj, hW⟩ := GlobalTheory.Mum.unimodLattice E H
  obtain ⟨D', ⟨T⟩⟩ := _root_.GlobalTheory.Mum.TensExist.exists_tens R hR.1 D W hpos hdet
  obtain ⟨_, o, hact, hψ⟩ := GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data R hR.1 E H D D' W hpos hdet T ρ hadj hW
  obtain ⟨Dm, hDm⟩ := GlobalTheory.T.tensorDegData_unitary_type R hR E H D D' W hpos hdet T ρ hadj hW hX hr o hact hψ
  exact ⟨E, _, _, _, H, Dm, D', _, o, hDm, _root_.GlobalTheory.Mum.Tens.nonempty_factor R hR.1 D D' W hpos hdet T hr⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

def KerKilledOn (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (V : S'.Opens) : Prop :=
  ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G),
    (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull
        (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen,
        s.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledLocus
end

