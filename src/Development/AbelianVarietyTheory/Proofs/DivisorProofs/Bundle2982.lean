module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSides
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleBoth

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_of_le {R : Type} [CommRing R] {W : (Sp R).Opens} (r : R) (h : W ≤ (Sp R).basicOpen (fnSp R r)) :
    IsUnit (fnOn W r) := isUnit_of_basicOpen_top _ (by
  have e := Scheme.preimage_basicOpen W.ι (fnSp R r)
  refine Eq.trans e.symm (top_le_iff.1 fun x _ => h x.2))

theorem mem_basicOpen_of_ne {R F : Type} [CommRing R] [Field F] (α : R →+* F) {r : R} (h : α r ≠ 0) {Z : Scheme.{0}}
    (s : Z ⟶ Sp F) (z : Z) : (s ≫ spMap α) z ∈ (Sp R).basicOpen (fnSp R r) := by
  have hpre : (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    refine (congrArg IsUnit (appTop_comp_spMap α s r)).mpr ?_
    exact ((IsUnit.mk0 _ h).map (fnSp _)).map s.appTop.hom
  exact (show z ∈ (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) from hpre.ge trivial)

theorem val_psiOn_rescale {R F : Type} [CommRing R] [IsDomain R] [Field F] (Q : DegPre R) (g : Q.X → (FractionRing R)ˣ)
    {W W₀ : (Sp R).Opens} (ψ : PsiOn Q W) (ψ₀ : PsiOn (GlobalTheory.PolDeg.rescale Q g) W₀) (y : Q.X) (a b : R)
    (hab : (g y : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a)
    (α : R →+* F) (hb : α b ≠ 0) (v : Fˣ) (hv : (v : F) * α b = α a) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme)
    (r₀ : Z ⟶ W₀.toScheme) (s : Z ⟶ Sp F) (hr : r ≫ W.ι = s ≫ spMap α) (hr₀ : r₀ ≫ W₀.ι = s ≫ spMap α)
    (z : Z) (J) (hJ : Good Q.P.L z J) :
    val (ψ₀.psi y) r₀ z J = gm s z ⊤ (unitOn v) * val (ψ.psi y) r z J := by
  have ha : α a ≠ 0 := hv ▸ mul_ne_zero v.ne_zero hb
  have ha' : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => ha (by rw [h, map_zero])
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => hb (by rw [h, map_zero])
  obtain ⟨W', l, l₀, la, lb, hm⟩ : ∃ W' : (Sp R).Opens, W' ≤ W ∧ W' ≤ W₀ ∧ W' ≤ (Sp R).basicOpen (fnSp R a) ∧
      W' ≤ (Sp R).basicOpen (fnSp R b) ∧ ∀ x, (s ≫ spMap α) x ∈ W' :=
    ⟨(W ⊓ W₀) ⊓ ((Sp R).basicOpen (fnSp R a) ⊓ (Sp R).basicOpen (fnSp R b)), inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right, fun x =>
      ⟨⟨(congrArg (fun q => q x ∈ W) hr).mp (r x).2, (congrArg (fun q => q x ∈ W₀) hr₀).mp (r₀ x).2⟩,
        mem_basicOpen_of_ne α ha s x, mem_basicOpen_of_ne α hb s x⟩⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Z ⟶ W'.toScheme, ρ ≫ W'.ι = s ≫ spMap α :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hm x), IsOpenImmersion.lift_fac _ _ _⟩
  let m : W'.toScheme ⟶ W.toScheme := (Sp R).homOfLE l
  let m₀ : W'.toScheme ⟶ W₀.toScheme := (Sp R).homOfLE l₀
  have f : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have f₀ : m₀ ≫ W₀.ι = W'.ι := Scheme.homOfLE_ι _ _
  have ua := isUnit_fnOn_of_le a la
  have ub := isUnit_fnOn_of_le b lb
  have hφ : m ≫ (toUnit (TW W) ≫ Q.c y).left = m₀ ≫ (toUnit (TW W₀) ≫ Q.c y).left := by
    show m ≫ W.ι ≫ (Q.c y).left = m₀ ≫ W₀.ι ≫ (Q.c y).left
    rw [← Category.assoc, f, ← Category.assoc, f₀]
  have key := GlobalTheory.PsiEvenPull.val_eq_of_app_injective Q.P.isLB
    (u := GlobalTheory.UU.scaleGen ub.unit (LB.pullGen Q.P.L _ _ (ψ₀.psi y) m₀))
    (u' := GlobalTheory.UU.scaleGen ua.unit (LB.pullGen Q.P.L _ _ (ψ.psi y) m))
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) hφ)
    (jK R ∣_ W') (GlobalTheory.PsiEvenPull.app_injective_generic W')
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ₀.psi_gen y) m₀))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m)) (fun x I hI => by
      have e : (jK R ∣_ W') ≫ W'.ι = (jK R ⁻¹ᵁ W').ι ≫ jK R := morphismRestrict_ι _ _
      have p := GlobalTheory.ArcSpecialise.psiOn_generic ψ y ((jK R ∣_ W') ≫ m) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f, e]) hI
      have p₀ := GlobalTheory.ArcSpecialise.psiOn_generic ψ₀ y ((jK R ∣_ W') ≫ m₀) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f₀, e]) hI
      have q : val ((GlobalTheory.PolDeg.rescale Q g).psi y) (jK R ⁻¹ᵁ W').ι x I =
          gm (jK R ⁻¹ᵁ W').ι x ⊤ (unitOn (g y)) * val (Q.psi y) (jK R ⁻¹ᵁ W').ι x I :=
        GlobalTheory.UU.val_scaleGen (unitOn (g y)) (Q.psi y) _ hI
      have ga := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e a ua.unit (Units.mk0 _ ha') ua.unit_spec rfl x
      have gb := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e b ub.unit (Units.mk0 _ hb') ub.unit_spec rfl x
      have w : unitOn (Units.mk0 _ ha') = unitOn (Units.mk0 _ hb') * unitOn (g y) :=
        (congrArg unitOn (Units.ext (hab.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hI).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hI).symm)
      refine (congrArg₂ (· * ·) gb ((val_pull hI _ _ _).trans (p₀.trans q))).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) ga ((val_pull hI _ _ _).trans p)).symm)
      rw [w, map_mul, _root_.mul_assoc]) Z ρ z J hJ
  have ga := gm_fnOn W' α _ _ hρ a ua.unit (Units.mk0 _ ha) ua.unit_spec rfl z
  have gb := gm_fnOn W' α _ _ hρ b ub.unit (Units.mk0 _ hb) ub.unit_spec rfl z
  have w : unitOn (Units.mk0 _ ha) = unitOn (Units.mk0 _ hb) * unitOn v :=
    (congrArg unitOn (Units.ext (hv.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
  have c : ρ ≫ m = r := by rw [← cancel_mono W.ι, Category.assoc, f, hρ, hr]
  have c₀ : ρ ≫ m₀ = r₀ := by rw [← cancel_mono W₀.ι, Category.assoc, f₀, hρ, hr₀]
  have k₂ := (congrArg₂ (· * ·) gb (val_pull hJ _ _ _)).symm.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm.trans
    (key.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) ga (val_pull hJ _ _ _)))))
  rw [w, map_mul, _root_.mul_assoc, c, c₀] at k₂
  exact mul_left_cancel k₂

theorem exists_isPullDeg_rescale : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  intro R V _ _ _ _ θ Q Q' h g g' ⟨ψ₀⟩ H
  have hsq : jK V ≫ specOf θ = 𝟙 (TK V).left ≫ spMap ((algebraMap V (FractionRing V)).comp θ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  obtain ⟨t, ht⟩ : ∃ t : (TK V).left ⟶ (TW (⊤ : (Sp R).Opens)).left, t ≫ (⊤ : (Sp R).Opens).ι = jK V ≫ specOf θ :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp R).Opens).ι (jK V ≫ specOf θ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have gp : IsGrpPullback Q'.P.A Q.P.A (spMap θ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec Q'.P.A) (fun _ => eSec Q.P.A) (fun _ => 1) Q'.rig Q.rig (spMap θ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : Q'.X, (Q'.c x).left ≫ proj h = spMap θ ≫ (Q.c (h.xe x)).left := h.c_pr
  have hv : ∀ (x : Q'.X) (z : (TK V).left) J J', Good Q.P.L z J → Good Q'.P.L z J' →
      val (ψ₀.psi (h.xe x)) t z J =
        (om h.w z J J' (Q'.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    obtain ⟨a, b, hb, hab, hab'⟩ := H x
    have e0 := val_psiOn_rescale Q g h.psiW ψ₀ (h.xe x) a b hab ((algebraMap V (FractionRing V)).comp θ)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hb) (g' x) hab' h.g t (𝟙 _)
      (h.g_comm.trans hsq) (ht.trans hsq) z J hJ
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn (g' x)) * val (Q'.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (g' x)) (Q'.psi x) (𝟙 _) hJ'
    refine e0.trans ?_
    rw [e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  obtain ⟨hD, h₁, h₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale Q g)
    (GlobalTheory.PolDeg.rescale Q' g') ψ₀ t ht gp h.w ((isGen_iff h.w).1 h.w_gen) hr h.xe hc hv
  exact ⟨hD, h₁, h₂⟩

end GlobalTheory.RescaleBoth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedSubmoduleOfFinrankLe
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.IsoSat

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isotropic_vector (D : Datum H) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) :
    ∃ x : D.La, x ≠ 0 ∧ ∀ a : 𝓞 E, D.EF (a • x) x = 0 := by
  by_cases h3 : 3 ≤ D.p + D.q
  · have hξ := GlobalTheory.OneSpace.cc_rt H
    have hξ0 := GlobalTheory.OneSpace.rt_ne H
    obtain ⟨G, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H D (H.rt : E) hξ hξ0 (D.p + D.q) rfl
    have hind := GlobalTheory.SplitGenus.indefinite D hp hq G φ hM
    obtain ⟨inj, span, hG, hdet, hEF⟩ := hM
    have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
      refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
      have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
      linear_combination (1 / 2 : E) * h2
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind
    have hz' : FD.herm G z z = 0 := hz
    obtain ⟨N, g, hN, hg⟩ := GlobalTheory.SplitGenus.exists_scaled_map (LinearMap.toSpanSingleton (𝓞 E) _ z) φ inj span
    have h1 : φ (g 1) = (N : E) • z := by rw [hg, LinearMap.toSpanSingleton_apply, one_smul]
    refine ⟨g 1, fun h => ?_, fun a => ?_⟩
    · rw [h, map_zero, eq_comm, smul_eq_zero] at h1
      exact h1.elim (Nat.cast_ne_zero.2 hN.ne') hz0
    · have h2 := hEF (a • g 1) (g 1)
      rw [map_smul φ, h1, show a • (N : E) • z = (a : E) • (N : E) • z from rfl, GlobalTheory.HermModel.herm_smul_left,
        GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right, hz'] at h2
      simp only [zero_mul, mul_zero, map_zero] at h2
      exact_mod_cast h2
  · obtain ⟨k, f, hk, hf⟩ := GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry E H (GlobalTheory.HostModel.hypDatum H) D
      (by change D.p = 1; omega) (by change D.q = 1; omega) 2 two_pos
    have hk0 : (k : ℤ) ^ 2 ≠ 0 := by
      have : k ≠ 0 := by
        rintro rfl
        simp at hk
      positivity
    refine ⟨f (1, 0), fun h => ?_, fun a => ?_⟩
    · have : ((1, 0) : (GlobalTheory.HostModel.hypDatum H).La) = 0 := (GlobalTheory.HostModel.hypDatum H).unimod.1 (LinearMap.ext fun y => by
        have := hf (1, 0) y
        rw [h, map_zero, LinearMap.zero_apply] at this
        rw [map_zero, LinearMap.zero_apply]
        exact (mul_eq_zero.1 this.symm).resolve_left hk0)
      exact one_ne_zero (congrArg Prod.fst this)
    · rw [← map_smul, hf, GlobalTheory.HostModel.hypDatum_smul, smul_zero, GlobalTheory.HostModel.hypDatum_EF_inl_inl, mul_zero]

theorem exists_saturation (D : Datum H) (W : Submodule (𝓞 E) D.La) (hW : W ≤ perp D W) :
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) W := by
  have := D.fin
  let Z : Submodule (𝓞 E) D.La :=
    { carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ W}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact nsmul_mem hx m
        · rw [mul_smul]; exact nsmul_mem hy n
      smul_mem' := by
        rintro a x ⟨n, hn, hx⟩
        exact ⟨n, hn, by rw [smul_comm]; exact W.smul_mem a hx⟩ }
  have hle : W ≤ Z := fun x hx => ⟨1, one_ne_zero, by rwa [one_smul]⟩
  refine ⟨Z, ⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨n, hn, hx⟩ y ⟨m, hm, hy⟩
    have := hW hx _ hy
    simpa [hn, hm] using this
  · rintro n x hn ⟨m, hm, hx⟩
    exact ⟨m * n, mul_ne_zero hm hn, by rwa [mul_smul]⟩
  · have h1 := Submodule.finrank_quotient_add_finrank (W.comap Z.subtype)
    have h2 : Module.finrank (𝓞 E) (Z ⧸ W.comap Z.subtype) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro x
      obtain ⟨⟨x, n, hn, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
      refine ⟨(n : 𝓞 E), Nat.cast_ne_zero.2 hn, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Nat.cast_smul_eq_nsmul]
      exact hx
    rw [← h1, h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]

theorem exists_succ (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z)
    (hr : Module.finrank (𝓞 E) Z + 1 ≤ min D.p D.q) :
    ∃ Z' : Submodule (𝓞 E) D.La, IsIsoSat D Z' ∧ Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) Z + 1 := by
  have := D.fin
  obtain ⟨D', f, ⟨hs, hk, hE⟩, hp, hq⟩ := exists_lowerDatum D Z hZ
  obtain ⟨x', hx0, hx⟩ := exists_isotropic_vector D' (by omega) (by omega)
  obtain ⟨x, rfl⟩ := hs x'
  have := D'.proj
  have hnot : ∀ a : 𝓞 E, a • (x : D.La) ∈ Z → a = 0 := fun a ha => by
    have h := (hk (a • x)).2 ha
    rw [map_smul, smul_eq_zero] at h
    exact h.resolve_right hx0
  let g : (Z × 𝓞 E) →ₗ[𝓞 E] D.La := Z.subtype.coprod (LinearMap.toSpanSingleton (𝓞 E) _ (x : D.La))
  have hg : ∀ u, g u = u.1 + u.2 • (x : D.La) := fun u => rfl
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun u hu => by
    rw [hg] at hu
    have h2 : u.2 = 0 := hnot _ (by rw [eq_neg_of_add_eq_zero_right hu]; exact neg_mem u.1.2)
    rw [h2, zero_smul, add_zero] at hu
    exact Prod.ext (Subtype.ext hu) h2
  obtain ⟨Z', h1, h2⟩ := exists_saturation D (LinearMap.range g) (by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have e1 : D.EF u.1 v.1 = 0 := hZ.1 u.1.2 _ v.1.2
    have e2 : ∀ (a : 𝓞 E) (z : Z), D.EF (a • (x : D.La)) z = 0 := fun a z => (a • x).2 _ z.2
    have e3 : D.EF (u.2 • (x : D.La)) (v.2 • (x : D.La)) = 0 := by
      have h := hx (H.bar v.2 * u.2)
      rw [← map_smul, hE, Submodule.coe_smul, mul_smul, D.adj, bar_bar] at h
      exact h
    rw [hg, hg]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [e1, e2, e3, ef_swap, e2]
    simp)
  refine ⟨Z', h1, ?_⟩
  rw [h2, ← (LinearEquiv.ofInjective g hinj).finrank_eq]
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.snd (𝓞 E) Z (𝓞 E)))
  rw [((LinearMap.snd (𝓞 E) Z (𝓞 E)).quotKerEquivOfSurjective LinearMap.snd_surjective).finrank_eq,
    Module.finrank_self, ← LinearMap.range_inl,
    ← (LinearEquiv.ofInjective _ LinearMap.inl_injective).finrank_eq] at h3
  omega

end GlobalTheory.LowFilt.IsoSat

namespace GlobalTheory.LowFilt

theorem exists_isIsoSat_finrank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ),
    r ≤ min D.p D.q → ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  intro E _ _ _ H D r
  induction r with
  | zero => exact fun _ => ⟨⊥, (isOpp_bot D).isIsoSat, finrank_bot _ _⟩
  | succ r ih =>
    intro hr
    obtain ⟨Z, hZ, rfl⟩ := ih (by omega)
    exact IsoSat.exists_succ D Z hZ hr

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_xfLevel_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R)))
    (hI₀ : GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hL₂ : Laws2 := hLL.2.1
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (AlgebraicClosure (FractionRing R)) :=
    charZero_of_injective_ringHom (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).injective
  have hB := C.P.D.tau_bimult
  have he := C.P.D.psi_even
  let s : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hs : s.toRingHom.comp (algebraMap (FractionRing R) _) = algebraMap (FractionRing R) F := s.comp_algebraMap
  have hj : spMap s.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing R)) = jFK (R := R) F := by
    rw [jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  let I := GlobalTheory.ArcExt.tateExt s.toRingHom hs hB hL I₀ (GlobalTheory.ArcOfModel.weilQkIs_qkExt hL hL₂ he hB s.toRingHom hs)
  have hext : ∀ n a, QkExt s.toRingHom (I₀.ev n a) (I.ev n a) := fun n a =>
    (GlobalTheory.TorusExt.qkExt_iff hB _ hs _ _).2 rfl
  refine ⟨I, ⟨?_, ?_⟩, fun n a => (hext n a).1⟩
  · show ((Units.map s.toRingHom.toMonoidHom (I₀.ζ l.M') : Fˣ) : F) = _
    rw [Units.coe_map]
    show s.toRingHom ((I₀.ζ l.M' : AlgebraicClosure (FractionRing R))) = _
    rw [hI₀.1]
    simp only [toF, RingHom.comp_apply]
    exact s.commutes _
  · intro k a σ hk x hx
    have hk1 : 1 ≤ k := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact l.A_pos
      · have := l.three_le; omega
    have hT := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR.1 C.t C.P
    obtain ⟨f₀, f₀₁, -⟩ := hT (AlgebraicClosure (FractionRing R)) k hk1
    obtain ⟨fF, fF₁, -⟩ := hT F k hk1
    obtain ⟨g₀, hg₁, hg₂⟩ := hI₀.2 k a σ hk (f₀ (I₀.ev k a)) ((f₀₁ _ _).2 rfl)
    let x' : TFK (R := R) F ⟶ C.P.A.A :=
      (Over.homMk (spMap s.toRingHom) hj : TFK (R := R) F ⟶ TFK (R := R) (AlgebraicClosure (FractionRing R))) ≫
        f₀ (I₀.ev k a)
    have hx' : C.P.ToA F k (I.ev k a) x' :=
      (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hLL R (maximalIdeal R) hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U _ F s k hk1
        (I₀.ev k a) (I.ev k a) _ x' (hext k a) rfl).1 ((f₀₁ _ _).2 rfl)
    have hxx : x = x' := ((fF₁ _ _).1 hx).trans ((fF₁ _ _).1 hx').symm
    refine ⟨spMap s.toRingHom ≫ g₀, ?_, ?_⟩
    · rw [Category.assoc, hg₁, hxx]
      simp only [x', Over.comp_left, Over.homMk_left, Category.assoc]
    · rw [Category.assoc, hg₂, ← hj]
      simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep.Setup

def RootsIn {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) (F : Polynomial V) : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (ψ : V₁ →+* D) (d : D), F.eval₂ (ψ.comp ρ) d = 0 → d ∈ ψ.range

theorem rootsIn_of_splits {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) {F : Polynomial V} (hF : F.Monic)
    (h : (F.map ρ).Splits) : RootsIn ρ F := by
  intro D _ _ ψ d hd
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 h
  rw [← Polynomial.eval₂_map, hm, (hF.map ρ).leadingCoeff, map_one, _root_.one_mul, Polynomial.eval₂_multiset_prod,
    Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  obtain ⟨a, -, ha⟩ := hd
  exact ⟨a, (sub_eq_zero.1 (by simpa using ha)).symm⟩

theorem exists_ext (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V) (L : Type) [Field L]
    [Algebra (FractionRing V) L] [FiniteDimensional (FractionRing V) L] (F : Polynomial V) (hF : F.Monic) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (σ : L →+* FractionRing V₁),
      GlobalTheory.Mum.Base V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧
      (σ.comp (algebraMap (FractionRing V) L)).comp (algebraMap V _) = (algebraMap V₁ _).comp ρ ∧ RootsIn ρ F := by
  haveI := hV.2
  let K := FractionRing V
  let F₁ : Polynomial L := F.map ((algebraMap K L).comp (algebraMap V K))
  let L₂ := F₁.SplittingField
  haveI : FiniteDimensional K L₂ := Module.Finite.trans L L₂
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := MumLevel.exists_galois_root K L₂ 1 le_rfl
  obtain ⟨V₁, _, _, _, ρ, e, -, hρ, he, -, -⟩ := MumLevel.exists_ring V hV E ζ 1 le_rfl hζ
  let τ : L₂ →+* FractionRing V₁ := e.toRingHom.comp j.toRingHom
  have hσ : ((τ.comp (algebraMap L L₂)).comp (algebraMap K L)).comp (algebraMap V K) = (algebraMap V₁ _).comp ρ :=
    RingHom.ext fun r => (congrArg e ((congrArg j (IsScalarTower.algebraMap_apply K L L₂ _).symm).trans
      (j.commutes _))).trans (he r)
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  haveI := hρ.1.2.2.1
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, τ.comp (algebraMap L L₂),
    ⟨hρ.1, (ρ.charZero_iff hρ.2.1).1 inferInstance⟩, hρ.2.1, hρ.2.2, hσ, rootsIn_of_splits ρ hF ?_⟩
  refine Polynomial.Splits.of_splits_map_of_injective hinj ?_ fun a ha => ?_
  · have := (Polynomial.SplittingField.splits F₁).map τ
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hσ] at this
    rwa [Polynomial.map_map]
  · exact IsIntegrallyClosed.isIntegral_iff.1 ⟨F.map ρ, hF.map ρ, by
      rw [← Polynomial.eval_map]; exact (Polynomial.mem_roots'.1 ha).2⟩

theorem RootsIn.exists_sq {V V₁ : Type} [CommRing V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {F : Polynomial V}
    (h : RootsIn ρ F) {s : V} (hs : Polynomial.X ^ 2 - Polynomial.C s ∣ F) : ∃ r : V₁, r ^ 2 = ρ s := by
  let D := AlgebraicClosure (FractionRing V₁)
  let ψ : V₁ →+* D := (algebraMap (FractionRing V₁) D).comp (algebraMap V₁ _)
  have hψ : Function.Injective ψ := (algebraMap (FractionRing V₁) D).injective.comp (IsFractionRing.injective V₁ _)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (ρ s)) two_pos
  obtain ⟨G, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := h D ψ d (by simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, hd])
  exact ⟨r, hψ (by rw [map_pow, hd])⟩


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


theorem exists_lift_genericFibre (C : UCompact Xo c) {O W : Type} [CommRing O] [CommRing W] (ev : O →+* W) [IsLocalHom ev]
    (t : Sp O ⟶ C.Z) (ξ : Sp W ⟶ pullback C.z (spMap C.b)) (h : spMap ev ≫ t = ξ ≫ pullback.fst _ _) :
    ∃ ζ : Sp O ⟶ pullback C.z (spMap C.b), ζ ≫ pullback.fst _ _ = t := by
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ C.z)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (ξ ≫ pullback.snd _ _)
  have e : φ ≫ CommRingCat.ofHom ev = CommRingCat.ofHom C.b ≫ β := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hβ, ← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (φ.hom a) := fun a => by
    refine (isUnit_map_iff ev _).1 ?_
    rw [show ev (φ.hom a) = β.hom (C.b a) from congrArg (fun χ => χ.hom a.1) e]
    exact (IsLocalization.map_units c.F a).map β.hom
  refine ⟨pullback.lift t (spMap (IsLocalization.lift (S := c.F) hu)) ?_, pullback.lift_fst _ _ _⟩
  rw [← hφ, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsLocalization.lift_comp (S := c.F) hu).symm)

theorem fromSpecStalk_bot {X : Scheme.{0}} [IsIntegral X] (z : X) (p : Sp (X.presheaf.stalk z)) (hp : p.asIdeal = ⊥) :
    X.fromSpecStalk z p = genericPoint X := by
  obtain ⟨q, hq⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes z
  have h : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (show p.asIdeal ≤ q.asIdeal from hp ▸ bot_le)
  exact ((hq ▸ h.map (X.fromSpecStalk z).continuous).antisymm (genericPoint_specializes _)).eq

end GlobalTheory.USep.Setup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateIsoGenericAbelianOfUniformisationStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  first | exact @GlobalTheory.LowDat.exists_tateIso_toA | exact GlobalTheory.LowDat.exists_tateIso_toA | (intros; apply GlobalTheory.LowDat.exists_tateIso_toA <;> assumption)
end
end

