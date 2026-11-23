module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.DualMapCompAlgebraMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgf

section Rings

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp_spMap_sesquilinear_fractions (f : R →+* R') (f' : R' →+* R'') : spMap f' ≫ spMap f = spMap (f'.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_algebraMap_sesquilinear_fractions (f : R →+* R') :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem fstHom_comp_dualMap' (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem fst_comp_algebraMap_dual : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_dualMap_ring (f : R →+* R') (f' : R' →+* R'') : (dualMap f').comp (dualMap f) = dualMap (f'.comp f) := by
  ext x <;> simp [dualMap]

theorem dualMap_eq_dualMapR' (f : R →+* R') : dualMap f = ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f := RingHom.ext fun _ => rfl

end Rings

theorem mono_spec_fraction_field (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  show Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)).op)
  infer_instance

set_option maxHeartbeats 1000000 in
theorem cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b a
  have hmono := mono_spec_fraction_field X.K
  set φ : 𝓞 X.K →+* X.K := algebraMap (𝓞 X.K) X.K with hφ
  have hA : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
  have hψ : (X.ψ b a).left ≫ X.B.t.G.hom = (X.C b).P.A.hom := Over.w (X.ψ b a)
  set F : Sp (DualNumber X.K) ⟶ X.B.t.G.left := spMap (dualMap φ) ≫ (X.C b).v.left ≫ (X.ψ b a).left with hFdef
  have hF : F ≫ X.B.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) ≫ spMap φ := by
    rw [hFdef, Category.assoc, Category.assoc, hψ, hA, spMap_comp_spMap_sesquilinear_fractions, spMap_comp_spMap_sesquilinear_fractions, dualMap_comp_algebraMap_sesquilinear_fractions]
  have m'c := X.m'.cart.1
  have mc := X.m.cart.1

  have hbase : ∀ r : Sp (DualNumber X.K) ⟶ X.t.G.left, r ≫ X.m'.φ = F →
      r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    intro r hr
    apply (cancel_mono (spMap φ)).1
    rw [Category.assoc, ← m'c.w, ← Category.assoc, hr, hF]
  refine ⟨?_, ?_⟩
  · let r₀ := m'c.lift F (spMap (algebraMap X.K (DualNumber X.K))) hF
    have hr₀ : r₀ ≫ X.m'.φ = F := m'c.lift_fst _ _ _
    have hr₀' : r₀ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := m'c.lift_snd _ _ _
    let u₀ : epsAt (under X.y) ⟶ Xo.univ.t.G := Over.homMk (r₀ ≫ X.m.φ) (by
      show (r₀ ≫ X.m.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) ≫ under X.y
      rw [Category.assoc, mc.w, ← Category.assoc, hr₀'])
    refine ⟨u₀, ⟨r₀, rfl, hr₀⟩, ?_⟩
    rintro u ⟨r, hr1, hr2⟩
    have e : r = r₀ := m'c.hom_ext (hr2.trans hr₀.symm) ((hbase r hr2).trans hr₀'.symm)
    apply Over.OverMorphism.ext
    rw [← hr1, e]
    rfl
  · rintro u ⟨r, hr1, hr2⟩
    have hrb := hbase r hr2
    refine ⟨?_, ?_⟩
    ·
      have hs : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ r = η[X.t.G].left := by
        refine m'c.hom_ext ?_ ?_
        · rw [Category.assoc, hr2, GlobalTheory.UU.eSec_comp_of_isGrpPullback X.m'.cart]
          have ht : spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom ≫ (X.C b).v.left =
              η[(X.C b).P.A].left := (X.C b).basis.1 0
          have hmon : η[(X.C b).P.A].left ≫ (X.ψ b a).left = η[X.B.t.G].left := by
            have := ((X.fam b).1 a).isMonHom
            exact congrArg CommaMorphism.left (IsMonHom.one_hom (f := X.ψ b a))
          rw [← Category.assoc, spMap_comp_spMap_sesquilinear_fractions, fstHom_comp_dualMap', ← spMap_comp_spMap_sesquilinear_fractions, Category.assoc,
            reassoc_of% ht, hmon]
        · rw [Category.assoc, hrb]
          show spMap (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom ≫ spMap (algebraMap X.K (DualNumber X.K)) = _
          rw [spMap_comp_spMap_sesquilinear_fractions, fst_comp_algebraMap_dual, Over.w η[X.t.G]]
          exact Spec.map_id _
      show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ u.left = _
      rw [← hr1, ← Category.assoc, hs, GlobalTheory.UU.eSec_comp_of_isGrpPullback X.m.cart, Hom.one_def]
      rfl
    ·
      have hπ : X.π b ≫ (X.C b).P.A.hom = (Z b).C'.P.A.hom ≫ spMap ((algebraMap X.K ℂ).comp φ) :=
        (X.map' b).2.1.2.1.1.w
      have hvo : (Z b).C'.v.left ≫ X.π b =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ((algebraMap X.K ℂ).comp φ)) ≫ (X.C b).v.left := (X.map' b).2.2.1
      have hw0 : (X.π b ≫ (X.ψ b a).left) ≫ X.B.t.G.hom =
          ((Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ)) ≫ spMap φ := by
        rw [Category.assoc, hψ, hπ, Category.assoc, spMap_comp_spMap_sesquilinear_fractions]
      let Φ₀ := m'c.lift (X.π b ≫ (X.ψ b a).left) ((Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ)) hw0
      have hΦ₁ : Φ₀ ≫ X.m'.φ = X.π b ≫ (X.ψ b a).left := m'c.lift_fst _ _ _
      have hΦ₂ : Φ₀ ≫ X.t.G.hom = (Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ) := m'c.lift_snd _ _ _
      have claim1 : ∀ s : ℂ, ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀ ≫ X.m.φ = (FU.ex i P (s • P a)).left := by
        intro s
        have hx1 : (((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀) ≫ X.t.G.hom = spMap (algebraMap X.K ℂ) := by
          rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w ((Z b).u.ex (fun _ => (Z b).c * s))]
          exact Category.id_comp _
        have hx2 : (((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀) ≫ X.m'.φ =
            ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ X.π b ≫ (X.ψ b a).left := by
          rw [Category.assoc, hΦ₁]
        rw [← Category.assoc]
        exact X.tie b a s _ hx1 hx2
      have claim2 : spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left = (Z b).C'.v.left ≫ Φ₀ ≫ X.m.φ := by
        have key : spMap (dualMap (algebraMap X.K ℂ)) ≫ r = (Z b).C'.v.left ≫ Φ₀ := by
          refine m'c.hom_ext ?_ ?_
          · rw [Category.assoc, hr2, Category.assoc, hΦ₁, reassoc_of% hvo, ← dualMap_eq_dualMapR', ← Category.assoc,
              spMap_comp_spMap_sesquilinear_fractions, dualMap_comp_dualMap_ring]
          · rw [Category.assoc, hrb, Category.assoc, hΦ₂, ← Category.assoc, Over.w (Z b).C'.v, spMap_comp_spMap_sesquilinear_fractions,
              dualMap_comp_algebraMap_sesquilinear_fractions, ← spMap_comp_spMap_sesquilinear_fractions]
            rfl
        rw [← hr1, ← Category.assoc, key, Category.assoc]
      have hline := GlobalTheory.CMPeriodCompare.isDerivAt0_line (φ := 𝟙 (Z b).C'.P.A.left) (t := (Z b).C'.v) (Z b).u ((Z b).C'.basis.1 0) (Z b).diff
      have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom hline (Φ₀ ≫ X.m.φ)
      have hfun : (fun z : Fin 1 → ℂ => (((Z b).u.ex (z 0 • fun _ => (Z b).c * (Z b).z)).left ≫ 𝟙 _) ≫ Φ₀ ≫ X.m.φ) =
          fun z => (FU.ex i P ((z 0 * (Z b).z) • P a)).left := by
        funext z
        have e : (z 0 • fun _ => (Z b).c * (Z b).z) = (fun _ : Fin (Z b).C'.P.g => (Z b).c * (z 0 * (Z b).z)) := by
          funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [Category.comp_id, e, claim1]
      rw [hfun, Category.comp_id, ← claim2] at h2
      let Dl : (Fin 1 → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight ((Z b).z • P a)
      have hhol : IsHolTo Set.univ (fun z => (FU.ex i P z).left) := by
        intro U f
        obtain ⟨h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.anHol FU i P hP U f
        simp only [Set.mem_univ, true_and]
        exact ⟨h1, h2⟩
      have hDl : Dl (fun _ => 1) = (Z b).z • P a := by simp [Dl]
      have hDz : ∀ z, Dl z = (z 0 * (Z b).z) • P a := fun z => by simp [Dl, smul_smul]
      obtain ⟨v₀, hv₀, -⟩ := (FU.ex_diff i P hP).1 ((Z b).z • P a)
      have h3 := GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear hhol Dl (w := fun _ => 1) (v := v₀.left) (by rw [hDl]; exact hv₀)
      have h3' : IsDerivAt0 (fun z : Fin 1 → ℂ => (FU.ex i P ((z 0 * (Z b).z) • P a)).left) (fun _ => 1) v₀.left := by
        have e : (fun z => (FU.ex i P (Dl z)).left) =
            fun z : Fin 1 → ℂ => (FU.ex i P ((z 0 * (Z b).z) • P a)).left := funext fun z => by
          rw [hDz]
        rw [← e]; exact h3
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique h2 h3']
      exact hv₀

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgf

def pureTypeSign (b : Bool) : ℤˣ := if b then 1 else -1

theorem sgnRt_eq_sign_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (b : Bool) :
    sgnRt H b = ((pureTypeSign b : ℤ) : ℂ) * H.rt0 := by
  cases b <;> simp [sgnRt, pureTypeSign]

open GlobalTheory.CM GlobalTheory.PointAlg ReciprocityTheory.GeometryOfNumbersTheory IsDedekindDomain in
set_option maxHeartbeats 1000000 in
theorem family_pure_periods_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P := by
  intro E _ _ _ H D l Xo cc g ty FU i Pe hP nn hnn hfi
  have hC := GlobalTheory.cmCurve_closed
  have hPt := GlobalTheory.cmPoint_closed
  have hT := GlobalTheory.thetaUnifAV_all
  have hL := GlobalTheory.allSixLaws.1
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hcm, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  have := PureType.finiteDimensional_base l
  let k : IntermediateField ℚ ℂ := M ⊔ KA l
  have hk : KA l ≤ k := le_sup_right
  have hfin : FiniteDimensional ℚ k := inferInstance
  let f : 𝓞 M →+* k := (IntermediateField.inclusion (le_sup_left : M ≤ k)).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, π, hg₀, hπ, hL₀⟩ := PureType.exists_baseChange hL.polBaseChange (spMap f) P
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := PureType.exists_baseChange hL.polBaseChange (spMap (algebraMap k ℂ)) P₀
  obtain ⟨v₀, hv₀, -⟩ := PureType.exists_tangent_over f hπ (hv.1 0)
  obtain ⟨u₀, hu⟩ := PureType.exists_isThetaUnif hT PC
  have hLL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (LB.isLB_pull P₀.isLB ψ) (LB.isLB_pull P.isLB _) hLC
      (LBIso.chartPull (chartPullPull P₀.L ψ ψ rfl) (chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀)
  obtain ⟨c, hc0, hc⟩ := hcm PC (ψ ≫ π) ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp_spMap _ _) rfl, hLL.symm⟩ u₀
  rw [hw] at hc
  obtain ⟨R, hR, -, y, t, m, vR, φ, hy, hj, -, -, hφ⟩ := hPt E H D l Xo g ty FU i Pe hP k hk hfin P₀ v₀ (hg₀.trans hg) hv₀
    PC ψ u₀ c (hgC.trans (hg₀.trans hg)) hψ hLC hu hc0 hc (fun _ => ∅) (fun _ => Set.finite_empty) ⊥ Subalgebra.fg_bot
  obtain ⟨-, bo, a₀, ha₀⟩ := periods_span_pure_decomposition E H (FU.Di i) g ty Pe hP nn hnn hfi
  let ε : Fin g → ℤˣ := fun j => pureTypeSign (bo j)
  let a : ∀ j, PureType.lat hP (((ε j : ℤ) : ℂ) * H.rt0) := fun j =>
    ⟨(a₀ j).1, (congrArg (fun ρ => (a₀ j).1 ∈ PureType.lat hP ρ) (sgnRt_eq_sign_mul H (bo j))).mp (a₀ j).2⟩
  have ha : ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ j, s j • Pe (a j) := ha₀
  have hρ : ∀ ρ : R →ₐ[k] ℂ, spMap ρ.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k ℂ) := fun ρ =>
    (spMap_comp_spMap _ _).trans (congrArg _ ρ.comp_algebraMap)
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hA : IsAbelianScheme t.G := by
    have := Xo.univ.proper
    have : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 this
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  have onto := onto_of_onto R.val.toRingHom Subtype.val_injective hA
    (Out.TLinPf.isAb_pullback (spMap (algebraMap k R)) P₀.A P₀.isAb) (fun n => φ (ε n) (a n)) fun y' => by
      obtain ⟨z, hz⟩ := FU.ex_onto i Pe hP (Over.homMk (y'.left ≫ m.φ) (by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w y']
        exact hj))
      obtain ⟨b, rfl⟩ := ha z
      choose x hx using fun n => exists_lift_pt (G := P₀.A) (G' := (Over.pullback (spMap (algebraMap k R))).obj P₀.A) hB.1 (t' := spMap R.val.toRingHom)
        ((u₀.ex fun _ => c * b n).left ≫ ψ) (by
          rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, hρ]
          exact Category.id_comp _)
      refine ⟨x, pt_ext m.cart.1 ?_⟩
      rw [prod_left m.cart hj _ (fun n => FU.ex i Pe (b n • Pe (a n))) fun n =>
        (Category.assoc _ _ _).trans ((hφ (ε n)).2 (a n) (b n) (x n).left (hx n) (Over.w (x n))),
        ← map_sum_eq_prod _ (FU.ex_add i Pe hP), hz]
      rfl
  have hs : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨K₁, hk₁, y₁, h₁, h₂, h₃⟩ := exists_numberField_point_of_countable k R hR (KA l)
    (IntermediateField.inclusion hk).toRingHom Xo.X Xo.s y hy (by
      refine (countable_points_of_onto hT hL E H D l Xo g ty FU PC).mono ?_
      rintro _ ⟨ρ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hy, spMap_comp_spMap]
        exact congrArg spMap (RingHom.ext fun x => ρ.commutes _)
      obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' Xo.univ.t (spMap ρ.toRingHom ≫ y)) := by
        let f := spMap ρ.toRingHom ≫ y
        let t := Xo.univ.t
        have h := isGrpPullback_pullback t.G f
        obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull _ _ t.G _ (cubeMapOf h) t.PP t.cub
        have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
            pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
        have pa : ∀ {T : Over (Sp ℂ)} (x : T ⟶ (Over.pullback f).obj t.G) a,
            pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
          Over.OverMorphism.ext (by
            show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
            rw [Category.assoc, hact, Category.assoc])
        have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
          refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
          · have := t.semi.comm; infer_instance
          · have := t.semi.smooth; change Smooth (pullback.snd t.G.hom f); infer_instance
          · have := t.semi.separated; change IsSeparated (pullback.snd t.G.hom f); infer_instance
          · have := t.semi.quasiCompact; change QuasiCompact (pullback.snd t.G.hom f); infer_instance
          · have := t.semi.geomConnected; change GeometricallyConnected (pullback.snd t.G.hom f); infer_instance
          · intro Ω _ _ q
            obtain ⟨E⟩ := t.semi.fibres Ω (q ≫ f)
            exact ⟨torusExtOfIso (pullCompIso q f t.G) E⟩
        refine ⟨⟨(Over.pullback f).obj t.G, hsemi,
          OAct.pullback f t.G t.act, (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, ?_, ?_⟩,
          ⟨⟨cubeMapOf h, h, rfl, hact, hc'⟩⟩⟩
        · intro a
          let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
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
          refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
      let κ := m.cart.1.lift m'.φ (t'.G.hom ≫ spMap ρ.toRingHom) (by rw [m'.cart.1.w, Category.assoc])
      have hγ : IsGrpPullback t'.G t.G (spMap ρ.toRingHom) κ :=
        m.cart.cancel (m'.cart.congr rfl (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
      let β := hB.1.lift ψ (PC.A.hom ≫ spMap ρ.toRingHom) (by rw [hψ.1.w, Category.assoc, hρ])
      have hβ : IsGrpPullback PC.A _ (spMap ρ.toRingHom) β :=
        hB.cancel (hψ.congr (hρ ρ).symm (hB.1.lift_fst _ _ _).symm) (hB.1.lift_snd _ _ _)
      choose w' hw₁ hw₂ using fun n => @exists_lift_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hγ (φ (ε n) (a n))
        ((hφ (ε n)).1.1 (a n))
      refine ⟨t', m', _, w', hw₁, fun y' => ?_⟩
      obtain ⟨x, hx⟩ := onto_lift hβ.1 hγ _ w' hw₂ (Category.id_comp _) (onto _) y'
      exact ⟨_, id, x, hx⟩)
  exact ⟨K₁, hk.trans hk₁, y₁, h₁, h₂, h₃.trans hj⟩

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.PureTypeLatticesOrthogonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem symplectic_form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h
  linarith

theorem Host_rt0_ne_neg : H.rt0 ≠ -H.rt0 := by
  intro h
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have hs := H.sqrt_neg_disc_sq
  rw [h0] at hs
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  apply hd
  linear_combination hs

theorem pure_type_lattices_orthogonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 := by
  intro E _ _ _ H D g ty P hP a b ha hb
  simp only [sgnRt, if_true, Bool.false_eq_true, if_false] at ha hb
  constructor
  · unfold sesq
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [GlobalTheory.CM.FamCompare.orth_of_pure hP ((PureType.lat hP H.rt0).smul_mem _ ha) hb]
    simp
  · unfold sesq
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [symplectic_form_skew D, GlobalTheory.CM.FamCompare.orth_of_pure hP ha ((PureType.lat hP (-H.rt0)).smul_mem _ hb)]
    simp

theorem pure_family_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ), IsPure hP x → (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧ (∀ y ∈ PureType.lat hP (sgnRt H true), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧ ∀ y ∈ PureType.lat hP (sgnRt H false), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) := by
  intro E _ _ _ H D g ty P hP p q x n hx hn

  have hsplit : ∀ y : D.La, ∃ a ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)),
      ∃ b ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)), n • y = a + b := by
    intro y
    have h := hn y
    have e : Set.range x = Set.range (x ∘ Sum.inl) ∪ Set.range (x ∘ Sum.inr) := by
      ext z; constructor
      · rintro ⟨(i | j), rfl⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨j, rfl⟩
      · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    rw [e, Submodule.span_union, Submodule.mem_sup] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hlatL : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)) ≤ PureType.lat hP (sgnRt H true) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx.1 i)
  have hlatR : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) ≤ PureType.lat hP (sgnRt H false) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hx.2 j)
  have hboth : ∀ z, z ∈ PureType.lat hP (sgnRt H true) → z ∈ PureType.lat hP (sgnRt H false) → z = 0 := by
    intro z h1 h2
    apply hP.2.1
    rw [map_zero]
    funext j
    by_cases hj : ty j (H.rt : E) = H.rt0
    · have : ty j (H.rt : E) ≠ -H.rt0 := by rw [hj]; exact Host_rt0_ne_neg
      exact h2 j (by simpa [sgnRt] using this)
    · exact h1 j (by simpa [sgnRt] using hj)
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    exact ⟨a, hlatL ha, b, hlatR hb, e⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have hb0 : b = 0 := hboth b (by
      have : b = n • y - a := by rw [e]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatL ha)) (hlatR hb)
    rw [e, hb0, add_zero]; exact ha
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have ha0 : a = 0 := hboth a (hlatL ha) (by
      have : a = n • y - b := by rw [e]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatR hb))
    rw [e, ha0, zero_add]; exact hb

end PositivityTheory.Xgf
end

