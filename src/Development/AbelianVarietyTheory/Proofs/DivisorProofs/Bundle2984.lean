module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGenerator
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_int_eq_mul_of_ne_zero {E : Type} [Field E] [NumberField E] (t : 𝓞 E) (ht : t ≠ 0) :
    ∃ (N : ℤ) (c : 𝓞 E), N ≠ 0 ∧ (N : 𝓞 E) = t * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {t}))
  refine ⟨(Ideal.absNorm (Ideal.span {t}) : ℤ), c, ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht
    exact_mod_cast this
  · rw [Int.cast_natCast, ← hc, mul_comm]

theorem eq_zero_of_forall_theta_mul {E : Type} [Field E] [NumberField E] {θ : 𝓞 E →+ ℤ} (hθ : θ ≠ 0)
    {t : 𝓞 E} (h : ∀ u, θ (t * u) = 0) : t = 0 := by
  by_contra ht
  obtain ⟨N, c, hN, hc⟩ := exists_int_eq_mul_of_ne_zero t ht
  apply hθ
  ext v
  have := h (c * v)
  rw [← mul_assoc, ← hc, ← zsmul_eq_mul, map_zsmul, smul_eq_mul] at this
  simpa [hN] using this

theorem exists_linear_theta_factor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  intro E _ _ _ H D Z' θ s hs hgen w
  have hθ : θ ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ (𝓞 E)).repr s i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hs ((Module.Free.chooseBasis ℤ (𝓞 E)).repr.injective (by ext i; simp [hne i]))
    obtain ⟨t, ht⟩ := hgen ((Module.Free.chooseBasis ℤ (𝓞 E)).coord i).toAddMonoidHom
    have := ht 1
    simp [h0] at this
    exact hi this
  have uniq : ∀ t t' : 𝓞 E, (∀ u, θ (t * u) = θ (t' * u)) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_forall_theta_mul hθ fun u => by rw [sub_mul, map_sub, h, sub_self])
  let ψ : D.La → 𝓞 E →+ ℤ := fun x => AddMonoidHom.mk' (fun u => D.EF (u • x) w) (fun a b => by simp [add_smul])
  choose T hT using fun x : Z' => hgen (ψ x)
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun x => ?_⟩
  · intro x y
    apply uniq
    intro u
    rw [← hT (x + y) u, add_mul, map_add (f := _), ← hT x u, ← hT y u]
    simp [ψ, smul_add]
  · intro c x
    show T (c • x) = c * T x
    apply uniq
    intro u
    rw [← hT (c • x) u, show c * T x * u = T x * (c * u) by ring, ← hT x (c * u)]
    simp only [ψ, AddMonoidHom.mk'_apply, Submodule.coe_smul, smul_smul]
    rw [show s * u * c = s * (c * u) by ring]
  · show θ (T x) = _
    have := hT x 1
    rw [mul_one, mul_one] at this
    rw [← this]
    simp only [ψ, AddMonoidHom.mk'_apply]
    exact D.adj s x w

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocalPull


set_option maxHeartbeats 3200000 in
theorem exists_pelUnif_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  intro E _ _ _ H R V _ _ _ _ _ _ hR hV t P θ hθ f hf hψ
  letI := H.starRing
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have aV := hV.1
  have hI : (maximalIdeal R).map θ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff θ a).2 ha
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (spMap θ) t
  let t' : SAB H (Sp V) := ⟨(Over.pullback (spMap θ)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (spMap θ) := m₁
  have hm₀ : m₀.φ = pullback.fst t.G.hom (spMap θ) := hm₁
  let W : (Sp R).Opens := PrimeSpectrum.basicOpen f
  have hψW : ∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R)) := hψ
  have hgen : (specOf θ).base (genericPoint (Sp V)) ∈ W := by
    rw [genericPoint_eq_bot_of_affine]
    show f ∉ Ideal.comap θ ⊥
    rw [Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  let x : Sp (FractionRing V) ⟶ Sp R := jK V ≫ specOf θ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK V).base z = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V (FractionRing V)) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
    show (specOf θ).base ((jK V).base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR P.D P.A t.G t.semi P.U W hψW (FractionRing V) x hxW
  obtain ⟨PK, cubK, symK, adjK, primK, mK, hmK⟩ := sabPull CubePf.cubePull x t
  let tK : SAB H (Sp (FractionRing V)) := ⟨(Over.pullback x).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PK, cubK, symK, adjK, primK⟩
  have hLK : LBIso tK.PP.L (P.U.LG.L.pull (pullback.fst t.G.hom x)) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    rw [P.bundle, ← hmK]
    exact ⟨wK, gK⟩
  have hMK : (P.U.LG.L.pull (pullback.fst t.G.hom x)).IsLB := pull_isLB P.U.LG.isLB _
  have hp : IsProper tK.G.hom := GlobalTheory.ZH.isProper_hom_of_relAmple hamp
  haveI := hp
  have hA : RelAmple tK.G tK.PP.L :=
    GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) hMK tK.PP.isLB
      (hLK.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl)) hamp
  have hK : KTriv tK.G tK.PP.L := GlobalTheory.MulDescent.kTriv_of_lbIso hMK tK.PP.isLB hLK.symm hkt

  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have dA : d = P.A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    P.A.smoothDim (eSec P.A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hpbG := isGrpPullback_pullback t.G x
  have hdB : SmoothOfRelativeDimension P.A.g tK.G.hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing V)) := GlobalTheory.GenericPol.toPolAV tK P.A.g hdB hp hA hK
  let oA' : A'.OAct (𝓞 E) := ⟨tK.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj tK⟩
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  have hbc : IsGrpPullback t'.G t.G (specOf θ) ((Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ)) :=
    ((isGrpPullback_of_iso (Iso.refl t'.G)).comp (isGrpPullback_pullback t.G (specOf θ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback t'.G (jK V)).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (P.U.LG.L.pull (pullback.fst t'.G.hom (jK V) ≫ (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))),
      wA.IsGen := by
    rw [← heA]
    exact LBIso.trans (pull_isLB tK.PP.isLB _) (pull_isLB hMK _) (pull_isLB P.U.LG.isLB _)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hLK _) ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen P.U.LG.isLB _ _⟩

  have hbc' : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (spMap θ) :=
    Category.id_comp _
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr P.bundle m₀.cm m₀.lin (hbc'.trans hm₀.symm) (e := specOf θ) m₀.base.symm
  have hψn := GlobalTheory.PelCoordPull.nonempty_psiOn P.D.toPre W ⟨_, hgen⟩ hψW
  have extA₀ : ∀ a, (Over.pullback (jK V)).map (t'.act.act a) ≫ eA.hom =
      eA.hom ≫ (OAct.pullback x t.G t.act).act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpbG.1.hom_ext
    · have a₁ : ((Over.pullback (jK V)).map (t'.act.act a)).left ≫ pullback.fst t'.G.hom (jK V) =
          pullback.fst t'.G.hom (jK V) ≫ (t'.act.act a).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act a).left ≫ pullback.fst t.G.hom (specOf θ) =
          pullback.fst t.G.hom (specOf θ) ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have a₃ : ((OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
          pullback.fst t.G.hom x ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have i₀ : (Iso.refl t'.G).hom.left = 𝟙 _ := rfl
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₃, heA, ← Category.assoc eA.hom.left, heA,
        i₀, Category.id_comp, reassoc_of% a₁, a₂, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := h4.unifBaseChange R V _ _ aR aV θ hI P.D P.A t.G t.semi P.U W hψn hgen
    t'.G (Iso.refl _) mR A' rfl eA meA wA t'.PP wL heL gL rL
  have extA : ∀ a, (Over.pullback (jK V)).map (t'.act.toRingAct.act a) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act a := by
    intro a
    rw [hgenU]
    exact extA₀ a
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R V _ _ aR aV θ P.D P.A t.G P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct
    (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      mod := mod'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := hLG
      lin := lin'
      w0 := w0' H.w0 P.w0 }
  exact ⟨t', P', hD, ⟨m₀⟩, xl, el⟩

end GlobalTheory.LocalPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationBlowupPullbackFiniteCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

theorem exists_normalisation_pullback_cover : ∀ {o : CommRingCat.{0}} [Algebra.FiniteType ℤ o] {Z Z' M : Scheme.{0}} (z : Z ⟶ Spec o) [LocallyOfFiniteType z] (b : Z' ⟶ Z) [IsProper b] (J : Z.IdealSheafData), FinalTheorems.Blowup b J → ∀ [IsIntegral M] [GlobalTheory.IsNormalScheme M] (U : Z.Opens) (g' : M ⟶ U.toScheme) [IsFinite g'], (∃ m, (g' ≫ U.ι) m ∉ J.support) → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (ν₁ : S₁ ⟶ (b ⁻¹ᵁ U).toScheme), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsFinite ν₁ ∧ ν₁ ≫ (b ∣_ U) = p₁ ≫ g' ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g' ≫ U.ι)) ∧ (∀ m, (g' ≫ U.ι) m ∉ J.support → m ∈ Set.range p₁) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (a : Sp R ⟶ (b ⁻¹ᵁ U).toScheme) (β : Sp R ⟶ M), a ≫ (b ∣_ U) = β ≫ g' → (∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support) → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν₁ = a ∧ ξ₁ ≫ p₁ = β := by
  intro o _ Z Z' M z _ b _ J hB _ _ U g' _ hne
  haveI : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ o
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  haveI : LocallyOfFiniteType (g' ≫ U.ι ≫ z) := inferInstance
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian (g' ≫ U.ι ≫ z)
  let Vi : Z.Opens := J.support.compl
  haveI hbV : IsIso (b ∣_ Vi) := GlobalTheory.Principalise.isIso_restrict_of_blowup hB Vi (fun x hx => hx)
  have monoV : ∀ {T : Scheme.{0}} (u v : T ⟶ Z'), u ≫ b = v ≫ b → Set.range (u ≫ b) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    have hu : Set.range u ⊆ ((b ⁻¹ᵁ Vi : Z'.Opens) : Set Z') := by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨w, rfl⟩
    have hv : Set.range v ⊆ ((b ⁻¹ᵁ Vi : Z'.Opens) : Set Z') := by
      rintro _ ⟨w, rfl⟩
      have := hr ⟨w, rfl⟩
      rw [huv] at this
      exact this
    have hm : Mono ((b ⁻¹ᵁ Vi).ι ≫ b) := by
      rw [← morphismRestrict_ι]; infer_instance
    rw [← Scheme.Opens.range_ι] at hu hv
    rw [← IsOpenImmersion.lift_fac _ u hu, ← IsOpenImmersion.lift_fac _ v hv]
    congr 1
    rw [← cancel_mono ((b ⁻¹ᵁ Vi).ι ≫ b)]
    simp only [← Category.assoc, IsOpenImmersion.lift_fac]
    exact huv
  let bU := b ∣_ U
  have hbU : bU ≫ U.ι = (b ⁻¹ᵁ U).ι ≫ b := morphismRestrict_ι _ _
  have monoU : ∀ {T : Scheme.{0}} (u v : T ⟶ (b ⁻¹ᵁ U).toScheme), u ≫ bU = v ≫ bU →
      Set.range (u ≫ bU ≫ U.ι) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    rw [← cancel_mono (b ⁻¹ᵁ U).ι]
    apply monoV
    · rw [Category.assoc, Category.assoc, ← hbU, ← Category.assoc, huv, Category.assoc]
    · rw [Category.assoc, ← hbU]; exact hr
  let V : M.Opens := (g' ≫ U.ι) ⁻¹ᵁ Vi
  obtain ⟨m₀, hm₀⟩ := hne
  haveI : Nonempty V := ⟨⟨m₀, hm₀⟩⟩
  let c₀ : (V : Scheme.{0}) ⟶ Z' := (g' ≫ U.ι) ∣_ Vi ≫ inv (b ∣_ Vi) ≫ (b ⁻¹ᵁ Vi).ι
  have hc₀ : c₀ ≫ b = V.ι ≫ g' ≫ U.ι := by
    simp only [c₀, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  have hr₀ : Set.range c₀ ⊆ Set.range (b ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show b (c₀ x) ∈ U
    rw [← Scheme.Hom.comp_apply, hc₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (g' (V.ι x)).2
  let c : (V : Scheme.{0}) ⟶ (b ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι c₀ hr₀
  have hcι : c ≫ (b ⁻¹ᵁ U).ι = c₀ := IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ bU = V.ι ≫ g' := by
    rw [← cancel_mono U.ι, Category.assoc, hbU, ← Category.assoc, hcι, hc₀, Category.assoc]
  let j : (V : Scheme.{0}) ⟶ pullback bU g' := pullback.lift c V.ι hc
  have hjs : j ≫ pullback.snd bU g' = V.ι := pullback.lift_snd _ _ _
  have hjf : j ≫ pullback.fst bU g' = c := pullback.lift_fst _ _ _
  haveI : IsProper bU := by dsimp only [bU]; infer_instance
  haveI : QuasiCompact (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance
  haveI : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd bU g')
  haveI : QuasiSeparated (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance
  haveI : QuasiSeparated j := QuasiSeparated.of_comp j (pullback.snd bU g')
  haveI : LocallyOfFiniteType (j ≫ pullback.snd bU g') := by rw [hjs]; infer_instance
  haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd bU g')
  haveI : GlobalTheory.IsNormalScheme (V : Scheme.{0}) := .of_isOpenImmersion V.ι
  haveI : IsReduced (V : Scheme.{0}) := inferInstance
  haveI : IsLocallyNoetherian (V : Scheme.{0}) := inferInstance
  haveI hfin : IsFinite j.fromNormalization :=
    GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := o) j
      (pullback.fst bU g' ≫ bU ≫ U.ι ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap j x).residueFieldMap
  let p₁ : j.normalization ⟶ M := j.fromNormalization ≫ pullback.snd bU g'
  let ν₁ : j.normalization ⟶ (b ⁻¹ᵁ U).toScheme := j.fromNormalization ≫ pullback.fst bU g'
  have hp₁ : j.toNormalization ≫ p₁ = V.ι := by
    show j.toNormalization ≫ j.fromNormalization ≫ pullback.snd bU g' = V.ι
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, hjs]
  have hcomm : ν₁ ≫ bU = p₁ ≫ g' := by simp [ν₁, p₁, pullback.condition]
  refine ⟨j.normalization, inferInstance, p₁, ν₁, GlobalTheory.IsNormalScheme.pred _, ?_, ?_, hcomm, ?_, ?_, ?_⟩
  · show IsProper (j.fromNormalization ≫ pullback.snd bU g')
    infer_instance
  · show IsFinite (j.fromNormalization ≫ pullback.fst bU g')
    infer_instance
  · obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hB.1
    have hpe : p₁ ≫ g' ≫ U.ι = (ν₁ ≫ (b ⁻¹ᵁ U).ι) ≫ b := by
      rw [← Category.assoc, ← hcomm, Category.assoc, hbU]; simp only [Category.assoc]
    have hK : D.KeepsRegular (ν₁ ≫ (b ⁻¹ᵁ U).ι) := by
      refine D.keepsRegular_of_dense _ (fun y => inferInstance) ((j.toNormalization.denseRange).mono ?_)
      rintro _ ⟨x, rfl⟩
      show (ν₁ ≫ (b ⁻¹ᵁ U).ι) (j.toNormalization x) ∉ D.idealSheaf.support
      rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
      intro h
      apply x.2
      have : j.toNormalization ≫ (ν₁ ≫ (b ⁻¹ᵁ U).ι) ≫ b = V.ι ≫ g' ≫ U.ι := by
        rw [← hpe, ← Category.assoc, hp₁]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this] at h
      exact h
    have e : J.comap (p₁ ≫ g' ≫ U.ι) = (D.pull (ν₁ ≫ (b ⁻¹ᵁ U).ι) hK).idealSheaf := by
      rw [GlobalTheory.EffCartierData.idealSheaf_pull, hD, hpe, Scheme.IdealSheafData.comap_comp]
    rw [e]
    exact GlobalTheory.EffCartierData.effCartier_idealSheaf _
  · intro m hm
    refine ⟨j.toNormalization ⟨m, hm⟩, ?_⟩
    show (j.toNormalization ≫ p₁) ⟨m, hm⟩ = m
    rw [hp₁]
    rfl
  · intro R _ _ _ a β hab hgen
    let d : Sp R ⟶ pullback bU g' := pullback.lift a β hab
    have hr : Set.range (jK R ≫ β) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show (g' ≫ U.ι) ((jK R ≫ β) w) ∉ J.support
      rw [← Scheme.Hom.comp_apply]
      simpa only [Category.assoc] using hgen w
    let y := IsOpenImmersion.lift V.ι (jK R ≫ β) hr
    have hy : y ≫ V.ι = jK R ≫ β := IsOpenImmersion.lift_fac _ _ _
    have hyj : y ≫ j = jK R ≫ d := by
      apply pullback.hom_ext
      · rw [Category.assoc, hjf, Category.assoc, pullback.lift_fst]
        apply monoU
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc, Category.assoc, hab]
        · have key : y ≫ c ≫ bU ≫ U.ι = jK R ≫ β ≫ g' ≫ U.ι := by
            rw [reassoc_of% hc, ← Category.assoc y, hy, Category.assoc]
          rw [Category.assoc, key]
          rintro _ ⟨w, rfl⟩
          exact hgen w
      · rw [Category.assoc, hjs, Category.assoc, pullback.lift_snd, hy]
    obtain ⟨ξ, ⟨-, hξ⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := FractionRing R)
      (nonZeroDivisors R) le_rfl j.fromNormalization (y ≫ j.toNormalization) d
      (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hyj])
    refine ⟨ξ, ?_, ?_⟩
    · show ξ ≫ j.fromNormalization ≫ pullback.fst bU g' = a
      rw [← Category.assoc, hξ, pullback.lift_fst]
    · show ξ ≫ j.fromNormalization ≫ pullback.snd bU g' = β
      rw [← Category.assoc, hξ, pullback.lift_snd]

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNat
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.sep_one_mod_maximal_mem_others : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  intro E _ _ n hn 𝔭 h𝔭
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI0 : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  set S := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(n : 𝓞 E)})).toFinset.erase 𝔭
    with hS
  have htop : 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 = ⊤ := by
    refine Ideal.sup_prod_eq_top fun 𝔮 h𝔮 => ?_
    rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0] at h𝔮
    obtain ⟨hne, hpr, hle⟩ := h𝔮
    have hbot : 𝔮 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.span_le, Set.singleton_subset_iff] at hle
      exact hn0 hle
    have hmax : 𝔮.IsMaximal := hpr.isMaximal hbot
    by_contra hc
    have e1 : 𝔭 = 𝔭 ⊔ 𝔮 := h𝔭.eq_of_le hc le_sup_left
    have h2 : 𝔮 ≤ 𝔭 := e1 ▸ le_sup_right
    exact hne (hmax.eq_of_le h𝔭.ne_top h2)
  have h1 : (1 : 𝓞 E) ∈ 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp h1
  refine ⟨e, ?_, fun 𝔮 hmax hn𝔮 hne => ?_⟩
  · have : e - 1 = -p := by rw [← hpe]; ring
    rw [this]; exact 𝔭.neg_mem hp
  · have hmem : 𝔮 ∈ S := by
      rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0]
      exact ⟨hne, hmax.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hn𝔮⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le hmem) he
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfOrthogo
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨θ, hθ⟩ := exists_theta_vec D m
  obtain ⟨ζ, hζZ, -, hζs, hopp⟩ := h.exists_rank_one hm θ hθ
  have himg' : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg'' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ (Z'.subtype + ℓ.smulRight (m + ζ ℓ)) = y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ)) := by
      ext x; simp
    rw [img, ← LinearMap.range_comp, this]
  have he𝔭 : e ∉ 𝔭 := fun h' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' he1))
  have hℓv : (e • ℓ₀) v ∉ 𝔭 := by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact fun h' => (h𝔭.isPrime.mem_or_mem h').elim he𝔭 hℓ₀
  have hker := range_le_of_ker (y ∘ₗ Z'.subtype) (e • ℓ₀) (y (m + ζ (e • ℓ₀))) 𝔭 h𝔭 (v := v) hv hℓv
  refine ⟨_, hopp (e • ℓ₀), fun 𝔮 h𝔮 hn𝔮 => ?_, ?_⟩
  · rw [himg', himg'']
    by_cases hq : 𝔮 = 𝔭
    · subst hq; exact hker.2
    · exact range_le_of_mem _ _ _ 𝔮 fun x => by
        rw [LinearMap.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · rw [himg'']
    intro hle
    have hu' := hle hker.1
    have hz : y (ζ (e • ℓ₀)) ∈ img D y Z' 𝔭 := by
      rcases hA with hA | hA
      · haveI := h𝔭
        have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
        have hn' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
        have he' := he _ h𝔭' hn' hA
        rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at he'
        have hbe : H.bar e ∈ 𝔭 := by
          have : H.bar.symm e = H.bar e := by rw [RingEquiv.symm_apply_eq, bar_bar]
          rwa [this] at he'
        rw [hζs, map_smul]
        exact Submodule.mem_sup_right (Submodule.smul_mem_smul hbe trivial)
      · exact hA (Submodule.mem_map_of_mem (hζZ _))
    apply hym
    have : y m = y (m + ζ (e • ℓ₀)) - y (ζ (e • ℓ₀)) := by simp
    rw [this]
    exact sub_mem hu' hz

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBijectiveOnTorsionCoprimeDegreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_bijective_on_torsion_coprime_degree : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (la : A ⟶ B) (mu : B ⟶ A) (d M : ℕ) (T : Over S), IsMonHom la → IsMonHom mu → la ≫ mu = 𝟙 A ^ d → mu ≫ la = 𝟙 B ^ d → M.Coprime d → (∀ y : T ⟶ A, y ^ M = 1 → y ≫ la = 1 → y = 1) ∧ (∀ g : T ⟶ B, g ^ M = 1 → ∃ y : T ⟶ A, y ^ M = 1 ∧ y ≫ la = g) := by
  first | (exact @GlobalTheory.isogeny_torsion_bij) | (exact GlobalTheory.isogeny_torsion_bij) | (intros; apply GlobalTheory.isogeny_torsion_bij <;> assumption)
end

