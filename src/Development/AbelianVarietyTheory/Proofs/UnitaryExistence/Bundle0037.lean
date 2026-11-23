module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

theorem exists_int_basis_of_fg {V : Type} [AddCommGroup V] [Module ℚ V] (Z : Submodule ℤ V)
    (hZ : Z.FG) {n : ℕ} (hn : Module.finrank ℚ (Submodule.span ℚ (Z : Set V)) = n) :
    ∃ bs : Fin n → V, LinearIndependent ℤ bs ∧ Submodule.span ℤ (Set.range bs) = Z := by
  haveI : Module.Finite ℤ Z := Module.Finite.iff_fg.2 hZ
  haveI : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
  haveI : Module.Free ℤ Z := inferInstance
  let b := Module.finBasis ℤ Z
  have hli : LinearIndependent ℤ (Z.subtype ∘ b) :=
    b.linearIndependent.map' Z.subtype Z.ker_subtype
  have hsp : Submodule.span ℤ (Set.range (Z.subtype ∘ b)) = Z := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hq : LinearIndependent ℚ (Z.subtype ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have h1 := finrank_span_eq_card hq
  have h2 : Submodule.span ℚ (Set.range (Z.subtype ∘ b)) = Submodule.span ℚ (Z : Set V) := by
    conv_rhs => rw [← hsp]
    rw [Submodule.span_span_of_tower]
  rw [h2, hn, Fintype.card_fin] at h1
  subst h1
  exact ⟨_, hli, hsp⟩

theorem latZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (Comp : Type) (X : Comp → Data E r), FJ.LatZ X ρ := by
  intro E _ _ _ r ρ Comp X cu
  obtain ⟨c, cu⟩ := cu
  have hZ : (Submodule.span ℤ (FJ.zGam (X c) cu) : Set (Matrix (Fin ρ) (Fin ρ) E)) =
      FJ.zGam (X c) cu := by
    have := Submodule.span_eq (AddSubgroup.toIntSubmodule (zGamSub (X c) cu))
    exact congrArg (fun S : Submodule ℤ (Matrix (Fin ρ) (Fin ρ) E) =>
      (S : Set (Matrix (Fin ρ) (Fin ρ) E))) this
  have hdim := _root_.GlobalTheory.finrank_skewHermitian_eq E ρ (X c).Ψ (X c).cmType
    (Submodule.span ℚ (Submodule.span ℤ (FJ.zGam (X c) cu) : Set (Matrix (Fin ρ) (Fin ρ) E))) (by
      rw [hZ]
      intro β
      constructor
      · intro h
        induction h using Submodule.span_induction with
        | mem x hx => exact hx.1
        | zero => intro a b; simp [cc_zero']
        | add x y _ _ hx hy =>
          intro a b
          rw [Matrix.add_apply, Matrix.add_apply, cc_add', hx, hy]; ring
        | smul q x _ hx =>
          intro a b
          have hq : cc (q : E) = q := by simp [cc]
          rw [Matrix.smul_apply, Matrix.smul_apply, Rat.smul_def, Rat.smul_def, cc_mul', hq, hx]
          ring
      · intro h
        obtain ⟨n, hn, hm⟩ := _root_.GlobalTheory.CuspCentre.exists_nsmul_mem_zGam E r ρ (X c) cu β h
        have h1 := Submodule.smul_mem (Submodule.span ℚ (FJ.zGam (X c) cu)) ((n : ℚ)⁻¹)
          (Submodule.subset_span hm)
        rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
          one_smul] at h1)
  obtain ⟨bs, h1, h2⟩ := exists_int_basis_of_fg _ (_root_.GlobalTheory.CuspCentre.span_zGam_fg E r ρ (X c) cu) hdim
  refine ⟨bs, h1, fun β => ?_⟩
  exact ((Set.ext_iff.1 hZ β).symm).trans (SetLike.ext_iff.1 h2 β).symm

end GlobalTheory.CuspCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAway
section
noncomputable section

namespace GlobalTheory.Frames.SecLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem appLE_bijective {Y Z : Scheme.{0}} (π : Z ⟶ Y) [IsOpenImmersion π] {V : Y.Opens} (hV : V ≤ π.opensRange)
    {V' : Z.Opens} (h : V' ≤ π ⁻¹ᵁ V) (h' : π ⁻¹ᵁ V ≤ V') : Function.Bijective (π.appLE V V' h).hom := by
  obtain rfl : V' = π ⁻¹ᵁ V := le_antisymm h h'
  rw [← Scheme.Hom.app_eq_appLE]
  haveI := π.isIso_app V hV
  exact ConcreteCategory.bijective_of_isIso (π.app V)

theorem exists_pow_mul_eq {Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {M : LB Y} (hM : M.IsLB)
    (U' : M.ι → Z.Opens) (h : ∀ i, U' i ≤ π ⁻¹ᵁ M.U i) (h' : ∀ i, π ⁻¹ᵁ M.U i ≤ U' i) (f : ∀ i, Γ(Z, U' i))
    (hf : ∀ i j, resG Z (inf_le_left : U' i ⊓ U' j ≤ U' i) (f i) =
      (π.appLE (M.U i ⊓ M.U j) (U' i ⊓ U' j) (inf_le_inf (h i) (h j))).hom (M.g i j).val *
        resG Z (inf_le_right : U' i ⊓ U' j ≤ U' j) (f j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ i, (π.appLE _ _ (h i)).hom (s.f i) =
      (π.appLE ⊤ (U' i) le_top).hom a ^ N * f i := by
  have k : ∀ i, U' i ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i) := fun i z hz => ⟨⟨z, rfl⟩, h i hz⟩
  have hb : ∀ i, Function.Bijective (π.appLE _ _ (k i)).hom := fun i =>
    appLE_bijective π inf_le_left (k i) (fun z hz => h' i hz.2)
  choose t ht using fun i => (hb i).2 (f i)
  have hmem : t ∈ secOn M π.opensRange := fun i j => by
    have k₂ : U' i ⊓ U' j ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i ⊓ M.U j) := fun z hz => ⟨k i hz.1, h j hz.2⟩
    apply (appLE_bijective π (inf_le_left.trans inf_le_left) k₂
      (fun z hz => ⟨h' i hz.1.2, h' j hz.2⟩)).1
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    have := hf i j
    rw [← ht i, ← ht j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    exact this
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  obtain ⟨N, u, hu⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M)
    (U := ⊤) isCompact_univ isQuasiSeparated_univ a le_top ha (GlobalTheory.LB.mkSec t hmem)
  let s : LB.Sec M := ⟨fun i => resG Y (le_inf le_top le_rfl) (GlobalTheory.LB.coord u i), fun i j => by
    change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG, GlobalTheory.LB.coord_rel u i j _ _ le_rfl, GlobalTheory.LB.resG_self]⟩
  refine ⟨N, s, fun i => ?_⟩
  have e : resG Y inf_le_left (resG Y le_top a ^ N) * t i =
      resG Y (inf_le_inf_right _ le_top) (GlobalTheory.LB.coord u i) := congrArg (fun w => GlobalTheory.LB.coord w i) hu
  have e₂ := congrArg (π.appLE _ _ (k i)).hom e
  rw [map_mul, ht, map_pow, map_pow, GlobalTheory.LB.resG_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG] at e₂
  exact (GlobalTheory.LB.appLE_resG _ _ _ _).trans e₂.symm

theorem exists_pow_mul_eq_linComb {X Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (e : (fun k => π ≫ φ k) = φ')
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ (N : ℕ) (s : LB.Sec (LB.LinComb L φ ε)), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ π ⁻¹ᵁ (LB.LinComb L φ ε).U j), (π.appLE _ _ hle).hom (s.f j) =
        (π.appLE ⊤ _ le_top).hom a ^ N * s'.f j := by
  subst e
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq π a ha (M := LB.LinComb L φ ε) (LB.isLB_linComb hL φ ε)
    (LB.LinComb L (fun k => π ≫ φ k) ε).U
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) s'.f (fun i j => by
      refine (s'.compat i j).trans (congrArg (· * _) ?_)
      exact congrArg Units.val (DVR.linComb_g_comp φ ε π i j))
  exact ⟨N, s, fun j _ => hs j⟩

theorem opensRange_of_isPullback {S : Type} [CommRing S] (g : S) {Y Z : Scheme.{0}} {π : Z ⟶ Y} {p : Y ⟶ Sp S}
    {p' : Z ⟶ Sp (Localization.Away g)} (h : IsPullback π p' p (spMap (algebraMap S (Localization.Away g))))
    [IsOpenImmersion π] : π.opensRange = Y.basicOpen (p.appTop.hom (toΓ S g)) := by
  have e : Y.basicOpen (p.appTop.hom (toΓ S g)) = p ⁻¹ᵁ PrimeSpectrum.basicOpen g :=
    (Scheme.preimage_basicOpen_top p _).symm.trans (congrArg (p ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := .of S) g))
  rw [e]
  ext y
  have r : Set.range (spMap (algebraMap S (Localization.Away g))) = (PrimeSpectrum.basicOpen g).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have r' := Scheme.Pullback.range_fst p (spMap (algebraMap S (Localization.Away g)))
  rw [r] at r'
  constructor
  · rintro ⟨z, rfl⟩
    have : π z ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) :=
      ⟨h.isoPullback.hom z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
    rw [r'] at this
    exact this
  · intro hy
    have : y ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) := by
      rw [r']; exact hy
    obtain ⟨w, rfl⟩ := this
    exact ⟨h.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem appLE_const {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {Y Z : Scheme.{0}} {π : Z ⟶ Y}
    {p : Y ⟶ Sp S} {p' : Z ⟶ Sp T} (w : π ≫ p = p' ≫ spMap φ) (U : Z.Opens) (a : S) :
    (π.appLE ⊤ U le_top).hom (p.appTop.hom (toΓ S a)) = resG Z le_top (p'.appTop.hom (toΓ T (φ a))) := by
  have e₁ : π.appTop.hom (p.appTop.hom (toΓ S a)) = p'.appTop.hom ((spMap φ).appTop.hom (toΓ S a)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, w]
  have e₂ : (spMap φ).appTop.hom (toΓ S a) = toΓ T (φ a) :=
    (congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e₂, ← e₁]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip

theorem isPullback_gxMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) :
    IsPullback (SecPull.gxMap φ x _ rfl) (fst (Over.mk (spMap φ ≫ x)) Xo.univ.t.G).left
      (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) :=
  IsPullback.of_right (by
    convert isPullback_gx (spMap φ ≫ x) using 1
    exact SecPull.gxMap_snd φ x _ rfl) (SecPull.gxMap_fst φ x _ rfl)
    (isPullback_gx x)

theorem exists_secBC_pow_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  intro E _ _ _ H Dw l Xo S _ x g s'
  have hP := isPullback_gxMap (algebraMap S (Localization.Away g)) x
  have hpr : IsProper (fst (Over.mk x) Xo.univ.t.G).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (isPullback_gx x) Xo.univ.proper
  have : CompactSpace (Over.mk x).left := inferInstanceAs (CompactSpace (Sp S))
  have : QuasiSeparatedSpace (Over.mk x).left := inferInstanceAs (QuasiSeparatedSpace (Sp S))
  have : CompactSpace (Gx x) :=
    QuasiCompact.compactSpace_of_compactSpace (fst (Over.mk x) Xo.univ.t.G).left
  have : QuasiSeparatedSpace (Gx x) :=
    quasiSeparatedSpace_of_quasiSeparated (fst (Over.mk x) Xo.univ.t.G).left
  have hoi : IsOpenImmersion (spMap (algebraMap S (Localization.Away g))) :=
    IsOpenImmersion.of_isLocalization g
  have : IsOpenImmersion (SecPull.gxMap (algebraMap S (Localization.Away g)) x _ rfl) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hoi
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq_linComb _ _ (opensRange_of_isPullback g hP) Xo.univ.t.PP.isLB
    (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap (algebraMap S (Localization.Away g)) ≫ x)) Xo.univ.t.G).left) (fun _ => 1)
    (funext fun _ => SecPull.gxMap_snd _ x _ rfl) s'
  refine ⟨N, s, SecPull.scalSec _ (algebraMap S (Localization.Away g) g ^ N) s',
    ⟨_, SecPull.gxMap_snd _ x _ rfl, SecPull.gxMap_fst _ x _ rfl, fun i h => ?_⟩, fun _ => rfl⟩
  have e₁ : scal x 1 i = 1 := by simp only [scal, Out.liftFun, map_one]
  rw [e₁, _root_.one_mul]
  refine (hs i h).trans (congrArg (· * s'.f i) ?_)
  rw [appLE_const _ hP.w]
  simp only [scal, Out.liftFun, map_pow]
  rfl

end GlobalTheory.Frames.SecLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriods
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem exists_framePeriods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hg hb hn k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hξ, hpos, hφ⟩ := _root_.GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hg hb hn k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hφa : ∀ a, φ a = (M.φ k a : Fin r → E) := fun a => rfl
  obtain ⟨-, hφ'⟩ := hφ φ hφa
  have hemb : ∀ (τ : E →+* ℂ) (v w : Fin r → E), Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := by
    intro τ v w
    funext a
    simp [Data.emb]
  let Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ)) := fun x =>
    AddMonoidHom.mk' (fun a j => perFr (M.X k) x (φ a) (relab c σ (e j).1) (e j).2) (by
      intro a b
      funext j
      simp only [Pi.add_apply, hper, map_add (f := _), hemb]
      split_ifs
      · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      · rw [Matrix.mulVec_add, Pi.add_apply])
  have hPf : IsPerFr e F M k Pf := fun x a j => rfl
  have hPf' : ∀ x v j, Pf x v j = if ((idx j).2 : ℕ) < (F.Di k).q then
      hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ v))
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ v)) (idx j).2 :=
    fun x v j => (hPf x v j).trans (hper x _ j)
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by rw [← hp0]
  obtain ⟨h1, h2⟩ := GlobalTheory.periods_eq_frame_periods E H Dw l Xo _ g _ F k r _ (M.X k).Gm φ (M.X k).Ψ idx Pf
    (hb.type k).2 hty hξ hpos hφ' hr hPf'
  have h3 := (GlobalTheory.per_move E H (F.Di k) r _ (M.X k).Gm φ (M.X k).Ψ (hb.type k).2 g idx _ hty hξ hpos hφ').1
    Pf hPf'
  rw [hdom]
  refine ⟨Pf, hPf, fun Pf' h' => ?_, fun x hx => (h1 x hx).1, h3, h2⟩
  funext x
  exact AddMonoidHom.ext fun a => funext fun j => (h' x a j).trans (hPf x a j).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfIsReducedOfRangeSubset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by
  haveI : Surjective (pullback.snd i a) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)
  exact ⟨inv (pullback.snd i a) ≫ pullback.fst i a, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem natCast_ne_zero_of_isUnit_of_fieldPoint {S : Scheme.{0}} {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ S) : (n : Ω) ≠ 0 := by
  have h := hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)
  rw [map_natCast] at h
  exact h.ne_zero

theorem finite_geometric_kernel_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (S : Scheme.{0}) (G G' Ga : Over S) [GrpObj G] [GrpObj G'] [GrpObj Ga] (io : Ga ⟶ G ⊗ G') (n : ℕ), IsSemiAbelian G' → IsMonHom io → IsClosedImmersion io.left → n.Prime → IsUnit (n : Γ(S, ⊤)) → (∀ (Y : Over S) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ io ≫ fst G G' = 1 → x = 1) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G G' = 1} := by
  intro hab S G G' Ga _ _ _ io n hG' hio hcl hp hn htors Ω _ _ t
  suffices H : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ Ga //
      x ≫ io ≫ fst G G' = 1} by
    have e : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
    rwa [e] at H
  haveI := hG'.comm
  haveI := hG'.smooth
  haveI := hG'.quasiCompact
  have h := isGrpPullback_pullback G' t
  let T : Over S := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t)
  let ρ : (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G') →* (T ⟶ G') := pushHom h _
  have hρ : ∀ y, (ρ y).left = y.left ≫ pullback.fst G'.hom t := fun y => rfl
  have hinj : Function.Injective ρ := fun y z hyz => by
    ext1
    refine pullback.hom_ext ?_ ((Over.w y).trans (Over.w z).symm)
    rw [← hρ, ← hρ, hyz]
  have hsurj : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (pullback.lift x.left (𝟙_ (Over (Sp Ω))).hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  let s : G' ⟶ G ⊗ G' := lift 1 (𝟙 G')
  have hs₁ : ∀ y : T ⟶ G', (y ≫ s) ≫ fst G G' = 1 := fun y => by
    rw [Category.assoc, lift_fst, MonObj.comp_one]
  have hs₂ : ∀ y : T ⟶ G', (y ≫ s) ≫ snd G G' = y := fun y => by
    rw [Category.assoc, lift_snd, Category.comp_id]
  let σ : (T ⟶ G') →* (T ⟶ G ⊗ G') := MonoidHom.mk' (fun y => y ≫ s) fun y z => by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]
    · rw [hs₂, MonObj.mul_comp, hs₂, hs₂]
  let κ : (T ⟶ Ga) →* (T ⟶ G ⊗ G') :=
    MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io
  haveI : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hκ : Function.Injective κ := fun x y hxy => (cancel_mono io).1 hxy
  let C := κ.range.comap (σ.comp ρ)
  have hC : Finite C := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one hab Ω ((Over.pullback t).obj G') n
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd G'.hom t)))
      (inferInstanceAs (QuasiCompact (pullback.snd G'.hom t))) (hG'.fibres Ω t) hp
      (natCast_ne_zero_of_isUnit_of_fieldPoint hn Ω t) C
      ((pullback.fst G'.hom t ≫ s.left) ⁻¹' Set.range io.left)
      (io.left.isClosedEmbedding.isClosed_range.preimage
        (pullback.fst G'.hom t ≫ s.left).continuous) (fun y => ⟨?_, fun hy => ?_⟩) ?_
    · rintro ⟨x, hx⟩ _ ⟨p, rfl⟩
      have e : x.left ≫ io.left = y.left ≫ pullback.fst G'.hom t ≫ s.left :=
        (congrArg (fun z => z.left) hx).trans (Category.assoc _ _ _)
      exact ⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩
    · haveI : IsReduced T.left := inferInstanceAs (IsReduced (Sp Ω))
      obtain ⟨b, hb⟩ := exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by
        rintro _ ⟨p, rfl⟩
        have e : (ρ y ≫ s).left = y.left ≫ pullback.fst G'.hom t ≫ s.left := Category.assoc _ _ _
        rw [e, Scheme.Hom.comp_apply]
        exact hy ⟨p, rfl⟩)
      exact ⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]),
        Over.OverMorphism.ext hb⟩
    · rintro y ⟨x, hx⟩ hy
      have hx1 : x = 1 := by
        refine htors T x (hκ ?_) ?_
        · rw [map_pow, hx, ← map_pow, hy, map_one, map_one]
        · rw [← Category.assoc]
          exact (congrArg (· ≫ fst G G') hx).trans (hs₁ _)
      refine hinj ?_
      rw [map_one, ← hs₂ (ρ y)]
      have e : ρ y ≫ s = 1 := hx.symm.trans (by rw [hx1, map_one])
      rw [e, MonObj.one_comp]
  choose r hr using hsurj
  have key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1},
      κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G G'))) := fun x => by
    rw [hr]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm
    · exact (Category.assoc _ _ _).trans (hs₂ _).symm
  refine Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1} =>
    (⟨r (x.1 ≫ io ≫ snd G G'), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)
  rw [key x, key y, show r (x.1 ≫ io ≫ snd G G') = r (y.1 ≫ io ≫ snd G G') from
    congrArg Subtype.val hxy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponential
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.LieFrame

theorem sum_single_apply {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (a : Fin (m τ) → ℂ) (i : Fin (m τ)) :
    (∑ i', a i' • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ, i⟩) = a i := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : e.symm ⟨τ, i⟩ ≠ e.symm ⟨τ, b⟩ := fun h =>
      hb (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
    simp [Pi.single_eq_of_ne this]
  · simp

theorem eq_sum_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∑ i, w (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ) = w := by
  funext j
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  by_cases h : τ' = τ
  · subst h
    exact sum_single_apply e τ' (fun i => w (e.symm ⟨τ', i⟩)) i
  · have h0 : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h0
      exact h (by simpa using hw _ h0)
    rw [h0, Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : e.symm ⟨τ', i⟩ ≠ e.symm ⟨τ, b⟩ := fun h' => h (Sigma.mk.inj (e.symm.injective h')).1
    simp [Pi.single_eq_of_ne this]

theorem exists_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), (∀ τ i, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (u τ i)) ∧ (∀ τ i, IsTanAt (S := CAt σ) (F.u k P) (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧ ∀ τ (w : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)), IsTanAt (S := CAt σ) (F.u k P) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ, IsCombAt (S := CAt σ) (F.u k P) (u τ) a w := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hu : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) v := fun τ i => (h2 _).exists
  choose u hu using hu
  refine ⟨u, hu, fun τ i => h1 _ _ (hu τ i), fun τ i => ?_, fun τ w hw hew => ?_⟩
  · refine (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ (hu τ i)).2 fun j hj => ?_
    by_cases hji : j = e.symm ⟨τ, i⟩
    · subst hji
      simp
    · exact absurd (Pi.single_eq_of_ne hji _) hj
  · obtain ⟨z, hz, huniq⟩ := h3 w hw
    have hs := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ hz).1 hew
    have hc := GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ)
    refine ⟨fun i => z (e.symm ⟨τ, i⟩), (hc (fun i => z (e.symm ⟨τ, i⟩)) w).2 ?_, fun a ha => ?_⟩
    · rw [eq_sum_single e τ z hs]
      exact hz
    · have h4 := huniq _ ((hc a w).1 ha)
      funext i
      exact (sum_single_apply e τ a i).symm.trans (congrFun h4 _)

end GlobalTheory.LieFrame
end

