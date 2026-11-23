module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOfDividingMaximalMinor
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullbackOfProjChart
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem IsHom.apply_genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (h : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  have e : (N.pt ≫ q) (IsLocalRing.closedPoint Ω') =
      (spMap φ.toRingHom ≫ M.pt) (IsLocalRing.closedPoint Ω') := by
    rw [show N.pt ≫ q = _ from h]
  have e' : q (N.pt (IsLocalRing.closedPoint Ω')) = M.pt (spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) := e
  rw [e']
  exact M.top_le_preimage_pt hW (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial

theorem IsHom.comp_id {N Q : RatModel o Ω'} {q : N.Z ⟶ M.Z} {a : Q.Z ⟶ N.Z} (h : M.IsHom N φ q)
    (ha : N.IsHom Q (AlgHom.id o Ω') a) : M.IsHom Q φ (a ≫ q) := by
  simpa only [AlgHom.id_comp] using h.comp ha

theorem exists_isHom_of_projChart {N₁ N₂ : RatModel o Ω'} {q₁ : N₁.Z ⟶ M.Z} {q₂ : N₂.Z ⟶ M.Z}
    (h₁ : M.IsHom N₁ φ q₁) (h₂ : M.IsHom N₂ φ q₂) {J : Type} [Finite J] {t : J → Ω'}
    (h : ∀ z, ∃ (W : M.Z.Opens) (i : J), q₁ z ∈ W ∧ N₁.Div t i z ∧ M.ProjChart N₂ φ q₂ W t) :
    ∃ a, N₂.IsHom N₁ (AlgHom.id o Ω') a := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨W, i, hz, hi, hc⟩ := h z
  obtain ⟨U, hU, hD, hR⟩ := hc.2 i hi.1
  refine ⟨q₁ ⁻¹ᵁ W ⊓ ⟨_, N₁.isOpen_setOf_div t i⟩, U, ⟨hz, hi⟩, hU,
    ⟨genericPoint N₂.Z, hD ▸ ⟨h₂.apply_genericPoint_mem ⟨_, hz⟩, div_genericPoint hi.1⟩⟩,
    fun x hx => mem_ringOn.2 fun w hw => ?_⟩
  rw [hR] at hx
  refine (Algebra.adjoin_le ?_ : _ ≤ N₁.O w) hx
  rintro _ (⟨y, hy, rfl⟩ | ⟨j, rfl⟩)
  · exact h₁.map_mem_O (ringOn_le_O (M := M) (U := W) (z := q₁ w) hw.1 hy)
  · exact hw.2.2 j

theorem exists_isPullback_of_projChart_of_isPullback {N P Q : RatModel o Ω'} {U₀ : M.Z.Opens} {b : N.Z ⟶ U₀.toScheme}
    {f : P.Z ⟶ M.Z} {ι : Q.Z ⟶ P.Z} [IsOpenImmersion ι] {g : Q.Z ⟶ U₀.toScheme} (hι : P.IsHom Q (AlgHom.id o Ω') ι)
    (hpb : IsPullback ι g f U₀.ι) {J : Type} [Finite J] {t : J → Ω'} (hb : M.IsHom N φ (b ≫ U₀.ι))
    (hf : M.IsHom P φ f)
    (h : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty →
      M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) :
    ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  have hU : ∀ {X : Scheme.{0}} (b : X ⟶ U₀.toScheme) (z : X), (b ≫ U₀.ι) z ∈ U₀ := fun b z => by
    rw [Scheme.Hom.comp_apply]
    exact (b z).2
  obtain ⟨a₀, ha₀⟩ : ∃ a, P.IsHom N (AlgHom.id o Ω') a := by
    refine exists_isHom_of_projChart hb hf (t := t) fun z => ?_
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (hU b z)
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h1.1 z hz
    exact ⟨W, i, hz, hi, h2⟩
  have hfι : M.IsHom Q φ (ι ≫ f) := hf.comp_id hι
  obtain ⟨c, hc⟩ : ∃ c, N.IsHom Q (AlgHom.id o Ω') c := by
    refine exists_isHom_of_projChart hfι hb (t := t) fun z => ?_
    have hz0 : (ι ≫ f) z ∈ U₀ := hpb.w ▸ hU g z
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hz0
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h2.1 (ι z) (by rwa [Scheme.Hom.comp_apply] at hz)
    refine ⟨W, i, hz, ⟨hi.1, fun j => ?_⟩, h1⟩
    rw [hι.O_eq z]
    exact hi.2 j
  have hw : a₀ ≫ f = b ≫ U₀.ι := IsHom.unique (φ := φ) (hf.comp_id ha₀) hb
  obtain ⟨a₁, e₁, e₂⟩ : ∃ a₁ : N.Z ⟶ Q.Z, a₁ ≫ ι = a₀ ∧ a₁ ≫ g = b :=
    ⟨hpb.lift a₀ b hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have ha₁ : Q.IsHom N (AlgHom.id o Ω') a₁ := by
    unfold IsHom at hι ha₀ ⊢
    have e : spMap (AlgHom.id o Ω').toRingHom = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp] at hι ha₀ ⊢
    rw [← cancel_mono ι, Category.assoc, e₁, hι, ha₀]
  have h₁ : a₁ ≫ c = 𝟙 N.Z := IsHom.unique (φ := AlgHom.id o Ω') (hc.comp_id ha₁) N.isHom_id
  have h₂ : c ≫ a₁ = 𝟙 Q.Z := IsHom.unique (φ := AlgHom.id o Ω') (ha₁.comp_id hc) Q.isHom_id
  have : IsIso a₁ := ⟨c, h₁, h₂⟩
  refine ⟨a₀, ha₀, ?_⟩
  exact hpb.of_iso (asIso a₁).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← e₁]) (by simp [← e₂]) (by simp) (by simp)

theorem exists_isPullback_of_projChart :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  intro o Ω _ _ _ M Ω' _ _ φ _ N P U₀ b f J _ t hb hf h
  have hbU : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀ := by
    rw [Scheme.Hom.comp_apply]
    exact (b _).2
  have hV : ((f ⁻¹ᵁ U₀ : P.Z.Opens) : Set P.Z).Nonempty := ⟨_, hf.apply_genericPoint_mem ⟨_, hbU⟩⟩
  exact @exists_isPullback_of_projChart_of_isPullback o Ω _ _ _ M Ω' _ _ φ N P (P.openPart _ hV) U₀ b f
    (f ⁻¹ᵁ U₀).ι (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U₀).ι)) (f ∣_ U₀) (P.isHom_openPart _ hV)
    (isPullback_morphismRestrict f U₀).flip J _ t hb hf h

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LocThetaConv

variable {X Y : Scheme.{0}}

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem appLE_resG (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) {U : Y.Opens} (e : U ≤ f ⁻¹ᵁ W')
    (a : Γ(X, W)) : (f.appLE W' U e).hom (resG X h a) =
      (f.appLE W U (e.trans fun _ hy => h hy)).hom a := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem resG_appLE (f : Y ⟶ X) {W : X.Opens} {U U' : Y.Opens} (h : U' ≤ U) (e : U ≤ f ⁻¹ᵁ W)
    (a : Γ(X, W)) : resG Y h ((f.appLE W U e).hom a) = (f.appLE W U' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem g_val (L : LB X) {K : Type} [Fintype K] [Subsingleton K] (φ : K → (Y ⟶ X)) (k : K)
    (i j : K → L.ι) : ((LB.LinComb L φ (fun _ => 1)).g i j).val =
      ((φ k).appLE (L.U (i k) ⊓ L.U (j k)) (LB.wchart L φ i ⊓ LB.wchart L φ j)
        (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))).hom
        (L.g (i k) (j k)).val := by
  simp only [LB.LinComb, zpow_one]
  erw [Fintype.prod_subsingleton _ k]
  rfl

theorem mem_one {L : LB X} {j : Fin 1 → L.ι} {x : X} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_pull' {L : LB X} (f : Y ⟶ X) {j : L.ι} {y : Y} :
    y ∈ (L.pull f).U (fun _ => j) ↔ f y ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_secOn (L : LB X) (V : X.Opens) (σ : LB.Sec (L.pull V.ι)) :
    ∃ τ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V,
      ∀ y ∈ nonzeroLocus σ, ∃ j, V.ι y ∈ X.basicOpen (τ j) := by
  set L₁ := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1) with hL₁
  have e : ∀ j : Fin 1 → L.ι, (L.pull V.ι).U (fun _ => j 0) ≤ V.ι ⁻¹ᵁ (V ⊓ L₁.U j) :=
    fun j y hy => ⟨y.2, mem_one.2 ((mem_pull' _).1 hy)⟩
  have e' : ∀ j : Fin 1 → L.ι, V.ι ⁻¹ᵁ (V ⊓ L₁.U j) ≤ (L.pull V.ι).U (fun _ => j 0) :=
    fun j y hy => (mem_pull' _).2 (mem_one.1 hy.2)
  have hV : V ≤ V.ι.opensRange := V.opensRange_ι.ge
  choose τ hτ using fun j : Fin 1 → L.ι =>
    (bijective_appLE V.ι _ (inf_le_left.trans hV) _ (e j) (e' j)).2 (σ.f fun _ => j 0)
  refine ⟨τ, fun i j => ?_, fun y hy => ?_⟩
  · apply (bijective_appLE V.ι (V ⊓ L₁.U i ⊓ L₁.U j) ((inf_le_left.trans inf_le_left).trans hV)
      ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
      (fun y hy => ⟨e i hy.1, (e j hy.2).2⟩) (fun y hy => ⟨e' i hy.1, e' j ⟨hy.1.1, hy.2⟩⟩)).1
    have h := σ.compat (fun _ => i 0) (fun _ => j 0)
    rw [← hτ i, ← hτ j] at h
    rw [map_mul]
    refine ((appLE_resG _ _ _ _).trans (resG_appLE _ _ _ _).symm).trans (h.trans ?_)
    congr 1
    · have h1 : ((L.pull V.ι).g (fun _ => i 0) (fun _ => j 0)).val =
          (V.ι.appLE (L.U (i 0) ⊓ L.U (j 0)) ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
            (fun y hy => ⟨(mem_pull' _).1 hy.1, (mem_pull' _).1 hy.2⟩)).hom
            (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : PUnit => V.ι) PUnit.unit _ _).trans (by rfl)
      have h2 : (L₁.g i j).val = resG X (fun y hy => ⟨mem_one.1 hy.1, mem_one.1 hy.2⟩ :
          L₁.U i ⊓ L₁.U j ≤ L.U (i 0) ⊓ L.U (j 0)) (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : Fin 1 => 𝟙 X) 0 _ _).trans (by rfl)
      rw [h1, h2]
      exact ((appLE_resG _ _ _ _).trans (appLE_resG _ _ _ _)).symm
    · exact (resG_appLE _ _ _ _).trans (appLE_resG _ _ _ _).symm
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    have h := Scheme.basicOpen_appLE V.ι _ _ (e fun _ => k PUnit.unit) (τ fun _ => k PUnit.unit)
    have h' := hτ fun _ => k PUnit.unit
    have hk' : y ∈ V.toScheme.basicOpen (σ.f fun _ => k PUnit.unit) := hk
    rw [← h'] at hk'
    exact (h.le hk').2

theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_secFam_fibNe : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q H z
  obtain ⟨N, σ, hz, hσ⟩ := H z
  obtain ⟨τ, hτ, hne⟩ := exists_secOn Q.L.L _ σ
  refine ⟨N, τ, hz, hτ, fun K _ _ x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hσ _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
  obtain ⟨j, hj⟩ := hne y hy
  have := Q.dim
  have : Smooth Q.G.hom := SmoothOfRelativeDimension.smooth S.g _
  obtain ⟨g, hg, hO⟩ := exists_point Q.G.hom x _ _ hj hyx
  exact ⟨g, j, hg, ((GlobalTheory.Points.le_preimage_basicOpen_iff g
    (GlobalTheory.Points.le_preimage_mono g (Scheme.basicOpen_le _ _) hO) (τ j)).1 hO).ne_zero⟩

end GlobalTheory.ZH.LocThetaConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable (S : ThetaSys o Ω)

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH

open MinorModel

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem exists_open_ringOn_contains_of_fg_of_finite {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (A : Subalgebra o Ω) (hA : A.FG) (F : Set Ω)
    (hF : F.Finite) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ A ≤ M.ringOn U ∧ ∀ x ∈ F, x ∈ M.ringOn U := by
  obtain ⟨s, rfl⟩ := hA
  have hT : ((s : Set Ω) ∪ F).Finite := s.finite_toSet.union hF
  let U : M.Z.Opens := ⟨⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z},
    hT.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x⟩
  have hU : ∀ x ∈ (s : Set Ω) ∪ F, x ∈ M.ringOn (U : Set M.Z) := fun x hx =>
    _root_.GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z hz =>
      Set.mem_iInter₂.1 hz x hx
  refine ⟨U, ⟨genericPoint M.Z, ?_⟩, ?_, fun x hx => hU x (Or.inr hx)⟩
  · show genericPoint M.Z ∈ ⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z}
    simp [M.O_genericPoint]
  · exact Algebra.adjoin_le fun x hx => hU x (Or.inl hx)

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem exists_open_over0_ringOn_of_fg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (S : _root_.GlobalTheory.ZH.ThetaSys o Ω) (M : _root_.GlobalTheory.ZH.RatModel o Ω) (R' : Subalgebra o Ω)
    (hfg : R'.FG) (hR : S.R ≤ R') (hn : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) (hd : M.HasDiv S.th) :
    ∃ U : M.Z.Opens, S.Over₀ M U ∧ R' ≤ M.ringOn U := by
  obtain ⟨U, hUne, hAU, hFU⟩ := exists_open_ringOn_contains_of_fg_of_finite M R' hfg
    (Set.range (fun x => (S.th x)⁻¹) ∪ Set.range (fun q : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => (S.FF q.1 q.2.1 q.2.2)⁻¹))
    ((Set.finite_range _).union (Set.finite_range _))
  exact ⟨U, ⟨hn, hp, hd, hUne, hR.trans hAU, fun x _ => hFU _ (Or.inl ⟨x, rfl⟩),
    fun T c k _ _ => hFU _ (Or.inr ⟨⟨T, c, k⟩, rfl⟩)⟩, hAU⟩

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem module_finite_of_subfield_le {Ω : Type} [Field Ω] {K K' : Subfield Ω} (h : K ≤ K')
    [Module.Finite K Ω] : Module.Finite K' Ω := by
  letI : Algebra K K' := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite K K' Ω

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem isProper_of_isProjOver_degeneration {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) : IsProper M.s := by
  obtain ⟨N, i, hi, e⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o N
  rw [← e]
  infer_instance


open CategoryTheory Limits AlgebraicGeometry in
open Classical in
theorem _root_.GlobalTheory.ZH.exists_minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [_root_.GlobalTheory.ZH.ArithBase o Ω] (S : _root_.GlobalTheory.ZH.ThetaSys o Ω), S.HasTests →
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω →
    ∃ (n a : ℕ) (GG : Fin n → S.J → Ω) (X Z : _root_.GlobalTheory.ZH.RatModel o Ω) (U₀ : Z.Z.Opens)
      (EE : Z.Lat S.J) (f : Z.Z ⟶ X.Z) (Xab : X.Z.Opens), X.IsNm S.th ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver X.s ∧
      Z.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) ∧
      S.Over₀ Z U₀ ∧ S.IsEE Z U₀ EE ∧ X.IsHom Z (AlgHom.id o Ω) f ∧
      (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab) ∧
      (∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, ∀ w : S.J → Ω,
        w ∈ Submodule.span (Z.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔
          ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ Z.O z) ∧
      ∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z,
        (∀ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) / S.th x₀ ^ (a * Fintype.card S.J) ∈ Z.O z) ∧
        (S.TT Z z = ⊥ ↔ ∃ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) ≠ 0 ∧
          S.th x₀ ^ (a * Fintype.card S.J) / Matrix.det (Matrix.of fun i j => GG (k i) j) ∈ Z.O z) := by
  intro o Ω _ _ _ _ S hT hfin
  haveI : Algebra.FiniteType ℤ o := _root_.GlobalTheory.ZH.ArithBase.ft (o := o) Ω
  haveI : CharZero Ω := _root_.GlobalTheory.ZH.ArithBase.char o (Ω := Ω)
  haveI : IsDedekindDomain o := _root_.GlobalTheory.ZH.ArithBase.ded (o := o) Ω
  have hwt := _root_.GlobalTheory.ZH.test_weights o Ω S
  obtain ⟨M₁, U₁, hAdm₁, hAff₁, -⟩ := _root_.GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S Unit (fun _ => 1) ⟨(), one_ne_zero⟩
    (by
      rw [show {x | ∃ i j : S.Gam × Unit, x = S.th j.1 * (fun _ => (1:Ω)) j.2 / (S.th i.1 * (fun _ => (1:Ω)) i.2)}
          = {x | ∃ i j, x = S.th j / S.th i} by ext x; simp]
      exact hfin)
  have hO₁ := hAdm₁.1
  have hreg₁ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω M₁ U₁ hO₁.normal
  have htst₁ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S M₁ U₁ hT hO₁
  have hsup₁ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M₁ U₁ hO₁
  have hiso₁ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁
  obtain ⟨EE₁, hEE₁, hspan₁⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_adm o Ω S M₁ U₁ hT hAdm₁
  have hFF₁ := _root_.GlobalTheory.ZH.FF_TT_ne_zero o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hdot₁ := _root_.GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hnorm := _root_.GlobalTheory.thetaSys_norm_FF_le_exp o Ω S hwt
  have hnd₁ := _root_.GlobalTheory.norm_val_FF_eq_of_div o Ω S M₁ U₁ hO₁ hsup₁ hnorm htst₁
  have hdot₁' := hdot₁ hnorm hnd₁ hFF₁ hspan₁
  obtain ⟨n, a, GG₀, hGG₀⟩ := _root_.GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁.2 hiso₁ hFF₁ hspan₁ hdot₁'
  obtain ⟨R', hR, GG, hfg, hGGeq, htests⟩ := _root_.GlobalTheory.ZH.exists_generators_at_all_tests o Ω S M₁ U₁ EE₁ n a GG₀ hO₁ hAff₁ hsup₁ hEE₁ hGG₀
  have hinj : Function.Injective (algebraMap o Ω) := (inferInstance : _root_.GlobalTheory.ZH.ArithBase o Ω).4
  obtain ⟨X, hXn, hXp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj S.Gam S.th S.th_ne hfin
  have hXnorm := hXn.isNormalScheme
  obtain ⟨UX, hOX, hRX⟩ := exists_open_over0_ringOn_of_fg S X R' hfg hR hXnorm hXp hXn.1
  have hregX := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω X UX hXnorm
  have htstX := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S X UX hT hOX
  have hsupX := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S X UX hOX
  have hisoX := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S X UX hOX hregX htstX hsupX
  have hminX := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S X UX R' hR n a GG hOX hRX hregX htstX hsupX hisoX hwt htests
  obtain ⟨ξ, hξ⟩ := hOX.ne
  obtain ⟨x₀, hx₀⟩ := hXn.1 ξ
  obtain ⟨k₀, hk₀, -⟩ := ((hminX ξ x₀ hx₀).2).1 (hisoX.2.2.1 ξ hξ)
  obtain ⟨Z, hZn, hZp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj (S.Gam × (S.J → Fin n))
    (fun q => S.th q.1 * Matrix.det (Matrix.of fun i j => (GG (q.2 i) j : Ω)))
    ⟨(x₀, k₀), mul_ne_zero hx₀.1 hk₀⟩
    (by
      haveI := hfin
      refine module_finite_of_subfield_le (K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j, x = S.th j / S.th i})) ?_
      refine Subfield.closure_le.2 (Set.union_subset (fun x hx => Subfield.subset_closure (Or.inl hx)) ?_)
      rintro x ⟨i, j, rfl⟩
      exact Subfield.subset_closure (Or.inr ⟨(i, k₀), (j, k₀), (mul_div_mul_right _ _ hk₀).symm⟩))
  have hZdiv := (_root_.GlobalTheory.ZH.isNm_normal_and_div_prod o Ω Z S.Gam S.th).2.1 (S.J → Fin n)
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)))
  have hZth : Z.HasDiv S.th := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨i, ((hZdiv i k z).1 h).1⟩
  have hZd : Z.HasDiv (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨k, ((hZdiv i k z).1 h).2⟩
  have hZnorm := hZn.isNormalScheme
  obtain ⟨UZ, hOZ, hRZ⟩ := exists_open_over0_ringOn_of_fg S Z R' hfg hR hZnorm hZp hZth
  have hregZ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω Z UZ hZnorm
  have htstZ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S Z UZ hT hOZ
  have hsupZ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S Z UZ hOZ
  have hisoZ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S Z UZ hOZ hregZ htstZ hsupZ
  obtain ⟨EE, hEE, hspanZ⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_hasDiv_minors o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ htests hZd
  have hminZ := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ hisoZ hwt htests
  obtain ⟨f, hf⟩ := hXn.exists_isHom (φ := AlgHom.id o Ω)
    (show Z.HasDiv (fun j => (AlgHom.id o Ω) (S.th j)) from hZth)
    (fun z => _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hZnorm z)
  let Xab : X.Z.Opens := ⟨{x | S.TT X x = ⊥}, by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨y₀, hy₀⟩ := hXn.1 x
    obtain ⟨k, hk, hmem⟩ := ((hminX x y₀ hy₀).2).1 hx
    refine ⟨{y | X.Div S.th y₀ y} ∩ {y | S.th y₀ ^ (a * Fintype.card S.J) /
      Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) ∈ X.O y}, ?_,
      (X.isOpen_setOf_div S.th y₀).inter
        (X.isOpen_setOf_mem_O _), hy₀, hmem⟩
    rintro y ⟨hy1, hy2⟩
    exact ((hminX y y₀ hy1).2).2 ⟨k, hk, hy2⟩⟩
  have hiso := _root_.GlobalTheory.ZH.isIso_morphismRestrict_of_isNm_prod o Ω X Z S.Gam (S.J → Fin n) S.th
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) f hXn hZn (isProper_of_isProjOver_degeneration Z hZp) hf Xab (by
      intro z hz
      obtain ⟨y₀, hy₀⟩ := hXn.1 z
      obtain ⟨k, hk, hmem⟩ := ((hminX z y₀ hy₀).2).1 hz
      refine ⟨k, hk, fun j => ?_⟩
      have h1 := (hminX z y₀ hy₀).1 j
      have ht : S.th y₀ ^ (a * Fintype.card S.J) ≠ 0 := pow_ne_zero _ hy₀.1
      have h2 := (X.O z).mul_mem h1 hmem
      beta_reduce at h1 hmem h2 ⊢
      rwa [div_mul_div_cancel₀ ht] at h2)
  exact ⟨n, a, fun k j => (GG k j : Ω), X, Z, UZ, EE, f, Xab, hXn, hXp, hZn, hOZ, hEE, hf, rfl, hiso, hspanZ, hminZ⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrder
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ZJ.exists_torsion_lift_of_residue :
    ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  intro p _ B G _ hG y n hn t ht
  have := hG.comm
  have := hG.smooth
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G n
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  have w : t.left ≫ (mulN G n).left =
      (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ht, e]
  obtain ⟨c, hc₁, hc₂⟩ := ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y
    (hP.lift _ _ w) (hP.lift_snd _ _ w)
  let b : Over.mk y ⟶ G := Over.homMk (c ≫ (torsion.ι G n).left) (by
    rw [Category.assoc, Over.w]; exact hc₁)
  refine ⟨b, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (c ≫ (torsion.ι G n).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hc₁]
  · change _ ≫ c ≫ (torsion.ι G n).left = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)

end GlobalTheory
end

