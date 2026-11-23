module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamUnifHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSwapComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

def chartPullPerm {X Y Y' : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ' : K' → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε' : K' → ℤ) (ε : K → ℤ) (h : Y' ⟶ Y) (e : K' ≃ K)
    (hc : ∀ k, φ' (e.symm k) = h ≫ φ k) (hε : ∀ k, ε' (e.symm k) = ε k) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) h :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j (e.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy (e.symm k)
      rw [hc] at this
      exact this
  { idx := fun j k => j (e.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (Fintype.prod_equiv e.symm _ _ fun k => ?_).symm
      rw [Category.id_comp, hc, hε] }

theorem psum_perm {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (I : Finset (Fin n)) : psum G x' I = h ≫ psum G x (I.map σ.toEmbedding) := by
  rw [CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => hx i

def chartPullCube {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (L : LB G.left) : ChartPull (cubeLB G x' L) (cubeLB G x L) h.left :=
  chartPullPerm L _ _ _ _ h.left (Equiv.ulift.trans ((Equiv.finsetCongr σ).trans Equiv.ulift.symm))
    (fun k => by
      show (psum G x' ((Equiv.finsetCongr σ).symm k.down)).left = h.left ≫ (psum G x k.down).left
      rw [psum_perm G h x x' σ hx, Over.comp_left]
      congr 3
      exact (Equiv.finsetCongr σ).apply_symm_apply k.down)
    (fun k => by
      show (-1 : ℤ) ^ (n - ((Equiv.finsetCongr σ).symm k.down).card) = (-1) ^ (n - k.down.card)
      simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply])

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_swap {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} (H : GAdj L₁ L₂ u u') : GAdj L₂ L₁ u' u :=
  LBIso.chartPull
    (chartPullCube G₁ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂, snd G₁ G₂ ≫ u'] ![fst G₂ G₁ ≫ u', snd G₂ G₁]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₁)
    (chartPullCube G₂ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂ ≫ u, snd G₁ G₂] ![fst G₂ G₁, snd G₂ G₁ ≫ u]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₂)
    (LBIso.symm H)

theorem gAdj_comp {S : Scheme.{0}} {G₁ G₂ G₃ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    [GrpObj G₃] [IsCommMonObj G₃] {L₁ : LB G₁.left} {L₂ : LB G₂.left} {L₃ : LB G₃.left} (hL₁ : L₁.IsLB)
    (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} {v : G₂ ⟶ G₃} {v' : G₃ ⟶ G₂}
    (H : GAdj L₁ L₂ u u') (H' : GAdj L₂ L₃ v v') : GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  LBIso.trans (LB.isLB_linComb hL₃ _ _) (LB.isLB_linComb hL₂ _ _) (LB.isLB_linComb hL₁ _ _)
    (LBIso.chartPull
      (chartPullCube G₃ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃ ≫ v, snd G₂ G₃]
        ![fst G₁ G₃ ≫ u ≫ v, snd G₁ G₃] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₃)
      (chartPullCube G₂ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃, snd G₂ G₃ ≫ v']
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂) H')
    (LBIso.chartPull
      (chartPullCube G₂ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂ ≫ u, snd G₁ G₂]
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂)
      (chartPullCube G₁ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂, snd G₁ G₂ ≫ u']
        ![fst G₁ G₃, snd G₁ G₃ ≫ v' ≫ u'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₁) H)

theorem gAdj_swap_comp :
    (∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : LB G₁.left)
      (L₂ : LB G₂.left), L₁.IsLB → L₂.IsLB → ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), GAdj L₁ L₂ u u' → GAdj L₂ L₁ u' u) ∧
    ∀ (S : Scheme.{0}) (G₁ G₂ G₃ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃]
      [IsCommMonObj G₃] (L₁ : LB G₁.left) (L₂ : LB G₂.left) (L₃ : LB G₃.left), L₁.IsLB → L₂.IsLB → L₃.IsLB →
      ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) (v : G₂ ⟶ G₃) (v' : G₃ ⟶ G₂), GAdj L₁ L₂ u u' → GAdj L₂ L₃ v v' →
        GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ H => gAdj_swap H,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ _ _ _ _ H H' => gAdj_comp h₁ h₂ h₃ H H'⟩

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentInvariantMorphismFlatExistsUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GalDescent

theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

theorem restrict_act {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} {Y Y' Z : Scheme.{0}}
    {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β)
    (hy' : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) (f : Z ⟶ Y) :
    ∃ act' : Gal ρ → (pullback β f ⟶ pullback β f), (∀ σ, act' σ ≫ pullback.snd β f = pullback.snd β f) ∧
      (∀ σ, act' σ ≫ (pullback.fst β f ≫ y') = (pullback.fst β f ≫ y') ≫ spMap (Gal.hom σ)) ∧
      ∀ σ, act' σ ≫ pullback.fst β f = pullback.fst β f ≫ act σ := by
  refine ⟨fun σ => pullback.lift (pullback.fst β f ≫ act σ) (pullback.snd β f)
    (by rw [Category.assoc, hβ, pullback.condition]), fun σ => pullback.lift_snd _ _ _, fun σ => ?_,
    fun σ => pullback.lift_fst _ _ _⟩
  rw [pullback.lift_fst_assoc, Category.assoc, hy', Category.assoc]

theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), β ≫ g₁ = β ≫ g₂ → g₁ = g₂ := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g₁ g₂ he
  have hS : Surjective (spMap ρ) := ⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩
  have hβS : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := β.surjective x
    have := congrArg (fun k : Y' ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (β.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _
    (_root_.GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' _).1
  rw [← cancel_mono (β.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) [IsAffine W] (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃ h₀ : Y ⟶ W, β ≫ h₀ = h := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W _ h hh
  obtain ⟨hinj, hdesc⟩ := _root_.GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ Set.range (β.app ⊤).hom := by
    intro x
    refine hdesc (h.appTop x) fun σ hle => ?_
    have e : h.appTop ≫ (act σ).appTop = h.appTop := by rw [← Scheme.Hom.comp_appTop, hh]
    have e' : (act σ).appLE (β ⁻¹ᵁ ⊤) (β ⁻¹ᵁ ⊤) hle = (act σ).appTop := by
      rw [Scheme.Hom.appLE]
      exact (congrArg ((act σ).app ⊤ ≫ ·) (Y'.presheaf.map_id _)).trans (Category.comp_id _)
    rw [e']
    exact congrArg (fun k => k.hom x) e
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ β.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Y'.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc β, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃! h₀ : Y ⟶ W, β ≫ h₀ = h := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W h hh
  have hS : Surjective (spMap ρ) := ⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin.2.2
  have hβS : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  have hβF : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip hF
  have : Finite (Gal ρ) := hgal.1
  have hsp : ∀ σ τ : Gal ρ, spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := fun σ τ => by
    rw [← Spec.map_comp]; rfl
  have hsp1 : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by rw [← Spec.map_id]; rfl
  have e1 : act 1 = 𝟙 Y' := hpb.hom_ext (by rw [hβ, Category.id_comp])
    (by rw [hy', Category.id_comp, hsp1, Category.comp_id])
  have e2 : ∀ σ τ, act (σ * τ) = act σ ≫ act τ := fun σ τ => hpb.hom_ext
    (by rw [hβ, Category.assoc, hβ, hβ])
    (by rw [hy', Category.assoc, hy', ← Category.assoc, hy', Category.assoc, hsp])
  have ei : ∀ σ, act σ ≫ act σ⁻¹ = 𝟙 Y' := fun σ => by rw [← e2, mul_inv_cancel, e1]
  have ei' : ∀ σ, act σ⁻¹ ≫ act σ = 𝟙 Y' := fun σ => by rw [← e2, inv_mul_cancel, e1]
  let ρ' : Gal ρ →* Aut Y' :=
    { toFun := fun σ => ⟨act σ⁻¹, act σ, ei' σ, ei σ⟩
      map_one' := by
        apply Aut.ext
        apply Iso.ext
        change act 1⁻¹ = 𝟙 Y'
        rw [inv_one, e1]
      map_mul' := by
        intro σ τ
        apply Aut.ext
        apply Iso.ext
        change act (σ * τ)⁻¹ = act τ⁻¹ ≫ act σ⁻¹
        rw [mul_inv_rev, e2] }
  have hρ' : ∀ g, (ρ' g).asIso.hom ≫ β = β := fun g => hβ g⁻¹
  have hinv : ∀ V : Y.Opens, IsAffineOpen V → ∀ s : Γ(Y', β ⁻¹ᵁ V),
      GlobalTheory.IsInvariantSection ρ' _ s → s ∈ Set.range (β.app V) := by
    intro V _ s hs
    refine (_root_.GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' V).2 s fun σ hle => ?_
    obtain ⟨h1, h2⟩ := hs σ⁻¹
    have key : ∀ (k : Y' ⟶ Y') (_ : k = act σ) (e : β ⁻¹ᵁ V ≤ k ⁻¹ᵁ (β ⁻¹ᵁ V)),
        (k.appLE _ _ e).hom s = s → ((act σ).appLE _ _ hle).hom s = s := by
      rintro k rfl e h; exact h
    exact key _ (show act σ⁻¹⁻¹ = act σ by rw [inv_inv]) h1 h2
  have hfib : Function.FactorsThrough h.base.hom β.base.hom := by
    intro a b hab
    obtain ⟨g, rfl⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant ρ' β hρ' hinv a b).1 hab
    show h a = h ((act g⁻¹) a)
    rw [← Scheme.Hom.comp_apply, hh]
  have hq : Topology.IsQuotientMap β.base.hom :=
    IsClosedMap.isQuotientMap β.isClosedMap β.base.hom.continuous β.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (β z) = h z := fun z => congrArg (fun k : C(Y', W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd β (V i).ι ≫ u = pullback.fst β (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst β (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd β (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    obtain ⟨act', ha1, ha2, ha3⟩ := restrict_act act hβ hy' (V i).ι
    have hinv' : ∀ σ, act' σ ≫ hi = hi := fun σ => by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      rw [reassoc_of% (ha3 σ), hh]
    obtain ⟨u, hu⟩ := exAff R R' ρ hfin hgal (V i).toScheme (pullback β (V i).ι) ((V i).ι ≫ y)
      (pullback.fst β (V i).ι ≫ y') (pullback.snd β (V i).ι) inferInstance (restrict_isPullback hpb _)
      act' ha1 ha2 i.1.toScheme hi hinv'
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    obtain ⟨act', ha1, ha2, -⟩ := restrict_act act hβ hy' f
    apply uniq R R' ρ hfin hgal _ (pullback β f) (f ≫ y) (pullback.fst β f ≫ y') (pullback.snd β f)
      inferInstance (restrict_isPullback hpb f) act' ha1 ha2 W
    let mi : pullback β f ⟶ pullback β (V i).ι := pullback.lift (pullback.fst β f)
      (pullback.snd β f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback β f ⟶ pullback β (V j).ι := pullback.lift (pullback.fst β f)
      (pullback.snd β f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd β (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd β f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd β (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : β ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ β) _ _ fun i => ?_
    change pullback.fst β (V i).ι ≫ _ = pullback.fst β (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd β (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd β (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g _ (hg.trans hglue.symm)

end GlobalTheory.GalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalOrbit

variable {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'}

theorem spMap_gal_comp (σ : Gal ρ) : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
  rw [← Spec.map_comp]; congr 1; ext r; exact σ.2 r

theorem spMap_gal_mul (σ τ : Gal ρ) :
    spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_gal_one : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

variable {X Z : Scheme.{0}} {f : X ⟶ Sp R} {p : Z ⟶ X} {s : Z ⟶ Sp R'}
  (hpb : IsPullback p s f (spMap ρ))

def act (σ : Gal ρ) : Z ⟶ Z :=
  hpb.lift p (s ≫ spMap (Gal.hom σ)) (by rw [Category.assoc, spMap_gal_comp, hpb.w])

@[reassoc] theorem galoisBaseChangeSchemeAction_comp_snd (σ : Gal ρ) : act hpb σ ≫ s = s ≫ spMap (Gal.hom σ) := hpb.lift_snd _ _ _

theorem act_one : act hpb 1 = 𝟙 Z := by
  have hp : act hpb 1 ≫ p = p := hpb.lift_fst _ _ _
  exact hpb.hom_ext (by rw [hp, Category.id_comp])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, spMap_gal_one, Category.comp_id, Category.id_comp])

theorem act_mul (σ τ : Gal ρ) : act hpb (σ * τ) = act hpb σ ≫ act hpb τ := by
  have hp (g : Gal ρ) : act hpb g ≫ p = p := hpb.lift_fst _ _ _
  exact hpb.hom_ext (by rw [hp, Category.assoc, hp, hp])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, Category.assoc, galoisBaseChangeSchemeAction_comp_snd, galoisBaseChangeSchemeAction_comp_snd_assoc, spMap_gal_mul])

def actAut : Gal ρ →* Aut Z where
  toFun σ :=
    { asIso :=
        { hom := act hpb σ⁻¹
          inv := act hpb σ
          hom_inv_id := by rw [← act_mul, inv_mul_cancel, act_one]
          inv_hom_id := by rw [← act_mul, mul_inv_cancel, act_one] } }
  map_one' := Aut.ext (Iso.ext (by change act hpb 1⁻¹ = 𝟙 Z; rw [inv_one, act_one]))
  map_mul' σ τ := Aut.ext (Iso.ext (by
    change act hpb (σ * τ)⁻¹ = act hpb τ⁻¹ ≫ act hpb σ⁻¹
    rw [mul_inv_rev, act_mul]))

end GlobalTheory.Mum.GalOrbit

namespace GlobalTheory.Mum

theorem gal_transitive_on_fibres : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'],
    Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) →
    ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z),
      h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  intro R R' _ _ _ hinj hG Y hfl Z p s hpb z z' hzz
  have : Finite (Gal (algebraMap R R')) := hG.1
  have : Flat Y.hom := hfl
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hp (σ : Gal (algebraMap R R')) : GalOrbit.act hpb σ ≫ p = p := hpb.lift_fst _ _ _
  have hinv : ∀ W : Y.left.Opens, IsAffineOpen W → ∀ u : Γ(Z, p ⁻¹ᵁ W),
      GlobalTheory.IsInvariantSection (GalOrbit.actAut hpb) _ u → u ∈ Set.range (p.app W) := by
    intro W hW u hu
    refine (InvFun.affine_inv (algebraMap R R') hinj hG hpb (GalOrbit.act hpb) hp
      (GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb) hW).2 u fun σ hσ => ?_
    obtain ⟨h₁, h₂⟩ := hu σ⁻¹
    have key : ∀ (τ τ' : Gal (algebraMap R R')) (_ : τ = τ') (e : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ ⁻¹ᵁ (p ⁻¹ᵁ W))
        (e' : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ' ⁻¹ᵁ (p ⁻¹ᵁ W)),
        ((GalOrbit.act hpb τ).appLE _ _ e).hom u = ((GalOrbit.act hpb τ').appLE _ _ e').hom u := by
      rintro τ _ rfl _ _; rfl
    exact (key _ _ (inv_inv σ).symm hσ h₁).trans h₂
  obtain ⟨g, hg⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant (GalOrbit.actAut hpb) p
    (fun g => hp g⁻¹) hinv z z').1 hzz
  exact ⟨g⁻¹, GalOrbit.act hpb g⁻¹, hp _, GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb _, hg⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
section
namespace GlobalTheory.AnPer

theorem gaussManinPeriods_of_span_taylor : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods :=
  fun HS HT ↦ gaussManinPeriods_of_parts (-1) GlobalTheory.PeriodFamily.famUnif_holds _root_.GlobalTheory.AnPer.periods_exist _root_.GlobalTheory.AnPer.pHom HS
    _root_.GlobalTheory.AnPer.pLie_holds _root_.GlobalTheory.AnPer.periodHom_push_end _root_.GlobalTheory.AnPer.ChernClause.pchern _root_.GlobalTheory.AnPer.period_fibre_eq_value HT

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePolarisationEqEighthPowerPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.GenPull

theorem lbIso_gen_pull : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' gm ψ hψ H
  have e0 : LBIso A'.L (A'.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id A'.isLB
  have hc : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have e1 : LBIso ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) (A'.L.pull (𝟙 _)) := by
    have := GlobalTheory.SiegelPullComp.iso_pull_pull A'.isLB U'.gen.hom.left U'.gen.inv.left
    rwa [hc] at this
  have e2 := GlobalTheory.SiegelPullComp.iso_pull U'.gen.inv.left U'.ext
  have e3 := GlobalTheory.SiegelPullComp.iso_pull_pull U'.LG.isLB (pullback.fst G'.hom (jK R)) U'.gen.inv.left
  have e4 := GlobalTheory.SiegelPullComp.iso_pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) H
  have e5 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB gm (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))
  have hq : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm = ψ ≫ FinalForm.φ := by
    rw [Category.assoc, hψ]
  rw [hq] at e5
  have e6 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB FinalForm.φ ψ
  have e7 := GlobalTheory.SiegelPullComp.iso_pull ψ (⟨FinalForm.w, FinalForm.w_gen⟩ : LBIso _ _)
  have e8 := GlobalTheory.SiegelPullComp.iso_pull_pull ρ.P.isLB (pullback.fst ρ.P.A.hom FinalForm.u₀) ψ
  have hA := A'.isLB
  have hG := U'.LG.isLB
  have hZ := FinalForm.L.isLB
  have hP := ρ.P.isLB
  refine LBIso.trans hA (pull_isLB (pull_isLB hA _) _) (pull_isLB hP _) (LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _) e0 e1.symm) ?_
  refine LBIso.trans (pull_isLB (pull_isLB hA _) _) (pull_isLB (pull_isLB hG _) _) (pull_isLB hP _) e2 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hG _) _) (pull_isLB hG _) (pull_isLB hP _) e3 ?_
  refine LBIso.trans (pull_isLB hG _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e4 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) (pull_isLB hP _) e5 ?_
  refine LBIso.trans (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e6.symm ?_
  exact LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e7 e8

end GlobalTheory.Poinc.GenPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreUniformisedModelPointGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section
namespace GlobalTheory.GenPb

theorem genfib_grpPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' ξ gm hgm ξ₀ hξ
  have := U'.gen_hom
  have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
  have gpA : IsGrpPullback A'.A G' (jK R) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) :=
    ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK R))).congr
      (Category.id_comp _) rfl
  have h2 : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ U₀.ι) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm) :=
    (gpA.comp hgm).congr hξ.symm rfl
  have hw : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) ≫ FinalForm.G.hom = (A'.A.hom ≫ ξ₀) ≫ U₀.ι := by
    have := h2.1.w
    simpa [Category.assoc] using this
  refine ⟨FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw,
    FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _, ?_⟩
  have h3 : IsGrpPullback A'.A ((Over.pullback FinalForm.u₀).obj ρ.P.A) ξ₀
      (FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw) :=
    IsGrpPullback.cancel FinalForm.cart (h2.congr rfl (by rw [FinalForm.cart.1.lift_fst, Category.assoc]))
      (FinalForm.cart.1.lift_snd _ _ _)
  exact h3.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)

end GlobalTheory.GenPb
end
end

