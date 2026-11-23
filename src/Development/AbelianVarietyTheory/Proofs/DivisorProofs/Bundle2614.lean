module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem galAct_nonempty : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hG U'
  have hex : ∀ σ : Gal ρ, ∃ a, GalMap hD U' σ a := _root_.GlobalTheory.Mum.exists_galMap R hR R' ρ hfin D D' hD A' G' hG U'
  choose act hact using hex
  exact ⟨{ act := act
           cart := fun σ => (hact σ).1
           act_one := _root_.GlobalTheory.Mum.galMap_unique R hR R' ρ hfin D D' hD A' G' hG U' 1 _ _ (hact 1) (_root_.GlobalTheory.Mum.galMap_one R hR R' ρ hfin D D' hD A' G' hG U')
           act_mul := fun σ τ => _root_.GlobalTheory.Mum.galMap_unique R hR R' ρ hfin D D' hD A' G' hG U' (σ * τ) _ _ (hact (σ * τ))
             (_root_.GlobalTheory.Mum.galMap_mul R hR R' ρ hfin D D' hD A' G' hG U' σ τ _ _ (hact σ) (hact τ))
           unif := fun σ => (hact σ).2 }⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliMapOfMarkedPeriodIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTIso

theorem one_comp_monHom {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : A ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_one' {S : Scheme.{0}} {A A' : Over S} [GrpObj A'] (f : A ⟶ A') : f ≫ (1 : A' ⟶ A') = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem pull_birig : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (f : A ⟶ A'), IsMonHom f → ∀ P : LB (G2 A').left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A' A') (fst A' A')).left) →
    (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).IsLB ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left)
      ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (snd A A) (fst A A)).left) := by
  intro S A A' _ _ _ _ f hf P hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hs
  haveI := hf
  set φ₂ := (lift (fst A A ≫ f) (snd A A ≫ f)).left with hφ₂
  have hP₂ : (P.pull φ₂).IsLB := pull_isLB hP _

  have triv : ∀ (l : A ⟶ G2 A) (l' : A' ⟶ G2 A'), l ≫ lift (fst A A ≫ f) (snd A A ≫ f) = f ≫ l' →
      ∀ t : (P.pull l'.left).Gen, t.IsGen → ∃ s : ((P.pull φ₂).pull l.left).Gen, s.IsGen := by
    intro l l' hl t ht
    have e₁ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull l'.left).pull f.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP f.left rfl
    have e₂ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull φ₂).pull l.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP l.left (by rw [hφ₂, ← Over.comp_left, ← Over.comp_left, hl])
    obtain ⟨s, hs⟩ := GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e₁.symm
      (pullGenLB t f.left) (pullGenLB_isGen ht f.left)
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP _) (pull_isLB hP₂ _) e₂ s hs
  refine ⟨hP₂, triv _ _ ?_ t₁ ht₁, triv _ _ ?_ t₂ ht₂, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · have eq : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A' A') (fst A' A')).left := by
      rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₁ : LBIso (P.pull φ₂) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pullback hs φ₂
    have e₂ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left))
        ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP φ₂ rfl
    have e₃ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull φ₂).pull (lift (snd A A) (fst A A)).left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq.symm
    exact LBIso.trans hP₂ (pull_isLB (pull_isLB hP _) _) (pull_isLB hP₂ _) e₁
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP₂ _) e₂.symm e₃)

theorem weil_pull_iso : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (F : A ≅ A'), IsMonHom F.hom → ∀ P : LB (G2 A').left, P.IsLB → ∀ (T : Over S) (k : ℤ) (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ), Out.WeilIs A' (P.pull (lift (𝟙 A') (𝟙 A')).left) k (x ≫ F.hom) (y ≫ F.hom) c →
    Out.WeilIs A ((P.pull (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left).pull (lift (𝟙 A) (𝟙 A)).left) k x y c := by
  intro S A A' _ _ _ _ F hF P hP T k x y c H
  haveI := hF
  set φ₂ := (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left with hφ₂
  have eq : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = F.hom.left ≫ (lift (𝟙 A') (𝟙 A')).left := by
    rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e₁ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ rfl
  have e₂ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull (lift (𝟙 A') (𝟙 A')).left).pull F.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq
  have iso := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁.symm e₂
  let x₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (x.left ≫ F.hom.left) (by simp)
  let y₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (y.left ≫ F.hom.left) (by simp)
  refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S A' A (𝟙 S) F.hom.left _ _ (pull_isLB hP _)
    (pull_isLB (pull_isLB hP _) _) (isGrpPullback_of_iso F) iso T k x y x₀ y₀ c rfl rfl).2 ?_
  exact GlobalTheory.UnifPoint.weilIs_congr (Category.comp_id _).symm rfl rfl H

theorem nonempty_objMap_of_markedIsom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  rintro p _ D R _ b N σ ρ o o' h hL h' hL' D' D'' t t' Q Q' e e' w u hN0
    ⟨-, hP, he, hk, hl, hw, hη⟩ ⟨-, hP', he', hk', hl', hw', hη'⟩ ⟨hiso, hmark⟩ hu

  have k1 : ∀ z, e z = 1 → e' (u z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk z).1 hz
    exact (hk' _).2 ⟨w x, hu x⟩
  have k2 : ∀ z, e' z = 1 → e (u.symm z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk' z).1 hz
    refine (hk _).2 ⟨w.symm x, ?_⟩
    apply u.injective
    rw [u.apply_symm_apply, ← hu, w.apply_symm_apply]
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := _root_.GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker o.A o'.A D.g D.g o.ab o'.ab h h' e e' u.toLinearMap he he' k1
  obtain ⟨f', ⟨hf', hfe'⟩, -⟩ := _root_.GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker o'.A o.A D.g D.g o'.ab o.ab h' h e' e u.symm.toLinearMap he' he k2
  obtain ⟨f₀, -, uid⟩ := _root_.GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker o.A o.A D.g D.g o.ab o.ab h h e e LinearMap.id he he (fun z hz => hz)
  obtain ⟨f₀', -, uid'⟩ := _root_.GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker o'.A o'.A D.g D.g o'.ab o'.ab h' h' e' e' LinearMap.id he' he' (fun z hz => hz)
  have hfe2 : ∀ z, e' (u z) = e z ≫ f := hfe
  have hfe2' : ∀ z, e (u.symm z) = e' z ≫ f' := hfe'
  haveI := hf
  haveI := hf'
  have c1 : f ≫ f' = 𝟙 _ := by
    rw [uid (f ≫ f') ⟨inferInstance, fun z => ?_⟩, uid (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e z) f f')
    rw [← hfe2]
    exact (by rw [u.symm_apply_apply]; rfl : e (LinearMap.id z) = e (u.symm (u z))).trans (hfe2' (u z))
  have c2 : f' ≫ f = 𝟙 _ := by
    rw [uid' (f' ≫ f) ⟨inferInstance, fun z => ?_⟩, uid' (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e' z) f' f)
    rw [← hfe2']
    exact (by rw [u.apply_symm_apply]; rfl : e' (LinearMap.id z) = e' (u (u.symm z))).trans (hfe2 (u.symm z))
  let F : o.A ≅ o'.A := ⟨f, f', c1, c2⟩
  haveI : IsMonHom F.hom := hf

  have hcomm : ∀ (c : D.O) z, u (ρ c *ᵥ z) = ρ c *ᵥ u z := by
    intro c
    have := LinearMap.ext_on_range (R := ℝ) (v := fun x => Q x) hP.2.2.2.1
      (f := (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)).restrictScalars ℝ)
      (g := (Matrix.toLin' (ρ c) ∘ₗ u.toLinearMap).restrictScalars ℝ) (fun x => by
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1, ← hu, ← hu, w.map_smul, hP'.1])
    intro z
    simpa using LinearMap.congr_fun this z
  have hact : ∀ c, o.act.act c ≫ f = f ≫ o'.act.act c := by
    intro c
    haveI := o.act.hom c
    haveI := o'.act.hom c
    obtain ⟨fa, -, ua⟩ := _root_.GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker o.A o'.A D.g D.g o.ab o'.ab h h' e e'
      (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)) he he' (fun z hz => by
        obtain ⟨x, rfl⟩ := (hk z).1 hz
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1]
        exact k1 _ ((hk _).2 ⟨_, rfl⟩))
    rw [ua (o.act.act c ≫ f) ⟨inferInstance, fun z => ?_⟩, ua (f ≫ o'.act.act c) ⟨inferInstance, fun z => ?_⟩]
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) f (o'.act.act c))
      rw [← hfe2, hcomm]
      exact hl' c (u z)
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) (o.act.act c) f)
      rw [hfe2]
      exact congrArg (· ≫ f) (hl c z)
  have hT : (toUnit (Over.mk (𝟙 (Sp ℂ)))).left = 𝟙 _ := by
    simpa using Over.w (toUnit (Over.mk (𝟙 (Sp ℂ))))
  have heta : ∀ y, (o.eta y).left ≫ f.left = 𝟙 _ ≫ (o'.eta y).left := by
    intro y
    obtain ⟨e₀, he₀⟩ := hmark y
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hη2 : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y = e ((N : ℂ)⁻¹ • Q (t y)) := hη y
    have hη2' : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y = e' ((N : ℂ)⁻¹ • Q' (t' y)) := hη' y
    have a1 : (toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y) ≫ f = toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y := by
      refine (congrArg (· ≫ f) hη2).trans ((hfe2 _).symm.trans (Eq.trans ?_ hη2'.symm))
      have hz : (N : ℂ)⁻¹ • N • Q' e₀ = Q' e₀ := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [map_smul, ← hu, he₀, map_add (f := _), map_nsmul, smul_add, hz, he'.1, (hk' (Q' e₀)).2 ⟨e₀, rfl⟩, _root_.mul_one]
    have a2 := congrArg (fun q => q.left) a1
    simp only [Over.comp_left, hT, Category.id_comp] at a2
    rw [Category.id_comp]
    exact a2
  obtain ⟨B1, B2, B3, B4⟩ := pull_birig (Sp ℂ) o.A o'.A f hf o'.P o'.isLB o'.rig₁ o'.rig₂ o'.symm
  have ew : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • Q' (w a)) = e ((k : ℂ)⁻¹ • Q a) ≫ f := by
    intro k a
    rw [hu, ← u.map_smul]
    exact hfe2 _
  have pol := _root_.GlobalTheory.biIso_of_weil o.A D.g o.ab h o.P (o'.P.pull (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left)
    o.isLB o.rig₁ o.rig₂ o.symm B1 B2 B3 B4 e D'.La Q D'.EF he hP.2.1 hk hw (fun k a a₂ c hk0 hc => by
      have W' := hw' k (w a) (w a₂) c hk0 (by rw [hiso]; exact hc)
      rw [ew, ew] at W'
      exact weil_pull_iso (Sp ℂ) o.A o'.A F inferInstance o'.P o'.isLB _ k _ _ _ W')
  exact ⟨{ φ := f.left
           φ₂ := (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left
           cart := isGrpPullback_of_iso F
           sq := ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
           act := fun c => by rw [← Over.comp_left, hact c, Over.comp_left]
           pol := pol
           eta := heta }⟩

end GlobalTheory.HTIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLev

theorem sFam_down : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) →
    Nonempty (SFam h n (zetaAway n)) := by
  intro h n N hn hN hnN hpow ⟨F⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  obtain ⟨j, hinj, hζ, hfes⟩ := _root_.GlobalTheory.SiegelTor.exists_inclusion_cycAway n N hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨Q⟩ := _root_.GlobalTheory.SiegLev.nonempty_sQuot h n N F j hn hN hnN hζ hfin het
  exact ⟨{
    X := Q.X
    s := Q.s
    smooth := Q.smooth
    qproj := Q.qproj
    univ := Q.univ
    princ := Q.princ
    rep := fun S s' c hred hdense hpr =>
      _root_.GlobalTheory.quotFam_represents h n N F j Q hn hN hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
    inj := fun R _ _ x y s' c hs h₁ h₂ =>
      _root_.GlobalTheory.SiegLev.SQuot.eq_of_siegPB h n N _ _ (zetaAway n) (zetaAway N) F j Q R x y s' c hs h₁ h₂ }⟩

end GlobalTheory.SiegLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCoker
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory
namespace DetIndexPadic

theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {x}) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span {x} = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) x.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [Padic.norm_p_pow]

theorem det_ne_zero_of_finite_coker (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T)
    (hc : Nat.card (T ⧸ LinearMap.range φ) ≠ 0) : LinearMap.det φ ≠ 0 := by
  classical
  set n := Nat.card (T ⧸ LinearMap.range φ)
  have hk : ∀ x : T, ∃ y, φ y = ((n : ℤ_[l])) • x := by
    intro x
    have h0 := card_nsmul_eq_zero' (G := T ⧸ LinearMap.range φ)
      (x := Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, by rw [hy, Nat.cast_smul_eq_nsmul]⟩
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose c hc' using fun i => hk (b i)
  let ψ : T →ₗ[ℤ_[l]] T := b.constr ℤ_[l] c
  have hcomp : φ ∘ₗ ψ = (n : ℤ_[l]) • LinearMap.id := by
    refine b.ext fun i => ?_
    simp [ψ, hc']
  have hd := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, _root_.mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) hd.symm

theorem norm_det_eq_of_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ),
    Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  intro l _ T _ _ _ _ φ a hcard
  classical
  have hl := (Fact.out : l.Prime)
  have hdet : LinearMap.det φ ≠ 0 := det_ne_zero_of_finite_coker l φ
    (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  set N := LinearMap.range φ with hN
  let e : T ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis ℤ_[l] T
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] T := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[l]] N := b'.equiv cb (Equiv.refl _)
  let f : T →ₗ[ℤ_[l]] T := N.subtype ∘ₗ (e' : T →ₗ[ℤ_[l]] N)
  have hc : ∀ i, f (b' i) = c i • b' i := by
    intro i
    have : f (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : T →ₗ[ℤ_[l]] N) = φ := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det φ) (LinearMap.det f) at hass
  rw [h1] at hass
  have hcq : Nat.card (T ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  have hne : ∏ i, c i ≠ 0 := fun h0 => hdet (hass.eq_zero_iff.2 h0)
  obtain ⟨u, hu⟩ := hass
  have h2 : ‖LinearMap.det φ‖ = ‖∏ i, c i‖ := by
    rw [← hu, norm_mul, PadicInt.norm_units, _root_.mul_one]
  have h3 : ‖∏ i, c i‖ = ‖((Nat.card (T ⧸ N) : ℕ) : ℚ_[l])‖ := by
    rw [hcq, Nat.cast_prod, norm_prod, norm_prod]
    exact Finset.prod_congr rfl fun i hi =>
      (norm_card_quot_span l (Finset.prod_ne_zero_iff.1 hne i hi)).symm
  rw [h2, h3, hcard]
  push_cast
  rw [Padic.norm_p_pow]

end DetIndexPadic
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMulIsoUniformisationGenericFibreOneConStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedMulIso_uniformisation_genericFibre_one_constant : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (N : ℕ) (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![𝟙 A.A.left, (mulA A.A N).left] ![(N : ℤ) ^ 2, -1])), α.IsGen → ∀ (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (mulA G N).left] ![(N : ℤ) ^ 2, -1])), β.IsGen → ∃ c : FractionRing V, c ≠ 0 ∧ ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ ((Over.pullback (jK V)).obj G).left), r ≫ ((Over.pullback (jK V)).obj G).hom = 𝟙 _ → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (val β (r ≫ pullback.fst G.hom (jK V)) z JG).val = GlobalTheory.UT.cst (FractionRing V) z c * (GlobalTheory.TorsFrameInt.wv w₀ r z JG JA ^ ((N : ℤ) ^ 2) * (GlobalTheory.TorsFrameInt.wv w₀ (r ≫ (mulA ((Over.pullback (jK V)).obj G) N).left) z JG JA)⁻¹ * val α (r ≫ U.gen.hom.left) z JA).val := by
  first | exact @GlobalTheory.GenericMove.move_one_const | exact GlobalTheory.GenericMove.move_one_const | (intros; apply GlobalTheory.GenericMove.move_one_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundary
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.CocExt

theorem sm_comp {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (x : Pt X D)
    (h : Sm W x) : Sm W (D := E) (spOver ψ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun z _ ↦ ?_⟩
  have := hi (Set.mem_univ ((spOver ψ).left.base z))
  simpa [Over.comp_left, Scheme.Hom.comp_base, Scheme.Hom.comp_apply] using this

theorem cocycle_extends : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  intro R _ X K W hW u hu
  choose σ hσ using GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover R X K W hW u hu
  have uniq : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D) (d d' : D),
      (∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        Sm W (D := E) (spOver ψ ≫ y) → ψ d = ψ d') → d = d' := by
    intro D _ _ y d d' h
    obtain ⟨e, -, he⟩ := GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D y (fun E _ _ ψ ↦ ψ d) (fun _ _ _ _ _ _ _ _ _ ↦ rfl)
    exact (he d (fun _ _ _ _ _ ↦ rfl)).trans (he d' (fun E _ _ ψ hψ ↦ h E ψ hψ)).symm
  have hA : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D),
      ∃ d : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E),
        Sm W (D := E) (spOver ψ ≫ spOver φ ≫ x) →
          σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ = ψ d := by
    intro D _ _ D' _ _ φ x
    refine (GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D' (spOver φ ≫ x)
      (fun E _ _ ψ ↦ σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ) ?_).exists
    intro E _ _ E' _ _ ψ θ hψ
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    have h1 := hσ D x E E' (ψ.comp φ) θ (by rw [← e]; exact hψ)
    have h2 := hσ D' (spOver φ ≫ x) E E' ψ θ hψ
    rw [← e] at h1
    simp only [map_sub]
    rw [show (θ.comp ψ).comp φ = θ.comp (ψ.comp φ) from rfl]
    linear_combination h1 - h2
  choose u' hu' using hA
  refine ⟨u', ?_, ?_⟩
  · intro D _ _ D' _ _ D'' _ _ φ ψ x _
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    apply uniq D'' (spOver (ψ.comp φ) ≫ x)
    intro E _ _ ρ hρ
    have h2 : Sm W (D := E) (spOver (ρ.comp ψ) ≫ spOver φ ≫ x) := by
      rw [← spOver_comp, Category.assoc, e]; exact hρ
    have h3 : Sm W (D := E) (spOver ρ ≫ spOver ψ ≫ spOver φ ≫ x) := by rw [e]; exact hρ
    rw [map_add (f := _), ← AlgHom.comp_apply, ← hu' D D'' (ψ.comp φ) x E ρ hρ, ← hu' D D' φ x E (ρ.comp ψ) h2,
      ← hu' D' D'' ψ (spOver φ ≫ x) E ρ h3, e]
    rw [show (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) from rfl]
    ring
  · refine ⟨fun D _ _ x ↦ σ D x D (AlgHom.id R D), ?_⟩
    intro D _ _ D' _ _ φ x hx
    have hx' : Sm W (D := D) (spOver (AlgHom.id R D) ≫ x) := by
      simpa only [spOver_id, Category.id_comp] using hx
    have h1 := hσ D x D D' (AlgHom.id R D) φ hx'
    rw [spOver_id, Category.id_comp, AlgHom.comp_id] at h1
    have hφx : Sm W (D := D') (spOver (AlgHom.id R D') ≫ spOver φ ≫ x) := by
      simpa only [spOver_id, Category.id_comp] using sm_comp φ x hx
    have h2 := hu' D D' φ x D' (AlgHom.id R D') hφx
    rw [AlgHom.id_comp, AlgHom.id_apply] at h2
    show u D D' φ x + -u' D D' φ x = _
    linear_combination h2 - h1

end GlobalTheory.PtExt.CocExt
end
end

