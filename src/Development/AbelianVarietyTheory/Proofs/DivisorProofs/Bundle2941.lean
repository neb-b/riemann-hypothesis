module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ImgPB

@[reassoc]
theorem tensorHom_fst_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (fst Y W).left = (fst X Z).left ≫ f.left := by
  rw [← Over.comp_left, tensorHom_fst, Over.comp_left]

@[reassoc]
theorem tensorHom_snd_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (snd Y W).left = (snd X Z).left ≫ h.left := by
  rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem image_idem_pullback : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  intro S' T g A G _ _ _ _ inc pr ε A' G' _ _ _ _ inc' pr' ε' ψ ψ₂ hinc hpr hip hpi hinc' hpr' hip' hpi' hψ hsq hεψ
  have hε' : inc' ≫ ε' = inc' := by rw [← hpi', ← Category.assoc, hip', Category.id_comp]
  have key : inc'.left ≫ ψ = inc'.left ≫ ψ ≫ pr.left ≫ inc.left := by
    rw [← Over.comp_left, hpi, ← hεψ, ← Category.assoc, ← Over.comp_left, hε']
  have hipl : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hip]; rfl
  have hipl' : inc'.left ≫ pr'.left = 𝟙 _ := by rw [← Over.comp_left, hip']; rfl
  have e2' : inc ≫ ε ≫ pr = 𝟙 G := by rw [← hpi, Category.assoc, reassoc_of% hip, hip]
  have e2 : inc.left ≫ ε.left ≫ pr.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.comp_left, e2']; rfl
  have e1 : pr'.left ≫ inc'.left ≫ ψ ≫ pr.left = ψ ≫ ε.left ≫ pr.left := by
    rw [← Category.assoc, ← Over.comp_left, hpi', ← Category.assoc, hεψ, Category.assoc]
  have hψp := hψ.1
  refine ⟨inc'.left ≫ ψ ≫ pr.left, (inc' ⊗ₘ inc').left ≫ ψ₂ ≫ (pr ⊗ₘ pr).left, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    key.trans (by simp only [Category.assoc]), ?_⟩
  · have w : (inc'.left ≫ ψ ≫ pr.left) ≫ G.hom = G'.hom ≫ g := by
      rw [Category.assoc, Category.assoc, Over.w pr, hψp.w, ← Category.assoc, Over.w inc']
    refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk _
      (fun s => hψp.lift (s.fst ≫ inc.left) s.snd (by rw [Category.assoc, Over.w inc]; exact s.condition) ≫ pr'.left)
      ?_ ?_ ?_)
    · intro s
      simp only [Category.assoc]
      rw [e1, hψp.lift_fst_assoc, Category.assoc, e2, Category.comp_id]
    · intro s
      rw [Category.assoc, Over.w pr', hψp.lift_snd]
    · intro s m hm1 hm2
      have hm : m ≫ inc'.left = hψp.lift (s.fst ≫ inc.left) s.snd
          (by rw [Category.assoc, Over.w inc]; exact s.condition) := by
        apply hψp.hom_ext
        · rw [hψp.lift_fst, ← hm1, Category.assoc, key]
          simp only [Category.assoc]
        · rw [hψp.lift_snd, Category.assoc, Over.w inc', hm2]
      calc m = m ≫ inc'.left ≫ pr'.left := by rw [hipl', Category.comp_id]
        _ = _ := by rw [← Category.assoc, hm]
  · intro U x y x₀ y₀ hx hy
    have h1 : (x₀ ≫ inc).left = (x ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hx, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have h2 : (y₀ ≫ inc).left = (y ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hy, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have hm := hψ.2 U (x ≫ inc') (y ≫ inc') (x₀ ≫ inc) (y₀ ≫ inc) h1 h2
    calc (x₀ * y₀).left = ((x₀ * y₀) ≫ inc).left ≫ pr.left := by
          rw [Over.comp_left, Category.assoc, hipl, Category.comp_id]
      _ = ((x * y) ≫ inc').left ≫ ψ ≫ pr.left := by
          rw [MonObj.mul_comp, MonObj.mul_comp, hm, Category.assoc]
      _ = _ := by rw [Over.comp_left, Category.assoc]
  · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, tensorHom_fst_left_assoc]
  · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, tensorHom_snd_left_assoc]
  · apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
    · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, hsq.1, tensorHom_fst_left_assoc]
      rw [← key]
    · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, hsq.2, tensorHom_snd_left_assoc]
      rw [← key]

end GlobalTheory.ImgPB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem zRel_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hS hZ
  obtain ⟨ψ, ψ₂, hψ, sqψ, hwP, hwl, hact⟩ := hA
  obtain ⟨φ, φ₂, hφ, sqφ, hcP, hcl⟩ := hS
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, hP₁, hl₁, hz₁⟩ := hZ
  haveI := mi₁
  haveI := mp₁
  have wi : (φ ≫ inc₁.left) ≫ w₁.A.hom = c₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w inc₁]; exact hφ.1.w
  let inc₂ : c₂.A ⟶ w₂.A := Over.homMk (hψ.1.lift (φ ≫ inc₁.left) c₂.A.hom wi) (hψ.1.lift_snd _ _ _)
  have inc₂_l : inc₂.left ≫ ψ = φ ≫ inc₁.left := hψ.1.lift_fst _ _ _
  have wp : (ψ ≫ pr₁.left) ≫ c₁.A.hom = w₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w pr₁]; exact hψ.1.w
  let pr₂ : w₂.A ⟶ c₂.A := Over.homMk (hφ.1.lift (ψ ≫ pr₁.left) w₂.A.hom wp) (hφ.1.lift_snd _ _ _)
  have pr₂_l : pr₂.left ≫ φ = ψ ≫ pr₁.left := hφ.1.lift_fst _ _ _
  have extW : ∀ {T : Over S₂} (a b : T ⟶ w₂.A), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hψ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have extC : ∀ {T : Over S₂} (a b : T ⟶ c₂.A), a.left ≫ φ = b.left ≫ φ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hφ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have pI : ∀ (T : Over S₂) (x : T ⟶ c₂.A), pushHom hψ T (x ≫ inc₂) = pushHom hφ T x ≫ inc₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ inc₂).left ≫ ψ = (x.left ≫ φ) ≫ inc₁.left
      rw [Over.comp_left, Category.assoc, inc₂_l, Category.assoc])
  have pP : ∀ (T : Over S₂) (x : T ⟶ w₂.A), pushHom hφ T (x ≫ pr₂) = pushHom hψ T x ≫ pr₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ pr₂).left ≫ φ = (x.left ≫ ψ) ≫ pr₁.left
      rw [Over.comp_left, Category.assoc, pr₂_l, Category.assoc])
  have mI : IsMonHom inc₂ := isMonHom_of_mul _ fun T x z => extW _ _ (congrArg (fun q => q.left)
    (calc pushHom hψ T ((x * z) ≫ inc₂) = pushHom hφ T (x * z) ≫ inc₁ := pI _ _
      _ = (pushHom hφ T x * pushHom hφ T z) ≫ inc₁ := by rw [map_mul]
      _ = (pushHom hφ T x ≫ inc₁) * (pushHom hφ T z ≫ inc₁) := MonObj.mul_comp _ _ _
      _ = pushHom hψ T (x ≫ inc₂) * pushHom hψ T (z ≫ inc₂) := by rw [pI, pI]
      _ = pushHom hψ T ((x ≫ inc₂) * (z ≫ inc₂)) := (map_mul _ _ _).symm))
  have mP : IsMonHom pr₂ := isMonHom_of_mul _ fun T x z => extC _ _ (congrArg (fun q => q.left)
    (calc pushHom hφ T ((x * z) ≫ pr₂) = pushHom hψ T (x * z) ≫ pr₁ := pP _ _
      _ = (pushHom hψ T x * pushHom hψ T z) ≫ pr₁ := by rw [map_mul]
      _ = (pushHom hψ T x ≫ pr₁) * (pushHom hψ T z ≫ pr₁) := MonObj.mul_comp _ _ _
      _ = pushHom hφ T (x ≫ pr₂) * pushHom hφ T (z ≫ pr₂) := by rw [pP, pP]
      _ = pushHom hφ T ((x ≫ pr₂) * (z ≫ pr₂)) := (map_mul _ _ _).symm))
  have h1 : inc₂ ≫ pr₂ = 𝟙 c₂.A := extC _ _ (by
    rw [Over.comp_left, Over.id_left, Category.assoc, pr₂_l, ← Category.assoc, inc₂_l, Category.assoc,
      ← Over.comp_left, ip₁, Over.id_left, Category.comp_id, Category.id_comp])
  have h2 : pr₂ ≫ inc₂ = act₂ e := extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, pr₂_l, Category.assoc, ← Over.comp_left, pi₁,
      hact])
  have eι : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = φ₂ ≫ (inc₁ ⊗ₘ inc₁).left := by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, sqψ.1, ← Category.assoc, ← Over.comp_left, tensorHom_fst, Category.assoc, ← Over.comp_left,
        tensorHom_fst, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.1,
        Category.assoc]
    · rw [Category.assoc, sqψ.2, ← Category.assoc, ← Over.comp_left, tensorHom_snd, Category.assoc, ← Over.comp_left,
        tensorHom_snd, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.2,
        Category.assoc]
  have P1 : LBIso (c₁.P.pull φ₂) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c₁.P φ₂ φ₂ rfl)
      (chartPullSame w₁.P _ (fun _ => (inc₁ ⊗ₘ inc₁).left) _ φ₂ fun _ => rfl) hP₁
  have P2 : LBIso (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull w₂.P (inc₂ ⊗ₘ inc₂).left (inc₂ ⊗ₘ inc₂).left rfl)
      (chartPullSame w₁.P _ (fun _ => ψ₂) _ (inc₂ ⊗ₘ inc₂).left fun _ => eι.symm) hwP
  have hP₂ : LBIso c₂.P (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) :=
    LBIso.trans c₂.isLB (pull_isLB c₁.isLB _) (pull_isLB w₂.isLB _) hcP
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB w₁.isLB _) (pull_isLB w₂.isLB _) P1 P2.symm)
  have lv : ∀ a, c₂.lev a ≫ inc₂ = w₂.lev (jl a) := fun a => extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, hcl, Category.assoc, ← Over.comp_left, hl₁, hwl])
  let T₀ : Over S₂ := 𝟙_ (Over S₂)
  let u : Over.mk (T₀.hom ≫ y) ⟶ 𝟙_ (Over S₁) := toUnit _
  have hu : u.left = y := by
    simp [u, T₀]
  have pL : ∀ a, pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := fun a => Over.OverMorphism.ext (by
    show (w₂.lev a).left ≫ ψ = u.left ≫ (w₁.lev a).left
    rw [hu, hwl])
  have pT : ∀ (b : Fin h ⊕ Fin h → ℤ) (r : O), pushHom hψ T₀ (c₂.lev b ≫ inc₂ ≫ act₂ r) =
      u ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r) := fun b r => Over.OverMorphism.ext (by
    show (c₂.lev b ≫ inc₂ ≫ act₂ r).left ≫ ψ = u.left ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r).left
    simp only [Over.comp_left, Category.assoc]
    rw [hact, reassoc_of% inc₂_l, reassoc_of% (hcl b), hu])
  have lz : ∀ a, w₂.lev a = (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := fun a =>
    extW _ _ (congrArg (fun q => q.left)
      (calc pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := pL a
        _ = preHom (G := w₁.A) u (List.ofFn fun k => c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)).prod := by
          rw [hz₁ a]; rfl
        _ = (List.ofFn fun k => u ≫ (c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl
        _ = (List.ofFn fun k => pushHom hψ T₀ (c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k))).prod := by
          simp only [pT]
        _ = pushHom hψ T₀ (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl))
  exact ⟨inc₂, pr₂, mI, mP, h1, h2, hP₂, lv, lz⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteClassBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.ClassCount


end GlobalTheory.ClassCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntClosureAutExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem intClosure_aut_extends : ∀ (o₁ Ω₁ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (z₁ : M₁.Z), letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ σ : (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[M₁.Z.presheaf.stalk z₁] (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂), ∃ σ' : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, σ' (b : Ω₂) = ((σ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : Ω₂) := by
  intro o₁ Ω₁ _ _ _ Ω₂ _ _ _ M₁ z₁ σ
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₁ := (M₁.stalkHom z₁).toAlgebra
  haveI : IsDomain (M₁.Z.presheaf.stalk z₁) := (M₁.stalkHom_injective z₁).isDomain _
  haveI : FaithfulSMul (M₁.Z.presheaf.stalk z₁) Ω₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M₁.stalkHom_injective z₁)
  haveI : IsFractionRing (M₁.Z.presheaf.stalk z₁) Ω₁ := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M₁.O z₁) x
    refine ⟨(M₁.stalkEquiv z₁).symm a, (M₁.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : M₁.O z₁, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₁ ((M₁.stalkEquiv z₁).symm c) = c := fun c => by
      change M₁.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic Ω₁ Ω₂ := inferInstance
  refine ⟨(galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ, fun b => ?_⟩
  have := algebraMap_galRestrict_apply (M₁.Z.presheaf.stalk z₁)
    ((galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ) b
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZe
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

namespace GlobalTheory.InvCoefUniq

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem valR_coef_eq_zero [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ a, IsInv G (v a) (dd a)) {W : G.left.Opens} (hW : IsAffineOpen W) (c : Fin n → Γ(G.left, W))
    (hc : ∀ f, ∑ a, c a * dd a W f = 0) (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W)
    (a : Fin n) : valR g W (c a) = 0 := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ G.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S ⟶ G := Over.homMk g hφ
  let s : Fin n → S := fun b => valR g W (c b)
  obtain ⟨u, hb, hu⟩ := GlobalTheory.HeatMod.TorField.exists_isLieBasis v
  let e : Fin n → DualNumber S := fun b => inr (s b)
  have he : ∀ i j, e i * e j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have a₃ : ∀ x, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x =
      inl (valR g W x) := a₂
  have key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0 := fun f => by
    have := congrArg (valR g W) (hc f)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s] using this
  have hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) *
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z := by
    refine Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)
    refine (b₂ f).trans ?_
    rw [add_eq_left]
    simp only [a₃, e]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum] using key f
  have h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1 := mul_eq_right.1 hP
  have h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1 :=
    GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _
  have hJ := GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S
  have hz := ((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0)
    (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _)
    (h1.trans h0.symm)
  have := congrArg TrivSqZeroExt.snd (congrFun hz a)
  simpa [e, s] using this

theorem coef_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  intro R _ G _ _ hs n v dd hd W c hc a
  haveI := hs
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2)
    ?_ (c a) 0 fun W' => ?_
  · intro x hx
    obtain ⟨W', hW', hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩
  · rw [GlobalTheory.KS.rsT_zero]
    exact GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg =>
      valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a

end GlobalTheory.InvCoefUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldPullbackAlongGroupHom
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

namespace GlobalTheory.Heat.PullField

theorem isInv_pbT_single : ∀ (R : Type) [CommRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) (u : TanM (𝟙 (Sp R)) B) (dd : Fld G.left) (e : Fld B.left), tv v ≫ q = tv u → IsInv G v dd → IsInv B u e → ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V), dd W (pbT q.left f W) = pbT q.left (e V f) W := by
  intro R _ G B _ _ _ _ q _ v u dd e hvu hd he V W hW f
  have hc : GlobalTheory.Heat.LiePush.pushL q v = ∑ a : Fin 1, (fun _ => (1 : R)) a • (fun _ => u) a := by
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext hvu
  rw [GlobalTheory.Heat.LiePush.isInv_pbT q hd (fun _ => he) (fun _ => 1) hc V f W hW]
  congr 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp [constFn]

end GlobalTheory.Heat.PullField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetract
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isAbelianScheme_of_retract_of_isSemiAbelian : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  intro S A G _ _ _ _ inc pr hA hG _ _ h
  have hApr : IsProper A.hom := hA.proper
  have hsep : IsSeparated G.hom := hG.separated
  have hpr : IsSeparated pr.left := by
    have e : pr.left ≫ G.hom = A.hom := Over.w pr
    have : IsSeparated (pr.left ≫ G.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp pr.left G.hom
  have hid : inc.left ≫ pr.left = 𝟙 G.left := by rw [← Over.comp_left, h, Over.id_left]
  have hci : IsClosedImmersion inc.left := by
    have : IsClosedImmersion (inc.left ≫ pr.left) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp inc.left pr.left
  refine ⟨hG.comm, hG.smooth, ?_, hG.geomConnected⟩
  have e : inc.left ≫ A.hom = G.hom := Over.w inc
  rw [← e]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory

theorem isClosed_singleton_of_isFinite : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ x : X,
    IsClosed ({f x} : Set Z) → IsClosed ({x} : Set X) := by
  intro X Z f hf x hx
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : f w = f x := (h.map f.continuous).mem_closed hx rfl
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hs : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representingScheme_of_finite_surjective_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (B S' : Over (Sp R)) (b : B ⟶ S') (P : LB (A ⊗ B).left), IsFinite S'.hom → Surjective S'.hom → Rep A b P → GlobalTheory.DualCon.Good g b.left → (∀ x : B.left, LiftAt A g b P x) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_of_liftAt | exact GlobalTheory.DualCon.hasRep_of_liftAt | (intros; apply GlobalTheory.DualCon.hasRep_of_liftAt <;> assumption)
end

