module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFpqcDesc

open GlobalTheory.SiegPBDescent GlobalTheory.SiegelPullComp

variable {h n : ℕ} {B B' B₁ : Type} [CommRing B] [CommRing B'] [CommRing B₁] {ζ' : B'} {ζ₁ : B₁}
  {T T₁ : Scheme.{0}} {s₁ : T₁ ⟶ Sp B₁}

theorem siegPB_id_of_fpqc (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} (c : SiegPre h n ζ' sc)
    (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (p : T₁ ⟶ T) [Flat p] [QuasiCompact p] [Surjective p]
    (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SiegPB c₁ c p) (k : SiegPB c₁ u p) : SiegPB c u (𝟙 T) := by
  obtain ⟨φ₁, hm⟩ := exists_of_siegPB m
  obtain ⟨ψ₁, hk⟩ := exists_of_siegPB k
  obtain ⟨φ₁₂, hφ, sq₁, iso₁, lev₁⟩ := (sRelBy_one_iff _ _ _ _).1 hm
  obtain ⟨ψ₁₂, hψ, sq₂, iso₂, lev₂⟩ := (sRelBy_one_iff _ _ _ _).1 hk
  have : Epi p := Flat.epi_of_flat_of_surjective p
  have : Flat φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Surjective φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : QuasiCompact φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Flat ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : Surjective ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : QuasiCompact ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : EffectiveEpi φ₁ := inferInstance
  have : EffectiveEpi ψ₁ := inferInstance
  let φ := EffectiveEpi.desc φ₁ ψ₁ (comp_eq_of_comp_eq b hn ho hu hm hk)
  have hφψ : φ₁ ≫ φ = ψ₁ := EffectiveEpi.fac _ _ _
  have w : φ ≫ u.A.hom = c.A.hom := by
    rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψ.1.w, hφ.1.w]
  have : Mono φ := mono_of_fac hφ.1 hψ.1 hφψ w
  let ψ := EffectiveEpi.desc ψ₁ φ₁ (fun g₁ g₂ e => by
    rw [← cancel_mono φ, Category.assoc, Category.assoc, hφψ]; exact e)
  have hψφ : ψ₁ ≫ ψ = φ₁ := EffectiveEpi.fac _ _ _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψφ, Category.comp_id],
    by rw [← cancel_epi ψ₁, ← Category.assoc, hψφ, hφψ, Category.comp_id]⟩
  have gp : IsGrpPullback c.A u.A (𝟙 T) φ :=
    GlobalTheory.ObjDescent.isGrpPullback_id hφ hψ φ hφψ (w.trans (Category.comp_id _).symm)
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 T ≫ (u.lev a).left := fun a => by
    rw [Category.id_comp, ← cancel_epi p, ← Category.assoc, ← lev₁ a, Category.assoc, hφψ, lev₂ a]
  have he : eSec (G2 c.A) ≫ φ₂ = eSec (G2 u.A) := by
    have e₀ : eSec c.A ≫ φ = 𝟙 _ ≫ eSec u.A := (cubeMapOf gp).e_comm
    rw [Category.id_comp] at e₀
    apply pullback.hom_ext
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (fst u.A u.A).left = eSec (G2 u.A) ≫ (fst u.A u.A).left
      rw [Category.assoc, sq.1, ← Category.assoc, eSec_fst, eSec_fst, e₀]
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (snd u.A u.A).left = eSec (G2 u.A) ≫ (snd u.A u.A).left
      rw [Category.assoc, sq.2, ← Category.assoc, eSec_snd, eSec_snd, e₀]
  have hiso : LBIso c.P (u.P.pull φ₂) := by
    have h₁ := c.isLB
    have h₂ := pull_isLB u.isLB φ₂
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ₂ (CechPic.cls _ u.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have hsq := GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 sq₁
    have e₂ : φ₁₂ ≫ φ₂ = ψ₁₂ := GlobalTheory.SiegDesc.isSquare_comp hφψ sq₁ sq sq₂
    have cl₁ : CechPic.cls c₁.P c₁.isLB = CechPic.pull φ₁₂ (CechPic.cls c.P c.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB c.isLB _)).2 iso₁
    have cl₂ : CechPic.cls c₁.P c₁.isLB = CechPic.pull ψ₁₂ (CechPic.cls u.P u.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB u.isLB _)).2 iso₂
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns T T₁ p (G2 c.A) _
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) hN inferInstance inferInstance inferInstance
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have cls_eSec {R : Type} [CommRing R] {ζ : R} {S : Scheme.{0}} {s : S ⟶ Sp R}
          (v : SiegPre h n ζ s) : CechPic.pull (eSec (G2 v.A)) (CechPic.cls v.P v.isLB) = 0 := by
        obtain ⟨t, ht⟩ := v.rig₁
        have z := (CechPic.cls_eq_zero_iff (pull_isLB v.isLB _)).2 ⟨t, ht⟩
        rw [CechPic.cls_pull v.isLB] at z
        rw [← eSec_sq, CechPic.pull_comp, z, map_zero]
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, he, cls_eSec u, cls_eSec c, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← hsq.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp, e₂,
        ← cl₂, ← cl₁, sub_self, map_zero]
  exact siegPB_of ((sRelBy_one_iff _ _ _ _).2 ⟨φ₂, gp, sq, hiso, lev⟩)

theorem siegPB_of_fpqc_cover (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁)
    (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y) (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal)
    [Flat p] [QuasiCompact p] [Surjective p] (m : SiegPB c₁ c p) (k : SiegPB c₁ u (p ≫ f)) : SiegPB c u f := by
  obtain ⟨⟨u', hu'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h n B (b.ζ : B) Y S sY (f ≫ sY) f u rfl
  have k' : SiegPB c₁ u' p := pb_cancel hu' k
  have e := pb_comp hu' (siegPB_id_of_fpqc b c u' c₁ p hn ho (hpr u' hu' hu) m k')
  rwa [Category.id_comp] at e

theorem classified_of_faithfullyFlat : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R R').comp β)), SiegPB c' c (spMap (algebraMap R R')) → ∃ f : Sp R' ⟶ F.X, f ≫ F.s = spMap ((algebraMap R R').comp β) ∧ SiegPB c' F.univ f) → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F R R' _ _ _ _ β c _ H
  have hn0 : n ≠ 0 := by omega
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have : Flat π := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective π := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : QuasiCompact π := inferInstance
  have hcomp : π ≫ spMap β = spMap ((algebraMap R R').comp β) := by
    simp only [π, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R) (Sp R') (spMap β)
    (spMap ((algebraMap R R').comp β)) π c hcomp
  obtain ⟨f', hf's, hf'⟩ := H c' hc'
  have hagree : pullback.fst π π ≫ f' = pullback.snd π π ≫ f' := by
    obtain ⟨⟨c₁, hc₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R') (pullback π π)
      (spMap ((algebraMap R R').comp β)) (pullback.fst π π ≫ spMap ((algebraMap R R').comp β))
      (pullback.fst π π) c' rfl
    have a₁ : SiegPB c₁ F.univ (pullback.fst π π ≫ f') := pb_comp hf' hc₁
    have b₁ : SiegPB c₁ c (pullback.fst π π ≫ π) := pb_comp hc' hc₁
    rw [pullback.condition] at b₁
    have b₂ : SiegPB c₁ c' (pullback.snd π π) := pb_cancel hc' b₁
    have a₂ : SiegPB c₁ F.univ (pullback.snd π π ≫ f') := pb_comp hf' b₂
    refine _root_.GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn ho F _ _ c₁ _ _ (by rw [Category.assoc, hf's]) ?_ a₁ a₂
    rw [Category.assoc, hf's, ← hcomp, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : IsRegularEpi π := isRegularEpi_of_flat_of_surjective_of_isAffine π
  let f := EffectiveEpi.desc π f' (fun g₁ g₂ e => by
    have := congrArg (pullback.lift g₁ g₂ e ≫ ·) hagree
    rwa [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] at this)
  have hf : π ≫ f = f' := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨f, ?_, ?_⟩
  · rw [← cancel_epi π, ← Category.assoc, hf, hf's, hcomp]
  · exact siegPB_of_fpqc_cover g n (cycAway n) (cycBase hn0) (Sp R) (Sp R') F.X (spMap β) _ F.s c c' F.univ π f
      hn ho F.princ hc' (by rw [hf]; exact hf')

end GlobalTheory.SiegFpqcDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem comp_eq_of_pair : ∀ (h n : ℕ) (B B' B₁ B₂ : Type) [CommRing B] [CommRing B'] [CommRing B₁] [CommRing B₂] (b : TBase B n) (ζ' : B') (ζ₁ : B₁) (ζ₂ : B₂) (T T₁ T₂ : Scheme.{0}) (sc : T ⟶ Sp B') (su : T ⟶ Sp B) (s₁ : T₁ ⟶ Sp B₁) (s₂ : T₂ ⟶ Sp B₂) (c : SiegPre h n ζ' sc) (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (c₂ : SiegPre h n ζ₂ s₂) (p₁ : T₁ ⟶ T) (p₂ : T₂ ⟶ T) (φ₁ : c₁.A.left ⟶ c.A.left) (ψ₁ : c₁.A.left ⟶ u.A.left) (φ₂ : c₂.A.left ⟶ c.A.left) (ψ₂ : c₂.A.left ⟶ u.A.left), 3 ≤ n → Odd n → u.Principal → SRelBy c₁ c 1 1 p₁ φ₁ → SRelBy c₁ u 1 1 p₁ ψ₁ → SRelBy c₂ c 1 1 p₂ φ₂ → SRelBy c₂ u 1 1 p₂ ψ₂ → ∀ (Z : Scheme.{0}) (g₁ : Z ⟶ c₁.A.left) (g₂ : Z ⟶ c₂.A.left), g₁ ≫ φ₁ = g₂ ≫ φ₂ → g₁ ≫ ψ₁ = g₂ ≫ ψ₂ := by
  intro h n B B' B₁ B₂ _ _ _ _ b ζ' ζ₁ ζ₂ T T₁ T₂ sc su s₁ s₂ c u c₁ c₂ p₁ p₂ φ₁ ψ₁ φ₂ ψ₂ hn ho hu m₁ k₁ m₂ k₂ Z g₁ g₂ e
  obtain ⟨-, hφ₁, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₁
  obtain ⟨-, hφ₂, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₂
  have hz : (g₁ ≫ c₁.A.hom) ≫ p₁ = (g₂ ≫ c₂.A.hom) ≫ p₂ := by
    rw [Category.assoc, Category.assoc, ← hφ₁.1.w, ← hφ₂.1.w, reassoc_of% e]
  obtain ⟨⟨o, ho'⟩, -⟩ := GlobalTheory.siegPre_pullback h n B₁ ζ₁ T₁ Z s₁ ((g₁ ≫ c₁.A.hom) ≫ s₁) (g₁ ≫ c₁.A.hom) c₁ rfl
  obtain ⟨κ, hκ⟩ := exists_of_siegPB ho'
  have a₁ := comp_by m₁ hκ
  rw [hz] at a₁
  obtain ⟨κ', hκ', hκ'b⟩ := cancel_by m₂ a₁
  have n₁ := comp_by k₁ hκ
  have n₂ := comp_by k₂ hκ'b
  rw [← hz] at n₂
  have r := GlobalTheory.SiegRigid.eq_of_sRelBy h n n 1 B B₁ b ζ₁ T Z su _ u o _ _ _ hn ho hu n₁ n₂
  obtain ⟨-, hκg, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ
  obtain ⟨-, hκ'g, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ'b
  have hl : g₁ ≫ c₁.A.hom = 𝟙 Z ≫ g₁ ≫ c₁.A.hom := (Category.id_comp _).symm
  have h₁ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ = g₁ := hκg.1.lift_fst _ _ _
  have h₀ : hκg.1.lift g₁ (𝟙 Z) hl ≫ o.A.hom = 𝟙 Z := hκg.1.lift_snd _ _ _
  have h₂ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' = g₂ := by
    apply hφ₂.1.hom_ext
    · rw [Category.assoc, hκ', ← Category.assoc, h₁, e]
    · rw [Category.assoc, hκ'g.1.w, ← Category.assoc, h₀, Category.id_comp]
  calc g₁ ≫ ψ₁ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ ≫ ψ₁ := by rw [← Category.assoc, h₁]
    _ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' ≫ ψ₂ := by rw [r]
    _ = g₂ ≫ ψ₂ := by rw [← Category.assoc, h₂]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem isPullback_of_sRelBy {h n : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S}
    {φ : c'.A.left ⟶ c.A.left} (m : SRelBy c' c 1 1 f φ) : IsPullback φ c'.A.hom c.A.hom f :=
  ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1.1

theorem iso_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n (b.ζ : B) su), 3 ≤ n → Odd n → u.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV u j) → ∃ φ : c.A.left ⟶ u.A.left, IsIso φ ∧ φ ≫ u.A.hom = c.A.hom ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ) := by
  intro g n B B' _ _ b ζ' S sc su c u hn ho hu hloc
  choose V j cV hj hx m k using hloc
  choose φV hm using fun x => exists_of_siegPB (m x)
  choose ψV hk using fun x => exists_of_siegPB (k x)
  have pφ : ∀ x, IsPullback (φV x) (cV x).A.hom c.A.hom (j x) := fun x => isPullback_of_sRelBy (hm x)
  have pψ : ∀ x, IsPullback (ψV x) (cV x).A.hom u.A.hom (j x) := fun x => isPullback_of_sRelBy (hk x)
  have oφ : ∀ x, IsOpenImmersion (φV x) := fun x => MorphismProperty.of_isPullback (pφ x).flip (hj x)
  have oψ : ∀ x, IsOpenImmersion (ψV x) := fun x => MorphismProperty.of_isPullback (pψ x).flip (hj x)
  let 𝒰 : c.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) φV
    (fun a => ⟨c.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pφ (c.A.hom a)) a).2 (hx _)⟩) oφ
  let 𝒰' : u.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) ψV
    (fun a => ⟨u.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pψ (u.A.hom a)) a).2 (hx _)⟩) oψ
  have pair := fun x y => comp_eq_of_pair g n B B' B' B' b ζ' ζ' ζ' S (V x) (V y) sc su (j x ≫ sc) (j y ≫ sc) c u
    (cV x) (cV y) (j x) (j y) (φV x) (ψV x) (φV y) (ψV y) hn ho hu (hm x) (hk x) (hm y) (hk y)
  have compat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ ψV x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ ψV y :=
    fun x y => pair x y _ _ _ pullback.condition
  let φ := 𝒰.glueMorphisms ψV compat
  have hφ : ∀ x, φV x ≫ φ = ψV x := fun x => 𝒰.ι_glueMorphisms ψV compat x
  have hw : φ ≫ u.A.hom = c.A.hom := by
    refine 𝒰.hom_ext _ _ fun x => ?_
    show φV x ≫ φ ≫ u.A.hom = φV x ≫ c.A.hom
    rw [reassoc_of% (hφ x), (pψ x).w, (pφ x).w]
  have key : ∀ x y (Z : Scheme.{0}) (g₁ : Z ⟶ (cV x).A.left) (g₂ : Z ⟶ (cV y).A.left),
      g₁ ≫ ψV x = g₂ ≫ ψV y → g₁ ≫ φV x = g₂ ≫ φV y := by
    intro x y Z g₁ g₂ e
    have e₁ : (g₁ ≫ φV x) ≫ c.A.hom = (g₂ ≫ (cV y).A.hom) ≫ j y := by
      calc (g₁ ≫ φV x) ≫ c.A.hom = g₁ ≫ φV x ≫ φ ≫ u.A.hom := by rw [hw, Category.assoc]
        _ = g₁ ≫ ψV x ≫ u.A.hom := by rw [reassoc_of% (hφ x)]
        _ = g₂ ≫ ψV y ≫ u.A.hom := by rw [reassoc_of% e]
        _ = _ := by rw [(pψ y).w, Category.assoc]
    let t := (pφ y).lift (g₁ ≫ φV x) (g₂ ≫ (cV y).A.hom) e₁
    have t₁ : t ≫ φV y = g₁ ≫ φV x := (pφ y).lift_fst _ _ _
    have t₂ : t ≫ (cV y).A.hom = g₂ ≫ (cV y).A.hom := (pφ y).lift_snd _ _ _
    have t₃ : t ≫ ψV y = g₁ ≫ ψV x := pair y x _ t g₁ t₁
    have tg : t = g₂ := (pψ y).hom_ext (t₃.trans e) t₂
    rw [← t₁, tg]
  have compat' : ∀ x y, pullback.fst (𝒰'.f x) (𝒰'.f y) ≫ φV x = pullback.snd (𝒰'.f x) (𝒰'.f y) ≫ φV y :=
    fun x y => key x y _ _ _ pullback.condition
  let ψ := 𝒰'.glueMorphisms φV compat'
  have hψ : ∀ x, ψV x ≫ ψ = φV x := fun x => 𝒰'.ι_glueMorphisms φV compat' x
  have i₁ : φ ≫ ψ = 𝟙 _ := 𝒰.hom_ext _ _ fun x => by
    show φV x ≫ φ ≫ ψ = φV x ≫ 𝟙 _
    rw [reassoc_of% (hφ x), hψ x, Category.comp_id]
  have i₂ : ψ ≫ φ = 𝟙 _ := 𝒰'.hom_ext _ _ fun x => by
    show ψV x ≫ ψ ≫ φ = ψV x ≫ 𝟙 _
    rw [reassoc_of% (hψ x), hφ x, Category.comp_id]
  exact ⟨φ, ⟨ψ, i₁, i₂⟩, hw, fun x => ⟨V x, j x, cV x, φV x, hj x, hx x, hm x, by rw [hφ x]; exact hk x⟩⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem siegPB_id_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n ζ su) (φ : c.A.left ⟶ u.A.left), IsIso φ → φ ≫ u.A.hom = c.A.hom → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ)) → SiegPB c u (𝟙 S) := by
  intro g n B B' _ _ ζ ζ' S sc su c u φ hi hw hloc
  have gp : IsGrpPullback c.A u.A (𝟙 S) φ := GlobalTheory.GrpLoc.isGrpPullback_local_on_base S c.A u.A φ hi hw fun p => by
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    exact ⟨V, j, cV.A, inferInstance, φV, hj, hx, ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1,
      ((sRelBy_one_iff _ _ _ _).1 k).choose_spec.1⟩
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 S ≫ (u.lev a).left := fun a => by
    refine GlobalTheory.GrpLoc.hom_ext_loc fun p => ?_
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    obtain ⟨-, -, -, -, lm⟩ := (sRelBy_one_iff _ _ _ _).1 m
    obtain ⟨-, -, -, -, lk⟩ := (sRelBy_one_iff _ _ _ _).1 k
    refine ⟨V, j, hj, hx, ?_⟩
    rw [Category.id_comp, ← reassoc_of% (lm a), ← lk a]
  have gp₂ : IsGrpPullback (G2 c.A) (G2 u.A) (𝟙 S) φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor gp gp sq.1 sq.2
  have rig (d : SiegPre g n ζ' sc) : Out.Rigidified (G2 d.A) d.P := by
    have he : eSec d.A ≫ (lift (1 : d.A ⟶ d.A) (𝟙 d.A)).left = eSec (G2 d.A) := by
      unfold eSec
      rw [← Over.comp_left]
      congr 1
      ext <;> simp [Hom.one_def]
    have z := (CechPic.cls_eq_zero_iff (pull_isLB d.isLB _)).2 d.rig₁
    rw [CechPic.cls_pull d.isLB] at z
    apply (CechPic.cls_eq_zero_iff (pull_isLB d.isLB _)).1
    rw [CechPic.cls_pull d.isLB, ← he, CechPic.pull_comp, z, map_zero]
  have rL : Out.Rigidified (G2 c.A) c.P := rig c
  have rL' : Out.Rigidified (G2 u.A) u.P := by
    have he : eSec u.A ≫ (lift (1 : u.A ⟶ u.A) (𝟙 u.A)).left = eSec (G2 u.A) := by
      unfold eSec
      rw [← Over.comp_left]
      congr 1
      ext <;> simp [Hom.one_def]
    have z := (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).2 u.rig₁
    rw [CechPic.cls_pull u.isLB] at z
    apply (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).1
    rw [CechPic.cls_pull u.isLB, ← he, CechPic.pull_comp, z, map_zero]
  have hiso : LBIso c.P (u.P.pull φ₂) :=
    GlobalTheory.RigidLocal.lbIso_of_local GlobalTheory.abelianSchemeLaws_all.1.globalFns S (G2 c.A) (G2 u.A) c.P u.P φ₂
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) c.isLB u.isLB rL rL' gp₂ fun p => by
        obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
        obtain ⟨φV₂, gm, sm, im, -⟩ := (sRelBy_one_iff _ _ _ _).1 m
        obtain ⟨ψV₂, -, sk, ik, -⟩ := (sRelBy_one_iff _ _ _ _).1 k
        have e₂ : φV₂ ≫ φ₂ = ψV₂ := GlobalTheory.SiegDesc.isSquare_comp rfl sm sq sk
        refine ⟨V, (G2 cV.A).left, j, (G2 cV.A).hom, φV₂, hj, hx, GlobalTheory.SiegDesc.isPullback_of_isSquare gm.1 sm, ?_⟩
        rw [e₂]
        exact im.symm.trans (pull_isLB c.isLB _) cV.isLB (pull_isLB u.isLB _) ik
  exact ⟨φ, φ₂, gp, sq, hiso, lev⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem glue_classifying : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV F.univ (j ≫ f) := by
  intro g n hg hn ho F S s' c hloc
  choose V j cV hj hx m f hfs hpb using hloc
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S V j (fun x => ⟨x, hx x⟩) hj
  have key : ∀ x y, pullback.fst (j x) (j y) ≫ f x = pullback.snd (j x) (j y) ≫ f y := by
    intro x y
    obtain ⟨⟨cP, hcP⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (pullback (j x) (j y)) s'
      (pullback.fst (j x) (j y) ≫ j x ≫ s') (pullback.fst (j x) (j y) ≫ j x) c (Category.assoc _ _ _)
    have hcP' : SiegPB cP c (pullback.snd (j x) (j y) ≫ j y) := by rw [← pullback.condition]; exact hcP
    have h₁ := pb_comp (hpb x) (pb_cancel (m x) hcP)
    have h₂ := pb_comp (hpb y) (pb_cancel (m y) hcP')
    refine GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn ho F _ _ cP _ _ ?_ ?_ h₁ h₂
    · rw [Category.assoc, hfs x]
    · rw [Category.assoc, hfs y, pullback.condition_assoc]
  let φ := 𝒰.glueMorphisms f key
  have hφ : ∀ x, j x ≫ φ = f x := fun x => 𝒰.ι_glueMorphisms f key x
  refine ⟨φ, 𝒰.hom_ext _ _ fun x => ?_, fun x => ⟨V x, j x, cV x, hj x, hx x, m x, by rw [hφ x]; exact hpb x⟩⟩
  show j x ≫ φ ≫ F.s = j x ≫ s'
  rw [reassoc_of% (hφ x), hfs x]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem classified_of_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F S s' c _ hloc
  obtain ⟨f, hf, hl⟩ := glue_classifying g n hg hn ho F S s' c hloc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨⟨u, hu⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X S F.s (f ≫ F.s) f F.univ rfl
  have hup : u.Principal := hpr u hu F.princ
  obtain ⟨φ, hi, hw, hφ⟩ := iso_of_local g n (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) S s' (f ≫ F.s) c u
    hn ho hup fun x => by
      obtain ⟨V, j, cV, hj, hx, h₁, h₂⟩ := hl x
      exact ⟨V, j, cV, hj, hx, h₁, pb_cancel hu h₂⟩
  have e := pb_comp hu (siegPB_id_of_local g n (cycAway n) (cycAway n) _ (zetaAway n) S s' (f ≫ F.s) c u φ hi hw hφ)
  rw [Category.id_comp] at e
  exact ⟨f, hf, e⟩

end GlobalTheory.SiegZar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegLev

section
variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h n ζ s}
  {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {d d' d'' : ℕ}

theorem sRel_trans (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c d' d f) (e : ℕ) : SRel c' c (d' * e) (d * e) f :=
  (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.2 e

end

theorem spMap_id_eq (o : Type) [CommRing o] : spMap (RingHom.id o) = 𝟙 _ := Spec.map_id _

theorem sFam_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N →
    Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  intro h n N o _ _ b hn hN hnN ⟨F⟩
  set ζ : o := (b.ζ : o) ^ (N / n)

  obtain ⟨c₀, h₀₁, h₀₂⟩ := (_root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) F.X F.X (F.s ≫ spMap (RingHom.id o)) F.s (𝟙 _) rfl
    (by simp)).2.2 F.univ
  have r₀₁ : SRel F.univ c₀ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₁
  have r₀₂ : SRel c₀ F.univ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₂
  have p₀ : c₀.Principal := sRel_principal r₀₂ F.princ
  obtain ⟨S₁, π, C, hfin, het, hsurj, hlow, huniv⟩ :=
    _root_.GlobalTheory.SiegCover.exists_levelCover h n N o o ζ b (RingHom.id o) F.X F.s c₀ hn hN hnN rfl p₀
  have hN0 : N ≠ 0 := hN.pos.ne'
  have pC : C.Principal := sRel_principal hlow p₀
  refine ⟨{
    X := S₁
    s := π ≫ F.s
    smooth := by
      haveI := F.smooth
      have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
      rwa [zero_add] at this
    qproj := _root_.GlobalTheory.isQProjOver_comp_of_isFinite_noetherian o _ _ π F.s hfin F.qproj
    univ := C
    princ := pC
    rep := ?_
    inj := ?_ }⟩
  · intro T s' c hred hdense hp
    obtain ⟨cl, hcl1, hcl2⟩ := _root_.GlobalTheory.SiegLower.exists_lower h n N o o ζ (b.ζ : o) (RingHom.id o) T s' c hN0 b.unit hnN rfl
    have pl : cl.Principal := sRel_principal hcl2 hp
    obtain ⟨f, hf, hfp⟩ := F.rep T (s' ≫ spMap (RingHom.id o)) cl hred
      (by rw [spMap_id_eq, Category.comp_id]; exact hdense) pl
    rw [spMap_id_eq, Category.comp_id] at hf
    subst hf
    have r1 : SRel c F.univ (N / n) 1 (𝟙 _ ≫ f) := sRel_trans ((sRel_one_one_iff _ _ _).2 hfp) hcl1
    have r2 : SRel c c₀ (N / n) 1 ((𝟙 _ ≫ f) ≫ 𝟙 _) := sRel_trans r₀₁ r1
    obtain ⟨t₁, ⟨ht₁, hC⟩, -⟩ := huniv T f c (by simpa using r2)
    exact ⟨t₁, by rw [← Category.assoc, ht₁], hC⟩
  · intro R _ _ x y s' c hxy hx hy
    have rx : SRel c C 1 1 x := (sRel_one_one_iff _ _ _).2 hx
    have ry : SRel c C 1 1 y := (sRel_one_one_iff _ _ _).2 hy
    have kx : SRel c c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale rx (N / n))
    have ky : SRel c c₀ (N / n) 1 (y ≫ π) := sRel_trans hlow (by simpa using sRel_scale ry (N / n))

    obtain ⟨cx, hcx⟩ := (_root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) F.X (Sp R) (F.s ≫ spMap (RingHom.id o))
      ((x ≫ π) ≫ F.s) (x ≫ π) rfl (by simp)).1 c₀
    have e1 : SRel cx c₀ 1 1 (x ≫ π) := (sRel_one_one_iff _ _ _).2 hcx
    have e2 : SRel cx c 1 (N / n) (𝟙 _) := sRel_cancel (f' := 𝟙 _) kx (by simpa using e1)
    have e3 : SRel cx c₀ 1 1 (𝟙 _ ≫ y ≫ π) := sRel_trans ky e2
    have fx : SiegPB cx F.univ (x ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e1)
    have fy : SiegPB cx F.univ (y ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e3)
    have hπ : x ≫ π = y ≫ π := F.inj R (x ≫ π) (y ≫ π) _ cx (by simpa using hxy) fx fy

    obtain ⟨Cx, hCx⟩ := (_root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h N o o (b.ζ : o) (b.ζ : o) (RingHom.id o) S₁ (Sp R) (π ≫ F.s)
      ((x ≫ π) ≫ F.s) x rfl (by rw [spMap_id_eq]; simp)).1 C
    have g1 : SRel Cx C 1 1 x := (sRel_one_one_iff _ _ _).2 hCx
    have g2 : SRel Cx c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale g1 (N / n))
    have g3 : SRel Cx c 1 1 (𝟙 _) := sRel_cancel (f' := 𝟙 _) rx (by simpa using g1)
    have g4 : SiegPB Cx C y := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans ry g3)
    exact (huniv (Sp R) (x ≫ π) Cx g2).unique ⟨rfl, hCx⟩ ⟨hπ.symm, g4⟩

end GlobalTheory.SiegLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickening
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_lifts_over_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hsm
  obtain ⟨C₀, _, _, i, r, hstd, hri⟩ := _root_.GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth R₀ B₀ hsm
  obtain ⟨C, _, _, p', hs', hp', hker', hC⟩ := _root_.GlobalTheory.Obs.standardSmooth_lift_of_sqZero R R₀ I hI π hπ hk C₀ hstd
  exact _root_.GlobalTheory.Obs.retractLift R R₀ I hI π hπ hk C C₀ p' hs' hp' hker' B₀ i r hri

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  first | exact @GlobalTheory.UPoinc.qk_lattice_oAct | exact GlobalTheory.UPoinc.qk_lattice_oAct | (intros; apply GlobalTheory.UPoinc.qk_lattice_oAct <;> assumption)
end

