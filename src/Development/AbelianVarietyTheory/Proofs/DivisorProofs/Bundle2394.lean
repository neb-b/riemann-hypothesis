module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.SiegelPullComp
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegPBDescent

variable {h n : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem sRelBy_one_iff (c' : SiegPre h n ζ' s') (c : SiegPre h n ζ s) (f : S' ⟶ S) (φ : c'.A.left ⟶ c.A.left) :
    SRelBy c' c 1 1 f φ ↔ ∃ φ₂, IsGrpPullback c'.A c.A f φ ∧ IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂) ∧
      ∀ a, (c'.lev a).left ≫ φ = f ≫ (c.lev a).left := by
  simp only [SRelBy, pow_one]
  exact ⟨fun ⟨x, ⟨ψ, y, z⟩, w⟩ => ⟨ψ, x, y, z, w⟩, fun ⟨ψ, x, y, z, w⟩ => ⟨x, ⟨ψ, y, z⟩, w⟩⟩

theorem exists_of_siegPB {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S} (m : SiegPB c' c f) :
    ∃ φ, SRelBy c' c 1 1 f φ :=
  (sRel_one_one_iff c' c f).2 m

theorem siegPB_of {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S} {φ} (m : SRelBy c' c 1 1 f φ) :
    SiegPB c' c f :=
  (sRel_one_one_iff c' c f).1 ⟨φ, m⟩

theorem comp_by {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : SRelBy c' c 1 1 f φ)
    (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  rw [sRelBy_one_iff] at m m' ⊢
  obtain ⟨φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ₂, hψ, hs', hw', hl'⟩ := m'
  refine ⟨ψ₂ ≫ φ₂, hψ.comp hφ, ⟨?_, ?_⟩, ?_, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem cancel_by {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {χ : c''.A.left ⟶ c.A.left} (m : SRelBy c' c 1 1 f φ)
    (n : SRelBy c'' c 1 1 (f' ≫ f) χ) : ∃ F, F ≫ φ = χ ∧ SRelBy c'' c' 1 1 f' F := by
  rw [sRelBy_one_iff] at m n
  obtain ⟨φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨χ₂, hχ, hs', hw', hl'⟩ := n
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hF, (sRelBy_one_iff _ _ _ _).2 ⟨F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a).left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a)
      have a₂ : (c'.lev a).left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem eSec_sq {X : Scheme.{0}} (A : Over X) [GrpObj A] :
    eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec (A ⊗ A) := by
  unfold eSec
  rw [← Over.comp_left]
  congr 1
  ext <;> simp [Hom.one_def]

theorem cls_eSec (c : SiegPre h n ζ s) : CechPic.pull (eSec (G2 c.A)) (CechPic.cls c.P c.isLB) = 0 := by
  obtain ⟨t, ht⟩ := c.rig₁
  have z := (CechPic.cls_eq_zero_iff (pull_isLB c.isLB _)).2 ⟨t, ht⟩
  rw [CechPic.cls_pull c.isLB] at z
  rw [← eSec_sq, CechPic.pull_comp, z, map_zero]

theorem eSec_fst {X : Scheme.{0}} (A : Over X) [GrpObj A] : eSec (A ⊗ A) ≫ (fst A A).left = eSec A := by
  unfold eSec
  rw [← Over.comp_left]
  congr 1
  simp

theorem eSec_snd {X : Scheme.{0}} (A : Over X) [GrpObj A] : eSec (A ⊗ A) ≫ (snd A A).left = eSec A := by
  unfold eSec
  rw [← Over.comp_left]
  congr 1
  simp

theorem mono_of_fac {T T₁ : Scheme.{0}} {G G' : Over T} {G₁ : Over T₁} [GrpObj G] [GrpObj G₁] {p : T₁ ⟶ T} [Flat p]
    [Surjective p] {φ₁ : G₁.left ⟶ G.left} {ψ₁ : G₁.left ⟶ G'.left} {φ : G.left ⟶ G'.left}
    (hφ : IsPullback φ₁ G₁.hom G.hom p) (hψ : IsPullback ψ₁ G₁.hom G'.hom p) (e : φ₁ ≫ φ = ψ₁)
    (w : φ ≫ G'.hom = G.hom) : Mono φ := by
  constructor
  intro W a b hab
  have hw : a ≫ G.hom = b ≫ G.hom := by rw [← w, ← Category.assoc, hab, Category.assoc]
  have : Epi (pullback.fst (a ≫ G.hom) p) := Flat.epi_of_flat_of_surjective _
  have ca : (pullback.fst (a ≫ G.hom) p ≫ a) ≫ G.hom = pullback.snd (a ≫ G.hom) p ≫ p := by
    rw [Category.assoc, pullback.condition]
  have cb : (pullback.fst (a ≫ G.hom) p ≫ b) ≫ G.hom = pullback.snd (a ≫ G.hom) p ≫ p := by
    rw [Category.assoc, ← hw, pullback.condition]
  have eq : hφ.lift _ _ ca = hφ.lift _ _ cb := by
    apply hψ.hom_ext
    · rw [← e, ← Category.assoc, ← Category.assoc, hφ.lift_fst, hφ.lift_fst, Category.assoc, Category.assoc, hab]
    · rw [hφ.lift_snd, hφ.lift_snd]
  rw [← cancel_epi (pullback.fst (a ≫ G.hom) p), ← hφ.lift_fst _ _ ca, ← hφ.lift_fst _ _ cb, eq]

section Core

variable {T T₁ : Scheme.{0}} {B₁ : Type} [CommRing B₁] {ζ₁ : B₁} {s₁ : T₁ ⟶ Sp B₁}

theorem comp_eq_of_comp_eq (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} {c : SiegPre h n ζ' sc}
    {u : SiegPre h n (b.ζ : B) su} {c₁ : SiegPre h n ζ₁ s₁} {p : T₁ ⟶ T} {φ₁ : c₁.A.left ⟶ c.A.left}
    {ψ₁ : c₁.A.left ⟶ u.A.left} (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SRelBy c₁ c 1 1 p φ₁)
    (k : SRelBy c₁ u 1 1 p ψ₁) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ c₁.A.left) (e : g₁ ≫ φ₁ = g₂ ≫ φ₁) :
    g₁ ≫ ψ₁ = g₂ ≫ ψ₁ := by
  obtain ⟨-, hφ, -⟩ := (sRelBy_one_iff _ _ _ _).1 m
  have hz : (g₁ ≫ c₁.A.hom) ≫ p = (g₂ ≫ c₁.A.hom) ≫ p := by
    rw [Category.assoc, Category.assoc, ← hφ.1.w, ← Category.assoc, e, Category.assoc]
  obtain ⟨⟨o, ho'⟩, -⟩ := GlobalTheory.siegPre_pullback h n B₁ ζ₁ T₁ Z s₁ ((g₁ ≫ c₁.A.hom) ≫ s₁) (g₁ ≫ c₁.A.hom) c₁ rfl
  obtain ⟨κ, hκ⟩ := exists_of_siegPB ho'
  have k₁ := comp_by m hκ
  rw [hz] at k₁
  obtain ⟨κ', hκ', hκ'b⟩ := cancel_by m k₁
  have n₁ := comp_by k hκ
  have n₂ := comp_by k hκ'b
  rw [← hz] at n₂
  have r := _root_.GlobalTheory.SiegRigid.eq_of_sRelBy h n n 1 B B₁ b ζ₁ T Z su _ u o _ _ _ hn ho hu n₁ n₂
  obtain ⟨-, hκg, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ
  obtain ⟨-, hκ'g, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ'b
  have hl : g₁ ≫ c₁.A.hom = 𝟙 Z ≫ g₁ ≫ c₁.A.hom := (Category.id_comp _).symm
  have h₁ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ = g₁ := hκg.1.lift_fst _ _ _
  have h₀ : hκg.1.lift g₁ (𝟙 Z) hl ≫ o.A.hom = 𝟙 Z := hκg.1.lift_snd _ _ _
  have h₂ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' = g₂ := by
    apply hφ.1.hom_ext
    · rw [Category.assoc, hκ', ← Category.assoc, h₁, e]
    · rw [Category.assoc, hκ'g.1.w, ← Category.assoc, h₀, Category.id_comp]
  calc g₁ ≫ ψ₁ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ ≫ ψ₁ := by rw [← Category.assoc, h₁]
    _ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' ≫ ψ₁ := by rw [r]
    _ = g₂ ≫ ψ₁ := by rw [← Category.assoc, h₂]

theorem siegPB_id_of_cover (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} (c : SiegPre h n ζ' sc)
    (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (p : T₁ ⟶ T) [IsFinite p] [Etale p] [Surjective p]
    (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SiegPB c₁ c p) (k : SiegPB c₁ u p) : SiegPB c u (𝟙 T) := by
  obtain ⟨φ₁, hm⟩ := exists_of_siegPB m
  obtain ⟨ψ₁, hk⟩ := exists_of_siegPB k
  obtain ⟨φ₁₂, hφ, sq₁, iso₁, lev₁⟩ := (sRelBy_one_iff _ _ _ _).1 hm
  obtain ⟨ψ₁₂, hψ, sq₂, iso₂, lev₂⟩ := (sRelBy_one_iff _ _ _ _).1 hk
  have : QuasiCompact p := inferInstance
  have : Flat p := inferInstance
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
    · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, he, cls_eSec u, cls_eSec c, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← hsq.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp, e₂,
        ← cl₂, ← cl₁, sub_self, map_zero]
  exact siegPB_of ((sRelBy_one_iff _ _ _ _).2 ⟨φ₂, gp, sq, hiso, lev⟩)

end Core

end GlobalTheory.SiegPBDescent

namespace GlobalTheory

theorem siegPB_of_finite_etale_cover : ∀ (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁) (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y), 3 ≤ n → Odd n → u.Principal → IsFinite p → Etale p → Surjective p → SiegPB c₁ c p → SiegPB c₁ u (p ≫ f) → SiegPB c u f := by
  intro h n B _ b S S₁ Y s s₁ sY c c₁ u p f hn ho hu _ _ _ m k
  obtain ⟨⟨u', hu'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h n B (b.ζ : B) Y S sY (f ≫ sY) f u rfl
  have k' : SiegPB c₁ u' p := SiegelPullComp.pb_cancel hu' k
  have e := SiegelPullComp.pb_comp hu' (SiegPBDescent.siegPB_id_of_cover b c u' c₁ p hn ho (hpr u' hu' hu) m k')
  rwa [Category.id_comp] at e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigidCyc

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_pullback : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  intro h M hM S S' s s' c o f hamp φ ψ φ₂ ψ₂ g q w l g' q' w' l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have hMu : IsUnit ((M : ℕ) : cycAway M) := isUnit_natCast (show M ≠ 0 by omega)
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (M : K) ≠ 0 := by
      have hu := hMu.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hamp hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hM hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ M = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (GlobalTheory.LowChart.isUnit_zetaAway M hM) c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigidCyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAbove
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_add_le_of_mul_le (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_A_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField),
    P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
    P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hD P b s t hG ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := fun a c R =>
    _root_.GlobalTheory.VolBr.BallFinite.bl_finite hHS k X p D hD P b s t hG a c R hAC
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := _root_.GlobalTheory.VolBr.Pair.isBallFam k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.VolBr.crude_upper_lc hHS hAC k X p D hD P b s t hG
  obtain ⟨δ, hδ, hrad⟩ := _root_.GlobalTheory.VolBr.log_ncard_ball_exp_le X.functionField (fun N => P.H (N : ℤ) 0) (fun N => P.Bl (N : ℤ) 0) (D + 1)
    (Nat.succ_pos D) (fun N => hball N 0) (fun N R => hfin N 0 R) C0 hC0 (ε / 3) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := _root_.GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow k X p D hD P s hG.s_mem.1 hG.s_ne (δ / 2) (by positivity)
  have hdA := GlobalTheory.T.smallSectionCount_nearPowers_le hHS hAC k X p D hD P b s t hG (ε / 3) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, (2 * C + 2) / δ ≤ (n : ℝ) ∧ 1 ≤ n :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and (eventually_ge_atTop 1)
  filter_upwards [hdA, hn] with n hdAn hnn
  obtain ⟨hnC, hn1⟩ := hnn
  have htend : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn1) tendsto_id
  filter_upwards [hdAn, htend.eventually hrad, eventually_ge_atTop 1] with m hdm hradm hm1
  have hnδ : 2 * C + 2 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1

  have hrad_le : 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)
        ≤ Real.exp 1 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 + (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hnδ (by linarith : (0 : ℝ) ≤ m)]
  have hSsub : {f | f ∈ P.H (n * m : ℕ) 0 ∧ f * s ^ m ∈ P.Bl (n * m : ℕ) m 2} ⊆
      P.Bl (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv (n * m) m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := _root_.GlobalTheory.VolBr.encard_mul_le_at_level k X p D hD P b s t hG (n * m) m (hfin _ _ _)
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  norm_cast at hlev
  have hkey := log_add_le_of_mul_le _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one) hlev
    (Set.ncard_le_ncard hSsub hEfin)
  have hX : (0 : ℝ) ≤ ((n : ℝ) * m) ^ (D + 1) := by positivity
  have hX3 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 3) hX
  simp only [Pair.lc] at hdm ⊢
  push_cast at hradm hkey hdm ⊢
  linarith

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartCover_toTerm {S : Scheme.{0}} {A : Over S} (f : A ⟶ Over.mk (𝟙 S)) :
    f = Over.homMk A.hom (by simp) := by
  ext1
  simpa using Over.w f

theorem comp_transl {S : Scheme.{0}} {G A : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) (h : A ⟶ G) :
    h ≫ transl y = h * (Over.homMk A.hom (by simp) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  exact chartCover_toTerm _

theorem chart_cover : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G']
    (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')),
    (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨
      ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) →
    ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  intro R _ _ S π G' _ N n x H p
  let t : Sp (G'.left.residueField p) ⟶ G'.left := G'.left.fromSpecResidueField p
  let s : Sp (G'.left.residueField p) ⟶ S := t ≫ G'.hom
  let g : Over.mk s ⟶ G' := Over.homMk t rfl
  have hp : g.left (IsLocalRing.closedPoint _) = p := Scheme.fromSpecResidueField_apply p _
  rcases H (G'.left.residueField p) s g with h1 | ⟨i, h2⟩
  · exact ⟨none, by simpa [Near.chart] using h1 ⟨_, hp⟩⟩
  · let c : Over.mk s ⟶ G' := (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i
    obtain ⟨b, hb⟩ := h2 ⟨IsLocalRing.closedPoint _, rfl⟩
    have key : (g * c) ≫ transl (x i)⁻¹ = g := by
      rw [comp_transl]
      have e : (Over.homMk (Over.mk s).hom (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ (x i)⁻¹ = c⁻¹ := by
        rw [GrpObj.comp_inv]; rfl
      rw [e, mul_inv_cancel_right]
    refine ⟨some i, b, ?_⟩
    rw [Near.chart_some, Scheme.Hom.comp_apply, hb]
    have e2 : ((g * c) ≫ transl (x i)⁻¹).left (IsLocalRing.closedPoint _) = p := by rw [key]; exact hp
    rw [Over.comp_left] at e2
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spMap_field_ext_cancel : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X), spMap io ≫ a = spMap io ≫ b → a = b := by
  first | exact @GlobalTheory.Mum.spMap_field_cancel | exact GlobalTheory.Mum.spMap_field_cancel | (intros; apply GlobalTheory.Mum.spMap_field_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationDirectSummand
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LiftSys.summand_of_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S' hS' hN S
  obtain ⟨N, hN⟩ := hN
  obtain ⟨hinf, hfull⟩ := _root_.GlobalTheory.LiftSys.K_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const S' S
  have hS : S.Full hI := hfull hS'
  have hsup : S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    ext c
    rw [_root_.GlobalTheory.LiftSys.Sys.mem_K_sup_iff R R₀ I hI π hπ hk X₀ s₀ S hρ hS c, _root_.GlobalTheory.LiftSys.Sys.mem_K_sup_iff R R₀ I hI π hπ hk X₀ s₀ S' hρ hS' c]
  exact ⟨⟨N, (_root_.GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero R I hI (Cr hI π s₀) (S'.K hI) (S.K hI) N hN hsup).1 hinf.symm⟩, hsup⟩
end

