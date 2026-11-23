module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegPinch

theorem glue_hom : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Z : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (k₁ : Y₁.left ⟶ Z.left) (k₂ : Y₂.left ⟶ Z.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → Flat Z.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback k₁ Y₁.hom Z.hom (Spec.map f₁) → IsPullback k₂ Y₂.hom Z.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → i₁ ≫ k₁ = i₂ ≫ k₂ → ∃ φ : Y.left ⟶ Z.left, IsPullback φ Y.hom Z.hom (𝟙 _) ∧ j₁ ≫ φ = k₁ ∧ j₂ ≫ φ = k₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Z Y₁ Y₂ Y₀ j₁ j₂ k₁ k₂ i₁ i₂ hY hZ pj₁ pj₂ pk₁ pk₂ pi₁ w₂ ej ek
  have poY := _root_.GlobalTheory.FlatPinch.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hY pj₁ pj₂ pi₁ ej w₂
  have poZ := _root_.GlobalTheory.FlatPinch.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Z Y₁ Y₂ Y₀ k₁ k₂ i₁ i₂ hZ pk₁ pk₂ pi₁ ek w₂
  let φ : Y.left ⟶ Z.left := poY.desc k₁ k₂ ek
  let ψ : Z.left ⟶ Y.left := poZ.desc j₁ j₂ ej
  have h₁ : φ ≫ ψ = 𝟙 _ := poY.hom_ext
    (by rw [← Category.assoc, poY.inl_desc, poZ.inl_desc, Category.comp_id])
    (by rw [← Category.assoc, poY.inr_desc, poZ.inr_desc, Category.comp_id])
  have h₂ : ψ ≫ φ = 𝟙 _ := poZ.hom_ext
    (by rw [← Category.assoc, poZ.inl_desc, poY.inl_desc, Category.comp_id])
    (by rw [← Category.assoc, poZ.inr_desc, poY.inr_desc, Category.comp_id])
  have hw : φ ≫ Z.hom = Y.hom ≫ 𝟙 _ := poY.hom_ext
    (by rw [Category.comp_id, ← Category.assoc, poY.inl_desc, pk₁.w, pj₁.w])
    (by rw [Category.comp_id, ← Category.assoc, poY.inr_desc, pk₂.w, pj₂.w])
  haveI : IsIso φ := ⟨ψ, h₁, h₂⟩
  exact ⟨φ, IsPullback.of_horiz_isIso ⟨hw⟩, poY.inl_desc _ _ _, poY.inr_desc _ _ _⟩

section Tools

variable {h n : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem srelBy_comp {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · simp only [pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sq_ext {S : Scheme.{0}} (A : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem isPullback_sq {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}
    (hp : IsPullback β G'.hom G.hom f) {β₂ : (G2 G').left ⟶ (G2 G).left} (hs : IsSquare β β₂) :
    IsPullback β₂ (G2 G').hom (G2 G).hom f := by
  have e : β₂ = (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left := by
    apply sq_ext
    · rw [hs.1]; exact (congrArg (fun q => q.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))).symm
    · rw [hs.2]; exact (congrArg (fun q => q.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))).symm
  rw [e]
  exact GlobalTheory.Mum.PowCart.isPullback_two hp

theorem sq_comp {G : Over S} {G' : Over S'} {G'' : Over S''} {β : G'.left ⟶ G.left} {β' : G''.left ⟶ G'.left}
    {β₂ : (G2 G').left ⟶ (G2 G).left} {β₂' : (G2 G'').left ⟶ (G2 G').left} (hs : IsSquare β β₂) (hs' : IsSquare β' β₂') :
    IsSquare (β' ≫ β) (β₂' ≫ β₂) :=
  ⟨by rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc],
   by rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]⟩

theorem sq_unique {G : Over S} {G' : Over S'} {β : G'.left ⟶ G.left} {β₂ β₂' : (G2 G').left ⟶ (G2 G).left}
    (hs : IsSquare β β₂) (hs' : IsSquare β β₂') : β₂ = β₂' :=
  sq_ext G (hs.1.trans hs'.1.symm) (hs.2.trans hs'.2.symm)

end Tools

theorem siegPB_of_pinch : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c c' : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c.Principal → c'.Principal → SiegPB c₁ c (Spec.map f₁) → SiegPB c₁ c' (Spec.map f₁) → SiegPB c₂ c (Spec.map f₂) → SiegPB c₂ c' (Spec.map f₂) → SiegPB c' c (𝟙 _) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ β c c' c₁ c₂ hc hc' m₁ m₁' m₂ m₂'
  have hn0 : n ≠ 0 := by omega
  have hbase : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]
  obtain ⟨c₀, m₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Spec R₁) (Spec R₀) (Spec.map f₁ ≫ Spec.map β)
    (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β) (Spec.map g₁) rfl (by simp [spMap])).1 c₁
  have m₀₂ : SiegPB c₀ c₂ (Spec.map g₂) := by
    have := GlobalTheory.SiegelPullComp.pb_comp m₁' m₀
    rw [hbase] at this
    exact GlobalTheory.SiegelPullComp.pb_cancel m₂' this
  obtain ⟨ρ₁, r₁⟩ := (sRel_one_one_iff _ _ _).2 m₀
  obtain ⟨ρ₂, r₂⟩ := (sRel_one_one_iff _ _ _).2 m₀₂
  obtain ⟨ψ₁, q₁⟩ := (sRel_one_one_iff _ _ _).2 m₁
  obtain ⟨ψ₁', q₁'⟩ := (sRel_one_one_iff _ _ _).2 m₁'
  obtain ⟨ψ₂, q₂⟩ := (sRel_one_one_iff _ _ _).2 m₂
  obtain ⟨ψ₂', q₂'⟩ := (sRel_one_one_iff _ _ _).2 m₂'
  have e' : ρ₁ ≫ ψ₁' = ρ₂ ≫ ψ₂' :=
    GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) _ _ _ _ c' c₀ _ _ _
      hn hodd hc' (srelBy_comp q₁' r₁) (by rw [hbase]; exact srelBy_comp q₂' r₂)
  have e : ρ₁ ≫ ψ₁ = ρ₂ ≫ ψ₂ :=
    GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) _ _ _ _ c c₀ _ _ _
      hn hodd hc (srelBy_comp q₁ r₁) (by rw [hbase]; exact srelBy_comp q₂ r₂)
  have hfl : Flat c.A.hom := by have := c.ab.smooth; infer_instance
  have hfl' : Flat c'.A.hom := by have := c'.ab.smooth; infer_instance
  obtain ⟨φ, hφp, hφ₁, hφ₂⟩ := glue_hom P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ c'.A c.A c₁.A c₂.A c₀.A ψ₁' ψ₂' ψ₁ ψ₂
    ρ₁ ρ₂ hfl' hfl q₁'.1.1 q₂'.1.1 q₁.1.1 q₂.1.1 r₁.1.1 r₂.1.1.w e' e
  have hφ : IsGrpPullback c'.A c.A (𝟙 _) φ := _root_.GlobalTheory.PinchHom.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ c'.A c.A c₁.A c₂.A c₀.A
    ψ₁' ψ₂' ψ₁ ψ₂ ρ₁ ρ₂ φ hfl' q₁'.1 q₂'.1 q₁.1 q₂.1 r₁.1 r₂.1 e' hφp hφ₁ hφ₂
  let φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left := (lift (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A))).left
  have sq : IsSquare φ φ₂ := ⟨congrArg (fun q => q.left) (lift_fst (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A))),
    congrArg (fun q => q.left) (lift_snd (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A)))⟩
  refine ⟨φ, φ₂, hφ, sq, ?_, fun a => ?_⟩
  · obtain ⟨χ₁', sχ₁', wχ₁'⟩ := q₁'.2.1
    obtain ⟨χ₁, sχ₁, wχ₁⟩ := q₁.2.1
    obtain ⟨χ₂', sχ₂', wχ₂'⟩ := q₂'.2.1
    obtain ⟨χ₂, sχ₂, wχ₂⟩ := q₂.2.1
    obtain ⟨τ₁, sτ₁, -⟩ := r₁.2.1
    obtain ⟨τ₂, sτ₂, -⟩ := r₂.2.1
    have eτ : τ₁ ≫ χ₁' = τ₂ ≫ χ₂' := by
      have h1 := sq_comp sχ₁' sτ₁
      have h2 := sq_comp sχ₂' sτ₂
      rw [e'] at h1
      exact sq_unique h1 h2
    have eχ₁ : χ₁' ≫ φ₂ = χ₁ := by
      have h1 := sq_comp sq sχ₁'
      rw [hφ₁] at h1
      exact sq_unique h1 sχ₁
    have pχ₁' := isPullback_sq q₁'.1.1 sχ₁'
    have pχ₂' := isPullback_sq q₂'.1.1 sχ₂'
    have pτ₁ := isPullback_sq r₁.1.1 sτ₁
    have pτ₂ := isPullback_sq r₂.1.1 sτ₂
    have hflat2 : Flat (G2 c'.A).hom := by
      have := hfl'
      exact GlobalTheory.ExtUnique.flat_tensorObj c'.A c'.A
    obtain ⟨hpatch, huniq⟩ := _root_.GlobalTheory.PinchUnits.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (G2 c'.A) (G2 c₁.A) (G2 c₂.A) (G2 c₀.A)
      χ₁' χ₂' τ₁ τ₂ hflat2 pχ₁' pχ₂' pτ₁ eτ pτ₂.w
    have hab₀ : IsAbelianScheme (G2 c₀.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ c₀.ab c₀.ab
    have hlift := _root_.GlobalTheory.PinchUnitLift.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (G2 c₀.A) hab₀ (G2 c₁.A).left (G2 c₁.A).hom τ₁ pτ₁.w
    have hL' := c'.isLB
    have hM : (c.P.pull φ₂).IsLB := pull_isLB c.isLB φ₂
    have cech_patching : ∀ {X X₁ X₂ X₀ : Scheme.{0}} (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X) (ρ₁ : X₀ ⟶ X₁) (ρ₂ : X₀ ⟶ X₂), ρ₁ ≫ ι₁ = ρ₂ ≫ ι₂ →
        (∀ u : Γ(X₀, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : X₀, gm ρ₁ x ⊤ v = gm (𝟙 X₀) x ⊤ u) →
        (∀ (U : X.Opens) (a₁ : Γ(X₁, ι₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(X₂, ι₂ ⁻¹ᵁ U)ˣ),
          (∀ x : X₀, ρ₁ x ∈ ι₁ ⁻¹ᵁ U → gm ρ₁ x (ι₁ ⁻¹ᵁ U) a₁ = gm ρ₂ x (ι₂ ⁻¹ᵁ U) a₂) →
          ∃ d : Γ(X, U)ˣ, pullU ι₁ U d = a₁ ∧ pullU ι₂ U d = a₂) →
        (∀ (U : X.Opens) (d d' : Γ(X, U)ˣ), pullU ι₁ U d = pullU ι₁ U d' → pullU ι₂ U d = pullU ι₂ U d' → d = d') →
        ∀ c : GlobalTheory.CechPic.Pic X, GlobalTheory.CechPic.pull ι₁ c = 0 → GlobalTheory.CechPic.pull ι₂ c = 0 → c = 0 := by
      open GlobalTheory.CechPic GlobalTheory.SmallGlue in
        intro X X₁ X₂ X₀ ι₁ ι₂ ρ₁ ρ₂ hsq hlift hpatch huniq c h₁ h₂
        have exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (q : Y ⟶ X)
            (h : GlobalTheory.CechPic.pull q (cls L hL) = 0) :
            ∃ a : ∀ j, Γ(Y, q ⁻¹ᵁ L.U j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : L.ι),
              q (f z) ∈ L.U i → q (f z) ∈ L.U j →
              gm f z (q ⁻¹ᵁ L.U i) (a i) = gm (f ≫ q) z (L.U i ⊓ L.U j) (L.g i j) * gm f z (q ⁻¹ᵁ L.U j) (a j) := by
          obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL q)).1 h
          have le : ∀ j, q ⁻¹ᵁ L.U j ≤ (L.pull q).U (fun _ => j) := fun j y hy => mem_pull.2 hy
          refine ⟨fun j => res (le j) (t.s (fun _ => j)), fun Z f z i j hi hj => ?_⟩
          have hm : f z ∈ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
          have := congrArg (gm f z _) (ht (fun _ => i) (fun _ => j))
          rw [map_mul, gm_res _ z _ hm, gm_res _ z _ hm] at this
          rw [gm_res f z (le i) hi, gm_res f z (le j) hj]
          exact this.trans (congrArg (· * _) (gm_pull_g L q f z (fun _ => i) (fun _ => j) hm.1 hm.2))
        
        have pullU_isGen_of_germ {X Y : Scheme.{0}} {L : LB X} (q : Y ⟶ X) (d : ∀ j, Γ(X, L.U j)ˣ) (i j : L.ι)
            (h : ∀ y : Y, q y ∈ L.U i → q y ∈ L.U j →
              gm (𝟙 Y) y (q ⁻¹ᵁ L.U i) (pullU q _ (d i)) =
                gm (𝟙 Y ≫ q) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (q ⁻¹ᵁ L.U j) (pullU q _ (d j))) :
            pullU q (L.U i ⊓ L.U j) (res inf_le_left (d i)) =
              pullU q (L.U i ⊓ L.U j) (L.g i j * res inf_le_right (d j)) := by
          refine unit_ext fun y hy => ?_
          have hm : q ((𝟙 Y : Y ⟶ Y) y) ∈ L.U i ⊓ L.U j := hy
          have e := h y hm.1 hm.2
          rw [gm_pull (𝟙 Y) q y _ hm.1, gm_pull (𝟙 Y) q y _ hm.2] at e
          rw [gm_pull (𝟙 Y) q y _ hm, gm_pull (𝟙 Y) q y _ hm, map_mul, gm_res (𝟙 Y ≫ q) y _ hm,
            gm_res (𝟙 Y ≫ q) y _ hm]
          exact e
        obtain ⟨L, hL, rfl⟩ := cls_surj c
        obtain ⟨α, hα⟩ := exists_units_of_pull_eq_zero hL ι₁ h₁
        obtain ⟨β, hβ⟩ := exists_units_of_pull_eq_zero hL ι₂ h₂
        have pt : ∀ x : X₀, ι₂ (ρ₂ x) = ι₁ (ρ₁ x) := fun x => congrArg (fun g => g x) hsq.symm
        have le : ∀ j, ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ρ₂ ⁻¹ᵁ (ι₂ ⁻¹ᵁ L.U j) := fun j x hx => by
          show ι₂ (ρ₂ x) ∈ L.U j
          rw [pt]; exact hx
        have hu : ∀ j (x : X₀), ι₁ (ρ₁ x) ∈ L.U j →
            gm (𝟙 X₀) x (ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹) =
              gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ := fun j x hx => by
          rw [map_mul, map_inv, gm_res (𝟙 X₀) x (le j) hx, gm_pull (𝟙 X₀) ρ₁ x _ hx,
            gm_pull (𝟙 X₀) ρ₂ x _ (le j hx), Category.id_comp, Category.id_comp]
        obtain ⟨w, hw⟩ := glue_unit (⊤ : X₀.Opens) (fun j => ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (fun _ => le_top)
          (fun x _ => by
            obtain ⟨j, hj⟩ := exists_chart hL (ι₁ (ρ₁ x))
            exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩)
          (fun j => pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹)
          (fun i j x hx => by
            refine (hu i x hx.1).trans (Eq.trans ?_ (hu j x hx.2).symm)
            rw [hα _ ρ₁ x i j hx.1 hx.2, hβ _ ρ₂ x i j (le i hx.1) (le j hx.2), hsq, mul_inv, _root_.mul_mul_mul_comm,
              mul_inv_cancel, _root_.one_mul])
        obtain ⟨v, hv⟩ := hlift w
        have hd : ∀ j, ∃ d : Γ(X, L.U j)ˣ, pullU ι₁ _ d = α j * (res le_top v)⁻¹ ∧ pullU ι₂ _ d = β j := fun j =>
          hpatch _ _ _ fun x hx => by
            have e : gm (𝟙 X₀) x ⊤ w = gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ :=
              (gm_res (𝟙 X₀) x (le_top : ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ⊤) hx w).symm.trans
                ((congrArg _ (hw j)).trans (hu j x hx))
            rw [map_mul, map_inv, gm_res ρ₁ x _ hx, hv, e, mul_inv, inv_inv, mul_inv_cancel_left]
        choose d hd₁ hd₂ using hd
        refine (cls_eq_zero_iff hL).2 ⟨⟨d⟩, fun i j => huniq _ _ _ ?_ ?_⟩
        · refine pullU_isGen_of_germ ι₁ d i j fun y hi hj => ?_
          rw [hd₁, hd₁, map_mul, map_mul, map_inv, map_inv, gm_res (𝟙 X₁) y _ hi, gm_res (𝟙 X₁) y _ hj,
            hα _ (𝟙 X₁) y i j hi hj, _root_.mul_assoc]
        · refine pullU_isGen_of_germ ι₂ d i j fun y hi hj => ?_
          rw [hd₂, hd₂]
          exact hβ _ (𝟙 X₂) y i j hi hj
    have key := cech_patching χ₁' χ₂' τ₁ τ₂ eτ hlift hpatch huniq
      (GlobalTheory.CechPic.cls c'.P hL' - GlobalTheory.CechPic.cls _ hM) ?_ ?_
    · exact (GlobalTheory.CechPic.cls_eq_iff hL' hM).1 (sub_eq_zero.1 key)
    · rw [map_sub, ← GlobalTheory.CechPic.cls_pull hL' χ₁' (pull_isLB hL' _), ← GlobalTheory.CechPic.cls_pull hM χ₁' (pull_isLB hM _),
        sub_eq_zero, GlobalTheory.CechPic.cls_eq_iff]
      refine LBIso.trans (pull_isLB hL' _) c₁.isLB (pull_isLB hM _) wχ₁'.symm ?_
      refine LBIso.trans c₁.isLB (pull_isLB c.isLB _) (pull_isLB hM _) wχ₁ ?_
      rw [← eχ₁]
      exact (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ χ₁').symm
    · have eχ₂ : χ₂' ≫ φ₂ = χ₂ := by
        have h1 := sq_comp sq sχ₂'
        rw [hφ₂] at h1
        exact sq_unique h1 sχ₂
      rw [map_sub, ← GlobalTheory.CechPic.cls_pull hL' χ₂' (pull_isLB hL' _), ← GlobalTheory.CechPic.cls_pull hM χ₂' (pull_isLB hM _),
        sub_eq_zero, GlobalTheory.CechPic.cls_eq_iff]
      refine LBIso.trans (pull_isLB hL' _) c₂.isLB (pull_isLB hM _) wχ₂'.symm ?_
      refine LBIso.trans c₂.isLB (pull_isLB c.isLB _) (pull_isLB hM _) wχ₂ ?_
      rw [← eχ₂]
      exact (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ χ₂').symm
  · have hpo := _root_.GlobalTheory.FlatPinch.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
      (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂)
      (by dsimp; infer_instance) (IsPullback.id_vert _) (IsPullback.id_vert _) (IsPullback.id_vert _) hbase (by simp)
    rw [Category.id_comp]
    have a₁ := q₁'.2.2 a
    have a₂ := q₁.2.2 a
    have a₃ := q₂'.2.2 a
    have a₄ := q₂.2.2 a
    simp only [pow_one] at a₁ a₂ a₃ a₄
    apply hpo.hom_ext
    · rw [← Category.assoc, ← a₁, Category.assoc, hφ₁, a₂]
    · rw [← Category.assoc, ← a₃, Category.assoc, hφ₂, a₄]

end GlobalTheory.SiegPinch
