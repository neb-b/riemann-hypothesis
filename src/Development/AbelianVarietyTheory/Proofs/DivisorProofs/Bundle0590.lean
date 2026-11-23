module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.EndLoc.ActUnr

section Chart

variable {X Y₁ Y₂ Z W : Scheme.{0}}

def chartPullPullAlong (L : LB X) (a₁ : Y₁ ⟶ X) (a₂ : Z ⟶ Y₁) (c₁ : Y₂ ⟶ X) (c₂ : W ⟶ Y₂) (h : Z ⟶ W)
    (e : a₂ ≫ a₁ = h ≫ c₂ ≫ c₁) : ChartPull ((L.pull a₁).pull a₂) ((L.pull c₁).pull c₂) h where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le J y hy := by
    have h₁ := mem_pull.1 (mem_pull.1 hy)
    have h₂ : (a₂ ≫ a₁) y ∈ L.U (J PUnit.unit PUnit.unit) := by simpa using h₁
    rw [e] at h₂
    exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
  g y J J' hj hj' := by
    have hc : ∀ K : PUnit → PUnit → L.ι, y ∈ ((L.pull a₁).pull a₂).U K →
        h y ∈ ((L.pull c₁).pull c₂).U (fun _ _ => K PUnit.unit PUnit.unit) := fun K hK => by
      have h₁ := mem_pull.1 (mem_pull.1 hK)
      have h₂ : (a₂ ≫ a₁) y ∈ L.U (K PUnit.unit PUnit.unit) := by simpa using h₁
      rw [e] at h₂
      exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
    have l₁ := gm_pull_g (L.pull a₁) a₂ (𝟙 Z) y J J' hj hj'
    rw [Category.id_comp] at l₁
    have l₂ := gm_pull_g L a₁ a₂ y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have l₃ := gm_pull_g (L.pull c₁) c₂ h y (fun _ _ => J PUnit.unit PUnit.unit)
      (fun _ _ => J' PUnit.unit PUnit.unit) (hc J hj) (hc J' hj')
    have l₄ := gm_pull_g L c₁ (h ≫ c₂) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 (hc J hj)) (mem_pull.1 (hc J' hj'))
    rw [l₁, l₂, l₃, l₄, e, Category.assoc]

theorem lbIso_pullPull_along (Q : LB X) (φ₂ : Y₁ ⟶ X) (m₁ m₂ : Y₁ ⟶ Y₁) (φ₂' : Y₂ ⟶ X) (m₁' m₂' : Y₂ ⟶ Y₂)
    (u : Y₂ ⟶ Y₁) (hφ : φ₂' = u ≫ φ₂) (h₁ : m₁' ≫ u = u ≫ m₁) (h₂ : m₂' ≫ u = u ≫ m₂)
    (H : LBIso ((Q.pull φ₂).pull m₁) ((Q.pull φ₂).pull m₂)) :
    LBIso ((Q.pull φ₂').pull m₁') ((Q.pull φ₂').pull m₂') :=
  LBIso.chartPull
    (chartPullPullAlong Q φ₂' m₁' φ₂ m₁ u (by rw [hφ, ← Category.assoc, h₁, Category.assoc]))
    (chartPullPullAlong Q φ₂' m₂' φ₂ m₂ u (by rw [hφ, ← Category.assoc, h₂, Category.assoc])) H

end Chart

section Square

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {B : Over S'} {φ : B.left ⟶ G.left}

def sqMap (w : φ ≫ G.hom = B.hom ≫ f) : (B ⊗ B).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst B B)) (pushPt w (snd B B))).left

theorem sqMap_fst (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (fst G G).left = (fst B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_fst (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem sqMap_snd (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (snd G G).left = (snd B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_snd (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem left_hom_ext {H Z : Scheme.{0}} {G : Over H} {x y : Z ⟶ (G ⊗ G).left}
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) : x = y := by
  have hw : y ≫ (G ⊗ G).hom = x ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← h1, Category.assoc]
  let x' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk x rfl
  let y' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk y hw
  have : x' = y' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h1) (Over.OverMorphism.ext h2)
  exact congrArg (fun t => t.left) this

theorem lift_left_comp_sqMap (w : φ ≫ G.hom = B.hom ≫ f) (x' y' : B ⊗ B ⟶ B) (x y : G ⊗ G ⟶ G)
    (hx : x'.left ≫ φ = sqMap w ≫ x.left) (hy : y'.left ≫ φ = sqMap w ≫ y.left) :
    (lift x' y').left ≫ sqMap w = sqMap w ≫ (lift x y).left := by
  apply left_hom_ext
  · rw [Category.assoc, sqMap_fst, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, sqMap_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc,
      ← Over.comp_left, lift_snd]

end Square

section Act

variable {O : Type} [Ring O]

theorem isRAct_pullback {H T : Scheme.{0}} (g : T ⟶ H) (AH : Over H) [GrpObj AH] (act : O → (AH ⟶ AH))
    (h : IsRAct AH act) : IsRAct ((Over.pullback g).obj AH) (fun a => (Over.pullback g).map (act a)) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · dsimp only
    rw [h.2.1]
    exact (Over.pullback g).map_id _
  · dsimp only
    rw [h.2.2.1, Functor.map_comp]
  · dsimp only
    rw [h.2.2.2, Functor.map_mul]

theorem isRAct_conj {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (e : B ≅ C) [IsMonHom e.hom]
    (act : O → (C ⟶ C)) (h : IsRAct C act) : IsRAct B (fun a => e.hom ≫ act a ≫ e.inv) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · simp only [h.2.1, Category.id_comp, Iso.hom_inv_id]
  · simp only [h.2.2.1, Category.assoc, Iso.inv_hom_id_assoc]
  · dsimp only
    rw [h.2.2.2, MonObj.mul_comp, MonObj.comp_mul]

theorem adj_along {H T : Scheme.{0}} {AH : Over H} {AT : Over T} [GrpObj AH] [GrpObj AT] {g : T ⟶ H}
    {χ : AT.left ⟶ AH.left} (w : χ ≫ AH.hom = AT.hom ≫ g) (act : O → (AH ⟶ AH)) (v : O → (AT ⟶ AT))
    (hv : ∀ a, (v a).left ≫ χ = χ ≫ (act a).left) {X : Scheme.{0}} (Q : LB X) (φ₂ : (AH ⊗ AH).left ⟶ X)
    (bar : O → O) (h : Adj AH (Q.pull φ₂) bar act) : Adj AT (Q.pull (sqMap w ≫ φ₂)) bar v := fun a =>
  lbIso_pullPull_along Q φ₂ _ _ (sqMap w ≫ φ₂) _ _ (sqMap w) rfl
    (lift_left_comp_sqMap w _ _ _ _
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_fst w, Category.assoc, Over.comp_left])
      (by rw [sqMap_snd]))
    (lift_left_comp_sqMap w _ _ _ _ (by rw [sqMap_fst])
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_snd w, Category.assoc, Over.comp_left]))
    (h a)

end Act

end GlobalTheory.EndLoc.ActUnr

namespace GlobalTheory.EndLoc


open ActUnr in
theorem formallyUnramified_actRep : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left)
    (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  intro S A _ _ Q O _ bar Rp hA
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let ψ : AT.left ⟶ A.left := pullback.fst A.hom f
  have hAT : IsGrpPullback AT A f ψ := isGrpPullback_pullback A f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : O → (AT ⟶ AT)) (χ : AT.left ⟶ Rp.AH.left)
      (φ₂' : (AT ⊗ AT).left ⟶ (A ⊗ A).left),
      IsRAct AT v ∧ IsSquare ψ φ₂' ∧ Adj AT (Q.pull φ₂') bar v ∧ IsGrpPullback AT Rp.AH g χ ∧ χ ≫ Rp.φ = ψ ∧
        ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := by
    intro g hgf
    have h' : IsGrpPullback ((Over.pullback g).obj Rp.AH) A f (pullback.fst Rp.AH.hom g ≫ Rp.φ) :=
      ((isGrpPullback_pullback Rp.AH g).comp Rp.pb).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso hAT h'
    haveI := he
    have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
    let χ : AT.left ⟶ Rp.AH.left := e.hom.left ≫ pullback.fst Rp.AH.hom g
    let v : O → (AT ⟶ AT) := fun a ↦ e.hom ≫ (Over.pullback g).map (Rp.act a) ≫ e.inv
    have hχφ : χ ≫ Rp.φ = ψ := by simp only [χ, Category.assoc]; exact heφ
    have hw : χ ≫ Rp.AH.hom = AT.hom ≫ g := by
      simp only [χ]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w e.hom
    have hv : ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := fun a ↦ by
      have hm : ((Over.pullback g).map (Rp.act a)).left ≫ pullback.fst Rp.AH.hom g =
          pullback.fst Rp.AH.hom g ≫ (Rp.act a).left := pullback.lift_fst _ _ _
      simp only [v, χ, Over.comp_left, Category.assoc]
      rw [reassoc_of% hie, hm]
    have hR : IsRAct AT v := isRAct_conj e _ (isRAct_pullback g Rp.AH Rp.act Rp.isAct)
    refine ⟨v, χ, sqMap hw ≫ Rp.φ₂, hR, ⟨?_, ?_⟩, adj_along hw Rp.act v hv Q Rp.φ₂ bar Rp.adj,
      Rp.pb.cancel ((hAT.congr hgf.symm hχφ.symm)) hw, hχφ, hv⟩
    · rw [Category.assoc, Rp.sq.1, ← Category.assoc, sqMap_fst, Category.assoc, hχφ]
    · rw [Category.assoc, Rp.sq.2, ← Category.assoc, sqMap_snd, Category.assoc, hχφ]
  obtain ⟨v₁, χ₁, φ₂₁, hR₁, hsq₁, hadj₁, hpb₁, hχ₁φ, hχ₁u⟩ := build g₁ rfl
  obtain ⟨v₂, χ₂, -, hR₂, -, -, hpb₂, hχ₂φ, hχ₂u⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχ : pullback.fst AT.hom j ≫ χ₁ = pullback.fst AT.hom j ≫ χ₂ := by
    apply Rp.pb.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχ₁φ, hχ₂φ]
    · rw [Category.assoc, Category.assoc, hpb₁.1.w, hpb₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : ∀ a, v₁ a = v₂ a := fun a ↦ by
    haveI := hR₁.1 a
    haveI := hR₂.1 a
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT AT hAbT (v₁ a) (v₂ a) ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₁ a).left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₂ a).left from pullback.lift_fst _ _ _]
      apply hAT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ (v₁ a).left) ≫ ψ
            = pullback.fst AT.hom j ≫ (v₁ a).left ≫ χ₁ ≫ Rp.φ := by rw [hχ₁φ, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χ₁ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% (hχ₁u a)]
          _ = pullback.fst AT.hom j ≫ χ₂ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% hχ]
          _ = pullback.fst AT.hom j ≫ (v₂ a).left ≫ χ₂ ≫ Rp.φ := by rw [reassoc_of% (hχ₂u a)]
          _ = (pullback.fst AT.hom j ≫ (v₂ a).left) ≫ ψ := by rw [hχ₂φ, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w (v₁ a), Over.w (v₂ a)]
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT ψ φ₂₁ v₁ hAT hsq₁ hR₁ hadj₁
  have e1 := hg' g₁ ⟨rfl, χ₁, hpb₁, hχ₁φ, hχ₁u⟩
  have e2 := hg' g₂ ⟨hg.symm, χ₂, hpb₂, hχ₂φ, fun a ↦ by rw [hv a]; exact hχ₂u a⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReduced
section
namespace GlobalTheory

theorem mem_minimalPrimes_of_disjoint_nonZeroDivisors {R : Type} [CommRing R] [IsReduced R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (hp : Disjoint (p : Set R) (nonZeroDivisors R)) :
    p ∈ minimalPrimes R := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hsub : (p : Set R) ⊆ ⋃ q ∈ hfin.toFinset, (q : Set R) := by
    intro x hx
    have hx' : x ∉ nonZeroDivisors R := Set.disjoint_left.mp hp hx
    rw [mem_nonZeroDivisors_iff_right] at hx'
    push Not at hx'
    obtain ⟨y, hxy, hy⟩ := hx'
    have hrad : (⊥ : Ideal R).radical = ⊥ := by
      exact nilradical_eq_zero R
    have : x ∈ ⋃ q ∈ (⊥ : Ideal R).minimalPrimes, (q : Set R) := by
      rw [Ideal.iUnion_minimalPrimes]
      refine ⟨y, ?_, ?_⟩
      · rw [hrad]; simpa using hy
      · rw [hrad]; simpa [mul_comm] using hxy
    simpa [Set.Finite.mem_toFinset] using this
  have hprime : ∀ q ∈ hfin.toFinset, q.IsPrime := fun q hq =>
    ((Set.Finite.mem_toFinset hfin).1 hq).isPrime
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ fun q hq _ _ => hprime q hq).1 hsub
  have hqm : q ∈ minimalPrimes R := (Set.Finite.mem_toFinset hfin).1 hq
  have : q ≤ p := hqm.2 ⟨inferInstance, bot_le⟩ hpq
  exact (le_antisymm hpq this) ▸ hqm

theorem total_fractions_isArtinian_isReduced (R : Type) [CommRing R] [IsReduced R]
    [IsNoetherianRing R] : IsArtinianRing (FractionRing R) ∧ IsReduced (FractionRing R) := by
  have hN : IsNoetherianRing (FractionRing R) :=
    IsLocalization.isNoetherianRing (nonZeroDivisors R) _ inferInstance
  have hRed : IsReduced (FractionRing R) := inferInstance
  refine ⟨?_, hRed⟩
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨hN, Ring.krullDimLE_zero_iff.mpr fun P hP => ?_⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  have key : ∀ (Q : Ideal (FractionRing R)), Q.IsPrime →
      Q.comap (algebraMap R (FractionRing R)) ∈ minimalPrimes R := by
    intro Q hQ
    have h := (IsLocalization.isPrime_iff_isPrime_disjoint (nonZeroDivisors R) (FractionRing R) Q).1 hQ
    have := h.1
    exact mem_minimalPrimes_of_disjoint_nonZeroDivisors _ h.2.symm
  have h1 := key P hP
  have h2 := key M hM.isPrime
  have hle : M.comap (algebraMap R (FractionRing R)) ≤ P.comap (algebraMap R (FractionRing R)) :=
    h2.2 ⟨h1.1.1, bot_le⟩ (Ideal.comap_mono hPM)
  have : P = M := by
    rw [← IsLocalization.map_under (nonZeroDivisors R) (FractionRing R) P,
      ← IsLocalization.map_under (nonZeroDivisors R) (FractionRing R) M]
    exact congrArg _ (le_antisymm (Ideal.comap_mono hPM) hle)
  exact this ▸ hM

theorem fractionRing_away_etale_isArtinian_isReduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  intro B _ _ f A' _ _ _
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  have : IsReduced A' := GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing B A'
  have : IsNoetherianRing (Localization.Away (algebraMap B A' f)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap B A' f)) _ inferInstance
  have : IsReduced (Localization.Away (algebraMap B A' f)) := inferInstance
  exact total_fractions_isArtinian_isReduced _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLinearCombinationZeroLeftAinfFrame
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobComb

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_sum {ι : Type} [Fintype ι] (c : ι → B) (g : ι → MvPowerSeries σ Q)
    (hg : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  choose t ht using fun i => In.top_iff.1 (hg i)
  refine In.top_iff.2 ⟨∑ i, c i • t i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ht i, smul_eq_C_mul]

theorem frob_sum (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {ι : Type} [Fintype ι] (c : ι → Q)
    (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i, c i • f i) = ∑ i, s (c i) • frob p s (f i) := by
  have hX : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) := HasSubst.X_pow hp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frob, ← coe_substAlgHom hX, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, map_smul]

end GlobalTheory.FrobComb

open GlobalTheory.FrobComb

theorem GlobalTheory.frob_comb_zero_left : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  intro p _ O _ _ _ ε F d k e U he b
  set b' : Fin d ⊕ Fin k → F.B := Sum.elim (fun _ => 0) b with hb'
  set c : Fin d ⊕ Fin k → F.B := fun j => F.σ (b' j) with hc
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have key : ∀ l i, (U * blk d k (p : F.B) 1) l i * c i = U l i * c i := by
    intro l i
    rcases i with i | i
    · simp [hc, hb']
    · simp [blk, Matrix.mul_diagonal]
  have hf : frob p F.s (comb b' e) = ∑ i, algebraMap F.B F.Q (c i) • frob p F.s (e i) := by
    rw [comb, frob_sum p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.s_alg]
  have hsplit : frob p F.s (comb b' e) - comb (U.mulVec c) e =
      ∑ i, algebraMap F.B F.Q (c i) •
        (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
    rw [hf]
    simp only [smul_sub, Finset.sum_sub_distrib]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [comb, Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, ← map_mul,
      map_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c _), key]
  rw [hsplit]
  exact in_top_sum c _ he
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusXiEqPMulUnit
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.QLog.BFrame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_xi (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.xi ε) = ∑ i ∈ Finset.range p, (1 + Sandwich.mu ε) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Sandwich.xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, Sandwich.mu,
    add_sub_cancel]
  congr 2
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε

theorem one_add_pow {ε : PreTilt O p} (F : BFrame ε) (i : ℕ) :
    (1 + (p : F.B) * F.τ) ^ i = 1 + (i : F.B) * ((p : F.B) * F.τ) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : F.B) * (p : F.B) ^ 2) * F.τ_sq

theorem a_frobenius_xi {ε : PreTilt O p} (F : BFrame ε) :
    F.a (WittVector.frobenius (Sandwich.xi ε)) = p * (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [frobenius_xi, map_sum]
  have h1 : ∀ i ∈ Finset.range p, F.a ((1 + Sandwich.mu ε) ^ i) = 1 + (i : F.B) * ((p : F.B) * F.τ) :=
    fun i _ => by rw [map_pow, map_add (f := _), map_one, ← F.p_τ, one_add_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : (∑ i ∈ Finset.range p, (i : F.B)) = ((p.choose 2 : ℕ) : F.B) := by
    rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]
  rw [h2]
  ring

theorem frobenius_xi_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F
  refine ⟨1 + ((p.choose 2 : ℕ) : F.B) * F.τ, ?_, ⟨((p.choose 2 : ℕ) : F.B), by ring⟩,
    a_frobenius_xi F⟩
  have h : (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) * (1 - ((p.choose 2 : ℕ) : F.B) * F.τ) = 1 := by
    linear_combination (-(((p.choose 2 : ℕ) : F.B)) ^ 2) * F.τ_sq
  exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩

end GlobalTheory.QLog.BFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.ValLin

lemma eval_map_hom {σ Q Q' : Type} [CommRing Q] [CommRing Q'] (R : Q →+* Q') (x : σ → Q)
    (P : MvPolynomial σ Q) :
    R (MvPolynomial.eval x P) = MvPolynomial.eval (fun i => R (x i)) (MvPolynomial.map R P) := by
  rw [MvPolynomial.eval_map]
  show R (MvPolynomial.eval₂ (RingHom.id Q) x P) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]

theorem hasVal_add_smul_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B) (f g : MvPowerSeries σ Q) (q r : Q), HasVal p z f q → (HasVal p z g r → HasVal p z (f + g) (q + r)) ∧ (∀ c : Q, HasVal p z (c • f) (c * q)) ∧ ∀ (B' Q' : Type) [CommRing B'] [CommRing Q'] [Algebra B' Q'] (ρ : B →+* B') (R : Q →+* Q'), (∀ b, R (algebraMap B Q b) = algebraMap B' Q' (ρ b)) → HasVal p (fun i => ρ (z i)) (map R f) (R q) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z f g q r hf
  refine ⟨?_, ?_, ?_⟩
  · intro hg m
    obtain ⟨N₁, h₁⟩ := hf m
    obtain ⟨N₂, h₂⟩ := hg m
    refine ⟨max N₁ N₂, fun N' hN => ?_⟩
    obtain ⟨b₁, hb₁⟩ := h₁ N' (le_trans (le_max_left _ _) hN)
    obtain ⟨b₂, hb₂⟩ := h₂ N' (le_trans (le_max_right _ _) hN)
    refine ⟨b₁ + b₂, ?_⟩
    rw [map_add (f := _), map_add (f := _), mul_add, map_add (f := _), ← hb₁, ← hb₂]
    ring
  · intro c m
    obtain ⟨k, b₀, hk⟩ := hF.denom c
    obtain ⟨N, h⟩ := hf (m + k)
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨b₀ * b, ?_⟩
    rw [map_smul, MvPolynomial.smul_eval]
    have e : c * q - c * MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') f)
        = c * algebraMap B Q (p ^ (m + k) * b) := by rw [← hb]; ring
    rw [e]
    simp only [map_mul, map_pow, map_natCast] at hk ⊢
    rw [← hk]
    ring
  · intro B' Q' _ _ _ ρ R hR m
    obtain ⟨N, h⟩ := hf m
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨ρ b, ?_⟩
    rw [trunc'_map]
    have := congrArg R hb
    rw [map_sub, eval_map_hom, hR] at this
    simp only [hR] at this
    rw [this]
    simp

end GlobalTheory.QLog.ValLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotentsStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  first | exact @GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | exact GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | (intros; apply GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents <;> assumption)
end

