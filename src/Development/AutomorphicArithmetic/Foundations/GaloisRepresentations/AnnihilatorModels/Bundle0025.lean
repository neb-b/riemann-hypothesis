module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CongKSOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

def CongKS : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ → (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) →
    ∀ (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → Flat π → ∀ (mπ : ObjMap E.univ M.univ π) (k : ℕ),
    ∃ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j))) (L : ∀ j, TjE E mπ (T j)) (d : Fin (D.n + 1) → ℕ)
      (h : ∀ j, KSOKE (L j) k (d j)), (∀ j, (h j).corr.r ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (h j).corr.p ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ∧
      PtId p (p ^ f) D.n (fn ((GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ϖ) fun j => (h j).corr

theorem congKS_of (h1 : TjExF) (h2 : TjEEx) (h3 : OrdKSE) (h4 : PtIdOfOrd) : CongKS := by
  intro p _ D O _ _ _ _ f b N r w _ hs M ϖ hϖ 𝔞 ρ ha hu E π hπ hf mπ k
  choose T hT using fun j : Fin (D.n + 1) => h1 p D O f b N r w hs M j (Nat.lt_succ_iff.1 j.2)
  have L := fun j : Fin (D.n + 1) => (h2 p D O f b N r w hs M j _ (T j) (hT j) 𝔞 ρ ha hu E π hπ mπ).some
  obtain ⟨d, h, e, ho⟩ := h3 p D O f b N r w hs M ϖ hϖ T 𝔞 ρ E π hπ hf mπ L k
  exact ⟨T, L, d, h, e, h4 _ _ _ _ _ _ ho⟩

end UpperTheory.Gal.crystallineComparison.Mod
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCorrBC
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem etale_restrict_of_isPullback {X Y W Z : Scheme.{0}} {h : Y ⟶ X} {t : W ⟶ X} {s : Z ⟶ Y} {g : Z ⟶ W}
    (hpb : IsPullback s g h t) (U : X.Opens) (ht : Etale (t ∣_ U)) : Etale (s ∣_ (h ⁻¹ᵁ U)) := by
  have P1 := isPullback_morphismRestrict t U
  have P2 := isPullback_morphismRestrict s (h ⁻¹ᵁ U)
  have P3 := isPullback_morphismRestrict h U
  have hcomm : ((s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U)) ≫ U.ι = (s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g ≫ t := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc, hpb.w]
  let top : (s ⁻¹ᵁ (h ⁻¹ᵁ U)).toScheme ⟶ (t ⁻¹ᵁ U).toScheme :=
    P1.lift ((s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U)) ((s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g) (by rw [hcomm, Category.assoc])
  have htop₁ : top ≫ (t ∣_ U) = (s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U) := P1.lift_fst _ _ _
  have htop₂ : top ≫ (t ⁻¹ᵁ U).ι = (s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g := P1.lift_snd _ _ _
  have pasted := P2.flip.paste_horiz hpb.flip
  have pasted' : IsPullback (top ≫ (t ⁻¹ᵁ U).ι) (s ∣_ (h ⁻¹ᵁ U)) t ((h ∣_ U) ≫ U.ι) := by
    rw [htop₂, morphismRestrict_ι]; exact pasted
  have left : IsPullback top (s ∣_ (h ⁻¹ᵁ U)) (t ∣_ U) (h ∣_ U) :=
    IsPullback.of_right pasted' htop₁ P1.flip
  exact MorphismProperty.of_isPullback (P := @Etale) left ht

theorem UpperTheory.Gal.crystallineComparison.Mod.corrBC_of :
    WModEx → RankN → SecEquiv → GrCard → CorrBC := by
  intro hW hR hS hG p _ D O _ _ _ _ f b N r w _ hstd M j hj T Y Z h s g hpb
  refine ⟨?_, ?_, ?_⟩
  · have := T.fin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip this
  · have hV : Y.basicOpen ((p : ℕ) : Γ(Y, ⊤)) = h ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
      rw [Scheme.preimage_basicOpen_top, map_natCast]
    rw [hV]
    exact etale_restrict_of_isPullback hpb _ T.et
  · intro K _ _ hp y
    haveI : ValuationRing K := ValuationRing.of_field K
    haveI : IsAlgClosed (FractionRing K) :=
      IsAlgClosed.of_ringEquiv K (FractionRing K) (FractionRing.algEquiv K K).symm.toRingEquiv
    obtain ⟨W⟩ := hW p D O b N M.X M.s M.univ w (Over.mk (y ≫ h))
    obtain ⟨hfin, hrk⟩ := hR p D O f b N r w hstd M K hp (y ≫ h) W
    obtain ⟨e, -⟩ := hS p D O f b N r w hstd M j hj T K hp (y ≫ h) W
    let E : {z : Spec (CommRingCat.of K) ⟶ Z // z ≫ s = y} ≃ {z : Sp K ⟶ T.Y // z ≫ T.s = y ≫ h} :=
      { toFun := fun z => ⟨z.1 ≫ g, by rw [Category.assoc, ← hpb.w, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨hpb.lift y z.1 z.2.symm, hpb.lift_fst _ _ _⟩
        left_inv := fun z => Subtype.ext (hpb.hom_ext (by rw [hpb.lift_fst, z.2]) (by rw [hpb.lift_snd]))
        right_inv := fun z => Subtype.ext (hpb.lift_snd _ _ _) }
    rw [Nat.card_congr E, Nat.card_congr e]
    exact hG _ _ _ _ hrk
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIdealSplit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_coprime_mul_le {A : Type} [CommRing A] [IsDedekindDomain A] (𝔞 J : Ideal A) (hJ : J ≠ ⊥) :
    ∃ (m : ℕ) (𝔟 : Ideal A), IsCoprime 𝔞 𝔟 ∧ 𝔞 ^ m * 𝔟 ≤ J := by
  classical
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ u hu =>
    refine ⟨0, ⊤, Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq _), ?_⟩
    rw [Ideal.isUnit_iff.mp hu]; exact le_top
  | h₃ a p ha hp ih =>
    have ha0 : a ≠ ⊥ := by
      rintro rfl; exact hJ (by simp)
    have hp0 : p ≠ ⊥ := by
      rintro rfl; exact hJ (by simp)
    obtain ⟨m, b, hcop, hle⟩ := ih ha0
    by_cases hap : 𝔞 ≤ p
    · refine ⟨m + 1, b, hcop, ?_⟩
      calc 𝔞 ^ (m + 1) * b = 𝔞 * (𝔞 ^ m * b) := by rw [pow_succ', _root_.mul_assoc]
        _ ≤ p * a := Ideal.mul_mono hap hle
    · have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have hc : IsCoprime 𝔞 p := by
        rw [Ideal.isCoprime_iff_sup_eq]
        by_contra h
        have h2 := hpm.eq_of_le h le_sup_right
        exact hap (h2 ▸ le_sup_left)
      refine ⟨m, p * b, IsCoprime.mul_right hc hcop, ?_⟩
      calc 𝔞 ^ m * (p * b) = p * (𝔞 ^ m * b) := by ring
        _ ≤ p * a := Ideal.mul_mono_right hle

theorem UpperTheory.Gal.crystallineComparison.Mod.idealSplit_of :
    IdealSplit := by
  intro A _ _ 𝔞 x hx ρ
  have hJ : Ideal.span {x} ≠ ⊥ := by simpa using hx
  obtain ⟨m, 𝔟, hc, hle⟩ := exists_coprime_mul_le 𝔞 (Ideal.span {x}) hJ
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp (hc.pow_left (m := ρ))
  refine ⟨m, j, ?_, fun a ha => hle (Ideal.mul_mem_mul ha hj)⟩
  have : j - 1 = -i := by rw [← hij]; ring
  rw [this]
  exact neg_mem hi
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLevPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.levPull_of :
    PullKer → LevPull := by
  intro _ p _ D R _ b N S S' s s' f o o₁ m 𝔞 ρ lv h
  exact GlobalTheory.UPel.HT.EtLev.isEtLev_exists_pull m h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdEmb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem img_comp (T : TjD M r w j c) {X X' : Scheme.{0}} (u : X' ⟶ X) (z : X ⟶ T.Y)
    (a : X ⟶ M.univ.A.left) (h : a ≫ M.univ.A.hom = z ≫ T.s)
    (h' : (u ≫ a) ≫ M.univ.A.hom = (u ≫ z) ≫ T.s) :
    u ≫ T.img z a h = T.img (u ≫ z) (u ≫ a) h' := by
  unfold TjD.img
  rw [← Category.assoc]
  congr 1
  apply T.ms.cart.1.hom_ext <;> simp

private theorem img_congr (T : TjD M r w j c) {X : Scheme.{0}} {z z' : X ⟶ T.Y}
    {a a' : X ⟶ M.univ.A.left} (h : a ≫ M.univ.A.hom = z ≫ T.s)
    (h' : a' ≫ M.univ.A.hom = z' ≫ T.s) (hz : z = z') (ha : a = a') :
    T.img z a h = T.img z' a' h' := by
  subst hz; subst ha; rfl

end

private theorem resPt_apply (V : Type) [CommRing V] [IsLocalRing V]
    (q : Spec (CommRingCat.of (IsLocalRing.ResidueField V))) :
    (resPt V) q = IsLocalRing.closedPoint V := by
  have : q = IsLocalRing.closedPoint (IsLocalRing.ResidueField V) := Subsingleton.elim _ _
  subst this
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

end UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.ordEmb_of :
    OrdGen → GenDown → ResClosed → OrdReadOf → EW → OrdEmb := by
  intro hOG hGD hRC hOR hEW
  intro p _ D O _ _ _ _ f b N r w _ hS M ϖ hϖ T Y h hflat I a ha hsep C g hpb hr himg
  intro V _ _ _ _ hpV y hgen φ hφ
  haveI := hRC V
  obtain ⟨hcl, hmax⟩ := hGD O ϖ hϖ M.X Y M.s h hflat _ hgen
  have hi : 0 < D.a := by rw [hS.a1]; exact Nat.one_pos
  have hcom : (IsLocalRing.maximalIdeal O).comap (b.t ⟨0, hi⟩) = w := by
    symm
    refine Ideal.IsMaximal.eq_of_le inferInstance ?_ fun x hx => hS.tw _ x hx
    exact Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hord : IsWOrd M.univ w (resPt V ≫ y ≫ h) := by
    refine hOG p D O b N hS.three hS.cop hS.pmem hS.m1 ⟨0, hi⟩ w hcom M _ hcl hmax _ _ fun q => ?_
    simp only [Scheme.Hom.comp_apply, resPt_apply]
    rfl
  obtain ⟨H, _, _, _, C₀, e, hfr, hfr1, hA, hB⟩ := hEW p D O f b N r w hS M T V hpV (y ≫ h)
    hcl hord φ hφ
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← hS.norm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let s : ∀ j, (C j).Sec y ≃ {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = y ≫ h} := fun j =>
    { toFun := fun z => ⟨z.1 ≫ g j, by rw [Category.assoc, ← (hpb j).w, ← Category.assoc, z.2]⟩
      invFun := fun z => ⟨(hpb j).lift y z.1 z.2.symm, (hpb j).lift_fst _ _ _⟩
      left_inv := fun z => Subtype.ext ((hpb j).hom_ext (by simpa using z.2.symm) (by simp))
      right_inv := fun z => Subtype.ext ((hpb j).lift_snd _ _ _) }
  have key : ∀ (j : Fin (D.n + 1)) (z : (C j).Sec y) (i : I) (e),
      resPt V ≫ z.1 ≫ (C j).r ≫ a i = (T j).img (resPt V ≫ z.1 ≫ g j) (resPt V ≫ y ≫ a i) e := by
    intro j z i e
    have e0 : ((C j).p ≫ a i) ≫ M.univ.A.hom = g j ≫ (T j).s := by
      rw [Category.assoc, ha, (hpb j).w]
    rw [himg j i e0]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (img_comp (T j) (resPt V ≫ z.1) (g j) _ e0
      (by simp only [Category.assoc]; rw [ha, (hpb j).w])).trans ?_
    refine img_congr _ _ _ (by simp) ?_
    simp only [Category.assoc]
    rw [← Category.assoc z.1, z.2]
  have hae : ∀ (j : Fin (D.n + 1)) (z : (C j).Sec y) (i : I),
      (resPt V ≫ y ≫ a i) ≫ M.univ.A.hom = (resPt V ≫ z.1 ≫ g j) ≫ (T j).s := by
    intro j z i
    simp only [Category.assoc]
    rw [ha, ← (hpb j).w, ← Category.assoc z.1, z.2]
  refine hOR (p ^ f) D.n _ (twist φ Y) _ _ (𝓞 D.F ⧸ w) H C₀ (fun j => (s j).trans (e j)) hcard hfr hfr1 ?_ ?_
  · intro j z z' h1 h2 h3
    obtain ⟨t1, t2⟩ := hA j (s j z) (s j z') h1 h2 h3
    refine hsep _ _ _ ?_ fun i => ?_
    · have t1' : resPt V ≫ (z.1 ≫ g j) ≫ (T j).t = resPt V ≫ (z'.1 ≫ g j) ≫ (T j).t := t1
      simp only [Category.assoc, hr]
      simpa only [Category.assoc] using t1'
    · simp only [Category.assoc]
      rw [key j z i (hae j z i), key j z' i (hae j z' i)]
      exact t2 _ _ _
  · intro j j' z z' hj h1 h2 h3
    obtain ⟨t1, t2⟩ := hB j j' (s j z) (s j' z') hj h1 h2 h3
    refine hsep _ _ _ ?_ fun i => ?_
    · have t1' : resPt V ≫ (z.1 ≫ g j) ≫ (T j).t =
          spMap φ ≫ resPt V ≫ (z'.1 ≫ g j') ≫ (T j').t := t1
      simp only [twist, Category.assoc, hr]
      simpa only [Category.assoc] using t1'
    · simp only [twist, Category.assoc]
      rw [key j z i (hae j z i), key j' z' i (hae j' z' i)]
      exact t2 _ _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdKSE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w 𝔞 : Ideal (𝓞 D.F)} {j c ρ : ℕ}
  {E : EtModel b N 𝔞 ρ} {π : E.X ⟶ M.X} {mπ : ObjMap E.univ M.univ π} {T : TjD M r w j c}

private theorem pm_hom {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A' m).hom ≫ f := by
  unfold GlobalTheory.KS.powMap
  exact Over.w _

private theorem pm_pr {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    GlobalTheory.KS.powMap f φ h m ≫ (GlobalTheory.KS.pr A i).left = (GlobalTheory.KS.pr A' i).left ≫ φ := by
  simp only [GlobalTheory.KS.powMap, GlobalTheory.KS.pr, ← Over.comp_left, Pi.lift_comp_π, Over.homMk_left]

private theorem ksR_hom (L : TjE E mπ T) (k : ℕ) :
    L.ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom = (GlobalTheory.KS.pow L.o.A k).hom ≫ L.t := by
  unfold TjE.ksR
  rw [Category.assoc, pm_hom, ← Category.assoc, Over.w]

private theorem ksR_pr (L : TjE E mπ T) (k : ℕ) (i : Fin k) :
    L.ksR k ≫ (GlobalTheory.KS.pr E.univ.A i).left = (GlobalTheory.KS.pr L.o.A i).left ≫ L.ψ.left ≫ L.mt.φ := by
  rw [TjE.ksR, Category.assoc, pm_pr, ← Category.assoc, ← Over.comp_left, Pi.map_π, Over.comp_left, Category.assoc]

private theorem localMap_hom (L : TjE E mπ T) (k : ℕ) :
    L.ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom = (GlobalTheory.KS.pow L.o.A k).hom ≫ L.s := pm_hom _ _ _ _

private theorem localMap_projection (L : TjE E mπ T) (k : ℕ) (i : Fin k) :
    L.ksP k ≫ (GlobalTheory.KS.pr E.univ.A i).left = (GlobalTheory.KS.pr L.o.A i).left ≫ L.ms.φ := pm_pr _ _ _ _ _

private theorem ks_pb (L : TjE E mπ T) (k : ℕ) :
    IsPullback (L.ksP k) ((GlobalTheory.KS.pow L.o.A k).hom ≫ L.g) ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) T.s := by
  rw [TjE.ksP]
  exact (GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback _ _ _ _ _ _ _ L.ms.cart.1 k).paste_vert L.pb

private theorem img_of (L : TjE E mπ T) {X : Scheme.{0}} (c : X ⟶ L.o.A.left) (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left)
    (hz : z = c ≫ L.o.A.hom ≫ L.g) (ha : a = c ≫ L.ms.φ ≫ mπ.φ) (e : a ≫ M.univ.A.hom = z ≫ T.s) :
    T.img z a e = c ≫ L.ψ.left ≫ L.mt.φ ≫ mπ.φ := by
  have key : ∀ hp : IsPullback T.ms.φ T.o.A.hom M.univ.A.hom T.s, hp.lift a z e = c ≫ L.m₀.φ := by
    intro hp
    apply hp.hom_ext
    · rw [hp.lift_fst, Category.assoc, L.tri, ha]
    · rw [hp.lift_snd, Category.assoc, L.m₀.cart.1.w, hz]
  rw [TjD.img, key]
  simp only [Category.assoc]
  rw [← Category.assoc L.m₀.φ, L.sq]
  simp only [Category.assoc]
  rw [L.tri']

end

theorem UpperTheory.Gal.crystallineComparison.Mod.ordKSE_of :
    CorrBC → OrdEmb → PowExt → EtInj → OrdKSE := by
  intro hBC hOE hPE hEI p _ D O _ _ _ _ f b N r w _ hs M ϖ hϖ T 𝔞 ρ E π hπ hfl mπ L k
  have hK : ∀ j : Fin (D.n + 1), KSOKE (L j) k (Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) (j : ℕ))) := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hBC p D O f b N r w hs M j (Nat.le_of_lt_succ j.isLt) (T j) _ _ _ _ _ (ks_pb (L j) k)
    exact ⟨h1, h2, h3⟩
  have heq : ∀ j, (L j).t ≫ E.s = (L j).s ≫ E.s := by
    intro j
    calc (L j).t ≫ E.s = (L j).t ≫ π ≫ M.s := by rw [hπ]
      _ = (L j).g ≫ (T j).t ≫ M.s := by rw [← Category.assoc, (L j).tπ, Category.assoc]
      _ = (L j).g ≫ (T j).s ≫ M.s := by rw [(T j).st]
      _ = (L j).s ≫ π ≫ M.s := by rw [← Category.assoc, ← (L j).pb.w, Category.assoc]
      _ = (L j).s ≫ E.s := by rw [hπ]
  refine ⟨fun j => Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) (j : ℕ)), hK, ?_, ?_⟩
  · intro j
    change (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (L j).ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s
    rw [← Category.assoc, ksR_hom, ← Category.assoc ((L j).ksP k), localMap_hom, Category.assoc, Category.assoc, heq j]
  · have hsm : Smooth E.univ.A.hom := @IsAbelianScheme.smooth _ _ _ E.univ.ab
    obtain ⟨hfl', hinj⟩ := hPE E.X E.univ.A k
    have hflat : Flat ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) := by
      haveI := hfl' hsm
      infer_instance
    have hM : ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) ≫ M.s = (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s := by
      rw [Category.assoc, hπ]
    rw [← hM]
    refine hOE p D O f b N r w hs M ϖ hϖ T _ _ hflat (Fin k ⊕ D.La)
      (Sum.elim (fun i => (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ)
        (fun y => (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ)) ?_ ?_ (fun j => (hK j).corr)
      (fun j => (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g) (fun j => ks_pb (L j) k) ?_ ?_
    · rintro (i | y)
      · simp only [Sum.elim_inl]
        rw [Category.assoc, mπ.cart.1.w, ← Category.assoc, Over.w]
      · simp only [Sum.elim_inr]
        rw [Category.assoc, Category.assoc, mπ.cart.1.w, ← Category.assoc (E.lv y).left, Over.w]
        simp
    · intro X u v huv hi
      have h0 : u ≫ (GlobalTheory.KS.pow E.univ.A k).hom = v ≫ (GlobalTheory.KS.pow E.univ.A k).hom :=
        hEI p D O b N hs.three hs.cop M 𝔞 ρ E π hπ mπ X _ _ (by simpa [Category.assoc] using huv)
          (fun y => by simpa [Category.assoc] using hi (Sum.inr y))
      apply hinj X u v h0
      intro i
      apply mπ.cart.1.hom_ext
      · simpa [Category.assoc] using hi (Sum.inl i)
      · simp only [Category.assoc, Over.w]
        exact h0
    · intro j
      change (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ π = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g) ≫ (T j).t
      rw [← Category.assoc, ksR_hom, Category.assoc, (L j).tπ]
      simp only [Category.assoc]
    · intro j i e
      rcases i with i | y
      · have hz : (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).o.A.hom ≫ (L j).g := by
          rw [← Category.assoc, Over.w]
        have ha : (L j).ksP k ≫ (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).ms.φ ≫ mπ.φ := by
          rw [← Category.assoc, localMap_projection, Category.assoc]
        have hr : (L j).ksR k ≫ (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).ψ.left ≫ (L j).mt.φ ≫ mπ.φ := by
          rw [← Category.assoc, ksR_pr]
          simp only [Category.assoc]
        exact hr.trans (img_of (L j) _ _ _ hz ha e).symm
      · obtain ⟨l, hl⟩ : ∃ l : 𝟙_ (Over (L j).Z) ⟶ (L j).o.A, l.left ≫ (L j).ms.φ = (L j).s ≫ (E.lv y).left := by
          refine ⟨Over.homMk ((L j).ms.cart.1.lift ((L j).s ≫ (E.lv y).left) (𝟙 _) ?_) ?_, ?_⟩
          · rw [Category.assoc, Over.w]
            simp
          · rw [IsPullback.lift_snd]
            simp
          · simp
        have hlev := (L j).lev y l hl
        have hlev' : l.left ≫ (L j).ψ.left ≫ (L j).mt.φ = (L j).t ≫ (E.lv y).left := by
          rw [← Category.assoc, ← Over.comp_left]
          exact hlev
        have hz : (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).o.A.hom ≫ (L j).g := by
          rw [Category.assoc, ← Category.assoc l.left, Over.w]
          simp
        have ha : (L j).ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).ms.φ ≫ mπ.φ := by
          rw [← Category.assoc ((L j).ksP k), localMap_hom]
          simp only [Category.assoc]
          rw [reassoc_of% hl]
        have hr : (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).ψ.left ≫ (L j).mt.φ ≫ mπ.φ := by
          rw [← Category.assoc ((L j).ksR k), ksR_hom]
          simp only [Category.assoc]
          rw [reassoc_of% hlev']
        exact hr.trans (img_of (L j) _ _ _ hz ha e).symm
end

