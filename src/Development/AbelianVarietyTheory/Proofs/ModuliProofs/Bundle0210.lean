module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNsmulOfDvd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkIso

open PrimCocycle

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

theorem exists_gen_axis {M M' : LB B.left} (hM : M.IsLB) (hM' : M'.IsLB) {T : Over S} (x y : T ⟶ B)
    (h : x = 1 ∨ y = 1) : ∃ t : ((LB.div (abelian₂ B M') (abelian₂ B M)).pull (lift x y).left).Gen, t.IsGen := by
  have key : ∀ {N : LB B.left}, N.IsLB →
      ∃ u : LB.Gen (LB.LinComb N (fun I => (lift x y).left ≫ lamφ B I) lamε), u.IsGen := fun {N} hN => by
    obtain ⟨u, hu, -⟩ := exists_gen hN (φ := PEmpty.elim) (ε := PEmpty.elim)
      (φ' := fun I => (lift x y).left ≫ lamφ B I) (ε' := lamε) (fun U _ g => by
        refine (Fintype.prod_empty _).trans (Eq.symm ((prod_lam x y g).trans ?_))
        rcases h with rfl | rfl
        · rw [_root_.one_mul, mul_right_comm (g y.left), mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
        · rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]) (LB.oneGen N)
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm)
    exact ⟨u, hu⟩
  obtain ⟨u, hu⟩ := key hM
  obtain ⟨u', hu'⟩ := key hM'
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullOut M (lamφ B) lamε _ _ fun _ => rfl)
    (chartPullOut M' (lamφ B) lamε _ _ fun _ => rfl) (IsoDescent.lbIso_of_gens hM hM' _ _ _ _ u hu u' hu')
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ _) w hw

theorem exists_gen_tensor {L : LB A.left} {M M' : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (h' : LBIso L (M'.pull ψ.left)) :
    ∃ t : ((LB.div (abelian₂ B M') (abelian₂ B M)).pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen := by
  have e : ∀ I, lamφ A I ≫ ψ.left = (ψ ⊗ₘ ψ).left ≫ lamφ B I := fun I =>
    congrArg (fun q => q.left)
      ((psum_hom (MonoidHom.mk' (fun z : A ⊗ A ⟶ A => z ≫ ψ) fun a b => MonObj.mul_comp a b ψ) (x2 A) I.down).trans
        ((congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])).trans
          (psum_hom (preHom (ψ ⊗ₘ ψ)) (x2 B) I.down).symm))
  obtain ⟨v, hv⟩ := h
  obtain ⟨v', hv'⟩ := h'
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullOut M (lamφ B) lamε _ _ e) (chartPullOut M' (lamφ B) lamε _ _ e)
    (LBIso.trans (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hM' _ _)
      (iso_linComb ((isGen_iff v).1 hv) (lamφ A) lamε).symm (iso_linComb ((isGen_iff v').1 hv') (lamφ A) lamε))
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ _) w hw

end GlobalTheory.HkIso

namespace GlobalTheory

open HkIso HeckePoint

theorem exists_objMap_of_isIsog_of_kerSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left), p.Prime → ¬ p ∣ l.M' → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  intro E _ _ _ H D l p S _ s o o₁ o₂ ψ₁ ψ₂ K hp hpM ⟨⟨hom₁, fin₁, et₁, sur₁, lin₁, bun₁⟩, lev₁⟩
    ⟨⟨hom₂, fin₂, et₂, sur₂, lin₂, bun₂⟩, lev₂⟩ ker₁ ker₂ hK
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab₁ := isAbelianScheme_of_proper o₁.t o₁.proper
  have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, homα, hα, uα⟩ := _root_.GlobalTheory.HkFactor.exists_unique_factor S _ _ _ ψ₁ ψ₂ hab hab₁ inferInstance hom₁ fin₁ et₁ sur₁ hom₂
    fun k _ _ t x hx => (ker₂ k t x).2 ((ker₁ k t x).1 hx)
  obtain ⟨β, -, hβ, -⟩ := _root_.GlobalTheory.HkFactor.exists_unique_factor S _ _ _ ψ₂ ψ₁ hab hab₂ inferInstance hom₂ fin₂ et₂ sur₂ hom₁
    fun k _ _ t x hx => (ker₁ k t x).2 ((ker₂ k t x).1 hx)
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have : Epi ψ₂.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₂ := Over.epi_of_epi_left ψ₂
  have : IsIso α := ⟨β, by rw [← cancel_epi ψ₁, reassoc_of% hα, hβ, Category.comp_id],
    by rw [← cancel_epi ψ₂, reassoc_of% hβ, hα, Category.comp_id]⟩
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos hp.pos 2)).map
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
    rwa [map_natCast] at this
  have i₀ : (lbPow o.t.PP.L (p ^ 2)).IsLB := DVR.linComb_isLB _ o.t.PP.isLB _ _
  have i₁ := pull_isLB o₁.t.PP.isLB (𝟙 _)
  have i₂ := pull_isLB o₂.t.PP.isLB α.left
  have hlam : LBIso (abelian₂ o₁.t.G (o₁.t.PP.L.pull (𝟙 _))) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    _root_.GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny S _ _ ψ₁ o₁.t.PP.L _ (p ^ 2) hab hab₁ o₁.t.PP.isLB o₁.ample
      (LB.isLB_div (DVR.linComb_isLB _ i₂ _ _) (DVR.linComb_isLB _ i₁ _ _)) hom₁ fin₁ et₁ sur₁ (pow_pos hp.pos 2) hunit
      (fun k _ _ t x hx => hK k t x ((ker₁ k t x).1 hx))
      (exists_gen_axis i₁ i₂ _ _ (Or.inl rfl)) (exists_gen_axis i₁ i₂ _ _ (Or.inr rfl))
      (exists_gen_tensor i₀ i₁ i₂ ψ₁
        (LBIso.chartPull (chartPullId _) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun _ => by simp) bun₁)
        (LBIso.chartPull (chartPullId _) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun _ => by
          rw [Category.id_comp, ← Over.comp_left, hα]) bun₂))
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso globalFns_holds hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientTripleFamilyReducedNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open CechPic

theorem exists_quotient_triple_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  intro E _ _ _ H R _ _ _ t g p B _ ψ M hR hp hprop hsm hamp hK hB hM hψ hf he hs hker hiso
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp R) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have := hB.comm
  have hred : IsReduced (Sp R) := inferInstance
  have hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R),
      Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = (p ^ 2) ^ g := fun k _ _ x => by
    rw [← pow_mul]; exact (hker k x).1
  have hMamp : Out.RelAmple B M := (_root_.GlobalTheory.relAmple_kTriv_of_descent_family R P (p ^ 2) B ψ M hR hn hB hM hψ hf he hs hc hiso).1
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen := cube_of_relAmple _ B M hB hM hMamp
  obtain ⟨act, hact⟩ := GlobalTheory.exists_oAct_descend_of_etale_isogeny (𝓞 E) (Sp R) t.G B ψ t.act hA hB hψ hf he hs
    fun k _ _ x z c hz => ((hker k x).2 z hz).2 c
  have hα : ∀ a, ψ ≫ act.act a = t.act.act a ≫ ψ := fun a => (hact a).symm
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    have h := (hR _ hn).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    have adjA : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G),
        lam m ((u ≫ ψ) ≫ act.act a) (v ≫ ψ) = lam m (u ≫ ψ) ((v ≫ ψ) ≫ act.act (H.bar a)) := by
      intro T u v
      rw [Category.assoc, Category.assoc, hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ act.act a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp R)} (x y : T ⟶ B), lam m (x ≫ act.act a) y = lam m x (y ≫ act.act (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)
          (cubeLB B ![fst B B ≫ act.act a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine _root_.GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny (Sp R) t.G B ψ M _ (p ^ 2) hA hB hM hMamp hN hψ hf he hs hn hunit
      (fun k _ _ x z hz => ((hker k x).2 z hz).1) (val _ _ ?_) (val _ _ ?_) ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
    · have e : ψ ⊗ₘ ψ = lift (fst t.G t.G ≫ ψ) (snd t.G t.G ≫ ψ) := by ext <;> simp
      rw [e]
      exact val _ _ (adjψ _ _)
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  obtain ⟨a₃, a₄⟩ := _root_.GlobalTheory.relAmple_kTriv_of_descent_family R P (p ^ 2) B ψ PP.L hR hn hB hP' hψ hf he hs hc hfinal
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, ⟨hψ, hf, he, hs, hact, hfinal⟩, fun _ _ => Iff.rfl⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem countable_addEquiv_of_free_finite (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] :
    Countable (La ≃+ La) := by
  let bas := Module.Free.chooseBasis ℤ La
  haveI : Countable La := bas.equivFun.injective.countable
  have hinj : Function.Injective (fun (gm : La ≃+ La) (i : Module.Free.ChooseBasisIndex ℤ La) => gm (bas i)) := by
    intro gm gm' h
    have h2 : gm.toAddMonoidHom.toIntLinearMap = gm'.toAddMonoidHom.toIntLinearMap :=
      bas.ext (fun i => congrFun h i)
    ext x
    exact LinearMap.congr_fun h2 x
  exact hinj.countable

theorem goodClass_of_lattice_families : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d r : ℕ) (La : Fin r → Type) [∀ i, AddCommGroup (La i)] (EF : ∀ i, LinearMap.BilinForm ℤ (La i)) (lam : ∀ i, Fin (2 * g) → La i) (ac : ∀ i, J → La i → La i) (B : Fin r → Set (Fin d → ℂ)) (Q : ∀ i, (Fin d → ℂ) → (La i →+ (Fin g → ℂ))) (Hm : Fin r → (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ t t', C t → TMap t' t (𝟙 _) → C t') → (∀ t, C t → t.Prim w w') → (∀ i, Function.Bijective (EF i) ∧ IsOpen (B i) ∧ IsPreconnected (B i) ∧ (∀ x, DifferentiableOn ℂ (fun bb => Q i bb x) (B i)) ∧ (∀ x, ac i w x + ac i w' x = x) ∧ (∀ x y, EF i (ac i w x) y = EF i x (ac i w' y)) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF i (lam i i₁) (lam i i₂) : ℂ) / ((N' ^ 2 : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∀ j₁ i₁, ∃ y, ac i j₁ (lam i i₁) = ∑ i', Mat j₁ i' i₁ • lam i i' + (N' ^ 2) • y) ∧ (∀ bb ∈ B i, (Function.Injective (Q i bb) ∧ DiscreteTopology ((Q i bb)).range ∧ Submodule.span ℝ (Set.range (Q i bb)) = ⊤ ∧ ((Hm i bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm i bb) z z).re) ∧ ∀ x y, (hermForm (Hm i bb) ((Q i bb) x) ((Q i bb) y)).im = EF i x y) ∧ ∀ j₁, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q i bb x) = Q i bb (ac i j₁ x)) ∧ ∀ y, y ≠ 0 → (hermForm (Hm i bb) (F y) (F y)).re < κ * (hermForm (Hm i bb) y y).re) ∧ (∀ bb ∈ B i, ∀ z' ∈ B i, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q i z' x = h (Q i bb x)) → bb = z') ∧ ∀ bb ∈ B i, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → C t) → (∀ t, C t → ∃ i, ∃ bb ∈ B i, (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀)) → GoodClass em C Mat κ w w' d := by
  intro h1 h2 h3 h4 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hqt⟩ := _root_.GlobalTheory.ZM.tmap_of_hasTh_complex h1 h2 g J Mat κ n hn hodd
  refine ⟨max j₀ 1, ?_⟩
  intro j hj N' hN' o _ b em C d r La _ EF lam ac B Q Hm hiso hprim hfam hcov
  subst hN'
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : j ≠ 0 := by have := le_trans (le_max_right _ _) hj; omega
  have hth := fun i => _root_.GlobalTheory.exists_holomorphic_thetaConstants_of_family h1 h2 h3 h4 o g (n ^ j) J b em w w' (La i) (EF i) (lam i) (ac i) d (B i) (Q i) (Hm i)
    hodd.pow (hfam i).1 (hfam i).2.1 (hfam i).2.2.2.1
    (fun bb hbb => ⟨((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1,
      (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 w).imp fun F hF => hF.1⟩)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1
  choose θ hθd hθ using hth
  have hsh := fun i bb (hbb : bb ∈ B i) t ht => _root_.GlobalTheory.ZM.shape_of_uniformised h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' t (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) Mat κ ht (hfam i).2.2.2.2.2.2.2.1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2
  have hbuild := fun i bb (hbb : bb ∈ B i) => _root_.GlobalTheory.thetaObject_of_lattice h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) (hfam i).1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1
    (fun j₁ => (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 j₁).imp fun F hF => hF.1)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1 (hfam i).2.2.2.2.2.2.1
  refine ⟨hiso, fun t ht => ⟨?_, hprim t ht⟩, r, B, θ, fun i => ⟨(hfam i).2.1, (hfam i).2.2.1, hθd i, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact hsh i bb hbb t hu
  · obtain ⟨t, htp, hu⟩ := hbuild i z hz
    exact ⟨t, (hfam i).2.2.2.2.2.2.2.2.2.2 z hz t hu htp, hθ i z hz t hu⟩
  · obtain ⟨hfree, hfin, -⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 (La i) (EF i) g (Q i z) (Hm i z)
      ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1
    haveI := countable_addEquiv_of_free_finite (La i)
    have hc : (⋃ gm : La i ≃+ La i, {z' ∈ B i | ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
        ∀ x, h (Q i z' x) = Q i z (gm x)}).Countable := by
      refine Set.countable_iUnion fun gm => Set.Subsingleton.countable ?_
      rintro z₁ ⟨hz₁, k₁, hk₁⟩ z₂ ⟨hz₂, k₂, hk₂⟩
      refine (hfam i).2.2.2.2.2.2.2.2.2.1 z₁ hz₁ z₂ hz₂ ⟨k₁.trans k₂.symm, fun x => ?_⟩
      rw [LinearEquiv.trans_apply, hk₁, ← hk₂, LinearEquiv.symm_apply_apply]
    refine hc.mono ?_
    rintro z' ⟨hz', c, hcz⟩
    obtain ⟨t, -, hu⟩ := hbuild i z hz
    obtain ⟨t', -, hu'⟩ := hbuild i z' hz'
    have ht' := hθ i z' hz' t' hu'
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha⟩ := _root_.GlobalTheory.coset_of_hasTh h1 h2 o g (n ^ j) J b _ _ t' n ℂ (𝟙 _) (θ i z') ⊥ hn.two_le
        (dvd_pow_self n hj1) ht' Ideal.isPrime_bot 0
      apply ha
      rw [hcz]
      simp
    rw [hcz] at ht'
    have hm := hqt j hj0 o b em t t' (θ i z) c hc0 (hsh i z hz t hu) (hsh i z' hz' t' hu') (hθ i z hz t hu) ht'
    obtain ⟨gm, h, hgm⟩ := _root_.GlobalTheory.exists_lattice_aut_of_tMap_id o g ((n ^ j) ^ 2) J b em w w' t t' (La i) (EF i) (lam i) (ac i) (Q i z) (Q i z')
      (Hm i z) (Hm i z') ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1.1 ((hfam i).2.2.2.2.2.2.2.2.1 z' hz').1.1 hu hu' hm
    exact Set.mem_iUnion.2 ⟨gm, hz', h, hgm⟩
  · intro t ht
    obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact ⟨i, bb, hbb, hθ i bb hbb t hu⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPts

theorem exists_geomPt (S : Scheme.{0}) (p : S) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S), Set.range x = {p} := by
  refine ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) (AlgebraicClosure (S.residueField p))))
      ≫ S.fromSpecResidueField p, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨IsLocalRing.closedPoint _, ?_⟩, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

theorem eq_comp_section {S X : Scheme.{0}} (g : X ⟶ S) [IsSeparated g] (τ : S ⟶ X) (w : τ ≫ g = 𝟙 S) {k : Type}
    [Field k] (x : Sp k ⟶ S) (z : Sp k ⟶ X) (hz : z ≫ g = x)
    (h : z (IsLocalRing.closedPoint k) ∈ Set.range τ) : x ≫ τ = z := by
  have : IsClosedImmersion (τ ≫ g) := by rw [w]; infer_instance
  have : IsClosedImmersion τ := IsClosedImmersion.of_comp _ g
  have : Surjective (pullback.fst z τ) := ⟨fun q => by
    rw [← Set.mem_range, Scheme.Pullback.range_fst, Subsingleton.elim q (IsLocalRing.closedPoint k)]
    exact h⟩
  have : IsIso (pullback.fst z τ) := isIso_of_isClosedImmersion_of_surjective _
  have e : (inv (pullback.fst z τ) ≫ pullback.snd z τ) ≫ τ = z := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  rw [← hz, ← e]
  simp only [Category.assoc, reassoc_of% w]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {J : Type}
    (σ : J → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (σ j).left) ↔ ∃ j, toUnit (Over.mk x) ≫ σ j = z := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨IsLocalRing.closedPoint k, rfl⟩)
    exact ⟨j, Over.OverMorphism.ext (eq_comp_section G.hom (σ j).left (Over.w _) x z.left (Over.w z) hj)⟩
  · rintro ⟨j, rfl⟩ _ ⟨q, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, _, (Scheme.Hom.comp_apply _ _ _).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {P : Ideal (𝓞 E)} {p i : ℕ}

theorem heckeSet_eq {S : Scheme.{0}} {t : SAB H S} {K K' : Set t.G.left} (hp : p ≠ 0) (h : HeckeSet D t P p i K)
    (h' : HeckeSet D t P p i K') (hle : K ⊆ K') : K = K' := by
  refine hle.antisymm fun g hg => ?_
  obtain ⟨k, _, _, z, hz⟩ := exists_geomPt _ g
  obtain ⟨C, hC, hk⟩ := h k (z ≫ t.G.hom)
  obtain ⟨C', hC', hk'⟩ := h' k (z ≫ t.G.hom)
  have : Finite C' := Nat.finite_of_card_ne_zero (by rw [hk'.2.2.2.2.1]; exact pow_ne_zero _ hp)
  have e : C = C' := Subgroup.eq_of_le_of_card_ge (fun u hu => (hC' u).2 (((hC u).1 hu).trans hle))
    (by rw [hk.2.2.2.2.1, hk'.2.2.2.2.1])
  have m : (Over.homMk z rfl : Over.mk (z ≫ t.G.hom) ⟶ t.G) ∈ C := by
    rw [e, hC']
    exact hz.subset.trans (Set.singleton_subset_iff.2 hg)
  exact (hC _).1 m (hz.symm.subset rfl)

theorem pow_eq_one {S : Scheme.{0}} {t : SAB H S} {T : Over S} {C : Subgroup (T ⟶ t.G)} (hp : (p : 𝓞 E) ∈ P)
    (h : t.HeckeKer T D P p i C) {x : T ⟶ t.G} (hx : x ∈ C) : x ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span t x (p ^ 2)).1 fun a ha => h.2.2.1 hx a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp
  rwa [map_natCast] at this

theorem exists_set (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp (KA l)} (o : Ob D l s)
    (C : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G)) (h : o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C) :
    ∃ K : Set o.t.G.left, EtSet o.t.G K ∧ HeckeSet D o.t P p i K ∧ (∀ z, z ∈ C ↔ Set.range z.left ⊆ K) ∧
      ∀ K', (∀ z ∈ C, Set.range z.left ⊆ K') → K ⊆ K' := by
  have := o.proper
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [h.2.2.2.2.1]; exact pow_ne_zero _ hA.2.2.1.ne_zero)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let σ : Fin n → (𝟙_ (Over (Sp k)) ⟶ o.t.G) := fun j => (e.symm j).1
  have tu : ∀ j, toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j = (e.symm j).1 := fun j => by
    apply Over.OverMorphism.ext
    simp [σ]
  have hσ : ∀ j, σ j ^ p ^ 2 = 1 := fun j => pow_eq_one (T := 𝟙_ (Over (Sp k))) hA.2.2.2.1 h (e.symm j).2
  have hC : (C : Set _) = Set.range (fun j => toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j) := by
    ext z
    refine ⟨fun hz => ⟨e ⟨z, hz⟩, by simp only [tu, Equiv.symm_apply_apply]⟩, ?_⟩
    rintro ⟨j, rfl⟩
    simp only [tu]
    exact (e.symm j).2
  obtain ⟨V, -, hV⟩ := _root_.GlobalTheory.exists_clopen_heckeKer_iff E H D l P p i n _ s o σ hA hσ
  have h1 : Set.range (𝟙 (Sp k) :) ⊆ V := (hV k _).2 ⟨fun a b hab => e.symm.injective (Subtype.ext
    (Over.OverMorphism.ext (by simpa [σ] using hab))), C, hC, h⟩
  have h2 := fun (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) =>
    (hV k' x).1 fun q _ => h1 ⟨q, rfl⟩
  refine ⟨⋃ j, Set.range (σ j).left, ?_, fun k' _ _ x => ?_, fun z => ?_, fun K' hK' => ?_⟩
  · obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_id o.t
    refine GlobalTheory.HkFam.etSet_of_lists _ _ (𝟙 _) o.t.G o.t.G m.φ (p ^ 2) n σ _
      ⟨o.t.semi.comm, o.t.semi.smooth, inferInstance, o.t.semi.geomConnected⟩ m.cart ?_ inferInstance inferInstance
      inferInstance ⟨hσ, by rw [hm]; rfl, fun k' _ _ x => (h2 k' x).1⟩
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  · obtain ⟨C', hC', hk⟩ := (h2 k' x).2
    refine ⟨C', fun z => ?_, hk⟩
    rw [range_subset_iff, ← SetLike.mem_coe, hC']
    rfl
  · rw [range_subset_iff, ← SetLike.mem_coe, hC]
    rfl
  · exact Set.iUnion_subset fun j => hK' _ (e.symm j).2

theorem existsUnique_carries {Xo : Moduli D l} (Z : KerScheme Xo P p i) (hA : admitted l P p) (k : Type) [Field k]
    [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (h : Xo.univ.t.HeckeKer (Over.mk y) D P p i C) : ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y rfl rfl
    (by simp [spMap]) Xo.univ
  have key : ∀ y' : Sp k ⟶ Xo.X, 𝟙 _ ≫ y = y' → ∀ C : Subgroup (Over.mk y' ⟶ Xo.univ.t.G),
      Xo.univ.t.HeckeKer (Over.mk y') D P p i C → ∃ C' : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C' ∧
      ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk y' ⟶ Xo.univ.t.G), v.left = u.left ≫ m.toSABMap.φ →
        (u ∈ C' ↔ v ∈ C) := by
    rintro _ rfl C h
    obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk (𝟙 (Sp k)))
    have hh : ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk (𝟙 _ ≫ y) ⟶ Xo.univ.t.G),
        v.left = u.left ≫ m.toSABMap.φ → (u ∈ Subgroup.comap ρ.toMonoidHom C ↔ v ∈ C) := fun u v e => by
      rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
      rfl
    exact ⟨_, (GlobalTheory.HkSetPull.heckeKer_iff D P p i m.toSABMap (Over.mk (𝟙 (Sp k))) _ C hh).2 h, hh⟩
  obtain ⟨C', h', hCC⟩ := key y (Category.id_comp _) C h
  obtain ⟨K, het, hK, hmem, hmin⟩ := exists_set hA o C' h'
  obtain ⟨z, ⟨hz, n, hn⟩, huniq⟩ := Z.rep _ (y ≫ Xo.s) inferInstance o K het hK
  have cc := fun z : Sp k ⟶ Z.Hk => (GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₁ o).2
    Z.π₁ z Z.m₁
  have pre : ∀ {z : Sp k ⟶ Z.Hk} (n : ObjMap o Z.o₁ z) (w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      Set.range (w.left ≫ n.toSABMap.φ) ⊆ Z.K ↔ Set.range w.left ⊆ n.toSABMap.φ ⁻¹' Z.K := fun n w => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_subset_iff]
  refine ⟨z, ?_, fun z' hz' => huniq z' ?_⟩
  · obtain ⟨m', hm'⟩ := (cc z).1 n
    have e : z ≫ Z.π₁ = y := (Xo.rep _ (y ≫ Xo.s) inferInstance o).unique
      ⟨(Category.assoc _ _ _).trans hz, ⟨m'⟩⟩ ⟨rfl, ⟨m⟩⟩
    have rigid : ∀ (y' : Sp k ⟶ Xo.X) (m' : ObjMap o Xo.univ y'), y = y' → m'.toSABMap.φ = m.toSABMap.φ := by
      rintro _ m' rfl
      exact GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o y (.inl inferInstance) _ _
        fun a => ⟨_, m'.eta a, m.eta a⟩
    refine ⟨e, fun u v huv => ?_⟩
    let w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G := Over.homMk (n.cart.1.lift u.left (𝟙 _) (by simpa using Over.w u))
      (n.cart.1.lift_snd _ _ _)
    have hw : w.left ≫ n.toSABMap.φ = u.left := n.cart.1.lift_fst _ _ _
    rw [← hCC w v (by rw [huv, ← hw, Category.assoc, ← hm', rigid _ m' e.symm]), hmem, hn, ← pre, hw]
  · obtain ⟨rfl, hc⟩ := hz'
    obtain ⟨n', hn'⟩ := (cc z').2 m
    refine ⟨(Category.assoc _ _ _).symm, n', heckeSet_eq hA.2.2.1.ne_zero hK
      (GlobalTheory.HkSetPull.heckeSet_pull D P p i n'.toSABMap _ Z.hecke) (hmin _ fun w hw => ?_)⟩
    have ww : w.left ≫ o.t.G.hom = 𝟙 _ := Over.w w
    let u : Over.mk z' ⟶ Z.o₁.t.G := Over.homMk (w.left ≫ n'.toSABMap.φ) (by
      rw [Category.assoc, n'.cart.1.w, reassoc_of% ww]; rfl)
    let v : Over.mk (z' ≫ Z.π₁) ⟶ Xo.univ.t.G := Over.homMk (w.left ≫ m.toSABMap.φ) (by
      rw [Category.assoc, m.cart.1.w, reassoc_of% ww]; rfl)
    exact (pre n' w).1 ((hc u v ((congrArg (w.left ≫ ·) hn').trans (Category.assoc _ _ _).symm)).2 ((hCC w v rfl).1 hw))

end GlobalTheory.HkPts

theorem GlobalTheory.kerScheme_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo 𝔓 p i), admitted l 𝔓 p → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C → ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C) ∧ (i ≤ D.p + D.q → Surjective Z.π₁) := by
  intro E _ _ _ H D l Xo P p i Z hA
  refine ⟨GlobalTheory.HkPts.existsUnique_carries Z hA, fun hi => ⟨fun q => ?_⟩⟩
  obtain ⟨k, _, _, y, hy⟩ := GlobalTheory.HkPts.exists_geomPt _ q
  obtain ⟨C, hC⟩ := GlobalTheory.exists_heckeKer E H D l Xo P p i hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 hi k y
  obtain ⟨z, ⟨rfl, -⟩, -⟩ := GlobalTheory.HkPts.existsUnique_carries Z hA k y C hC
  obtain ⟨a, ha⟩ := hy.symm.subset rfl
  exact ⟨z a, (Scheme.Hom.comp_apply _ _ _).symm.trans ha⟩
end

