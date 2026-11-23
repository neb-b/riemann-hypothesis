module

public import Mathlib
public import GroundTheory.TateCohomology.Bundle0007
public import GroundTheory.TateCohomology.Bundle0005
public import GroundTheory.TateCohomology.CupTateShift
public import GroundTheory.TateCohomology.Bundle0001
public import GroundTheory.TateCohomology.DimensionShift
public import GroundTheory.TateCohomology.TateConnecting
public import GroundTheory.TateCohomology.CoresRes

@[expose] public section

-- bundled from GroundTheory.TateCohomology.CohTrivialPGroup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

section Helpers

universe u

variable {k H : Type u} [CommRing k] [Group H] {A B : Rep.{u} k H}

theorem hom_nsmul_apply (f : A ⟶ B) (n : ℕ) (x : A) : f.hom (n • x) = n • f.hom x :=
  map_nsmul f.hom.toLinearMap n x

theorem hom_zero_apply (f : A ⟶ B) : f.hom 0 = 0 :=
  map_zero f.hom.toLinearMap

end Helpers

variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]

theorem isZero_tateCohomology_of_nsmul_injective {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) (A : Rep ℤ H) (n : ℤ)
    (hinj : Function.Injective fun x : tateCohomology A n => p • x) :
    IsZero (tateCohomology A n) := by
  obtain ⟨m, hm⟩ := hH.exists_card_eq
  have hcard : Fintype.card H = p ^ m := by rw [← Nat.card_eq_fintype_card, hm]
  have key : ∀ (j : ℕ) (x : tateCohomology A n), p ^ j • x = 0 → x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      apply ih
      apply hinj
      change p • (p ^ j • x) = p • 0
      rw [smul_zero, ← mul_smul, ← pow_succ']
      exact hx
  have : Subsingleton (tateCohomology A n) :=
    ⟨fun x y => by
      rw [key m x (hcard ▸ card_smul_tateCohomology A n x),
        key m y (hcard ▸ card_smul_tateCohomology A n y)]⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem tateAcyclic_of_shortExact_of_comp_eq_nsmul {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) {S : ShortComplex (Rep ℤ H)} (hS : S.ShortExact) (e : S.X₂ ≅ S.X₁)
    (hf : S.f ≫ e.hom = p • 𝟙 S.X₁) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ := by
  intro n
  have hmono : Mono ((tateCohomologyFunctor n).map S.f) := by
    have h : Mono ((tateCohomologyFunctor (n - 1 + 1)).map S.f) :=
      (TateCohomology.exact₁ hS (n - 1)).mono_g ((h₃ (n - 1)).eq_of_src _ _)
    rwa [sub_add_cancel] at h
  have : (tateCohomologyFunctor (R := ℤ) (G := H) n).Additive := by
    unfold tateCohomologyFunctor; infer_instance
  have hmono' : Mono ((tateCohomologyFunctor n).map (p • 𝟙 S.X₁)) := by
    rw [← hf, Functor.map_comp]
    infer_instance
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at hmono'
  have hinj := (ModuleCat.mono_iff_injective _).1 hmono'
  refine isZero_tateCohomology_of_nsmul_injective hH S.X₁ n fun a b hab => hinj ?_
  simpa using hab

theorem tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion (hG : IsPGroup p G)
    (A : Rep ℤ G) (hA : ∀ x : A, p • x = 0 → x = 0) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let f : A ⟶ A := p • 𝟙 A
  have hf : Function.Injective f.hom := fun a b hab => by
    have h : p • (a - b) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [f, nsmul_id_hom_apply] using hab
    exact sub_eq_zero.mp (hA _ h)
  have : Mono f := (Rep.mono_iff_injective f).2 hf
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
      mono_f := inferInstanceAs (Mono f)
      epi_g := coequalizer.π_epi }
  have hC : IsZero (tateCohomology S.X₃ q) :=
    (TateCohomology.exact₃ hS q).isZero_X₂ (h₁.eq_of_src _ _) (h₂.eq_of_tgt _ _)
  have hCt : ∀ y : S.X₃, p • y = 0 := by
    have hsurj : Function.Surjective (cokernel.π f).hom :=
      (Rep.epi_iff_surjective _).1 coequalizer.π_epi
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have h0 := congrArg (fun φ : A ⟶ cokernel f => φ.hom x) (cokernel.condition f)
    simp only [Rep.hom_comp, Rep.zero_hom] at h0
    rw [← hom_nsmul_apply, ← nsmul_id_hom_apply]
    exact h0
  obtain ⟨tC, cC⟩ := tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero hG S.X₃ hCt q hC
  have hf0 : S.f ≫ (Iso.refl S.X₁).hom = p • 𝟙 S.X₁ := Category.comp_id _
  have t := tateAcyclic_of_shortExact_of_comp_eq_nsmul hG hS (Iso.refl S.X₁) hf0 tC
  refine ⟨t, ?_⟩
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have h₃ : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact cC H
  have hf' : (S.map (resFunctor H.subtype)).f ≫ (Iso.refl (S.map (resFunctor H.subtype)).X₁).hom =
      p • 𝟙 (S.map (resFunctor H.subtype)).X₁ := by
    show (resFunctor H.subtype).map (p • 𝟙 A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have c := tateAcyclic_of_shortExact_of_comp_eq_nsmul (hG.to_subgroup H) hS'
    (Iso.refl (S.map (resFunctor H.subtype)).X₁) hf' h₃
  rw [ShortComplex.map_X₁] at c
  exact c

theorem tateAcyclic_cohTrivial_of_isZero_of_isZero (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let π : Rep.free ℤ G A.V ⟶ A := Rep.freeLift ℤ G A fun a => a
  have hπ : Function.Surjective π.hom := fun a =>
    ⟨Finsupp.single a (MonoidAlgebra.single 1 1), by
      have hmod : A.hV2 = AddCommGroup.toIntModule A.V := Subsingleton.elim _ _
      simp only [π]
      simp
      rw [hmod]
      exact one_zsmul a⟩
  have : Epi π := (Rep.epi_iff_surjective π).2 hπ
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
      mono_f := equalizer.ι_mono
      epi_g := inferInstanceAs (Epi π) }
  have hfree : ∀ x : Rep.free ℤ G A.V, p • x = 0 → x = 0 := fun x hx =>
    (smul_eq_zero.mp hx).resolve_left (Fact.out : p.Prime).ne_zero
  have hK : ∀ x : S.X₁, p • x = 0 → x = 0 := by
    have hinj : Function.Injective (kernel.ι π).hom :=
      (Rep.mono_iff_injective _).1 equalizer.ι_mono
    intro x hx
    apply hinj
    rw [hom_zero_apply]
    apply hfree
    rw [← hom_nsmul_apply, hx, hom_zero_apply]
  have h2 : TateAcyclic S.X₂ := tateAcyclic_free A.V
  have k₁ : IsZero (tateCohomology S.X₁ (q + 1)) :=
    h₁.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS q) (isIso_δ_of_tateAcyclic hS h2 q)).symm
  have k₂ : IsZero (tateCohomology S.X₁ (q + 1 + 1)) :=
    h₂.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS (q + 1))
      (isIso_δ_of_tateAcyclic hS h2 (q + 1))).symm
  obtain ⟨tK, cK⟩ :=
    tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion hG S.X₁ hK (q + 1) k₁ k₂
  have t3 := TateAcyclic.of_shortExact_X₁ hS h2 tK
  have c2 : CohTrivial S.X₂ := cohTrivial_free A.V
  have c3 := CohTrivial.of_shortExact_X₁ hS c2 cK
  exact ⟨t3, c3⟩

theorem cohTrivial_of_isZero_of_isZero (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    CohTrivial A :=
  (tateAcyclic_cohTrivial_of_isZero_of_isZero hG A q h₁ h₂).2

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.CupTate
section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tensorInvariants {A B : Rep.{u} k G} (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ B).ρ.invariants :=
  ⟨x.1 ⊗ₜ[k] y.1, fun g => by
    change A.ρ g x.1 ⊗ₜ[k] B.ρ g y.1 = x.1 ⊗ₜ[k] y.1
    rw [x.2 g, y.2 g]⟩


omit [Fintype G] in
theorem cupH_zero_zero_π {A B : Rep.{u} k G} (f : (Fin 0 → G) → A) (g : (Fin 0 → G) → B)
    (hf : (inhomogeneousCochains.d A 0).hom f = 0) (hg : (inhomogeneousCochains.d B 0).hom g = 0)
    (fg : (Fin 0 → G) → (A ⊗ B : Rep k G)) (hfg : (inhomogeneousCochains.d (A ⊗ B) 0).hom fg = 0)
    (h : ∀ v, fg v = f v ⊗ₜ[k] g v) :
    cupH rfl (π A 0 (cocyclesMk f hf)) (π B 0 (cocyclesMk g hg)) = π (A ⊗ B) 0 (cocyclesMk fg hfg) := by
  rw [cupH_π]
  congr 1
  apply cocycles_ext
  rw [iCocycles_cupCocycles, iCocycles_mk, iCocycles_mk, iCocycles_mk]
  funext v
  rw [cupCochain_apply, h]
  have hv : ∀ w : Fin 0 → G, w = v := fun w => Subsingleton.elim _ _
  rw [hv (fun i : Fin 0 => v ⟨i, by omega⟩), hv (fun j : Fin 0 => v ⟨0 + j, by omega⟩)]
  simp [Fin.partialProd]


set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem tateCup_zero_zero (A B : Rep.{u} k G) (x : A.ρ.invariants) (y : B.ρ.invariants) :
    tateCup 0 0 A B 0 (add_zero 0)
        (((tateCohomologyZeroIso k G).app A).inv.hom (Submodule.Quotient.mk x))
        (((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y)) =
      ((tateCohomologyZeroIso k G).app (A ⊗ B)).inv.hom
        (Submodule.Quotient.mk (tensorInvariants x y)) := by
  obtain ⟨zA, hzA⟩ := exists_tateComplex_cycles_zero A x
  obtain ⟨zB, hzB⟩ := exists_tateComplex_cycles_zero B y
  obtain ⟨zAB, hzAB⟩ := exists_tateComplex_cycles_zero (A ⊗ B) (tensorInvariants x y)
  rw [tateCohomologyZeroIso_inv_mk A zA x hzA.symm, tateCohomologyZeroIso_inv_mk B zB y hzB.symm,
    tateCohomologyZeroIso_inv_mk (A ⊗ B) zAB _ hzAB.symm]
  rw [tateCup_of_nonpos 0 le_rfl]
  apply moduleIso_hom_injective (tateLeftIso A B 0)
  rw [tateLeftIso_cupL, tateCup_of_pos_of_nonpos (by norm_num) le_rfl]
  apply moduleIso_hom_injective (tateRightIso (augIdeal k G ⊗ A) B (0 + 1))
  rw [tateRightIso_cupR]
  apply moduleIso_hom_injective (tateIsoH ((augIdeal k G ⊗ A) ⊗ (augIdeal k G ⊗ B)) (0 + 1 + 1) 2
    (by norm_num))
  have hA1 := tateIsoH_tδ_homologyπ (augSES_shortExact A) 0 zA
  have hB1 := tateIsoH_tδ_homologyπ (augSES_shortExact B) 0 zB
  have hAB1 := tateIsoH_tδ_homologyπ (augSES_tensorRight_shortExact A B) 0 zAB
  have hxA : ∀ v, ((tateComplex A).iCycles 0).hom zA v = x.1 := fun v => congrFun hzA v
  have hyB : ∀ v, ((tateComplex B).iCycles 0).hom zB v = y.1 := fun v => congrFun hzB v
  have hxyAB : ∀ v, ((tateComplex (A ⊗ B)).iCycles 0).hom zAB v = x.1 ⊗ₜ[k] y.1 :=
    fun v => congrFun hzAB v
  have hcup0 := cupH_zero_zero_π _ _ (tate_d_iCycles A 0 zA) (tate_d_iCycles B 0 zB) _
    (tate_d_iCycles (A ⊗ B) 0 zAB)
    (fun v => (hxyAB v).trans (congrArg₂ (fun a b => a ⊗ₜ[k] b) (hxA v).symm (hyB v).symm))
  have e_left := δ_cupH_left (augSES_shortExact A) B (augSES_tensorRight_shortExact A B)
    (p := 0) (q := 0) rfl rfl
    (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA)))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_right := δ_cupH_right (augSES_shortExact B) (augIdeal k G ⊗ A)
    (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) (p := 0) (q := 1) rfl rfl
    (δ (augSES_shortExact A) 0 (0 + 1) rfl
      (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA))))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_br := congr(($(tδ_comp_tateIsoH (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1)).hom
    ((tateLeftIso A B 0).hom.hom (((tateComplex (A ⊗ B)).homologyπ 0).hom zAB)))
  have e_base := tateIsoH_tateCup (n := 1) (m := 1) (l := 2) (p := 0 + 1) (q := 0 + 1) (r := 0 + 1 + 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (augIdeal k G ⊗ A) (augIdeal k G ⊗ B) ((augShiftδ A 0).hom (((tateComplex A).homologyπ 0).hom zA))
    ((augShiftδ B 0).hom (((tateComplex B).homologyπ 0).hom zB))
  refine Eq.trans (moduleHom_smul _ _ _) ?_
  refine Eq.trans (congrArg (tsgn k (0 + 1) • ·) e_base) ?_
  refine Eq.trans (congrArg₂ (fun s t => tsgn k (0 + 1) • cupH (show 1 + 1 = 2 by rfl) s t)
    hA1 hB1) ?_
  refine Eq.trans ?_ e_br.symm
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1 (1 + 1)
    rfl).hom hAB1).symm
  refine Eq.trans ?_ (congrArg (fun t => δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl (δ (augSES_tensorRight_shortExact A B) 0 (0 + 1) rfl t)) hcup0)
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl).hom e_left).symm
  refine Eq.trans ?_ e_right.symm
  have hs : tsgn k (0 + 1) = (-1 : k) ^ 1 := by
    rw [tsgn_add_one]
    simp [tsgn]
  rw [hs]
  rfl


set_option maxHeartbeats 800000 in
theorem tateCup_unique_of_agrees (μ : ∀ p q : ℤ, TateCupFam k G p q)
    (hpos : ∀ (n m l : ℕ) [NeZero n] [NeZero m] [NeZero l] (hl : n + m = l) (A B : Rep.{u} k G)
      (a : tateCohomology A n) (b : tateCohomology B m),
      (tateIsoH (A ⊗ B) l l rfl).hom.hom (μ n m A B l (by omega) a b) =
        cupH hl ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH B m m rfl).hom.hom b))
    (hleft : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        μ (p + 1) q (augIdeal k G ⊗ A) B (r + 1) (by omega)
          ((tδ (augSES_shortExact A) p (p + 1) rfl).hom a) b)
    (hright : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        tsgn k p • μ p (q + 1) A (augIdeal k G ⊗ B) (r + 1) (by omega) a
          ((tδ (augSES_shortExact B) q (q + 1) rfl).hom b))
    (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m → ∀ (A B : Rep.{u} k G) (r : ℤ)
      (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q),
      μ p q A B r h a b = tateCup p q A B r h a b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm A B r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso A B r)
    rw [tateLeftIso_cupL, tateLeftIso_hom]
    refine (hleft p q A B r h a b).trans ?_
    exact ih _ (by omega) (p + 1) q rfl _ _ _ _ _ _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A B r)
    rw [tateRightIso_cupR, tateRightIso_hom]
    refine (hright p q A B r h a b).trans ?_
    exact congrArg (tsgn k p • ·) (ih _ (by omega) p (q + 1) rfl _ _ _ _ _ _)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ B) l l rfl)
    rw [hpos n m' l hl, tateIsoH_tateCup rfl rfl rfl h hl]

theorem tateCup_δ_left {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
    (hEB : (E.map (tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology E.X₃ p) (b : tateCohomology B q) :
    (TateCohomology.δ hEB r).hom (tateCup p q E.X₃ B r h a b) =
      tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((TateCohomology.δ hE p).hom a) b :=
  tateCup_connecting_left _ p q rfl hE B hEB r h a b

theorem tateCup_δ_right {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  exact tateCup_connecting_right _ p q rfl hE A hAE r h a b

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.SplittingModule
section
set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section Construction

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)

theorem isZero_groupCohomology_coind_two : IsZero (groupCohomology (coindSES.obj M).X₂ 2) :=
  ((tateAcyclic_coindSES_X₂ M) 2).of_iso (tateIsoH _ 2 2 rfl).symm

theorem exists_cocycle_δ_eq : ∃ f : cocycles₁ (coindSES.obj M).X₃,
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ f) = u := by
  have : Epi (δ (coindSES_shortExact M) 1 2 rfl) :=
    epi_δ_of_isZero (coindSES_shortExact M) 1 (isZero_groupCohomology_coind_two M)
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective _).1 this u
  obtain ⟨f, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance v
  exact ⟨f, hv⟩

noncomputable def splittingCocycle : cocycles₁ (coindSES.obj M).X₃ :=
  (exists_cocycle_δ_eq M u).choose

theorem δ_splittingCocycle :
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ (splittingCocycle M u)) = u :=
  (exists_cocycle_δ_eq M u).choose_spec

noncomputable def splittingSES : ShortComplex (Rep.{u} k G) :=
  pullbackSES (coindSES.obj M) (cocycleHom (splittingCocycle M u))

theorem splittingSES_shortExact : (splittingSES M u).ShortExact :=
  pullbackSES_shortExact (cocycleHom (splittingCocycle M u)) (coindSES_shortExact M)

noncomputable abbrev splittingModule : Rep.{u} k G := (splittingSES M u).X₂


omit [Fintype G] in
theorem map_H1π_augCocycle {H : Type u} [Group H] (φ : H →* G) {A : Rep.{u} k G}
    (f : cocycles₁ A) :
    map (A := res φ (augIdeal k G)) (B := res φ A) (MonoidHom.id H)
      ((resFunctor φ).map (cocycleHom f)) 1 (H1π _ (augCocycle k φ)) =
    map φ (𝟙 (res φ A)) 1 (H1π A f) := by
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  congr 1
  apply cocycles₁_ext
  intro h
  exact cocycleHom_augIdealSubOne f (φ h)

noncomputable def splittingSESResHom {H : Type u} [Group H] (φ : H →* G) :
    (splittingSES M u).map (resFunctor φ) ⟶ (coindSES.obj M).map (resFunctor φ) where
  τ₁ := 𝟙 _
  τ₂ := (resFunctor φ).map (pullbackFst _ (cocycleHom (splittingCocycle M u)))
  τ₃ := (resFunctor φ).map (cocycleHom (splittingCocycle M u))
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2

theorem δ_splittingSES_res_δ₀ {H : Type u} [Group H] (φ : H →* G) :
    δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
      (δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ))) =
    map φ (𝟙 (res φ M)) 2 u := by
  rw [δ₀_augTrivSES_res]
  have hN := groupCohomology.δ_naturality ((shortExact_res φ).2 (splittingSES_shortExact M u))
    ((shortExact_res φ).2 (coindSES_shortExact M)) (splittingSESResHom M u φ) 1 2 rfl
  have e : (map (MonoidHom.id H) (𝟙 (res φ M)) 2).hom
      (δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
        (H1π (res φ (augIdeal k G)) (augCocycle k φ))) =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map (A := res φ (augIdeal k G)) (B := res φ (coindSES.obj M).X₃) (MonoidHom.id H)
          ((resFunctor φ).map (cocycleHom (splittingCocycle M u))) 1).hom
          (H1π _ (augCocycle k φ))) :=
    congr(($hN).hom (H1π _ (augCocycle k φ)))
  have hid : ∀ y, (map (A := res φ M) (B := res φ M) (MonoidHom.id H) (𝟙 (res φ M)) 2).hom y =
      y := fun y => by
    rw [groupCohomology.map_id]
    rfl
  have hR := congr(($(δ_comp_map_res φ (coindSES_shortExact M) 1 2 rfl)).hom
    (H1π _ (splittingCocycle M u)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hR
  have hR' : (map φ (𝟙 (res φ M)) 2).hom u =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map φ (𝟙 (res φ (coindSES.obj M).X₃)) 1).hom (H1π _ (splittingCocycle M u))) := by
    conv_lhs => rw [← δ_splittingCocycle M u]
    exact hR
  refine (hid _).symm.trans (e.trans ?_)
  rw [map_H1π_augCocycle φ (splittingCocycle M u)]
  exact hR'.symm

end Construction

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.TateResEqZeroOfNsmulEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateCores_app_tateRes_app_apply (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (n : ℤ)
    (x : tateCohomology A n) :
    ((tateCores S n).app A).hom (((tateRes S n).app A).hom x) = S.index • x := by
  have h := congrArg (fun f => f.hom x) (tateRes_app_comp_tateCores_app S A n)
  simpa using h

end GroundTheory.GroupCoh
end

