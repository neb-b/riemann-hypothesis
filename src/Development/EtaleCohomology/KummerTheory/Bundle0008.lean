module

public import Development.EtaleCohomology.KummerTheory.Bundle0002
public import Development.EtaleCohomology.KummerTheory.FinalTheorems
public import Development.EtaleCohomology.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.ISupFinSuccEq
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.IndPf

open LateralTheory.KummerTheory.ContCut

theorem isMV_opens {Y : Scheme.{0}} (U V : Y.Opens) (h : U ⊔ V = ⊤) :
    IsMV (Y.homOfLE inf_le_left) (Y.homOfLE inf_le_right) U.ι V.ι := by
  refine ⟨inferInstance, inferInstance, isPullback_opens_inf U V, fun x => ?_⟩
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  have hx : x ∈ (U ⊔ V) := by rw [h]; trivial
  exact hx

theorem inf_affine {Y : Scheme.{0}} {R : CommRingCat.{0}} (q : Y ⟶ Spec R) [IsSeparated q]
    {V₁ V₂ : Y.Opens} (h1 : IsAffineOpen V₁) (h2 : IsAffineOpen V₂) : IsAffineOpen (V₁ ⊓ V₂) :=
  (isAffineHom_diagonal_iff (f := q)).mp inferInstance ⊤ (isAffineOpen_top _) V₁ (by simp) V₂ (by simp) h1 h2

theorem iSup_fin_succ_eq {Y : Scheme.{0}} {n : ℕ} (V : Fin (n + 1) → Y.Opens) :
    (⨆ i, V i) = (⨆ i : Fin n, V i.castSucc) ⊔ V (Fin.last n) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup (fun j : Fin n => V j.castSucc) j)
  · exact sup_le (iSup_le fun j => le_iSup V j.castSucc) (le_iSup V _)

theorem main (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop)
    (hA : ∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p)
    (hM : ∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
      P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) :
    ∀ (n : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Spec R) [IsSeparated q] (V : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (V i)) → (⨆ i, V i) = ⊤ → P Y q := by
  intro n
  induction n with
  | zero =>
    intro Y q _ V _ hV
    have : IsEmpty Y := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⊤ : Y.Opens) := trivial
      rw [← hV] at hx
      obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact i.elim0
    have : IsAffine Y := inferInstance
    exact hA Y q
  | succ n ih =>
    intro Y q _ V hA' hV
    set U : Y.Opens := ⨆ i : Fin n, V i.castSucc with hUdef
    set V' : Y.Opens := V (Fin.last n)
    have hUV : U ⊔ V' = ⊤ := by rw [← hV, iSup_fin_succ_eq]
    refine hM _ _ U.ι V'.ι q (isMV_opens U V' hUV) ?_ ?_ ?_
    ·
      refine ih U (U.ι ≫ q) (fun i => U.ι ⁻¹ᵁ V i.castSucc) (fun i => ?_) ?_
      · exact (hA' _).preimage_of_isOpenImmersion U.ι
          (by rw [Scheme.Opens.opensRange_ι]; exact le_iSup (fun j : Fin n => V j.castSucc) i)
      · rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
    · have : IsAffine V' := hA' (Fin.last n)
      exact hA _ _
    ·
      rw [← Category.assoc, Scheme.homOfLE_ι]
      refine ih _ ((U ⊓ V').ι ≫ q) (fun i => (U ⊓ V').ι ⁻¹ᵁ (V i.castSucc ⊓ V')) (fun i => ?_) ?_
      · exact (inf_affine q (hA' _) (hA' _)).preimage_of_isOpenImmersion _
          (by rw [Scheme.Opens.opensRange_ι]
              exact inf_le_inf_right _ (le_iSup (fun j : Fin n => V j.castSucc) i))
      · rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]

theorem Ind_of : LateralTheory.KummerTheory.ContCut.Ind := by
  intro R P hA hM X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, hU⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
    (U := Set.univ)).mp ⟨isCompact_univ, isOpen_univ⟩
  have : Finite s := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine main R P hA hM n X p (fun i => ((e.symm i : s) : X.affineOpens)) (fun i => (e.symm i : s).1.2) ?_
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e ⟨a, ha⟩, ?_⟩
  simpa using hxa

end LateralTheory.KummerTheory.IndPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.LHCutGlue
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem ghostSec_of (hG : Ghost) (h1 : Corep) (h2 : HomKill) : GhostSec := by
  intro Λ _ S C hi hz N m hl j hj U x hx
  have : C.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi => hz i hi)
  obtain ⟨P, z, hP⟩ := h1 Λ S U
  obtain ⟨f, rfl⟩ := (hP (C.X j)).2 x
  obtain ⟨g, hg⟩ := hG (SlShv Λ S) C hi N m (fun j hj => h2 Λ S C N j (hl j hj)) j hj P f
    ((hP _).1 (hx.trans rfl))
  refine ⟨(g.hom.app (op U)).hom z, ?_⟩
  have := congrArg (fun φ : P ⟶ C.X j => (φ.hom.app (op U)).hom z) hg
  refine this.trans ?_
  generalize N ^ (m + 1) = k
  induction k with
  | zero => simp only [zero_smul]; rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

theorem glob_of (h1 : ConeCx) (h2 : GhostSec) : Glob := by
  intro Λ _ I J K μ hJ hK X S p r M γ hc N m hl j hj U x hx
  obtain ⟨C, hi, hz, e, he, hd⟩ := h1 Λ μ hJ hK p r M γ hc
  have hloc : ∀ j : ℤ, j < m → CxLoc C N j := by
    intro j hj U x hx u
    obtain ⟨V, g, hg, y, hy⟩ := hl j hj U (e j U x) (by rw [← hd j (j + 1) rfl, hx, map_zero]) u
    refine ⟨V, g, hg, (e _ V).symm y, (e j V).injective ?_⟩
    rw [hd (j - 1) j (by omega), AddEquiv.apply_symm_apply, hy, map_nsmul, he]
  obtain ⟨y, hy⟩ := h2 Λ S C hi hz N m hloc j hj U ((e j U).symm x) ((e (j + 1) U).injective (by
    rw [hd j (j + 1) rfl, AddEquiv.apply_symm_apply, hx, map_zero]))
  refine ⟨e _ U y, ?_⟩
  rw [← hd (j - 1) j (by omega), hy, map_nsmul, AddEquiv.apply_symm_apply]

theorem clsMore_of (hD : Dict) : ClsMore := by
  intro Λ _ I X n
  obtain ⟨_, d2, d3, d4, _⟩ := hD Λ I X n
  have h0 : IsCls (0 : CochainComplex.HomComplex.CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 := by
    obtain ⟨a, ha⟩ := d2 0
    have := (d4 _ _ _ _ ha (d4 _ _ _ _ ha ha).2).1
    rwa [add_neg_cancel, add_neg_cancel] at this
  refine ⟨h0, ?_, ?_, ?_⟩
  · intro N x a h
    induction N with
    | zero => rw [zero_nsmul, zero_nsmul]; exact h0
    | succ N ih => rw [succ_nsmul, succ_nsmul]; exact (d4 _ _ _ _ ih h).1
  · intro ι _ x a h
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact h0
    | insert t s ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht]; exact (d4 _ _ _ _ (h t) ih).1
  · intro m hm x x' a a' h h'
    obtain rfl : m = n - 1 := by omega
    have := (d3 _ _ (d4 _ _ _ _ h (d4 _ _ _ _ h' h').2).1).2
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_zero] at this

theorem lh_of (hD : Dict) (hG : Ghost) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : ExIso) (h5 : ConeCx) (h6 : Corep)
    (h7 : HomKill) : LH :=
  goal_of hD h1 h2 h3 (glob_of h5 (ghostSec_of hG h6 h7)) h4

end LateralTheory.KummerTheory.LHCut
end

-- bundled from Development.EtaleCohomology.KummerTheory.LimAssemblePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def LimRatBij : Prop := ∀ (l : ℕ) [Fact l.Prime] (P Q : Type 1) [AddCommGroup P] [Module ℤ_[l] P] [AddCommGroup Q]
  [Module ℤ_[l] Q] (f : P →ₗ[ℤ_[l]] Q) (N : ℕ), 0 < N → IsoUpTo N f → Function.Bijective (f.baseChange ℚ_[l])

def LimRatAssemble : Prop := A9 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → (∀ a ≤ M, QBasis l (c a)) →
  ∀ (e : ∀ a : ℤ, Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i)
    (Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i),
  (∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s)) →
  Function.Bijective (Φ.baseChange ℚ_[l]) →
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0),
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y

theorem limAssembleCut (h1 : LimRatBij) (h2 : LimRatAssemble) : LimAssemble := by
  intro hA9 l _ X Y S pX pY n i M N r c hnM hN hB e Φ hΦ hiso
  exact h2 hA9 l pX pY n i M r c hnM hB e Φ hΦ (h1 l _ _ Φ N hN hiso)

theorem limRatBij : LimRatBij := by
  intro l _ P Q _ _ _ _ f N hN hiso
  have hPl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)
  have hQl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)
  have hNS : ((N : ℤ_[l])) ∈ nonZeroDivisors ℤ_[l] :=
    mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hN.ne')
  have hne : ∀ s ∈ nonZeroDivisors ℤ_[l], algebraMap ℤ_[l] ℚ_[l] s ≠ 0 := fun s hs =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hsm : ∀ {V : Type 1} [AddCommGroup V] [Module ℤ_[l] V] (s : nonZeroDivisors ℤ_[l]) (w : ℚ_[l] ⊗[ℤ_[l]] V),
      s • w = algebraMap ℤ_[l] ℚ_[l] s • w := fun s w => by
    rw [Submonoid.smul_def, algebraMap_smul]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) w
    simp only [TensorProduct.mk_apply] at hs
    have h1 : (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) (f x) = 0 := by
      rw [TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, ← hs, hsm, map_smul, hw, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mp h1
    have h2 : N • ((t : ℤ_[l]) • x) = 0 := hiso.1 _ (by rw [map_smul]; exact ht)
    have h3 : (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) x = 0 := by
      refine (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mpr
        ⟨⟨(N : ℤ_[l]) * t, Submonoid.mul_mem _ hNS t.2⟩, ?_⟩
      rw [Submonoid.mk_smul, mul_smul, Nat.cast_smul_eq_nsmul]; exact h2
    rw [TensorProduct.mk_apply] at h3
    rw [h3, hsm] at hs
    exact (smul_eq_zero.mp hs).resolve_left (hne _ s.2)
  · intro w
    obtain ⟨⟨z, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) w
    simp only [TensorProduct.mk_apply] at hs
    obtain ⟨x, hx⟩ := hiso.2 z
    have hc := hne _ (Submonoid.mul_mem _ hNS s.2)
    refine ⟨(algebraMap ℤ_[l] ℚ_[l] ((N : ℤ_[l]) * s))⁻¹ • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x), ?_⟩
    rw [map_smul, LinearMap.baseChange_tmul, hx, ← Nat.cast_smul_eq_nsmul ℤ_[l], TensorProduct.tmul_smul, ← hs,
      Submonoid.smul_def, ← mul_smul, ← algebraMap_smul ℚ_[l] ((N : ℤ_[l]) * s) w]
    exact inv_smul_smul₀ hc w

theorem hl_sub (hA9 : A9) (l : ℕ) [Fact l.Prime] (E : Spc) (m j : ℤ) (hm : m < 0) : Subsingleton (Hl l E m j) := by
  constructor
  intro x y
  apply Subtype.ext
  funext k
  exact ((hA9 (ZMod (l ^ k)) (tw (l ^ k) j)).1 E m hm).elim _ _

set_option maxHeartbeats 800000 in
theorem limRatAssemble : LimRatAssemble := by
  intro hA9 l _ X Y S pX pY n i M r c hnM hB e Φ hΦ hbij
  let T := fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0
  let g : ∀ a : ℤ, T a →ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i := fun a =>
    (TensorProduct.lift (e a)).baseChange ℚ_[l] ∘ₗ
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ_[l] ℚ_[l] _ _).symm.toLinearMap
  have hg : ∀ a x y, g a (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) =
      (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y := by
    intro a x y
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    erw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
    rw [LinearMap.baseChange_tmul, TensorProduct.lift.tmul, mul_one]
  let κ₀ := DirectSum.toModule ℚ_[l] ℤ _ g
  have hκ₀ : ∀ a x y, κ₀ (DirectSum.lof ℚ_[l] ℤ T a
      (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y := by
    intro a x y
    simp only [κ₀, DirectSum.toModule_lof]
    exact hg a x y
  have hsm : ∀ (a : ℤ) (t : ℤ_[l]) (y : Hl l (sch.obj Y) (n - a) 0) (u : HQ l (sch.obj X) a i),
      u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (t • y)) = algebraMap ℤ_[l] ℚ_[l] t • (u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) := by
    intro a t y u
    rw [← TensorProduct.tmul_smul, TensorProduct.tmul_smul (R := ℤ_[l]), algebraMap_smul]
  let ψ₀ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]] ⨁ a : ℤ, T a :=
    { toFun := fun y => ∑ a : Fin (M + 1), ∑ s : Fin (r a), DirectSum.lof ℚ_[l] ℤ T ((a : ℕ) : ℤ)
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c a s) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y a s))
      map_add' := fun y z => by
        simp only [Pi.add_apply, TensorProduct.tmul_add, map_add (f := _), Finset.sum_add_distrib]
      map_smul' := fun t y => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hsm, map_smul, algebraMap_smul] }
  let ψ := ψ₀.liftBaseChange ℚ_[l]
  have key : ∀ u, κ₀ (ψ u) = Φ.baseChange ℚ_[l] u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _)]
    | tmul q y =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul]
      change q • κ₀ (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _
      rw [hΦ y, TensorProduct.tmul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hκ₀, TensorProduct.tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hsurj : Function.Surjective ψ := by
    intro d
    suffices h : d ∈ LinearMap.range ψ from h
    induction d using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | of a t =>
      change DirectSum.lof ℚ_[l] ℤ T a t ∈ _
      by_cases ha0 : a < 0
      · haveI := hl_sub hA9 l (sch.obj X) a i ha0
        have : t = 0 := by
          induction t using TensorProduct.induction_on with
          | zero => rfl
          | add u v hu hv => rw [hu, hv, add_zero]
          | tmul u v =>
            have : u = 0 := by
              induction u using TensorProduct.induction_on with
              | zero => rfl
              | add u v hu hv => rw [hu, hv, add_zero]
              | tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
            rw [this, TensorProduct.zero_tmul]
        rw [this, map_zero]; exact Submodule.zero_mem _
      by_cases haM : (M : ℤ) < a
      · haveI := hl_sub hA9 l (sch.obj Y) (n - a) 0 (by omega)
        have : t = 0 := by
          induction t using TensorProduct.induction_on with
          | zero => rfl
          | add u v hu hv => rw [hu, hv, add_zero]
          | tmul u v =>
            have : v = 0 := by
              induction v using TensorProduct.induction_on with
              | zero => rfl
              | add u v hu hv => rw [hu, hv, add_zero]
              | tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
            rw [this, TensorProduct.tmul_zero]
        rw [this, map_zero]; exact Submodule.zero_mem _
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)
      have hm : m < M + 1 := by omega
      have hbase : ∀ (s : Fin (r m)) (q : ℚ_[l]) (y : Hl l (sch.obj Y) (n - (m : ℤ)) 0),
          DirectSum.lof ℚ_[l] ℤ T (m : ℤ) (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s) ⊗ₜ[ℚ_[l]] (q ⊗ₜ[ℤ_[l]] y)) ∈
            LinearMap.range ψ := by
        intro s q y
        refine ⟨q ⊗ₜ[ℤ_[l]] (Pi.single (M := fun a : Fin (M + 1) => Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
          ⟨m, hm⟩ (Pi.single s y)), ?_⟩
        rw [LinearMap.liftBaseChange_tmul]
        change q • (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _
        rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin (M + 1))]
        · rw [Finset.sum_eq_single s]
          · simp only [Pi.single_eq_same]
            rw [← map_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          · intro s' _ hs'; rw [Pi.single_eq_same, Pi.single_eq_of_ne hs', TensorProduct.tmul_zero,
              TensorProduct.tmul_zero, map_zero]
          · intro h; exact absurd (Finset.mem_univ s) h
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb]
          simp only [Pi.zero_apply, TensorProduct.tmul_zero, map_zero, Finset.sum_const_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hspan := (hB m (by omega)).2
      suffices goal : ∀ t' : HQ l (sch.obj X) (m : ℤ) i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - (m : ℤ)) 0,
          DirectSum.lof ℚ_[l] ℤ T (m : ℤ) t' ∈ LinearMap.range ψ from goal t
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add u v hu hv => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hv
      | tmul u v =>
        have hu : u ∈ Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s : HQ l (sch.obj X) (m : ℤ) i)) := by
          rw [hspan]; exact Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨s, rfl⟩ := hu
          induction v using TensorProduct.induction_on with
          | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
          | add v w hv hw => rw [TensorProduct.tmul_add, map_add (f := _)]; exact Submodule.add_mem _ hv hw
          | tmul q y => exact hbase s q y
        | zero => rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [TensorProduct.add_tmul, map_add (f := _)]; exact Submodule.add_mem _ hu hw
        | smul k u _ hu => rw [← TensorProduct.smul_tmul', map_smul]; exact Submodule.smul_mem _ k hu
  have hbijκ : Function.Bijective κ₀ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro d hd
      obtain ⟨u, rfl⟩ := hsurj d
      rw [key] at hd
      have : u = 0 := (injective_iff_map_eq_zero _).mp hbij.1 u hd
      rw [this, map_zero]
    · intro w
      obtain ⟨u, rfl⟩ := hbij.2 w
      exact ⟨ψ u, key u⟩
  exact ⟨LinearEquiv.ofBijective κ₀ hbijκ, fun a x y => hκ₀ a x y⟩

theorem LimAssemble_of : LimAssemble := limAssembleCut limRatBij limRatAssemble

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.LimExtHlPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem lex_red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (Ht.cast hn hi x) = Ht.cast hn hi (red Q q E n i x) := by
  subst hn hi; rfl

theorem lex_cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    Ht.cast hn hi (x + y) = Ht.cast hn hi x + Ht.cast hn hi y := by
  subst hn hi; rfl

theorem lex_cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    Ht.cast hn hi (m • x) = m • Ht.cast hn hi x := by
  subst hn hi; rfl

theorem lex_ext_red (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (a n i : ℤ) (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold ext
  rw [lex_red_cast, (hA Q q hq _).1, pull_red, pull_red]

theorem lex_ext_add_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x x' : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (x + x') y = ext q pX pY a n i x y + ext q pX pY a n i x' y := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), AddMonoidHom.add_apply, lex_cast_add]

theorem lex_ext_add_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht q (sch.obj X) a i) (y y' : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), lex_cast_add]

theorem lex_ext_nsmul_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (m • x) y = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, lex_cast_nsmul]

theorem lex_ext_nsmul_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, lex_cast_nsmul]

def lexF (hA : A11) (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0) : Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => ext (l ^ k) pX pY a n i (lev l x k) (lev l y k), fun k => by
    have : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change red (l ^ (k + 1)) (l ^ k) _ n i (ext (l ^ (k + 1)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))) =
      ext (l ^ k) pX pY a n i (x.1 k) (y.1 k)
    exact (lex_ext_red hA _ _ (pow_dvd_pow l (Nat.le_succ k)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))).trans
      (congrArg₂ _ (x.2 k) (y.2 k))⟩

theorem LimExtHl_of : LimExtHl := by
  intro hA l _ X Y S pX pY a n i
  refine ⟨LinearMap.mk₂ ℤ_[l] (lexF hA l pX pY a n i) ?_ ?_ ?_ ?_, fun x y k => ?_⟩
  · intro x x' y
    apply Subtype.ext; funext k
    exact lex_ext_add_left (l ^ k) pX pY a n i (x.1 k) (x'.1 k) (y.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i ((r • x).1 k) (y.1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_left (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · intro x y y'
    apply Subtype.ext; funext k
    exact lex_ext_add_right (l ^ k) pX pY a n i (x.1 k) (y.1 k) (y'.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i (x.1 k) ((r • y).1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_right (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · rfl

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.OneExPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def TwRes0 : Prop := ∀ (q : ℕ) [NeZero q] {U X : Scheme.{0}} (x : U ⟶ X) (ζ₀ : Prim q Γ(X, ⊤)) (ζ : Prim q Γ(U, ⊤)),
  Sec.res x (twGen 0 ζ₀) = twGen 0 ζ

def DegreeZeroSectionExists : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom s) h).symm

theorem OneEx_of (hT : TwSec) (hR : TwRes0) (hS : DegreeZeroSectionExists) : OneEx := by
  intro q _ A _ hA hq
  obtain ⟨⟨ζ₀⟩, -⟩ := hT q A hA hq
  obtain ⟨α, hα⟩ := hS (ZMod q) (tw q 0) (Spec (CommRingCat.of A)) (twGen 0 ζ₀)
  refine ⟨_, α, rfl, ?_⟩
  intro U x ζ
  refine (hα U x).trans ((sec_res_map (resι (ZMod q) (tw q 0)) (x : U ⟶ Spec (CommRingCat.of A)) (twGen 0 ζ₀)).trans ?_)
  rw [hR q (x : U ⟶ Spec (CommRingCat.of A)) ζ₀ ζ]
  rfl

end LateralTheory.KummerTheory
end
end

