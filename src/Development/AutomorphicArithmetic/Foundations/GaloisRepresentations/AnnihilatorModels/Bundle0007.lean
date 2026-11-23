module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.POrdDecomp
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison

private theorem val_map_sum {α P : Type} (s : Finset α) (f : α → P) :
    s.val.map f = ∑ x ∈ s, ({f x} : Multiset P) := by
  rw [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (s.val.map f)
  rw [Multiset.map_map] at h
  exact h.symm

open Classical in
private theorem partIn (hIn : CountIn) {k H P : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j + 1).filter
        (fun D => C ≤ D), g (D.map C.mkQ)
      = ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨hbij, hrk, -⟩ := hIn k H C hC
  refine Finset.sum_bij (fun D _ => D.map C.mkQ) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    have := hrk D hD.2
    omega
  · intro D₁ h₁ D₂ h₂ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Subtype.ext_iff.mp (@hbij.1 ⟨D₁, h₁.2⟩ ⟨D₂, h₂.2⟩ he)
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    obtain ⟨⟨D, hD⟩, hDE⟩ := hbij.2 E
    refine ⟨D, ?_, hDE⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hD⟩
    have := hrk D hD
    simp only at hDE
    rw [hDE] at this
    omega
  · intro D hD
    rfl

open Classical in
private theorem partZero (hIn : CountIn) {k H : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] :
    (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = 0).filter
        (fun D => C ≤ D) = ∅ := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro hD hCD
  have := Submodule.finrank_mono hCD
  omega

open Classical in
private theorem partOut (hIn : CountIn) (hOut : CountOut) {k H P : Type} [Field k] [Finite k]
    [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H)
    (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
        (fun D => ¬ C ≤ D), g (D.map C.mkQ)
      = Nat.card k ^ j •
        ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨-, -, hrk⟩ := hIn k H C hC
  have hmaps : ∀ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
      (fun D => ¬ C ≤ D), D.map C.mkQ ∈
        Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j) := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    rw [← hrk D hD.2]
    exact hD.1
  rw [Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  rw [Finset.sum_congr rfl (g := fun _ => g E) (fun D hD => by rw [(Finset.mem_filter.mp hD).2])]
  rw [Finset.sum_const]
  congr 1
  have hc : Nat.card k ^ j = Nat.card { D // ¬C ≤ D ∧ Submodule.map C.mkQ D = E } := by
    rw [hOut k H C hC E, hE]
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    rw [hrk D h2, h3, hE]

end UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ordDecomp_of :
    CountIn → CountOut → OrdDecomp := by
  intro hIn hOut q n P F I _ v hv
  obtain ⟨k, H, _, _, _, _, _, C, A', e, hq, hn, hC, hve⟩ := hv
  classical
  haveI : Finite H := Module.finite_of_finite k
  haveI : Finite (Submodule k H) :=
    Finite.of_injective (fun S : Submodule k H => (S : Set H)) SetLike.coe_injective
  haveI : Finite (H ⧸ C) := Module.finite_of_finite k
  haveI : Finite (Submodule k (H ⧸ C)) :=
    Finite.of_injective (fun S : Submodule k (H ⧸ C) => (S : Set (H ⧸ C))) SetLike.coe_injective
  letI : Fintype (Submodule k H) := Fintype.ofFinite _
  letI : Fintype (Submodule k (H ⧸ C)) := Fintype.ofFinite _
  letI hG : ∀ m : ℕ, Fintype (Gr k H m) := fun m =>
    (inferInstance : Fintype {D : Submodule k H // Module.finrank k D = m})
  have key : ∀ j : Fin (n + 1), Multiset.map (v j) Finset.univ.val =
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => C ≤ D), ({F (A' (D.map C.mkQ))} : Multiset P) +
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => ¬ C ≤ D), ({A' (D.map C.mkQ)} : Multiset P) := by
    intro j
    rw [← Finset.sum_ite]
    rw [val_map_sum, ← Equiv.sum_comp (e j).symm]
    rw [Finset.sum_subtype (F := hG j)
      (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ))
      (p := fun D : Submodule k H => Module.finrank k D = (j : ℕ)) (by simp)]
    refine Finset.sum_congr rfl ?_
    intro D _
    have h := hve j ((e j).symm D)
    rw [Equiv.apply_symm_apply] at h
    by_cases hCD : C ≤ D.1
    · rw [h.1 hCD]
      simp [hCD]
    · rw [h.2 hCD]
      simp [hCD]
  refine ⟨fun j => ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
    ({A' E} : Multiset P), ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    exfalso
    have h1 := Submodule.finrank_le E
    have h2 := Submodule.finrank_quotient_add_finrank C
    omega
  · rw [key 0]
    simp only [Fin.val_zero]
    have h0 := partZero hIn C hC
    have h1 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) 0
    simp only [pow_zero, one_smul] at h1
    convert congrArg₂ (· + ·) (congrArg (fun s => ∑ D ∈ s, ({F (A' (D.map C.mkQ))} : Multiset P)) h0) h1
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
  · intro j
    rw [key j.succ]
    simp only [Fin.val_succ]
    have h2 := partIn hIn C hC (fun E => ({F (A' E)} : Multiset P)) j
    have h3 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) (j + 1)
    rw [hq] at h3
    have h4 : ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
        ({F (A' E)} : Multiset P) = Multiset.map F
          (∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
            ({A' E} : Multiset P)) := by
      rw [← val_map_sum, ← val_map_sum, Multiset.map_map]
      rfl
    rw [← h4]
    convert congrArg₂ (· + ·) h2 h3
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSameNormRing
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem mapP_mapP {R B C ι : Type} [CommRing R] [CommRing B] [CommRing C] (f : R →+* B) (g : B →+* C)
    (N : Polynomial (MvPolynomial ι R)) : mapP g (mapP f N) = mapP (g.comp f) N := by
  simp only [mapP, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun p => MvPolynomial.map_map f g p

private theorem step_one (hPP : PtsProd) {R C C' ι J : Type} [CommRing R] [CommRing C] [CommRing C'] [Algebra R C]
    [Fintype ι] [Fintype J] (S : J → Type) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)]
    (N : J → Polynomial (MvPolynomial ι R)) (a : J → ℕ) (s : ∀ j, ι → S j) (ρ : C →+* C')
    (I : J → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (S j →ₐ[R] C))
    (h : ∀ j, mapP (algebraMap R C) (N j) = ∏ i, form fun k => z j i (s j k)) :
    ((pts a fun j i k => ρ (z j i (s j k))).map form).prod = mapP (ρ.comp (algebraMap R C)) (∏ j, N j ^ a j) := by
  rw [hPP C C' ρ ι J I a (fun j i k => z j i (s j k))]
  simp_rw [← h]
  rw [← mapP_mapP]
  congr 1
  simp only [mapP, Polynomial.map_prod, Polynomial.map_pow]

theorem UpperTheory.Gal.crystallineComparison.sameNormRing_of :
    NormRead → ValLift → PtsProd → CongrRad → SameNormRing := by
  intro hNR hVL hPP hCR l R _ 𝔞 hB J _ S _ _ d hS a b ι _ s hV B _ _ hl I _ z hz B' _ ρ hρ
  choose N hN using fun j => hNR l (d j) R (S j) (hS j) hB.closed ι (s j)
  have hB1 : ∀ j, mapP (algebraMap R B) (N j) = ∏ i, form fun k => z j i (s j k) :=
    fun j => (hN j).1 B hl (I j) (z j) (hz j)
  have key : mapP (ρ.comp (algebraMap R B)) (∏ j, N j ^ a j) = mapP (ρ.comp (algebraMap R B)) (∏ j, N j ^ b j) := by
    refine hCR R 𝔞 hB.rad ι _ _ ?_ B' _ hρ
    intro 𝔭 hp
    haveI : 𝔭.IsPrime := hp.1.1
    obtain ⟨V, _, _, _, _, _, hl', hc⟩ := hVL R (l : R) hB.nzd 𝔭
    have hl0 : (l : V) ≠ 0 := by simpa using hl'
    refine ⟨IsLocalRing.ResidueField V, inferInstance, (IsLocalRing.residue V).comp (algebraMap R V), ?_, ?_⟩
    · rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hc]
    · have hfin : ∀ j, Finite (S j →ₐ[R] V) := fun j => ((hN j).2 V hl0).1
      letI : ∀ j, Fintype (S j →ₐ[R] V) := fun j => @Fintype.ofFinite _ (hfin j)
      have hV1 : ∀ j, mapP (algebraMap R V) (N j) = ∏ i : S j →ₐ[R] V, form fun k => i (s j k) :=
        fun j => ((hN j).2 V hl0).2 (S j →ₐ[R] V) id Function.bijective_id
      have hm := hV V hl0 (by rw [hc]; exact hp) (fun j => S j →ₐ[R] V) (fun j i => i) (fun j => Function.bijective_id)
      rw [← step_one hPP S N a s (IsLocalRing.residue V) (fun j => S j →ₐ[R] V) (fun j i => i) hV1,
        ← step_one hPP S N b s (IsLocalRing.residue V) (fun j => S j →ₐ[R] V) (fun j i => i) hV1, hm]
  show ((pts a fun j i k => ρ (z j i (s j k))).map form).prod = ((pts b fun j i k => ρ (z j i (s j k))).map form).prod
  rw [step_one hPP S N a s ρ I z hB1, step_one hPP S N b s ρ I z hB1, key]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.secChart_of :
    SecChart := by
  intro l Y T U hU
  haveI := T.fin
  letI := T.alg U
  have hZ : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have hsq : Spec.map (T.p.app U) ≫ hU.fromSpec = hZ.fromSpec ≫ T.p := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec T.p hU hZ le_rfl
  refine ⟨hZ, fun B _ _ => ?_⟩
  have hrange : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Set.range z.1 ⊆ Set.range hZ.fromSpec := by
    rintro z _ ⟨x, rfl⟩
    rw [hZ.range_fromSpec]
    have hx : (z.1 ≫ T.p) x ∈ Set.range hU.fromSpec := by
      rw [z.2]
      unfold ptOf
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hx
    simpa using hx
  have hlift : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Spec.map (T.p.app U ≫ Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z)))
        = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B)) := by
    intro z
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, hsq, Spec.map_preimage,
      IsOpenImmersion.lift_fac_assoc]
    exact z.2
  refine ⟨{ toFun := fun g => ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hZ.fromSpec, ?_⟩,
            invFun := fun z =>
              { toRingHom := (Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z))).hom
                commutes' := fun r => by
                  have h := congrArg (fun φ => φ.hom r) (Spec.map_injective (hlift z))
                  exact h }
            left_inv := fun g => ?_
            right_inv := fun z => ?_ }, fun z => rfl⟩
  · show _ = Spec.map _ ≫ hU.fromSpec
    rw [Category.assoc, ← hsq, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact g.commutes r
  · apply AlgHom.coe_ringHom_injective
    show (Spec.preimage _).hom = (CommRingCat.ofHom g.toRingHom).hom
    congr 1
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact (IsOpenImmersion.lift_uniq _ _ _ _ rfl).symm
  · apply Subtype.ext
    show Spec.map (Spec.preimage _) ≫ _ = _
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSmoothClosed
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem away_closed (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (a : O) (ha : a ≠ 0)
    (x : Localization.Away a) (hx : IsIntegral O x) : ∃ o : O, algebraMap O _ o = x := by
  classical
  have hunit : ∀ y : Submonoid.powers a, IsUnit (Algebra.ofId O (FractionRing O) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n (IsUnit.mk0 _ ?_)
    rw [Algebra.ofId_apply]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  let f : Localization.Away a →ₐ[O] FractionRing O :=
    IsLocalization.liftAlgHom (M := Submonoid.powers a) hunit
  have hinj : Function.Injective f := by
    have h := (IsLocalization.lift_injective_iff (M := Submonoid.powers a)
      (S := Localization.Away a) (g := algebraMap O (FractionRing O)) hunit).mpr ?_
    · exact h
    · intro x y
      rw [(IsLocalization.injective (Localization.Away a)
          (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff,
        (IsFractionRing.injective O (FractionRing O)).eq_iff]
  have hcl : IsIntegrallyClosedIn O (Localization.Away a) :=
    f.isIntegrallyClosedIn hinj inferInstance
  exact IsIntegrallyClosedIn.algebraMap_eq_of_integral hx

theorem UpperTheory.Gal.crystallineComparison.smoothClosed_of :
    SmoothClosed := by
  intro l O R _ _ _ _ _ _ hl c hc
  classical
  have hM : Algebra.algebraMapSubmonoid R (Submonoid.powers (l : O)) = Submonoid.powers (l : R) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_natCast]
  haveI : IsLocalization (Submonoid.powers (l : R)) (R ⊗[O] Localization.Away (l : O)) := by
    rw [← hM]
    infer_instance
  let e : (R ⊗[O] Localization.Away (l : O)) ≃ₐ[R] Localization.Away (l : R) :=
    IsLocalization.algEquiv (Submonoid.powers (l : R)) _ _
  have hc' : IsIntegral R (e.symm c) := hc.map e.symm
  obtain ⟨s, hs⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := O) (S := R)
    (B := Localization.Away (l : O))).2 ⟨e.symm c, hc'⟩
  have key : ∀ s : R ⊗[O] integralClosure O (Localization.Away (l : O)), ∃ r : R,
      algebraMap R (R ⊗[O] Localization.Away (l : O)) r =
        (TensorProduct.toIntegralClosure O R (Localization.Away (l : O)) s :
          R ⊗[O] Localization.Away (l : O)) := by
    intro s
    induction s with
    | tmul r y =>
      obtain ⟨o, ho⟩ := away_closed O (l : O) hl y.1 y.2
      refine ⟨algebraMap O R o * r, ?_⟩
      show _ = r ⊗ₜ[O] y.1
      rw [← ho, Algebra.algebraMap_eq_smul_one (A := Localization.Away (l : O)), ← TensorProduct.smul_tmul,
        Algebra.smul_def]
      rfl
    | add x y hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      exact ⟨r1 + r2, by simp only [map_add (f := _), h1, h2]; rfl⟩
  obtain ⟨r, hr⟩ := key s
  refine ⟨r, ?_⟩
  rw [← e.commutes r, hr, hs]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSmoothRed
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.smoothRed_of :
    SmoothReduced :=
  _root_.GlobalTheory.isReduced_of_smooth_over_field
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem form_map' {A A' ι : Type} [CommRing A] [CommRing A'] [Fintype ι] (ρ : A →+* A') (c : ι → A) :
    (form c).map (MvPolynomial.map ρ) = form (fun k => ρ (c k)) := by
  unfold form
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem form_eval' {A ι : Type} [CommRing A] [Fintype ι] (x y : ι → A) :
    Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k) (form y) =
      ∑ k, MvPolynomial.C (x k - y k) * MvPolynomial.X k := by
  unfold form
  show Polynomial.eval _ _ = _
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_sub, sub_mul]

private theorem form_natDegree' {A ι : Type} [CommRing A] [Fintype ι] [Nontrivial A] (v : Multiset (ι → A)) :
    ((v.map form).prod).natDegree = v.card := by
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_def, form, Polynomial.natDegree_X_sub_C]
    simp
  · intro f hf
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.monic_X_sub_C _

theorem UpperTheory.Gal.crystallineComparison.snBasic_of :
    SameNormBasic := by
  intro A ι _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A' _ ρ u u' h
    unfold SameNorm at h ⊢
    have e := congrArg (Polynomial.map (MvPolynomial.map ρ)) h
    simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, form_map'] at e
    simpa [Multiset.map_map, Function.comp_def] using e
  · intro x u u' h
    simp only [SameNorm, Multiset.map_cons, Multiset.prod_cons] at h ⊢
    exact (show (form x).Monic from Polynomial.monic_X_sub_C _).isRegular.left h
  · intro _ u u' h
    unfold SameNorm at h
    have e := congrArg Polynomial.natDegree h
    rwa [form_natDegree', form_natDegree'] at e
  · intro x u u' h hx
    unfold SameNorm at h
    have e := congrArg (Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k)) h
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map] at e
    simp only [Function.comp_def, form_eval'] at e
    rw [← e]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.2 ⟨x, hx, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsBC
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsBC_of :
    SplitsBC := by
  intro R R' S B _ _ _ _ _ _ _ _ _ I z hz
  let z' : I → (R' ⊗[R] S →ₐ[R'] B) := fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId R' B) (z i) (fun _ _ => Commute.all _ _)
  have hz' : ∀ i (r : R') (s : S), z' i (r ⊗ₜ s) = algebraMap R' B r * z i s := by
    intro i r s
    simp [z', Algebra.ofId_apply]
  refine ⟨z', ?_, ?_⟩
  · have key : ∀ x, splitMap z' x =
        splitMap z (Algebra.TensorProduct.cancelBaseChange R R' B B S x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul b y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [tmul_add, map_add (f := _), ha, hc]
        | tmul r s =>
          funext i
          rw [splitMap_tmul, hz', Algebra.TensorProduct.cancelBaseChange_tmul, splitMap_tmul]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    have hfun : (⇑(splitMap z') : B ⊗[R'] (R' ⊗[R] S) → (I → B)) =
        (splitMap z) ∘ (Algebra.TensorProduct.cancelBaseChange R R' B B S) := funext key
    unfold Splits
    rw [hfun]
    exact hz.comp (AlgEquiv.bijective _)
  · intro i s
    rw [hz']
    simp
end

