module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCongrRad
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.congrRad_of :
    CongrRad := by
  intro R _ 𝔞 h𝔞 ι N N' H B' _ g hg
  have key : ∀ (a : ℕ) (m : ι →₀ ℕ),
      AddMonoidAlgebra.coeff (N.coeff a) m - AddMonoidAlgebra.coeff (N'.coeff a) m ∈ 𝔞 := by
    intro a m
    rw [← h𝔞.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔭 h𝔭
    obtain ⟨κ, _, f, hker, hf⟩ := H 𝔭 h𝔭
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have := congrArg (fun p => AddMonoidAlgebra.coeff (p.coeff a) m) hf
    simpa [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map] using this
  refine Polynomial.ext fun a => MvPolynomial.ext _ _ fun m => ?_
  simp only [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]
  rw [← sub_eq_zero, ← map_sub]
  exact hg _ (key a m)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCountIn
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.countIn_of :
    CountIn := by
  intro k H _ _ _ _ C hC
  have key : ∀ D : Submodule k H, Module.finrank k D
      = Module.finrank k (Submodule.map C.mkQ D) + Module.finrank k ↥(D ⊓ C) := by
    intro D
    have h := (C.mkQ.domRestrict D).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
    rw [← h, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨D₁, h₁⟩ ⟨D₂, h₂⟩ h
    simp only at h
    have e₁ := Submodule.comap_map_mkQ C D₁
    have e₂ := Submodule.comap_map_mkQ C D₂
    rw [h, e₂, sup_eq_right.mpr h₂] at e₁
    rw [sup_eq_right.mpr h₁] at e₁
    exact Subtype.ext e₁.symm
  · intro E
    refine ⟨⟨Submodule.comap C.mkQ E, ?_⟩, ?_⟩
    · intro x hx
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero C).mpr hx]
    · exact Submodule.map_comap_eq_self (by simp [Submodule.range_mkQ])
  · intro D hD
    rw [key D, inf_eq_right.mpr hD, hC]
  · intro D hD
    have hle : Module.finrank k ↥(D ⊓ C) ≤ 1 := hC ▸ Submodule.finrank_mono inf_le_right
    have hne : Module.finrank k ↥(D ⊓ C) ≠ 1 := by
      intro h1
      apply hD
      have := Submodule.eq_of_le_of_finrank_eq (inf_le_right : D ⊓ C ≤ C) (h1.trans hC.symm)
      exact this ▸ inf_le_left
    rw [key D]
    omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCountOut
section
noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem countOut_of : CountOut := by
  intro k H _ _ _ _ _ C hC E
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property C.mkQ E.subtype (Submodule.mkQ_surjective C)
  have hsec : ∀ (s : E →ₗ[k] H), C.mkQ ∘ₗ s = E.subtype → ∀ e : E, C.mkQ (s e) = e := by
    intro s hs e
    exact LinearMap.congr_fun hs e
  let S := {s : E →ₗ[k] H // C.mkQ ∘ₗ s = E.subtype}
  have hF : ∀ s : S, ¬C ≤ LinearMap.range s.1 ∧ Submodule.map C.mkQ (LinearMap.range s.1) = E := by
    intro s
    constructor
    · intro hle
      haveI : Nontrivial C := Module.nontrivial_of_finrank_eq_succ hC
      obtain ⟨c, hc⟩ := exists_ne (0 : C)
      obtain ⟨e, he⟩ := LinearMap.mem_range.1 (hle c.2)
      have h1 : C.mkQ (s.1 e) = e := hsec s.1 s.2 e
      have h2 : C.mkQ (c : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 c.2
      rw [he, h2] at h1
      have e0 : e = 0 := Subtype.ext h1.symm
      apply hc
      apply Subtype.ext
      rw [← he, e0, map_zero]
      rfl
    · rw [← LinearMap.range_comp, s.2, Submodule.range_subtype]
  let F : S → {D : Submodule k H // ¬C ≤ D ∧ Submodule.map C.mkQ D = E} :=
    fun s => ⟨LinearMap.range s.1, hF s⟩
  have hFb : Function.Bijective F := by
    constructor
    · intro s t h
      have h' : LinearMap.range s.1 = LinearMap.range t.1 := congrArg Subtype.val h
      apply Subtype.ext
      apply LinearMap.ext
      intro e
      have hm : s.1 e ∈ LinearMap.range t.1 := h' ▸ LinearMap.mem_range_self s.1 e
      obtain ⟨e', he'⟩ := LinearMap.mem_range.1 hm
      have h1 := hsec t.1 t.2 e'
      rw [he', hsec s.1 s.2 e] at h1
      have : e' = e := Subtype.ext h1.symm
      rw [← he', this]
    · rintro ⟨D, hnot, hmap⟩
      have hdisj : ∀ x ∈ D, x ∈ C → x = 0 := by
        intro x hxD hxC
        by_contra hx
        apply hnot
        intro y hy
        have hx' : (⟨x, hxC⟩ : C) ≠ 0 := fun h => hx (congrArg Subtype.val h)
        obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').1 hC ⟨y, hy⟩
        have : a • x = y := congrArg Subtype.val ha
        rw [← this]
        exact D.smul_mem a hxD
      let f : D →ₗ[k] H ⧸ C := C.mkQ ∘ₗ D.subtype
      have hf : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro d hd
        apply Subtype.ext
        exact hdisj d.1 d.2 ((Submodule.Quotient.mk_eq_zero C).1 hd)
      have hr : LinearMap.range f = E := by
        rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
      let φ : D ≃ₗ[k] E := (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)
      have hφ : ∀ d : D, ((φ d : E) : H ⧸ C) = C.mkQ d := fun d => rfl
      let s : E →ₗ[k] H := D.subtype ∘ₗ (φ.symm : E →ₗ[k] D)
      have hs : C.mkQ ∘ₗ s = E.subtype := by
        apply LinearMap.ext
        intro e
        have h1 := hφ (φ.symm e)
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      show LinearMap.range s = D
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.symm), Submodule.range_subtype]
  let G : (E →ₗ[k] C) → S := fun g =>
    ⟨s0 + C.subtype ∘ₗ g, by
      apply LinearMap.ext
      intro e
      have h1 := LinearMap.congr_fun hs0 e
      have h2 : C.mkQ (g e : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 (g e).2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _), Submodule.subtype_apply] at h1 ⊢
      rw [h2, add_zero, h1]⟩
  have hGb : Function.Bijective G := by
    constructor
    · intro g g' h
      apply LinearMap.ext
      intro e
      apply Subtype.ext
      have := LinearMap.congr_fun (congrArg Subtype.val h) e
      simpa [G] using this
    · rintro ⟨s, hs⟩
      have hmem : ∀ e, s e - s0 e ∈ C := by
        intro e
        apply (Submodule.Quotient.mk_eq_zero C).1
        have h1 := hsec s hs e
        have h2 := hsec s0 hs0 e
        simp only [Submodule.mkQ_apply] at h1 h2
        rw [Submodule.Quotient.mk_sub, h1, h2, sub_self]
      refine ⟨LinearMap.codRestrict C (s - s0) hmem, Subtype.ext ?_⟩
      apply LinearMap.ext
      intro e
      simp [G]
  have hcard : Nat.card (E →ₗ[k] C) = Nat.card k ^ Module.finrank k E := by
    haveI : Fintype k := Fintype.ofFinite k
    haveI : Finite (E →ₗ[k] C) := Module.finite_of_finite k
    haveI : Fintype (E →ₗ[k] C) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := E →ₗ[k] C), Nat.card_eq_fintype_card (α := k), Module.card_eq_pow_finrank (K := k) (V := E →ₗ[k] C),
      Module.finrank_linearMap k k E C, hC, mul_one]
  rw [← Nat.card_eq_of_bijective F hFb, ← Nat.card_eq_of_bijective G hGb, hcard]

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDinvExact
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma UpperTheory.Gal.crystallineComparison.map_id_eq_rTensor {F B L U V : Type} [Field F] [AddCommGroup B] [Module F B]
    [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (f : U →ₗ[L] V) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x = LinearMap.rTensor B (f.restrictScalars F) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private lemma UpperTheory.Gal.crystallineComparison.inter_map {F G B L U V : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {ρ : Representation L G U} {ρ' : Representation L G V} {f : U →ₗ[L] V} (hf : Inter ρ ρ' f) (g : G) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map (ρ g) (σ g) x) =
      AlgebraTensorModule.map (ρ' g) (σ g) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp [hf g u]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.Gal.crystallineComparison.dinvExact_of :
    DinvExact := by
  intro F G B _ _ _ _ σ L _ _ U V W _ _ _ _ _ _ _ _ _ _ _ _ ρU ρV ρW i p hi hp hinj hex hfin
  have hI : Function.Injective (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars F) hinj
    intro x y hxy
    apply h
    rw [← map_id_eq_rTensor, ← map_id_eq_rTensor]
    exact hxy
  have hE : Function.Exact (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B))
      (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_exact (f := i.restrictScalars F) (g := p.restrictScalars F) B hex
    have e1 : (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) : U ⊗[F] B → V ⊗[F] B) =
        LinearMap.rTensor B (i.restrictScalars F) := funext (map_id_eq_rTensor i)
    have e2 : (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) : V ⊗[F] B → W ⊗[F] B) =
        LinearMap.rTensor B (p.restrictScalars F) := funext (map_id_eq_rTensor p)
    rw [e1, e2]
    exact h
  have key : (Dinv σ ρU).map (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) =
      Dinv σ ρV ⊓ LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · refine (mem_Dinv σ).2 fun g => ?_
        rw [← inter_map σ hi, (mem_Dinv σ).1 hx g]
      · exact (hE _).2 ⟨x, rfl⟩
    · rintro ⟨hy, hk⟩
      obtain ⟨x, rfl⟩ := (hE y).1 hk
      refine ⟨x, (mem_Dinv σ).2 fun g => hI ?_, rfl⟩
      rw [inter_map σ hi, (mem_Dinv σ).1 hy g]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine (mem_Dinv σ).2 fun g => ?_
    rw [← inter_map σ hp, (mem_Dinv σ).1 hx g]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      ((AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)).domRestrict (Dinv σ ρV))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
    have h2 : finrank L (Submodule.comap (Dinv σ ρV).subtype
        (LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))) =
        finrank L (Dinv σ ρU) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← key]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hI _)).symm
    rw [h2] at h1
    omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDinvExt
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem mem_baseChange_iInf_ker_sub_id_of_baseChange_eq {F L X ι : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup X] [Module F X] (A : ι → X →ₗ[F] X) (z : L ⊗[F] X)
    (hz : ∀ k, (A k).baseChange L z = z) :
    z ∈ (⨅ k, LinearMap.ker (A k - LinearMap.id)).baseChange L := by
  let b := Module.Free.chooseBasis F L
  let e : L ⊗[F] X ≃ₗ[F] (Module.Free.ChooseBasisIndex F L →₀ X) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl F X)).trans (finsuppScalarLeft F X _)
  have nat : ∀ (f : X →ₗ[F] X) (w : L ⊗[F] X) j, e (f.baseChange L w) j = f (e w j) := by
    intro f w j
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [e, finsuppScalarLeft_apply_tmul_apply]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  have hmem : ∀ j, e z j ∈ ⨅ k, LinearMap.ker (A k - LinearMap.id) := by
    intro j
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro k
    have h := congrArg (fun w => e w j) (hz k)
    simpa only [nat] using h
  have hsingle : ∀ j (x : X), e.symm (Finsupp.single j x) = b j ⊗ₜ[F] x := by
    intro j x
    simp [e]
  have hz' : z = (e z).sum (fun j x => b j ⊗ₜ[F] x) := by
    conv_lhs => rw [← e.symm_apply_apply z, ← Finsupp.sum_single (e z)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsingle j _
  rw [hz']
  exact Submodule.sum_mem _ fun j _ => Submodule.tmul_mem_baseChange_of_mem _ (hmem j)

theorem UpperTheory.Gal.crystallineComparison.dinvExt_of :
    DinvExt := by
  unfold DinvExt
  intro F G B _ _ _ _ σ L _ _ V _ _ ρ
  let T : G → (V ⊗[F] B) →ₗ[F] (V ⊗[F] B) := fun g => AlgebraTensorModule.map (ρ g) (σ g)
  have hD : Dinv σ ρ = ⨅ g, LinearMap.ker (T g - LinearMap.id) := rfl
  have comm : ∀ g (w : (L ⊗[F] V) ⊗[F] B),
      AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (extRep L ρ g) (σ g) w) =
        (T g).baseChange L (AlgebraTensorModule.assoc F F L L V B w) := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u c =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a v => simp [T, extRep, AlgebraTensorModule.map_tmul]
      | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  ext z
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hz
    rw [hD]
    apply mem_baseChange_iInf_ker_sub_id_of_baseChange_eq
    intro g
    have h : AlgebraTensorModule.map (extRep L ρ g) (σ g)
        ((AlgebraTensorModule.assoc F F L L V B).symm z) =
          (AlgebraTensorModule.assoc F F L L V B).symm z := by
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hz
      exact hz g
    have h2 := congrArg (AlgebraTensorModule.assoc F F L L V B) h
    rwa [comm, LinearEquiv.apply_symm_apply] at h2
  · intro hz
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [comm, LinearEquiv.apply_symm_apply]
    obtain ⟨w, rfl⟩ := hz
    have hfix : T g ∘ₗ (Dinv σ ρ).subtype = (Dinv σ ρ).subtype := by
      refine LinearMap.ext fun s => ?_
      have hs := s.2
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hs
      exact hs g
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfix]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtAway
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etAway_of :
    SecChart → EtChart → EtAwayChart := by
  intro hsec het l Y T U hU
  obtain ⟨hZ, hpts⟩ := hsec l Y T U hU
  have hfin := @IsFinite.finite_app _ _ _ T.fin U hU
  letI : Algebra Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U) := (T.p.app U).hom.toAlgebra
  refine EtAway.mk hfin (het l Y T U hU) ?_
  intro K _ _ _ hl
  obtain ⟨e, -⟩ := hpts K
  rw [Nat.card_congr e]
  exact T.deg K hl _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtChart
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem ring_step {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
    (a : R) (f : R →+* R') (g : S →+* S') (h : R' →+* S') (hc : h.comp f = g.comp (algebraMap R S))
    (hf : letI := f.toAlgebra; IsLocalization.Away a R')
    (hg : letI := g.toAlgebra; IsLocalization.Away (algebraMap R S a) S') (het : h.Etale) :
    Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[R] S) := by
  classical
  letI : Algebra R R' := f.toAlgebra
  letI : Algebra S S' := g.toAlgebra
  letI : Algebra S (Localization.Away a ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid S (Submonoid.powers a) =
      Submonoid.powers (algebraMap R S a) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' := by
    rw [hM]; exact hg
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (Localization.Away a ⊗[R] S) := IsLocalization.tensorRight _ (Submonoid.powers a)
  let e1 := IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) R'
  let e2 := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
    (Localization.Away a ⊗[R] S) S'
  have key : algebraMap (Localization.Away a) (Localization.Away a ⊗[R] S) =
      e2.symm.toRingEquiv.toRingHom.comp (h.comp e1.toRingEquiv.toRingHom) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    have h1 : e1 (algebraMap R (Localization.Away a) r) = f r := by
      rw [AlgEquiv.commutes]; rfl
    have h2 : h (f r) = g (algebraMap R S r) := by
      rw [← RingHom.comp_apply, hc, RingHom.comp_apply]
    have h3 : e2.symm (g (algebraMap R S r)) =
        algebraMap S (Localization.Away a ⊗[R] S) (algebraMap R S r) := by
      rw [← AlgEquiv.commutes e2.symm]; rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv]
    rw [h1, h2, h3]
    simp [Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [← RingHom.etale_algebraMap, key]
  exact RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ het)

private theorem appLE_step {Y Z : Scheme.{0}} (p : Z ⟶ Y) (D U' : Y.Opens) [Etale (p ∣_ D)] (hUD : U' ≤ D)
    (hU' : IsAffineOpen U') (W' : Z.Opens) (hW' : IsAffineOpen W') (e : W' ≤ p ⁻¹ᵁ U') :
    (p.appLE U' W' e).hom.Etale := by
  have hV : IsAffineOpen (D.ι ⁻¹ᵁ U') :=
    hU'.preimage_of_isOpenImmersion D.ι (by rw [Scheme.Opens.opensRange_ι]; exact hUD)
  have hW : IsAffineOpen ((p ⁻¹ᵁ D).ι ⁻¹ᵁ W') :=
    hW'.preimage_of_isOpenImmersion _
      (by rw [Scheme.Opens.opensRange_ι]; exact e.trans (fun x hx => hUD hx))
  have e' : (p ⁻¹ᵁ D).ι ⁻¹ᵁ W' ≤ (p ∣_ D) ⁻¹ᵁ (D.ι ⁻¹ᵁ U') := by
    intro x hx
    have h1 := e hx
    have h2 : D.ι ((p ∣_ D) x) = p ((p ⁻¹ᵁ D).ι x) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    change D.ι ((p ∣_ D) x) ∈ U'
    rw [h2]
    exact h1
  have H := HasRingHomProperty.appLE @Etale (p ∣_ D) ‹_›
    ⟨D.ι ⁻¹ᵁ U', hV⟩ ⟨(p ⁻¹ᵁ D).ι ⁻¹ᵁ W', hW⟩ e'
  rw [morphismRestrict_appLE] at H
  refine (Scheme.Hom.appLE_congr _ _ ?_ ?_ (fun f => f.hom.Etale)).mp H
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUD]
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (e.trans (fun x hx => hUD hx))]

theorem UpperTheory.Gal.crystallineComparison.etChart_of :
    EtChart := by
  unfold EtChart
  intro l Y T U hU
  letI := T.alg U
  haveI := T.fin
  haveI := T.et
  have hZU : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have e0 : T.Z.basicOpen ((T.p.app U).hom (l : Γ(Y, U))) ≤
      T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, U)) := (Scheme.preimage_basicOpen T.p _).ge
  have hUD : Y.basicOpen (l : Γ(Y, U)) ≤ Y.basicOpen (l : Γ(Y, ⊤)) := by
    have hres : (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (l : Γ(Y, ⊤)) =
        (l : Γ(Y, U)) := map_natCast _ l
    rw [← hres, Scheme.basicOpen_res]
    exact inf_le_right
  have het := appLE_step T.p (Y.basicOpen (l : Γ(Y, ⊤))) (Y.basicOpen (l : Γ(Y, U))) hUD
    (hU.basicOpen _) _ (hZU.basicOpen _) e0
  refine ring_step (l : Γ(Y, U))
    (Y.presheaf.map (homOfLE (Y.basicOpen_le (l : Γ(Y, U)))).op).hom
    (T.Z.presheaf.map (homOfLE (T.Z.basicOpen_le ((T.p.app U).hom (l : Γ(Y, U))))).op).hom
    (T.p.appLE _ _ e0).hom ?_ (hU.isLocalization_basicOpen _) (hZU.isLocalization_basicOpen _) het
  rw [← CommRingCat.hom_comp]
  change _ = CommRingCat.Hom.hom (T.p.app U ≫ _)
  congr 1
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtUnit
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etUnit_of :
    EtOfUnit := by
  intro l R S B _ _ _ _ _ h hl
  have hl' : IsUnit (algebraMap R B (l : R)) := by simpa using hl
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) hl').toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) hl' r).symm
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.Away (l : R)) B B S)
end

