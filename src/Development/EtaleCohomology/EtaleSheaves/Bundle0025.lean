module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.EtaleCohomology.EtaleSheaves.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.EtaleCohomology.EtaleSheaves.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.Bundle0015
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensCut
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.HensCut

def LocAIC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B), (0 : B) ∉ M → AIC B →
  IsDomain (Localization M) ∧ AIC (Localization M)

def MonicSplits : Prop := ∀ (R : Type) [CommRing R] [IsDomain R], AIC R → ∀ p : Polynomial R, p.Monic →
  ∃ s : Multiset R, p = (s.map fun a => Polynomial.X - Polynomial.C a).prod

def IdemPart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ) (y : Fin n → A), ∏ l, y l = 0 →
  IsUnit (∑ l, ∏ m ∈ Finset.univ.erase l, y m) →
  ∃ e : Fin n → A, (∀ l, IsIdempotentElem (e l)) ∧ (∀ l m, l ≠ m → e l * e m = 0) ∧ ∑ l, e l = 1 ∧ ∀ l, e l * y l = 0

def ColimHens : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) (c : Cocone D), IsColimit c →
  (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) →
  (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) →
  (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
    IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
    ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧ a - (D.map f).hom a₀ ∈ I.map (β.app j').hom) →
  ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

def PartDiag : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) ∧
    (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) ∧
    (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
      IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
      ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧
        a - (D.map f).hom a₀ ∈ I.map (β.app j').hom)

theorem goal_of (_hL : LocAIC) (_hM : MonicSplits) (_hI : IdemPart) (hC : ColimHens) (hD : PartDiag) :
    LateralTheory.E.QuotAcycCut.Hens := by
  intro q B _ _ I hB hq
  obtain ⟨J, _, _, D, β, hst, ha, hb, hc⟩ := hD q B I hB hq
  obtain ⟨K, hK, he⟩ := hC B I J D β (colimit.cocone D) (colimit.isColimit D) ha hb hc
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, hst, ?_, K, hK, he⟩
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have h1 : IsUnit ((q : B)) := hq
  have h2 := h1.map ((β.app j) ≫ (colimit.cocone D).ι.app j).hom
  simpa using h2

end LateralTheory.E.HensCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ImgOf
section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ImgPf

theorem Img_of : LateralTheory.E.ChowCut.Img := by
  intro A _ Z X h p _ hh hZ
  have := hh
  have := hZ
  have : QuasiCompact h := inferInstance
  have : IsIntegralHom (h.toImage ≫ h.imageι) := by rw [Scheme.Hom.toImage_imageι]; exact hh
  refine ⟨h.image, h.toImage, h.imageι ≫ p, inferInstance, inferInstance,
    IsIntegralHom.of_comp h.toImage h.imageι, inferInstance, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc]

end LateralTheory.E.ImgPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntFibPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntFibPf

lemma eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

lemma eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

lemma isPushout_quot (A : Type) [CommRing A] [IsLocalRing A] {B : CommRingCat.{0}} (ψ : CommRingCat.of A ⟶ B) :
    IsPushout ψ (CommRingCat.ofHom (IsLocalRing.residue A))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map
        : IsLocalRing.ResidueField A →+* _)) := by
  have w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _)) := by
    constructor; ext a; rfl
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
      (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)
  · rename_i s; intro a ha
    have hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      have h1 := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
      simp only [Ideal.mem_comap, RingHom.mem_ker, h1,
        (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    exact hle ha
  · intro s; ext b; rfl
  · intro s; ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    exact h1
  · intro s m h1 h2
    ext b
    have := congrArg (fun f => f.hom b) h1
    exact this

theorem IntFib_of : LateralTheory.E.IntPBPf.IntFib := by
  intro A _ _ X p hp
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩
  · rw [← IsIntegralHom.SpecMap_iff, hψ]; infer_instance
  · intro q i h
    have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)
    have hP' : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p
        (LateralTheory.E.t_E2Cut.cpt A) :=
      hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp [hψ]) (by simp)
    rw [← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]
    exact eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _)
      (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))

end LateralTheory.E.IntFibPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntHensPf
section
noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.IntHensPf

theorem mem_sub (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) (S : Subalgebra A B)
    {n : ℕ} (c : Fin n → B) (g : Fin n → (algebraMap A B '' (m : Set A))) (hc : ∀ i, c i ∈ S) :
    ∃ y ∈ m.map (algebraMap A S), (y : B) = ∑ i, c i • (g i : B) := by
  choose a ha hag using fun i => (g i).2
  refine ⟨∑ i, ⟨c i, hc i⟩ * algebraMap A S (a i), Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i)), ?_⟩
  change S.val _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, smul_eq_mul, ← hag]; rfl

theorem jac (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B] :
    (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal n
  exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm

theorem evalS (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Subalgebra A B) (p : S[X]) (y : S) :
    ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := by
  rw [eval_map]; exact (eval₂_hom S.val.toRingHom y).symm

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Algebra A B]
    [Algebra.IsIntegral A B] : HenselianRing B ((maximalIdeal A).map (algebraMap A B)) := by
  classical
  refine ⟨by simpa only [Ideal.jacobson_bot] using jac A B, fun f hf a0 h0 h1 => ?_⟩
  set J := (maximalIdeal A).map (algebraMap A B) with hJ
  obtain ⟨n1, c1, g1, hs1⟩ := Submodule.mem_span_set'.1 h0
  obtain ⟨v, hv⟩ := h1.exists_left_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hu : u * f.derivative.eval a0 - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  obtain ⟨n2, c2, g2, hs2⟩ := Submodule.mem_span_set'.1 hu
  set s : Finset B := insert a0 (insert u (f.coeffs ∪ (Finset.univ.image c1 ∪ Finset.univ.image c2)))
  let S := Algebra.adjoin A (s : Set B)
  have hsS : ∀ x ∈ s, x ∈ S := fun x hx => Algebra.subset_adjoin hx
  haveI : Module.Finite A S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)
  let JS := (maximalIdeal A).map (algebraMap A S)
  haveI : HenselianRing S JS := GlobalTheory.henselianRing_of_finite A JS (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A S)
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc => hsS c (by simp [s, Finset.mem_coe.1 hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, hsS a0 (by simp [s])⟩
  let uS : S := ⟨u, hsS u (by simp [s])⟩
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  have h0S : g.eval b0 ∈ JS := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c1 g1 (fun i => hsS _ (by simp [s]))
    convert hy using 1
    apply Subtype.ext
    rw [hyv, hs1, evalS, hgf]
  have h1S : IsUnit (Ideal.Quotient.mk JS (g.derivative.eval b0)) := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c2 g2 (fun i => hsS _ (by simp [s]))
    have : uS * g.derivative.eval b0 - 1 ∈ JS := by
      convert hy using 1
      apply Subtype.ext
      rw [hyv, hs2]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, evalS]
      rw [← derivative_map, hgf]
    rw [← Ideal.Quotient.eq, map_mul, map_one] at this
    exact ⟨⟨_, _, (mul_comm _ _).trans this, this⟩, rfl⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian g hgm b0 h0S h1S
  refine ⟨(a : B), ?_, ?_⟩
  · rw [IsRoot.def, ← hgf, ← evalS, ha.eq_zero]; rfl
  · have := Ideal.mem_map_of_mem S.val.toRingHom ha'
    rw [Ideal.map_map] at this
    simpa using this

theorem IntHens_of : LateralTheory.E.IntPBPf.IntHens := by
  intro A B _ _ _ φ hφ
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  exact hens A B

end LateralTheory.E.IntHensPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntegralNormalization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf

def OpenNbhdIC : Prop := ∀ {Z : Scheme.{0}} (U : Z.Opens), AICSch Z → (U : Set Z).Nonempty → AICSch U.toScheme

def FFAlg : Prop := ∀ {Z : Scheme.{0}} [IsIntegral Z], AICSch Z → IsAlgClosed Z.functionField

def NormAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g], AICSch g.normalization

theorem spec_field_qc (K : Type) [Field K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W) : QuasiCompact g := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U _
  exact (Set.toFinite _).isCompact

theorem Norm_of (h0 : OpenNbhdIC) (h1 : FFAlg) (h2 : NormAIC) : LateralTheory.E.ChowCut.Norm := by
  intro Z W f _ hZ ⟨U, s, hU, hs⟩
  have : IsIntegral Z := hZ.1
  have hUa := h0 U hZ hU
  have := hUa.1
  have := h1 hUa
  let g0 : Spec (CommRingCat.of U.toScheme.functionField) ⟶ U.toScheme := U.toScheme.fromSpecStalk _
  let g := g0 ≫ s
  have := spec_field_qc _ g
  refine ⟨g.normalization, g.fromNormalization, inferInstance, h2 _ g, ?_⟩
  have hg0 : IsDominant g0 := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.range_fromSpecStalk]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec U.toScheme).def ▸ closure_mono (Set.singleton_subset_iff.mpr (specializes_refl _)))
  have hU' : IsDominant U.ι := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact (U.isOpen.dense hU).closure_eq
  have e : g.toNormalization ≫ g.fromNormalization ≫ f = g0 ≫ U.ι := by
    rw [reassoc_of% g.toNormalization_fromNormalization, Category.assoc, hs]
  have : IsDominant (g.toNormalization ≫ g.fromNormalization ≫ f) := by rw [e]; infer_instance
  exact IsDominant.of_comp g.toNormalization _

end LateralTheory.E.NormPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LEtaleLiftPf
section
noncomputable section

namespace LateralTheory.E.LEtaleLiftPf

def LChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Algebra.IsStandardEtale A (Localization.Away g)

theorem LEtaleLift_of (hC : LChart) : LateralTheory.E.LFactorPf.LEtaleLift := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hS⟩ := hC A I A' φ
  let φ' : Localization.Away g →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom g hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale I (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I) (fun b => (Ideal.Quotient.eq_zero_iff_mem).symm) φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom A A' _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A' _ a)).trans (show φ' (algebraMap A' _ a) = φ a by simp [φ'])

end LateralTheory.E.LEtaleLiftPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafBdryPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Set Order TopologicalSpace Topology

namespace LateralTheory.E.LeafBdryPf

def univIC (Y : Type*) [TopologicalSpace Y] [IrreducibleSpace Y] : IrreducibleCloseds Y where
  carrier := univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

lemma withBot_lt_of_add_one_le {a b : WithBot ℕ∞} (h : a + 1 ≤ b) (hb : b < ⊤) (ha : a ≠ ⊥) : a < b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      have hb' : b < ⊤ := by
        rw [← WithBot.coe_top] at hb
        exact WithBot.coe_lt_coe.mp hb
      have h' : a + 1 ≤ b := by exact_mod_cast h
      have ha' : a ≠ ⊤ := (lt_of_le_of_lt (le_self_add.trans h') hb').ne
      exact WithBot.coe_lt_coe.mpr ((ENat.add_one_le_iff ha').mp h')

theorem dim_lt_of_closedEmbedding {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [IrreducibleSpace Y]
    (f : Z → Y) (hf : IsClosedEmbedding f) (hfin : topologicalKrullDim Y < ⊤) (hne : (range f)ᶜ.Nonempty) :
    topologicalKrullDim Z < topologicalKrullDim Y := by
  have hY : Nonempty (IrreducibleCloseds Y) := ⟨univIC Y⟩
  by_cases hZ : Nonempty (IrreducibleCloseds Z)
  · have hlt : ∀ c : IrreducibleCloseds Z, IrreducibleCloseds.map f hf.continuous c < univIC Y := by
      intro c
      refine lt_of_le_of_ne (fun x _ => trivial) ?_
      intro heq
      obtain ⟨y, hy⟩ := hne
      have h1 : (IrreducibleCloseds.map f hf.continuous c : Set Y) ⊆ range f := by
        rw [IrreducibleCloseds.coe_map]
        exact closure_minimal (image_subset_range _ _) hf.isClosed_range
      apply hy
      apply h1
      rw [heq]
      trivial
    let g : WithTop (IrreducibleCloseds Z) → IrreducibleCloseds Y :=
      fun o => WithTop.recTopCoe (univIC Y) (IrreducibleCloseds.map f hf.continuous) o
    have hg : StrictMono g := by
      intro a b hab
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (by simp)
      | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact hlt a
        | coe b =>
          exact IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing (WithTop.coe_lt_coe.mp hab)
    have h := krullDim_le_of_strictMono g hg
    rw [krullDim_WithTop] at h
    exact withBot_lt_of_add_one_le h hfin (bot_lt_krullDim).ne'
  · rw [not_nonempty_iff] at hZ
    have : topologicalKrullDim Z = ⊥ := krullDim_eq_bot
    rw [this]
    exact bot_lt_krullDim

theorem LeafBdry_of : LateralTheory.E.LeafGeoCut.LeafBdry := by
  intro Y B W p ι hι hirr hfin hne
  have : IsClosedImmersion (pullback.fst p ι) := inferInstance
  refine dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_
  rw [Scheme.Pullback.range_fst, ← preimage_compl]
  exact hne

end LateralTheory.E.LeafBdryPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafClosedPf

theorem LeafClosed_of : LateralTheory.E.LeafGeoCut.LeafClosed := by
  intro B V
  let Z : TopologicalSpace.Closeds B := ⟨(V : Set B)ᶜ, V.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp [Z]

end LateralTheory.E.LeafClosedPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCochainVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCochainVanishPf

variable {R : Type} [CommRing R]

theorem free_ext_zero (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.hom.app (op U)).hom (freeGen R P U x) = 0) : φ = 0 := by
  have h0 : (0 : (free R).obj P ⟶ G).hom = 0 := rfl
  refine Sheaf.hom_ext ?_
  rw [h0]
  refine sheafify_hom_ext _ _ _ G.property ?_
  ext U : 2
  refine ModuleCat.free_hom_ext (fun x => ?_)
  exact (h U.unop x.down).trans (by erw [Limits.comp_zero]; rfl)

theorem chains_isZero (E : Spc) (p : ℤ) (hp : 0 < p) : Limits.IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => ?_)
  have : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  omega

theorem cochain_zero_of (E : Spc) {U V : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (K : Cx R) (k : ℤ)
    (γ : Cochain ((chains R).obj E) K k)
    (hU : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0)
    (hV : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) :
    γ = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : 0 < p
  · exact (chains_isZero (R := R) E p hp).eq_of_src _ _
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
  have hφ : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q hpq = 0 := by
    have := hc.2.2 (op (SimplexCategory.mk N))
    rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
      ((free R).map (g.app (op (SimplexCategory.mk N))))), Limits.comp_zero]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hU N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
    · rw [biprod.inr_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hV N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
  rw [← Iso.hom_inv_id_assoc (chainsXIso R E N) (γ.v _ _ hpq), hφ, Limits.comp_zero]

end LateralTheory.E.LeafCochainVanishPf

theorem LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := by
  intro R _ U V E f g hc K k γ hU hV
  exact LateralTheory.E.LeafCochainVanishPf.cochain_zero_of E f g hc K k γ hU hV
end
end

