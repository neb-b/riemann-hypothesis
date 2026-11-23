module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0028
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.Bundle0034

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncKerPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.TruncationKernel

def RelDesc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo' : IsPushout φ' e u φ'',
  Function.Injective (rpl q i (Spec.map φ') (Spec.map φ'') (Spec.map u) (Spec.map e)
    (by rw [← Spec.map_comp, ← Spec.map_comp, hpo'.w]) n)

theorem fgt_injective_of_pull_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n) := by
  intro R _ F U E f n hs
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  have hdec : c.1 = mappingCone.descCochain _ ((mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia))
      (δ m n γ) hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm, hγ]
    simp
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hc' := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by lia)) hc
  simp at hc'
  set a := (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia) with ha
  have hz : δ m n (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) = 0 := by
    rw [δ_sub, δ_units_smul, δ_ofHom_comp]
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg] at hc'
    exact hc'
  obtain ⟨w, hw⟩ := hs m hm (CohomologyClass.mk (Cocycle.mk _ n hm hz))
  obtain ⟨w', rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) w' (zero_add m)) = _ at hw
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at hw
  obtain ⟨k, hk, α0, hα0⟩ := hw
  change δ k m α0 = (Cochain.ofHom ((chains R).map f)).comp w'.1 (zero_add m) -
    (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) at hα0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, mappingCone.descCochain _ (-α0) (γ + n.negOnePow • w'.1) hk, ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ hm, δ_add, δ_units_smul, Cocycle.δ_eq_zero, smul_zero, add_zero]
  conv_rhs => rw [hdec]
  rw [mappingCone.ext_cochain_from_iff _ m n hm]
  refine ⟨?_, ?_⟩
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, mappingCone.inl_fst_assoc]
    simp only [δ_neg, hα0, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul, mappingCone.inl_snd_assoc, zero_comp, Cochain.zero_comp, add_zero]
    abel
  · simp

end LateralTheory.E.TruncationKernel
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.inclPf
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.inclPf

universe v u

set_option linter.dupNamespace false in
abbrev E (M : ℤ) := ComplexShape.embeddingUpIntGE M

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (M : ℤ)

lemma xiso_indep {i j : ℕ} {p : ℤ} (hi : (E M).f i = p) (hj : (E M).f j = p) :
    K.stupidTruncXIso (E M) hi = K.stupidTruncXIso (E M) hj := by
  obtain rfl : i = j := (E M).injective_f (hi.trans hj.symm)
  rfl

lemma trd (i j : ℕ) :
    (K.stupidTrunc (E M)).d ((E M).f i) ((E M).f j) ≫ (K.stupidTruncXIso (E M) (i := j) rfl).hom =
      (K.stupidTruncXIso (E M) (i := i) rfl).hom ≫ K.d ((E M).f i) ((E M).f j) := by
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.extend_d_eq _ _ rfl rfl, HomologicalComplex.restriction]


open Classical in
def iotaf (p : ℤ) : (K.stupidTrunc (E M)).X p ⟶ K.X p :=
  if h : ∃ i, (E M).f i = p then (K.stupidTruncXIso (E M) h.choose_spec).hom else 0

lemma iotaf_eq (i : ℕ) : iotaf K M ((E M).f i) = (K.stupidTruncXIso (E M) (i := i) rfl).hom := by
  have h : ∃ j, (E M).f j = (E M).f i := ⟨i, rfl⟩
  rw [iotaf, dite_eq_left h, xiso_indep K M h.choose_spec rfl]

lemma stupidTruncation_GE_isZero_below_bound (p : ℤ) (hp : p < M) : IsZero ((K.stupidTrunc (E M)).X p) :=
  HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun i h => by simp [E] at h; omega)

lemma mem (p : ℤ) (hp : M ≤ p) : (E M).f (p - M).toNat = p := by simp [E]; omega

def iota : K.stupidTrunc (E M) ⟶ K where
  f := iotaf K M
  comm' p q hpq := by
    simp only [ComplexShape.up_Rel] at hpq
    by_cases hp : M ≤ p
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, (E M).f j = q := ⟨i + 1, by simp [E] at hpq ⊢; omega⟩
      rw [iotaf_eq, iotaf_eq]
      exact (trd K M i j).symm
    · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _

lemma iota_iso (p : ℤ) (hp : M ≤ p) : IsIso ((iota K M).f p) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
  show IsIso (iotaf K M _)
  rw [iotaf_eq]; infer_instance

lemma iota_nat {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (E M) ≫ iota L M = iota K M ≫ g := by
  ext p
  simp only [HomologicalComplex.comp_f]
  by_cases hp : M ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
    show _ ≫ iotaf L M _ = iotaf K M _ ≫ _
    rw [iotaf_eq, iotaf_eq]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom _ _ rfl
  · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _
end

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {A B I : CochainComplex C ℤ} (φ : A ⟶ B) (M : ℤ)

def P (m : ℤ) (c : Cochain B I m) : Cochain A I m := (Cochain.ofHom φ).comp c (zero_add m)

lemma precomp_injective [I.IsStrictlyGE 0] (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (m : ℤ) (hm : m + M ≤ 0) :
    Function.Injective (P (I := I) φ m) := by
  intro c c' h
  ext p q hpq
  by_cases hp : M ≤ p
  · have := hiso p hp
    have h' := congrArg (fun x : Cochain A I m => x.v p q hpq) h
    simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h'
    exact (cancel_epi _).1 h'
  · exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _

lemma precomp_surjective₂ (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (hz : ∀ p, p < M → IsZero (A.X p)) (m : ℤ) :
    Function.Surjective (P (I := I) φ m) := by
  intro d
  refine ⟨Cochain.mk (fun p q hpq => if h : M ≤ p then (haveI := hiso p h; inv (φ.f p)) ≫ d.v p q hpq else 0), ?_⟩
  ext p q hpq
  simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  by_cases hp : M ≤ p
  · rw [dite_eq_left hp]; simp
  · exact (hz p (by omega)).eq_of_src _ _
end

section
variable {R : Type} [CommRing R] {A B I : Cx R} (φ : A ⟶ B)

lemma cpull_mk (n : ℤ) (z : Cocycle B I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (Cocycle.mk (P φ n z) (n + 1) rfl
      (by simp [P, Cocycle.δ_eq_zero])) := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1

lemma cpull_bij [I.IsStrictlyGE 0] (M : ℤ) (hiso : ∀ p, M ≤ p → IsIso (φ.f p))
    (hz : ∀ p, p < M → IsZero (A.X p)) (n : ℤ) (hn : n + 1 + M ≤ 0) :
    Function.Bijective (cpull φ I n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := precomp_surjective₂ φ M hiso hz (n - 1) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨β', precomp_injective φ M hiso n (by omega) ?_⟩
    rw [Cocycle.mk_coe] at hβ
    rw [← hβ, P, P, δ_ofHom_comp]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨c, hc⟩ := precomp_surjective₂ φ M hiso hz n (z : Cochain A I n)
    have hδ : δ n (n + 1) c = 0 := by
      apply precomp_injective φ M hiso (n + 1) (by omega)
      have : P φ (n + 1) (δ n (n + 1) c) = δ n (n + 1) (P φ n c) := by simp [P]
      rw [this, hc, Cocycle.δ_eq_zero]; simp [P]
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hδ), ?_⟩
    rw [cpull_mk]
    congr 1
    apply Cocycle.ext
    simp only [Cocycle.mk_coe]
    exact hc
end

theorem incl_of : LateralTheory.E.stupidPf.incl := by
  intro R _ I _ K L g N
  refine ⟨iota K (-(N : ℤ)), iota L (-(N : ℤ)), iota_nat _ g, fun n hn => ⟨?_, ?_⟩⟩
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso K _) (stupidTruncation_GE_isZero_below_bound K _) n (by omega)
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso L _) (stupidTruncation_GE_isZero_below_bound L _) n (by omega)

end LateralTheory.E.inclPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.longPfSes
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.longPfSes
open LateralTheory.E.CxDescPf

variable {R : Type} [CommRing R]

theorem eF (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (ComplexShape.embeddingUpIntGE (-(N : ℤ))).f (i + N).toNat = i := by
  show -(N : ℤ) + (((i + N).toNat : ℕ) : ℤ) = i; omega

def trX (K : Cx R) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (tr K N).X i ≅ K.X i := K.stupidTruncXIso _ (eF N i h)

theorem trZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i < -(N : ℤ)) : IsZero ((tr K N).X i) :=
  K.isZero_stupidTrunc_X _ i (by intro k; show -(N : ℤ) + (k : ℤ) ≠ i; omega)

theorem tr_d (K : Cx R) (N : ℕ) (i j : ℤ) (hi : -(N : ℤ) ≤ i) (hj : -(N : ℤ) ≤ j) :
    (tr K N).d i j = (trX K N i hi).hom ≫ K.d i j ≫ (trX K N j hj).inv := by
  have h1 := eF N i hi
  have h2 := eF N j hj
  simp only [trX, HomologicalComplex.stupidTruncXIso, tr, HomologicalComplex.stupidTrunc, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rw [HomologicalComplex.extend_d_eq _ _ h1 h2, HomologicalComplex.restriction_d_eq _ _ h1 h2]
  simp [HomologicalComplex.restrictionXIso]

theorem trm_f {K L : Cx R} (g : K ⟶ L) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) :
    (trm g N).f i = (trX K N i h).hom ≫ g.f i ≫ (trX L N i h).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom g _ (eF N i h)

abbrev Sg (K : Cx R) (N : ℕ) : Cx R :=
  (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ)))

theorem SgZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i ≠ -((N + 1 : ℕ) : ℤ)) : IsZero ((Sg K N).X i) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

def ιf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K N).X i ⟶ (tr K (N + 1)).X i :=
  if h : -(N : ℤ) ≤ i then (trX K N i h).hom ≫ (trX K (N + 1) i (by push_cast; omega)).inv else 0

def ι (K : Cx R) (N : ℕ) : tr K N ⟶ tr K (N + 1) where
  f := ιf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h : -(N : ℤ) ≤ i
    · have hj : -(N : ℤ) ≤ j := by omega
      rw [ιf, dite_eq_left h, ιf, dite_eq_left hj, tr_d K N i j h hj, tr_d K (N + 1) i j (by push_cast; omega) (by push_cast; omega)]
      simp
    · rw [ιf, dite_eq_right h, zero_comp]
      exact (trZ K N i (by omega)).eq_of_src _ _

def pf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K (N + 1)).X i ⟶ (Sg K N).X i :=
  if h : i = -((N + 1 : ℕ) : ℤ) then
    (trX K (N + 1) i (by omega)).hom ≫ eqToHom (by rw [h]) ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) _ (K.X (-((N + 1 : ℕ) : ℤ))) i h).inv
  else 0

def pp (K : Cx R) (N : ℕ) : tr K (N + 1) ⟶ Sg K N where
  f := pf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hj : j = -((N + 1 : ℕ) : ℤ)
    · exact (trZ K (N + 1) i (by push_cast at hj ⊢; omega)).eq_of_src _ _
    · exact (SgZ K N j hj).eq_of_tgt _ _

theorem ιp (K : Cx R) (N : ℕ) : ι K N ≫ pp K N = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  by_cases h : -(N : ℤ) ≤ i
  · exact (SgZ K N i (by push_cast; omega)).eq_of_tgt _ _
  · show ιf K N i ≫ _ = 0
    rw [ιf, dite_eq_right h, zero_comp]

theorem nat1 {K L : Cx R} (g : K ⟶ L) (N : ℕ) : ι K N ≫ trm g (N + 1) = trm g N ≫ ι L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : -(N : ℤ) ≤ i
  · show ιf K N i ≫ _ = _ ≫ ιf L N i
    rw [ιf, dite_eq_left h, ιf, dite_eq_left h, trm_f g N i h, trm_f g (N + 1) i (by push_cast; omega)]
    simp
  · exact (trZ K N i (by omega)).eq_of_src _ _

theorem nat2 {K L : Cx R} (g : K ⟶ L) (N : ℕ) :
    pp K N ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) =
      trm g (N + 1) ≫ pp L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : i = -((N + 1 : ℕ) : ℤ)
  · subst h
    show pf K N _ ≫ _ = _ ≫ pf L N _
    rw [pf, dite_eq_left rfl, pf, dite_eq_left rfl, trm_f g (N + 1) _ (by omega)]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleObjXSelf]
  · exact (SgZ L N i h).eq_of_tgt _ _

theorem sesK (K : Cx R) (N : ℕ) : (ShortComplex.mk (ι K N) (pp K N) (ιp K N)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h : -(N : ℤ) ≤ i
  · have hz : IsZero ((Sg K N).X i) := SgZ K N i (by push_cast; omega)
    have : IsIso (ιf K N i) := by rw [ιf, dite_eq_left h]; infer_instance
    have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).f := this
    refine ShortComplex.ShortExact.mk' ?_ inferInstance (hz.epi _)
    rw [ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)]
    infer_instance
  · by_cases h' : i = -((N + 1 : ℕ) : ℤ)
    · have hz : IsZero ((tr K N).X i) := trZ K N i (by omega)
      have : IsIso (pf K N i) := by subst h'; rw [pf, dite_eq_left rfl]; exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))
      have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).g := this
      refine ShortComplex.ShortExact.mk' ?_ (hz.mono _) inferInstance
      rw [ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)]
      infer_instance
    · have hz2 : IsZero ((tr K (N + 1)).X i) := trZ K (N + 1) i (by push_cast at h' ⊢; omega)
      have hz1 : IsZero ((tr K N).X i) := trZ K N i (by omega)
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz2) (hz1.mono _) ((SgZ K N i h').epi _)

theorem ses : LateralTheory.E.longPf.Ses := fun _ _ N =>
  ⟨fun K => ι K N, fun K => pp K N, fun K => ιp K N, fun K => sesK K N, fun g => ⟨nat1 g N, nat2 g N⟩⟩

theorem long_of (hLES : LateralTheory.E.longPf.LES) : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPf.long_of hLES ses

end LateralTheory.E.longPfSes
end
end

