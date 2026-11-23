module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0010
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPBPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafPBInvSp : Prop := ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (sp R)

def LeafPBCmp : Prop := A1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ i : ℤ, Eqv _ e (tw q i)

def LeafAffEqv : Prop := A1 → ∀ (q : ℕ) [NeZero q] {E E' : Spc} (e : E ⟶ E'),
  (∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
    (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) →
  ∀ i : ℤ, Eqv _ e (tw q i)

def LeafPBMap : Prop := ∀ (N : ℕ) (R : Type) [CommRing R],
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx (pullback V (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)

theorem leafPBCmp_of (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPBCmp := by
  intro hA1 q _ N R _ _
  obtain ⟨V, e, h1, h2, h3⟩ := hMap N R
  exact ⟨V, e, h1, h2, hAff hA1 q e h3⟩

theorem leafPBInvSp : LeafPBInvSp := by
  intro q R _ hq U ⟨x⟩
  have f : U ⟶ Spec (CommRingCat.of R) := x
  have h1 := hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have h2 := h1.map f.appTop.hom
  simpa using h2

theorem pull_cast' {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (Ht.cast hn hi x) = Ht.cast (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (hA : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast', (hA q).2.1 f hE]
  | succ k ih =>
    show pull _ f _ _ ((cup q (cpow q x k) x).cast (by push_cast; ring) (by push_cast; ring)) =
      (cup q (cpow q (pull _ f _ _ x) k) (pull _ f _ _ x)).cast (by push_cast; ring) (by push_cast; ring)
    rw [pull_cast', (hA q).1, ih]

theorem LeafPB_of' (hGeo : LeafGeo) (hCmp : LeafPBCmp) : LeafPB := by
  have hInv := leafPBInvSp
  intro hA1 hA6 hD1 q _ N R _ hq n i
  obtain ⟨V, e, h1, h2, h3⟩ := hCmp hA1 q N R hq
  have hD := hD1 q V (hInv q R hq) n i
  have hPR : Inv q (PR N 0 R) := hGeo.2.1 q N 0 R hq
  refine (Function.Bijective.of_comp_iff' (h3 i n) _).1 ?_
  convert hD using 1
  funext a
  simp only [Function.comp_apply, poly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast', (hA6 q).1, pull_cpow' hA6 q e hPR, ← pull_comp, h1, hyp, (hA6 q).2.2.1 e _ hPR, h2]

theorem LeafPB_of (hGeo : LeafGeo) (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPB :=
  LeafPB_of' hGeo (leafPBCmp_of hMap hAff)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafHensH : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (C : Type) [CommRing C] (K : Ideal C), HenselianRing C K →
  IsUnit (q : C) → ∀ i : ℤ, Eqv (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i)

def LeafAffQuot : Prop := LeafQuot → ∀ (d : ℕ) (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) →
  ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I →
  Function.Bijective ((Ideal.Quotient.mk K).comp (η.comp (ψ.comp MvPolynomial.C)))

def LeafExcAff : Prop := Hyp → LeafIndExc → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I → ∃ h,
  Exc q (opnMap (Spec.map (CommRingCat.ofHom (η.comp ψ))) (off C K) (off _ (Ideal.span (Set.range MvPolynomial.X))) h)

theorem spMap_comp' {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  change sch.map _ = sch.map _ ≫ sch.map _
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_spMap_bij {A B : Type} [CommRing A] [CommRing B] (e : A →+* B) (he : Function.Bijective e)
    {S : Type} [CommRing S] (F : Shv S) : Eqv S (spMap e) F := by
  let E := RingEquiv.ofBijective e he
  have h1 : (E.symm : B →+* A).comp e = RingHom.id A := by ext x; exact E.symm_apply_apply x
  have h2 : e.comp (E.symm : B →+* A) = RingHom.id B := by ext x; exact E.apply_symm_apply x
  have : IsIso (spMap e) := ⟨⟨spMap (E.symm : B →+* A), by rw [← spMap_comp', h2, spMap_id'],
    by rw [← spMap_comp', h1, spMap_id']⟩⟩
  exact eqv_iso _ F

theorem LeafPrdAff_of (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h2 : LeafAffQuot) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff := by
  intro hyp d q _ R B C _ _ _ ψ η hq hψ I K hη hK hH hI' hy n i
  have hth : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hT hyp d)
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqC : IsUnit (q : C) := by simpa using hq.map ((η.comp ψ).comp MvPolynomial.C)
  obtain ⟨h, hE⟩ := h3 hyp hI d q R B C ψ η hq hψ I K hη hK hI'
  have hnat := (hth q).1 (MvPolynomial (Fin d) R) C (η.comp ψ) (Ideal.span (Set.range MvPolynomial.X)) K MvPolynomial.X rfl
    hy h hqP
  have hg := (hth q).2.2.1 R (Ideal.span (Set.range MvPolynomial.X)) rfl hq n i
  let p := pull (ZMod q) (spMap ((η.comp ψ).comp (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) (tw q i) n
  have hmk := h1 hyp q C K hH hqC i n
  have he := eqv_spMap_bij _ (h2 hQ d R B C ψ η hψ I K hη hK hI') (tw q i) n
  have hp : Function.Bijective p := by
    rw [spMap_comp'] at he
    have e2 : (pull (ZMod q) (spMap (Ideal.Quotient.mk K) ≫ spMap (η.comp (ψ.comp MvPolynomial.C))) (tw q i) n : _ → _) =
        (pull (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i) n) ∘ p := funext fun x => pull_comp _ _ _ _ _ x
    rw [e2] at he
    exact (Function.Bijective.of_comp_iff' hmk p).1 he
  have hpb : ∀ b, p b = pull (ZMod q) (spMap (η.comp ψ)) (tw q i) n (pull (ZMod q) (spMap MvPolynomial.C) (tw q i) n b) :=
    fun b => by
      change pull _ _ _ _ b = _
      rw [← pull_comp, ← spMap_comp']
  refine (Function.Bijective.of_comp_iff _ hp).1 ?_
  have key := (hE (n + 2 * d) (i + d)).comp hg
  convert key using 1
  funext b
  refine Eq.trans ?_ (hA hyp.2.2.2.2.1 q _ _ _ n (2 * d) i d _ _).symm
  rw [hnat, Function.comp_apply, hpb]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdHocPfX
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem sq (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (f : E' ⟶ E)
    (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X) (h : f ≫ π = π') {n m i k : ℤ} (x : Ht q E n i) (b : Hs q (opn U) m k) :
    Hs.pull q (abvRel U f π' π h) _ _ (Hs.act q (P := abv U π) x (Hs.pull q (abvMap U π) _ _ b)) =
      Hs.act q (P := abv U π') (pull _ f _ _ x) (Hs.pull q (abvMap U π') _ _ b) := by
  have e := AN a6 q _ _ (abvRel U f π' π h) n m i k x (Hs.pull q (abvMap U π) _ _ b)
  rw [← hs_pull_comp, abvRel_abvMap] at e
  exact e

theorem prd_sum (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}}
    (U : X.Opens) {A : Type} (E : A → PSh) (P : PSh) (g : ∀ a, E a ⟶ P) (t : IsColimit (Cofan.mk P g))
    (π : P ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X) (h : ∀ a, g a ≫ π = π' a) {m k : ℤ} (b : Hs q (opn U) m k)
    (hb : ∀ a, Prd q U (E := disc.obj (E a)) (disc.map (π' a)) b) :
    Prd q U (E := disc.obj P) (disc.map π) b := by
  intro n i
  have h' : ∀ a, disc.map ((Cofan.mk P g).inj a) ≫ disc.map π = disc.map (π' a) := fun a => by
    rw [← disc.map_comp]; exact congrArg disc.map (h a)
  have tS : IsColimit (Cofan.mk (disc.obj P) fun a => disc.map (g a)) := isColimitCofanMkObjOfIsColimit disc E g t
  have hΦ := S (ZMod q) (tw q i) A (fun a => disc.obj (E a)) _ ⟨tS⟩ n
  have hΨ := HS q X U A E (Cofan.mk P g) ⟨t⟩ π π' h' (n + m) (i + k)
  have hP : Function.Bijective (Pi.map fun a (x : Ht q (disc.obj (E a)) n i) =>
      Hs.act q (P := abv U (disc.map (π' a))) x (Hs.pull q (abvMap U (disc.map (π' a))) _ _ b)) :=
    Function.Bijective.piMap fun a => hb a n i
  refine (Function.Bijective.of_comp_iff' hΨ _).1 ?_
  convert hP.comp hΦ using 1
  all_goals try rfl
  funext x
  funext a
  exact sq AN a6 q U _ _ _ (h' a) x b

theorem inj_aug_RPrdH {J : Type} [SmallCategory J] (D : J ⥤ PSh) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc : Coc D c) (N : SimplexCategoryᵒᵖ) (σ : Fin (N.unop.len + 1) ⥤ J) :
    inj D N σ ≫ ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X) = c (σ.obj 0) := by
  ext U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ (σ.map (homOfLE (Fin.zero_le 0)))) U) x

theorem LeafPrdHoc_of (lvl : LeafPrdLevel) (L : LeafLevel) (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) :
    LeafPrdHoc := by
  intro hyp q _ J _ D X U c hc m k b hb
  refine lvl hyp q X U _ (aug c hc) m k b fun N => ?_
  exact prd_sum S HS AN hyp.2.2.2.2.1 q U (fun σ : Fin (N.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) ((hoc D).obj N)
    (inj D N) (L J D N).some ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X)
    (fun σ : Fin (N.unop.len + 1) ⥤ J => c (σ.obj 0)) (inj_aug_RPrdH D c hc N) b
    (fun σ : Fin (N.unop.len + 1) ⥤ J => hb (σ.obj 0))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdRingPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem prd_sub_C_mem {σ R : Type} [CommRing R] (p : MvPolynomial σ R) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    have e : p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) =
        (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add (f := _)]; ring
    rw [e]; exact Ideal.add_mem _ hp hr
  | mul_X p i _ =>
    have e : p * MvPolynomial.X i - MvPolynomial.C (MvPolynomial.constantCoeff (p * MvPolynomial.X i)) =
        p * MvPolynomial.X i := by simp
    rw [e]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem prd_nbhd_psi {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (φ : A →+* B)
    (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B) (hφ : Nbhd φ I) (hψ : ψ.Etale)
    (hIB : I.map φ = Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)))
    (hl : ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ) :
    Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) := by
  refine ⟨hψ, ?_⟩
  have hQ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ := by
    rw [Ideal.map_span, hIB, ← Set.range_comp]; rfl
  have key : ∀ a : A, ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) - φ a ∈
      (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ := by
    intro a; rw [hQ, ← neg_sub]; exact (Ideal.neg_mem_iff _).2 (hl a)
  constructor
  · set_option synthInstance.maxHeartbeats 200000 in
      rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff p)
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have h1 := prd_sub_C_mem p
    have h2 : ψ p - ψ (MvPolynomial.C (MvPolynomial.constantCoeff p)) ∈
        (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ := by
      rw [← map_sub]; exact Ideal.mem_map_of_mem _ h1
    have h3 : φ a ∈ I.map φ := by
      rw [← hQ]
      have h5 := Ideal.sub_mem _ hx h2
      rw [sub_sub_cancel, ← ha] at h5
      have h6 := Ideal.sub_mem _ h5 (key a)
      rwa [sub_sub_cancel] at h6
    have h4 : Ideal.Quotient.mk I a = 0 := by
      apply hφ.2.1
      rw [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]; exact h3
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [← ha, h4, map_zero, sub_zero] at h1
    exact h1
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hφ.2.2 (Ideal.Quotient.mk (I.map φ) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hx' : φ a - b ∈ (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ := by
      rw [hQ]; exact hx
    have h7 := Ideal.add_mem _ (key a) hx'
    rwa [sub_add_sub_cancel] at h7

theorem prd_indNbhd_of_nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) :
    IndNbhd φ I := by
  refine ⟨Discrete PUnit, inferInstance, inferInstance, (Functor.const _).obj (CommRingCat.of B),
    { app := fun _ => CommRingCat.ofHom φ, naturality := fun _ _ _ => by simp }, 𝟙 _, ⟨?_⟩, fun _ => ⟨h, ?_⟩⟩
  · exact { desc := fun s => s.ι.app ⟨⟨⟩⟩
            fac := fun s j => by rcases j with ⟨⟨⟩⟩; simp
            uniq := fun s m hm => by simpa using hm ⟨⟨⟩⟩ }
  · simp

theorem prd_off_le {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J ≤ I.map f) : off B J ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ off A I := by
  intro x hx h'
  apply hx
  change (J : Set B) ⊆ x.asIdeal
  have h'' : (I : Set A) ⊆ (Ideal.comap f x.asIdeal) := h'
  exact hJ.trans (Ideal.map_le_iff_le_comap.2 h'')

theorem prd_opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens)
    (U : X.Opens) (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) (h'' : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map f ≫ sch.map g = sch.map (f ≫ g)
    rw [Functor.map_comp]

theorem prd_opnMap_congr {X' X : Scheme.{0}} {f f' : X' ⟶ X} (e : f = f') (U' : X'.Opens) (U : X.Opens)
    (h : U' ≤ f ⁻¹ᵁ U) (h' : U' ≤ f' ⁻¹ᵁ U) : opnMap f U' U h = opnMap f' U' U h' := by
  subst e; rfl

theorem prd_exc_left (q : ℕ) {P'' P' P : Arrow Spc} {φ : P'' ⟶ P'} {ψ : P' ⟶ P} (h : Exc q (φ ≫ ψ))
    (h' : Exc q ψ) : Exc q φ := fun n i => by
  have e : ⇑(Hs.pull q (φ ≫ ψ) n i) = Hs.pull q φ n i ∘ Hs.pull q ψ n i := funext (hs_pull_comp q φ ψ n i)
  have h2 := h n i
  rw [e] at h2
  exact (Function.Bijective.of_comp_iff _ (h' n i)).1 h2

theorem prd_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  change sch.map _ ≫ sch.map _ = sch.map _
  rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem prd_pull_bij {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Bijective g) (q : ℕ)
    (i n : ℤ) : Function.Bijective (pull _ (spMap g) (tw q i) n) := by
  let e := RingEquiv.ofBijective g hg
  have hid : ∀ (T : Type) [CommRing T], spMap (RingHom.id T) = 𝟙 _ := fun T _ => by
    change sch.map _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, CategoryTheory.Functor.map_id]
  have h1 : spMap g ≫ spMap (e.symm : S →+* R) = 𝟙 _ := by
    rw [prd_spMap_comp]
    have : g.comp (e.symm : S →+* R) = RingHom.id S := by ext x; exact e.apply_symm_apply x
    rw [this, hid]
  have h2 : spMap (e.symm : S →+* R) ≫ spMap g = 𝟙 _ := by
    rw [prd_spMap_comp]
    have : (e.symm : S →+* R).comp g = RingHom.id R := by ext x; exact e.symm_apply_apply x
    rw [this, hid]
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap (e.symm : S →+* R)) (tw q i) n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

theorem prd_le_comp {X'' X' X : Scheme.{0}} {f : X'' ⟶ X'} {g : X' ⟶ X} {U'' : X''.Opens} {U' : X'.Opens}
    {U : X.Opens} (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) : U'' ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro x hx
  have h2 := h' (h hx)
  simpa using h2

theorem prd_transfer (hAN : LeafActNat) (a6 : DivisorNaturality) {d q : ℕ} [NeZero q] {A' C : Type} [CommRing A'] [CommRing C]
    (IA : Ideal A') (K : Ideal C) (m : A' →+* C) (hm : off C K ≤ Spec.map (CommRingCat.ofHom m) ⁻¹ᵁ off A' IA)
    (cA : Hs q (opn (off A' IA)) (2 * d) d) (cC : Hs q (opn (off C K)) (2 * d) d)
    (hcl : Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm) _ _ cA = cC)
    (hexc : Exc q (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm))
    (hpull : ∀ n i : ℤ, Function.Bijective (pull _ (spMap m) (tw q i) n))
    (hC : ∀ n i : ℤ, Function.Bijective fun b : Ht q (sp C) n i => Hs.act q (P := opn (off C K)) b cC)
    (n i : ℤ) : Function.Bijective fun a : Ht q (sp A') n i => Hs.act q (P := opn (off A' IA)) a cA := by
  refine (Function.Bijective.of_comp_iff' (hexc _ _) _).1 ?_
  have e : (⇑(Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm) (n + 2 * d) (i + d)) ∘
      fun a : Ht q (sp A') n i => Hs.act q (P := opn (off A' IA)) a cA) =
      (fun b : Ht q (sp C) n i => Hs.act q (P := opn (off C K)) b cC) ∘ ⇑(pull _ (spMap m) (tw q i) n) := by
    funext a
    simp only [Function.comp]
    have e2 := hAN a6 q _ _ (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm) n (2 * d) i d a cA
    rw [hcl] at e2
    exact e2
  rw [e]; exact (hC n i).comp (hpull n i)

theorem LeafPrdRing_of (hQ : LeafQuot) (hIE : LeafIndExc) (hT : LeafThom) (hPA : LeafPrdAff) (hAN : LeafActNat) :
    LeafPrdRing := by
  intro hyp H d q _ A _ I hq hI hch c hc h n i
  have hyp' := hyp
  obtain ⟨a1, -, -, a4, a6, -, -, -, b1, -, -, e1⟩ := hyp'
  obtain ⟨B, _, φ, ψ, hφ, hψ, hIB, hl⟩ := hch
  obtain ⟨th, hth⟩ := hT hyp d
  have hTh : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ ⟨th, hth⟩
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  have hqR : IsUnit (q : A ⧸ I) := by simpa using hq.map (Ideal.Quotient.mk I)
  have hqA' : IsUnit (q : H.obj A I) := by simpa using hq.map (H.η A I)
  have hqC : IsUnit (q : H.obj B (I.map φ)) := by simpa using hqB.map (H.η B (I.map φ))
  obtain ⟨m, hmdef⟩ : ∃ m, m = H.map (I := I) (J := I.map φ) φ Ideal.le_comap_map := ⟨_, rfl⟩
  have hmη : m.comp (H.η A I) = (H.η B (I.map φ)).comp φ := by rw [hmdef]; exact H.map_η _ _
  have hK' : (I.map φ).map (H.η B (I.map φ)) = (I.map (H.η A I)).map m := by
    rw [Ideal.map_map, Ideal.map_map, hmη]
  have hy : Ideal.span (Set.range fun j => H.η B (I.map φ) (ψ (MvPolynomial.X j))) =
      (I.map φ).map (H.η B (I.map φ)) := by
    have e := congrArg (Ideal.map (H.η B (I.map φ))) hIB
    rw [e, Ideal.map_span, ← Set.range_comp]; rfl
  have hm : off _ ((I.map φ).map (H.η B (I.map φ))) ≤ Spec.map (CommRingCat.ofHom m) ⁻¹ᵁ off _ (I.map (H.η A I)) :=
    prd_off_le _ _ _ (le_of_eq hK')
  have hB : off _ ((I.map φ).map (H.η B (I.map φ))) ≤
      Spec.map (CommRingCat.ofHom (H.η B (I.map φ))) ⁻¹ᵁ off B (I.map φ) := prd_off_le _ _ _ le_rfl
  have hφo : off B (I.map φ) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A I := prd_off_le _ _ _ le_rfl
  have excA := hIE a1 a4 b1 q (H.η A I) I hI (H.ind A I) hq h
  have excB := hIE a1 a4 b1 q (H.η B (I.map φ)) (I.map φ) (hI.map φ) (H.ind B _) hqB hB
  have excφ := hIE a1 a4 b1 q φ I hI (prd_indNbhd_of_nbhd φ I hφ) hq hφo
  have hSpec : Spec.map (CommRingCat.ofHom m) ≫ Spec.map (CommRingCat.ofHom (H.η A I)) =
      Spec.map (CommRingCat.ofHom (H.η B (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hmη]
  have hΦG : opnMap _ _ _ hm ≫ opnMap _ _ _ h = opnMap _ _ _ hB ≫ opnMap _ _ _ hφo := by
    rw [prd_opnMap_comp _ _ _ _ _ hm h (prd_le_comp hm h), prd_opnMap_comp _ _ _ _ _ hB hφo (prd_le_comp hB hφo)]
    exact prd_opnMap_congr hSpec _ _ _ _
  have excΦ : Exc q (opnMap _ _ _ hm) := by
    refine prd_exc_left q ?_ excA
    rw [hΦG]; exact exc_comp q excB excφ
  have hcl : Hs.pull q (opnMap _ _ _ hm) _ _ (Hs.pull q (opnMap _ _ _ h) _ _ c) =
      thom d q (H.obj B (I.map φ)) ((I.map φ).map (H.η B (I.map φ))) _ hy := by
    rw [← hs_pull_comp, hΦG, hs_pull_comp, hc B φ (fun j => ψ (MvPolynomial.X j)) hIB.symm hφo hφ.1]
    exact (hTh q).1 B (H.obj B (I.map φ)) (H.η B (I.map φ)) (I.map φ) _ (fun j => ψ (MvPolynomial.X j)) hIB.symm hy hB hqB
  have hpull : ∀ n i : ℤ, Function.Bijective (pull _ (spMap m) (tw q i) n) := by
    intro n i
    have := H.hens A I
    have := H.hens B (I.map φ)
    have eA := e1 q (H.obj A I) (I.map (H.η A I)) hqA' i n
    have eC := e1 q (H.obj B (I.map φ)) ((I.map φ).map (H.η B (I.map φ))) hqC i n
    have hle : I.map (H.η A I) ≤ ((I.map φ).map (H.η B (I.map φ))).comap m := by
      rw [hK']; exact Ideal.le_comap_map
    have hqm : Function.Bijective (Ideal.quotientMap _ m hle) := by
      have hqA := hQ A (H.obj A I) (H.η A I) I (H.ind A I)
      have hqB' := hQ B (H.obj B (I.map φ)) (H.η B (I.map φ)) (I.map φ) (H.ind _ _)
      have hcomp : ⇑(Ideal.quotientMap _ m hle) ∘ ⇑(Ideal.quotientMap (I.map (H.η A I)) (H.η A I) Ideal.le_comap_map) =
          ⇑(Ideal.quotientMap ((I.map φ).map (H.η B (I.map φ))) (H.η B (I.map φ)) Ideal.le_comap_map) ∘
          ⇑(Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
        funext x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [Function.comp, Ideal.quotientMap_mk]
        rw [show m (H.η A I a) = H.η B (I.map φ) (φ a) from RingHom.congr_fun hmη a]
      exact (Function.Bijective.of_comp_iff _ hqA).1 (by rw [hcomp]; exact hqB'.comp hφ.2)
    have hsq : spMap (Ideal.Quotient.mk ((I.map φ).map (H.η B (I.map φ)))) ≫ spMap m =
        spMap (Ideal.quotientMap _ m hle) ≫ spMap (Ideal.Quotient.mk (I.map (H.η A I))) := by
      rw [prd_spMap_comp, prd_spMap_comp, Ideal.quotientMap_comp_mk]
    have e : ⇑(pull _ (spMap (Ideal.Quotient.mk ((I.map φ).map (H.η B (I.map φ))))) (tw q i) n) ∘
        ⇑(pull _ (spMap m) (tw q i) n) = ⇑(pull _ (spMap (Ideal.quotientMap _ m hle)) (tw q i) n) ∘
        ⇑(pull _ (spMap (Ideal.Quotient.mk (I.map (H.η A I)))) (tw q i) n) := by
      funext x
      simp only [Function.comp]
      rw [← pull_comp, ← pull_comp, hsq]
    exact (Function.Bijective.of_comp_iff' eC _).1 (by rw [e]; exact (prd_pull_bij _ hqm q i n).comp eA)
  have hC := fun n i => hPA hyp d q (A ⧸ I) B (H.obj B (I.map φ)) ψ (H.η B (I.map φ)) hqR
    (prd_nbhd_psi I φ ψ hφ hψ hIB hl) (I.map φ) _ (H.ind B _) rfl (H.hens B _) hIB.symm hy n i
  exact prd_transfer hAN a6 (I.map (H.η A I)) _ m hm _ _ hcl excΦ hpull hC n i

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChPush : Prop := ∀ (q : ℕ) (P : Arrow Spc),
  IsPushout ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map (dbl.inl P))
    ((chains (ZMod q)).map (dbl.inr P))

def LeafHKSplit : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B D : Cx R} (f : A ⟶ B) (l r : B ⟶ D)
  (s : D ⟶ B), IsPushout f f l r → r ≫ s = 𝟙 _ → ∀ p : D ⟶ cokernel f, l ≫ p = cokernel.π f → r ≫ p = 0 →
  Function.Injective (HK.pull R p F n) ∧ ∀ x, HK.pull R r F n x = 0 → ∃ y, HK.pull R p F n y = x

theorem hk_pull_pull {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R f F n (HK.pull R g F n x) = HK.pull R (f ≫ g) F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hk_pull_zero {R : Type} [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem LeafRel_of (h1 : LeafChPush) (h2 : LeafHKSplit) : LeafRel := by
  intro q i
  have ex : ∀ P : Arrow Spc, ∃ p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ ∧ (chains _).map (dbl.inr P) ≫ p = 0 := fun P =>
    ⟨(h1 q P).desc (cokernel.π _) 0 (by simp), (h1 q P).inl_desc _ _ _, (h1 q P).inr_desc _ _ _⟩
  choose p hl hr using ex
  have hs : ∀ P : Arrow Spc, (chains (ZMod q)).map (dbl.inr P) ≫ (chains _).map (dbl.fold P) = 𝟙 _ := fun P => by
    rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]
  have mem : ∀ (P : Arrow Spc) (n : ℤ) x, HK.pull _ (p P) (tw q i) n x ∈ Hs q P n i := fun P n x => by
    change HK.pull _ ((chains _).map (dbl.inr P)) (tw q i) n (HK.pull _ (p P) (tw q i) n x) = 0
    rw [hk_pull_pull, hr, hk_pull_zero]
  refine ⟨fun P n => AddEquiv.ofBijective ((HK.pull _ (p P) (tw q i) n).codRestrict _ (mem P n)) ⟨fun x y h => ?_, fun x => ?_⟩,
    fun P n p' hl' hr' x => ?_⟩
  · exact (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).1 (congrArg Subtype.val h)
  · obtain ⟨y, hy⟩ := (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).2 x.1 x.2
    exact ⟨y, Subtype.ext hy⟩
  · have e : p' = p P := (h1 q P).hom_ext (hl'.trans (hl P).symm) (hr'.trans (hr P).symm)
    subst e; rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

