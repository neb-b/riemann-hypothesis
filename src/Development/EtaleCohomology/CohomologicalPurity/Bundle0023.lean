module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0016
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0009
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0011
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0018
public import Development.EtaleCohomology.CohomologicalPurity.LeafFstHocPf

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfQuot
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem quotC_bij (d : ℕ) (R : Type) [CommRing R] :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
      MvPolynomial.C) := by
  have hJ : Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) = MvPolynomial.X '' Set.univ := Set.image_univ.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ, MvPolynomial.mem_ideal_span_X_image] at hr
    by_contra h
    obtain ⟨i, -, hi⟩ := hr 0 (by rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_pos rfl]; exact h)
    exact hi rfl
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hJ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push_neg at hcon
    have : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    subst this
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
      ← MvPolynomial.constantCoeff_eq, sub_self] at hm
    exact hm rfl

theorem leafAffQuot_pf : LeafAffQuot := by
  intro hQ d R B C _ _ _ ψ η hψ I K hη hK hI
  subst hK
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI
  have b2 := hψ.2
  have b3 := hQ B C η _ hη
  have e : (Ideal.Quotient.mk _).comp (η.comp (ψ.comp MvPolynomial.C)) =
      ((Ideal.quotientMap _ η Ideal.le_comap_map).comp (Ideal.quotientMap _ ψ Ideal.le_comap_map)).comp
        ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
          MvPolynomial.C) := by
    ext r; simp [Ideal.quotientMap_mk]
  rw [e]
  exact (b3.comp b2).comp (quotC_bij d R)

theorem LeafPrdAff_of' (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff :=
  LeafPrdAff_of hT hA h1 leafAffQuot_pf h3 hQ hI

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPurProjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurProjPf

open PurPf

def HsCast {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) : Hs q P N' I' := by
  subst hN; subst hI; exact x

theorem HsCast_val {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    (HsCast hN hI x).1 = Ht.cast hN hI x.1 := by
  subst hN; subst hI; rfl

theorem HsCast_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {N N' I I' : ℤ} (hN : N = N') (hI : I = I')
    (x : Hs q P N I) : Hs.pull q φ N' I' (HsCast hN hI x) = HsCast hN hI (Hs.pull q φ N I x) := by
  subst hN; subst hI; rfl

theorem HsCast_fgt {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    Hs.fgt q P N' I' (HsCast hN hI x) = Ht.cast hN hI (Hs.fgt q P N I x) := by
  subst hN; subst hI; rfl

theorem act_val (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : (Hs.act q a b).1 = cup q (pull _ (dbl.fold P) _ n a) b.1 := by
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change cup q (pull _ (dbl.fold P) _ n a) b.1 -
    pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1)) = _
  rw [(hA q).1, hb]
  simp only [map_zero, sub_zero]

theorem act_cup (hA : DivisorNaturality) (hR : DivisorRingCompatibility) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m k i j l : ℤ}
    (x : Ht q P.right n i) (y : Ht q P.right m j) (c : Hs q P k l) :
    Hs.act q (cup q x y) c = HsCast (by ring) (by ring) (Hs.act q x (Hs.act q y c)) := by
  apply Subtype.ext
  rw [HsCast_val, act_val hA, act_val hA, act_val hA, (hA q).1, (hR q _).2.1]

theorem fgt_act (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (s : Hs q P m j) : Hs.fgt q P _ _ (Hs.act q a s) = cup q a (Hs.fgt q P m j s) := by
  change pull _ (dbl.inl P) _ _ (Hs.act q a s).1 = cup q a (pull _ (dbl.inl P) _ _ s.1)
  rw [act_val hA, (hA q).1, ← pull_comp, show dbl.inl P ≫ dbl.fold P = 𝟙 _ from pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _, pull_id]

theorem purT_char {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : ∃ e : Ht q (T P).E n i,
      pull _ (pullback.fst (T P).π (sch.map P.ι)) _ _ e = pull _ (pullback.snd (T P).π (sch.map P.ι)) _ _ x ∧
      Hs.pull q (abvMap P.U (T P).π) _ _ (purT T q P n i x) =
        Hs.act q (P := abv P.U (T P).π) e (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  refine ⟨(AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
    (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n x), ?_, ?_⟩
  · exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).1 i n)
  · unfold purT
    rw [dite_eq_left h]
    exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))

end PurProjPf

open PurPf PurProjPf

theorem LeafPurProj_of : EtalePurityProjection := by
  intro hH d T q _ P hq n m i j a b
  have hA : DivisorNaturality := hH.2.2.2.2.1
  have hR : DivisorRingCompatibility := hH.2.2.2.2.2.1
  obtain ⟨eb, heb1, heb2⟩ := purT_char T q P hq m j b
  obtain ⟨ex, hex1, hex2⟩ := purT_char T q P hq (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)
  have hex : ex = cup q (pull (ZMod q) (T P).π (tw q i) n a) eb := by
    apply (((T P).ok q hq).1 (i + j) (n + m)).1
    set_option synthInstance.maxHeartbeats 200000 in
      rw [hex1, (hA q).1, (hA q).1, heb1, ← pull_comp, ← pull_comp, pullback.condition]
  have hN : n + (m + 2 * (d : ℤ)) = n + m + 2 * d := by ring
  have hI : i + (j + (d : ℤ)) = i + j + d := by ring
  have key : purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) =
      HsCast hN hI (Hs.act q (P := opn P.U) (n := n) (i := i) a (purT T q P m j b)) := by
    apply (((T P).ok q hq).2.2.1 (n + m + 2 * d) (i + j + d)).1
    rw [hex2, hex, HsCast_pull]
    refine (act_cup hA hR q (P := abv P.U (T P).π) (pull (ZMod q) (T P).π (tw q i) n a) eb
      (Hs.pull q (abvMap P.U (T P).π) (2 * d) d (fcl d q P))).trans ?_
    rw [TubeCut.LeafActNat_of hA q _ _ (abvMap P.U (T P).π) n (m + 2 * d) i (j + d) a (purT T q P m j b), heb2]
    rfl
  rw [key, HsCast_fgt]
  exact congrArg (Ht.cast hN hI) (fgt_act hA q (P := opn P.U) a (purT T q P m j b))

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTailRepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem Vec.hom_subsingleton (N k : ℕ) (U : Scheme.{0}) (v w : Vec N k U) : Subsingleton (v ⟶ w) := by
  constructor
  intro a b
  apply Subtype.ext; apply Units.ext
  rw [← sub_eq_zero]
  set s : Γ(U, ⊤) := (a.1 : Γ(U, ⊤)) - b.1 with hs_def
  have hs : ∀ i, s * w.1 i = 0 := fun i => by rw [hs_def, sub_mul, ← a.2 i, ← b.2 i, sub_self]
  have hcov : (⊤ : U.Opens) ≤ iSup fun i => U.basicOpen (w.1 i) := by
    intro p _
    obtain ⟨i, -, hp⟩ := w.2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hp⟩
  refine U.sheaf.eq_of_locally_eq' (fun i => U.basicOpen (w.1 i)) ⊤ (fun i => homOfLE le_top) hcov s 0 fun i => ?_
  have hu : IsUnit (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op (w.1 i)) :=
    U.toRingedSpace.isUnit_res_basicOpen (w.1 i)
  have h0 := congrArg (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op) (hs i)
  rw [map_mul, map_zero] at h0
  change U.presheaf.map _ s = U.presheaf.map _ 0
  rw [map_zero]
  exact (hu.mul_left_eq_zero).1 h0

theorem off_le_C (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp
  simp only [off, Scheme.Hom.mem_preimage] at hp ⊢
  intro hI
  apply hp
  have hI' : ∀ x ∈ I, Polynomial.C x ∈ p.asIdeal := fun x hx => hI hx
  show ((Ideal.map Polynomial.C I : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  exact Ideal.map_le_iff_le_comap.2 (fun x hx => hI' x hx)

def LeafTailNerve : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R')
    (e₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)))
    (e₂ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0))),
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n ≫ e₂.hom =
      e₁.hom ≫ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R' ⟶ PR d 0 R').app (op (SimplexCategory.mk 0))

def LeafTailRep0 : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : (PR (d + 1) 1 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : (PR d 0 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off A I).toScheme),
      (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app (op (SimplexCategory.mk 0)) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep_of (hN : LeafTailNerve) (h0 : LeafTailRep0) : LeafTailRep := by
  intro d R _ n
  obtain ⟨R', _, ψ, e₁, e₂, w₁⟩ := hN d R n
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w₂⟩ := h0 d R'
  refine ⟨A, inferInstance, I, φ.comp ψ, hI, h, disc.mapIso (e₁ ≪≫ f₁), disc.mapIso (e₂ ≪≫ f₂), ?_⟩
  change disc.map _ ≫ disc.map (e₂.hom ≫ f₂.hom) = disc.map (e₁.hom ≫ f₁.hom) ≫ disc.map (yoneda.map _)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, w₁, Category.assoc, w₂, Category.assoc]

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTauResPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

theorem pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E') (x : Ht q E' 2 1) :
    ∀ k : ℕ, pull _ f (tw q k) (2 * k) (cpow q x k) = cpow q (pull _ f (tw q 1) 2 x) k
  | 0 => by
    rw [cpow_zero, cpow_zero, pull_cast, (h q).2.1 f hI]
  | k + 1 => by
    rw [cpow_succ, cpow_succ, pull_cast, (h q).1, pull_cpow h q f hI x k]

theorem hyp_pull (h : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR (d + 1) 0 R)) :
    pull _ (pr d R).hom (tw q 1) 2 (hyp q (d + 1) 0 R) = hyp q (d + 1) 1 R := by
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q 1) 2
    (c1 q (prod.fst ≫ Pj.line (d + 1) 0)) = c1 q (prod.fst ≫ Pj.line (d + 1) 1)
  rw [(h q).2.2.1 _ _ hI, prod.map_fst_assoc, Pj.incl_line]

theorem tauRes_unit (H : Hyp) (hG : LeafGeo) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (m : ℕ) (n i : ℤ) a :
    pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a := by
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hI := hG.2.1 q (d + 1) 0 R hq
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q i) n
    (poly q (d + 1) 0 R m n i a) = _
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, pull_cpow h6 q _ hI, ← pull_comp, prod.map_snd, Category.comp_id]
  congr 3
  exact hyp_pull h6 q d R hI

theorem LeafTau_ofU (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau := by
  have hL := tauLin
  have hF := tauFgt
  intro H q _ d R _ hq
  have hR' := tauRes_unit H hG q d R hq
  obtain ⟨δ, hδ, -, -⟩ := hBd
  have hm : Mono (pr d R).hom := hG.1 d R
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hUb := hU hPB hTl H q d R hq
  have hPB' := hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq
  have hpoly0 := poly_zero hL
  have hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0 :=
    fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩
  have hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i) := by
    intro N i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨u, rfl⟩ := ((hδ q _ hm n i).2.2 σ).1 hσ
    obtain ⟨a, ha⟩ := (hUb n i).2 u
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR' d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR' d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR' d (2 * d) d a'] at e2
    have hab : a' = 0 - b := (hUb _ _).1 (by
      rw [hL, hpoly0, zero_sub, hb]
      exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))
    apply hinj
    rw [ha', hτ, hab]
  · rintro τ ⟨a, ha⟩ n i
    constructor
    · intro x y hxy
      obtain ⟨ex, hex, hex'⟩ := hT H q d R n i x a
      obtain ⟨ey, hey, hey'⟩ := hT H q d R n i y a
      have h1 := congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy
      dsimp only at h1
      have fx := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ
      have fy := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ
      rw [ha] at fx fy
      replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))
      have h2 := congrFun ((hPB' _ _).1 h1) (Fin.last d)
      rw [hex, hey] at h2
      exact cast_inj _ _ h2
    · intro σ
      obtain ⟨c, hc⟩ := (hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
      have k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n := by
        simp only [Fin.val_last]; ring
      have k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i := by
        simp only [Fin.val_last]; ring
      refine ⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩
      obtain ⟨e, he, he'⟩ := hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a
      have hlast : (e - c) (Fin.last d) = 0 := by
        rw [Pi.sub_apply, he, cast_cast, sub_self]
      have hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc) := by
        unfold poly
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]
        rfl
      have hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _
            (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by
        have hfx := hF h6 q (pr d R) n (2 * d) i d
          (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ
        rw [ha] at hfx
        rw [hL, map_sub, hc]
        exact congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
          (he'.symm.trans hfx.symm)
      have hg : (fun j : Fin d => (e - c) j.castSucc) = 0 := (hUb _ _).1 (by
        rw [hpoly0, ← hR', ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTauTopPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tt_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'')
    (h4 : i' = i'') (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = Ht.cast (h1.trans h3) (h2.trans h4) a := by
  subst h1; subst h2; subst h3; subst h4; rfl

theorem tt_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f _ _ (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f _ _ a) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_right {q : ℕ} {E : Spc} {n i m j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (b : Ht q E m j) : cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_left {q : ℕ} {E : Spc} {n i m j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i)
    (b : Ht q E m j) : cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tauTop : LeafTauTop := by
  intro H q _ d R _ n i x a
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hr : DivisorRingCompatibility := H.2.2.2.2.2.1
  let e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)) :=
    Fin.lastCases (motive := fun j : Fin (d + 1) =>
        Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)))
      (x.cast (by simp) (by simp))
      (fun j => (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring))
  refine ⟨e, by simp [e], ?_⟩
  have he : ∀ j : Fin d, e j.castSucc = (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring)
      (by simp only [Fin.val_castSucc]; ring) := fun j => by simp [e]
  have hl : e (Fin.last d) = x.cast (by simp) (by simp) := by simp [e]
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, Fin.sum_univ_castSucc]
  refine (add_comm _ _).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, tt_pull_cast, tt_cup_cast_left, (h6 q).1, (hr q _).2.1, tt_cup_cast_right]
    repeat rw [tt_cast_cast]
    rfl
  · rw [hl, tt_pull_cast, tt_cup_cast_left]
    repeat rw [tt_cast_cast]
    rfl

theorem LeafTauTop_of : LeafTauTop := tauTop

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafUnivSumPf
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem ev_pb {P Q R : PSh} (f : P ⟶ R) (g : Q ⟶ R) (U : AlgebraicGeometry.Scheme.{0}ᵒᵖ) :
    IsPullback ((pullback.fst f g).app U) ((pullback.snd f g).app U) (f.app U) (g.app U) :=
  (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj U)

theorem ev_cofan {A : Type} {X : A → PSh} (c : Cofan X) (hc : IsColimit c) (U : AlgebraicGeometry.Scheme.{0}ᵒᵖ) :
    Nonempty (IsColimit (Cofan.mk (c.pt.obj U) fun a => (c.inj a).app U)) :=
  ⟨(isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) X c.inj).1
    (isColimitOfPreserves ((evaluation _ _).obj U) hc)⟩

theorem leafUnivSum : LeafUnivSum := by
  intro A X c ⟨hc⟩ Y G f g
  let ι : ∀ a, pullback (c.inj a ≫ f) g ⟶ pullback f g := fun a =>
    pullback.map (c.inj a ≫ f) g f g (c.inj a) (𝟙 G) (𝟙 Y) (by simp) (by simp)
  have h1 : ∀ a, ι a ≫ pullback.fst f g = pullback.fst _ _ ≫ c.inj a := fun a => by simp only [ι, pullback.map, pullback.lift_fst]
  have h2 : ∀ a, ι a ≫ pullback.snd f g = pullback.snd _ _ := fun a => by simp only [ι, pullback.map, pullback.lift_snd, Category.comp_id]
  change Nonempty (IsColimit (Cofan.mk (pullback f g) ι))
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ ι).2 ?_
  dsimp only [evaluation_obj_obj, evaluation_obj_map]
  have hcU := ev_cofan c hc U
  have f1 : ∀ a z, (pullback.fst f g).app U ((ι a).app U z) =
      (c.inj a).app U ((pullback.fst (c.inj a ≫ f) g).app U z) := fun a z =>
    show ((ι a ≫ pullback.fst f g).app U) z = ((pullback.fst _ _ ≫ c.inj a).app U) z by rw [h1 a]
  have f2 : ∀ a z, (pullback.snd f g).app U ((ι a).app U z) =
      (pullback.snd (c.inj a ≫ f) g).app U z := fun a z =>
    show ((ι a ≫ pullback.snd f g).app U) z = ((pullback.snd (c.inj a ≫ f) g).app U) z by rw [h2 a]
  refine Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma
    (Cofan.mk ((pullback f g).obj U) fun j => (ι j).app U)).2 ⟨?_, ?_⟩)
  · rintro ⟨a, z⟩ ⟨b, w⟩ e
    change (ι a).app U z = (ι b).app U w at e
    have e1 := congr_arg ((pullback.fst f g).app U) e
    rw [f1, f1] at e1
    obtain ⟨rfl, hw⟩ := (Cofan.inj_apply_eq_iff_of_isColimit hcU.some _ _).1 e1
    rw [cast_eq] at hw
    have e2 := congr_arg ((pullback.snd f g).app U) e
    rw [f2, f2] at e2
    rw [Types.ext_of_isPullback (ev_pb (c.inj a ≫ f) g U) hw.symm e2]
  · intro p
    obtain ⟨a, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hcU.some ((pullback.fst f g).app U p)
    change (c.inj a).app U y = _ at hy
    obtain ⟨z, hz1, hz2⟩ := Types.exists_of_isPullback (ev_pb (c.inj a ≫ f) g U) y
      ((pullback.snd f g).app U p) (by
        have : ((pullback.fst f g ≫ f).app U) p = ((pullback.snd f g ≫ g).app U) p := by rw [pullback.condition]
        change f.app U ((c.inj a).app U y) = _
        rw [hy]; exact this)
    refine ⟨⟨a, z⟩, ?_⟩
    change (ι a).app U z = p
    refine Types.ext_of_isPullback (ev_pb f g U) ?_ ?_
    · rw [f1, hz1, hy]
    · rw [f2, hz2]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

