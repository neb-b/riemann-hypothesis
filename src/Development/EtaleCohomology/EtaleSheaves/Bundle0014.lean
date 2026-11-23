module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafKumCut

def LeafTwist : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nonempty (Prim q B) →
  ∀ n i j : ℤ, Nonempty (Ht q (sp B) n i ≃+ Ht q (sp B) n j)

def EtaleFirstCohomologyMultiplicativeGroupPicard : Prop := Hyps → DivisorPicardCompatibility

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ (a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1)
    (b : Ht q (sp B) 1 1 →+ H ℤ (sp B) Gm 1), Function.Exact a b

theorem prim_of_isAlgClosed (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k)) :
    Nonempty (Prim q k) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)))
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem finite_of_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup N] [Finite A]
    (a : A →+ M) (b : M →+ N) (h : Function.Exact a b) (hb : Finite b.range) : Finite M := by
  have hK : Finite b.ker := by
    have : (b.ker : Set M) = Set.range a := by ext x; exact h x
    have hf : (Set.range a).Finite := Set.finite_range a
    rw [← this] at hf
    exact hf.to_subtype
  have hQ : Finite (M ⧸ b.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange b).symm.toEquiv
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup b.ker
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  have : Nonempty (M ⧸ b.ker) := ⟨0⟩
  exact Nat.mul_ne_zero (Nat.card_pos).ne' (Nat.card_pos).ne'

theorem goal_of (hT : LeafTwist) (hG : EtaleFirstCohomologyMultiplicativeGroupPicard) (hS : LeafKumSeq) : LeafKum := by
  intro hy q _ k B _ _ _ _ hq hU hP i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨ζ⟩ := prim_of_isAlgClosed q k hq
  obtain ⟨e⟩ := hT hy q B ⟨ζ.map (algebraMap k B)⟩ 1 i 1
  obtain ⟨a, b, hab⟩ := hS hy q B hqB
  obtain ⟨E⟩ := hG hy B
  have hr : Finite b.range := by
    refine Finite.of_injective (β := {c : CommRing.Pic B // c ^ q = 1})
      (fun y => ⟨Additive.toMul (E y.1), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      have h0 : q • x = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]
      have : q • E y.1 = 0 := by rw [← hx, ← map_nsmul, ← map_nsmul, h0, map_zero, map_zero]
      rw [← toMul_nsmul, this, toMul_zero]
    · intro y z h
      apply Subtype.ext
      apply E.injective
      apply Additive.toMul.injective
      exact congrArg Subtype.val h
  have : Finite (Ht q (sp B) 1 1) := finite_of_exact a b hab hr
  exact Finite.of_equiv _ e.symm.toEquiv

end LateralTheory.E.LeafKumCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLinePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafLinePf

theorem det_mulVec_one (A : Type) [CommRing A] (g : GL (Fin 1) A) :
    (g : Matrix (Fin 1) (Fin 1) A).mulVec (fun _ => 1) = ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) • (fun _ => (1 : A)) := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, Matrix.det_unique]

def e1 (A : Type) [CommRing A] : Um 1 A := ⟨fun _ => 1, by
  rw [Set.range_const]; exact Ideal.span_singleton_one⟩

def secF (A : Type) [CommRing A] : SingleObj (GL (Fin 1) A) ⥤ Um 1 A where
  obj _ := e1 A
  map g := ⟨(g, Matrix.GeneralLinearGroup.det g), det_mulVec_one A g⟩
  map_id _ := Subtype.ext (Prod.ext rfl (map_one _))
  map_comp f g := Subtype.ext (Prod.ext rfl (map_mul _ _ _))

theorem eqToHom_val {A : Type} [CommRing A] {v w : Um 1 A} (h : v = w) : (eqToHom h).1 = 1 := by
  cases h; rfl

theorem comp_val {A : Type} [CommRing A] {u v w : Um 1 A} (a : u ⟶ v) (b : v ⟶ w) : (a ≫ b).1 = b.1 * a.1 := rfl

theorem det_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 1) A) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g) : Bˣ) : B) = f ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.map_det]
  rfl

def secNat : glCat 1 ⟶ pglCat 1 where
  app A := (secF A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => Subtype.ext (funext fun _ => (map_one f.hom).symm)) (fun _ _ g => ?_)
    apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val, one_mul, mul_one]
    refine Prod.ext rfl ?_
    ext
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom (show GL (Fin 1) A from g)) : (B : Type)ˣ) : (B : Type)) =
      f.hom ((Matrix.GeneralLinearGroup.det (show GL (Fin 1) A from g) : (A : Type)ˣ) : (A : Type))
    exact det_map f.hom _

theorem ofCatMap_comp {C D F : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) (β : D ⟶ F) :
    ofCatMap α ≫ ofCatMap β = ofCatMap (α ≫ β) := rfl

theorem ofCatMap_id (C : CommRingCat.{0} ⥤ Cat.{0,0}) : ofCatMap (𝟙 C) = 𝟙 _ := rfl

def sec : ofCat (glCat 1) ⟶ PGL 1 := ofCatMap secNat

theorem sec_pr : sec ≫ PGL.pr 1 = 𝟙 (ofCat (glCat 1)) := rfl

theorem single_eqToHom {M : Type} [Monoid M] {x y : SingleObj M} (h : x = y) : (eqToHom h : x ⟶ y) = (1 : M) := by
  cases h; rfl

theorem sec_line : sec ≫ PGL.line 1 = 𝟙 (ofCat (glCat 1)) := by
  rw [sec, PGL.line]
  erw [ofCatMap_comp]
  rw [← ofCatMap_id]
  congr 1
  apply NatTrans.ext
  funext A
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => ?_)
  erw [single_eqToHom]
  change _ = ((1 : GL (Fin 1) A) * (id g : GL (Fin 1) A)) * 1
  rw [one_mul, mul_one]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det (id g : GL (Fin 1) A)) = (id g : GL (Fin 1) A)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

end LateralTheory.E.LeafLinePf

namespace LateralTheory.E.D2
open LateralTheory.E.LeafLinePf

theorem LeafLine_of (hA : LeafA6nat) : LeafLine := by
  intro q _ P E h L c hc
  obtain ⟨h0, -, heq⟩ := hc
  have hw : 𝟙 E ≫ L = (L ≫ sec) ≫ PGL.pr 1 := by
    rw [Category.assoc, sec_pr, Category.id_comp, Category.comp_id]
  let σ : E ⟶ PB L := pullback.lift (𝟙 E) (L ≫ sec) hw
  have hpr : σ ≫ PB.pr L = 𝟙 E := pullback.lift_fst _ _ _
  have hline : σ ≫ PB.line L = L := by
    rw [PB.line, ← Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.assoc, sec_line, Category.comp_id]
  have h' : Inv q (PB L) := inv_of (PB.pr L) h
  have hm : ∀ j, P.map σ h h' (P.map (PB.pr L) h' h (P.ι h j (c j))) = P.ι h j (c j) := by
    intro j
    rw [P.map_ι, P.map_ι, ← pull_comp, hpr, pull_id]
  have hx : P.map σ h h' (P.deg1 h' (c1 q (PB.line L))) = P.deg1 h (c1 q L) := by
    rw [Collected.deg1, P.map_ι, pull_cast, (hA q).2.2.1 σ (PB.line L) h', hline]
  have := congrArg (P.map σ h h') heq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add (f := _), map_mul, map_pow, map_zero, zero_add, hm, hx,
    map_one, h0] at this
  simp only [one_mul, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero, mul_one] at this
  linear_combination this

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem pull_cast_nat {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi; rfl

abbrev PB.over {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) : PB (f ≫ V) ⟶ PB V :=
  pullback.map (f ≫ V) (PGL.pr N) V (PGL.pr N) f (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem PB.over_pr {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.pr V = PB.pr (f ≫ V) ≫ f := by
  simp only [PB.over, PB.pr, pullback.map, pullback.lift_fst]

theorem PB.over_line {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.line V = PB.line (f ≫ V) := by
  simp only [PB.over, PB.line, pullback.map, pullback.lift_snd_assoc, Category.comp_id]

theorem LeafNat_of (hA : LeafA6nat) : LeafNat := by
  intro q _ P E E' f h h' N V c hc
  obtain ⟨h0, hz, hs⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [← P.map_ι f h h', h0, map_one]
  · intro j hj; simp [hz j hj]
  · have hg := congrArg (P.map (PB.over f V) (inv_of (PB.pr (f ≫ V)) h) (inv_of (PB.pr V) h')) hs
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at hg
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, P.map_ι, Collected.deg1, pull_cast_nat, ← pull_comp, PB.over_pr]
    rw [(hA q).2.2.1 _ _ (inv_of (PB.pr V) h'), PB.over_line]

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNewtonPf
section
noncomputable section
open PowerSeries

namespace LateralTheory.E.LeafNewtonPf

def nser {A : Type 1} [CommRing A] (c : ℕ → A) : PowerSeries A :=
  -(X * PowerSeries.derivative (mk c)) * (mk c).invOfUnit 1

lemma uniq {A : Type 1} [CommRing A] {f g s : PowerSeries A} (hf : constantCoeff f = 1) (h : s * f = g) :
    g * f.invOfUnit 1 = s := by
  rw [← h, mul_assoc, mul_invOfUnit f 1 (by simp [hf]), mul_one]

lemma nser_eq {A : Type 1} [CommRing A] (c : ℕ → A) {s : PowerSeries A} (h0 : constantCoeff (mk c) = 1)
    (h : s * mk c = -(X * PowerSeries.derivative (mk c))) : nser c = s := uniq h0 h

lemma nser_spec {A : Type 1} [CommRing A] (c : ℕ → A) (h0 : c 0 = 1) :
    nser c * mk c = -(X * PowerSeries.derivative (mk c)) := by
  unfold nser
  rw [mul_assoc, invOfUnit_mul (mk c) 1 (by simp [h0]), mul_one]

lemma map_deriv {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (f : PowerSeries A) :
    map φ (PowerSeries.derivative f) = PowerSeries.derivative (map φ f) := by
  ext n
  simp [coeff_derivative, coeff_map, map_mul, map_natCast]

lemma part1 {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A) (h0 : c 0 = 1) (k : ℕ) :
    φ (LateralTheory.E.D2.newton c k) = LateralTheory.E.D2.newton (fun j => φ (c j)) k := by
  have hm : map φ (mk c) = mk (fun j => φ (c j)) := by ext n; simp [coeff_map]
  have key : nser (fun j => φ (c j)) = map φ (nser c) := by
    apply nser_eq _ (by simp [h0])
    have := congrArg (map φ) (nser_spec c h0)
    rw [map_mul, hm, map_neg, map_mul, map_X, map_deriv, hm] at this
    exact this
  show φ (coeff k (nser c)) = coeff k (nser (fun j => φ (c j)))
  rw [key, coeff_map]

lemma part2 {A : Type 1} [CommRing A] (c d e : ℕ → A) (hc : c 0 = 1) (hd : d 0 = 1)
    (he : ∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) (k : ℕ) :
    LateralTheory.E.D2.newton e k = LateralTheory.E.D2.newton c k + LateralTheory.E.D2.newton d k := by
  have hm : mk e = mk c * mk d := by ext n; rw [coeff_mk, he, coeff_mul]; simp [coeff_mk]
  have he0 : e 0 = 1 := by rw [he]; simp [hc, hd]
  have key : nser e = nser c + nser d := by
    apply nser_eq _ (by simp [he0])
    rw [hm, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := nser_spec c hc
    have h2 := nser_spec d hd
    linear_combination (mk d) * h1 + (mk c) * h2
  show coeff k (nser e) = coeff k (nser c) + coeff k (nser d)
  rw [key, map_add (f := _)]

lemma geom {A : Type 1} [CommRing A] (x : A) : mk (fun k => x ^ k) * (1 - C x * X) = 1 := by
  ext n
  rcases n with _ | n
  · simp [mul_sub]
  · rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C x), coeff_succ_mul_X, coeff_C_mul]
    simp [pow_succ, mul_comm]

lemma part3 {A : Type 1} [CommRing A] (c : ℕ → A) (x : A) (h0 : c 0 = 1) (h1 : c 1 = -x)
    (h2 : ∀ j, 1 < j → c j = 0) (k : ℕ) (hk : 0 < k) : LateralTheory.E.D2.newton c k = x ^ k := by
  have hm : mk c = 1 - C x * X := by
    ext n
    rcases n with _ | _ | n
    · simp [h0]
    · simp [h1]
    · rw [coeff_mk, h2 _ (by omega)]
      simp [coeff_one]
  have key : nser c = C x * X * mk (fun k => x ^ k) := by
    apply nser_eq _ (by simp [h0])
    rw [mul_assoc, hm, geom, mul_one]
    simp [map_sub, mul_comm]
  show coeff k (nser c) = x ^ k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [key, mul_comm (C x) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_mk, pow_succ, mul_comm]

theorem LeafNewton_of : LateralTheory.E.D2.LeafNewton :=
  ⟨fun _ _ _ _ φ c h0 k => part1 φ c h0 k,
   fun _ _ c d e hc hd he k => part2 c d e hc hd he k,
   fun _ _ c x h0 h1 h2 k hk => part3 c x h0 h1 h2 k hk⟩

end LateralTheory.E.LeafNewtonPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOneLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneLocPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have h2 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} (P.map g.op x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg _ h2)

theorem ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (Sx.res g x) := by
  unfold ev
  have hn := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hn
  change _ = _ at hn
  rw [Sx.res, ← freeGen_res]
  exact hn.symm

def LeafPrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

theorem LeafOneLoc_of (hprim : LeafPrimLoc) : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := by
  intro q _ E hE α hα U x
  obtain ⟨S, hS, hP⟩ := hprim q U (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  exact ⟨ζ, (ev_res α.1 0 0 (by simp) g x).trans (hα V (Sx.res g x) ζ)⟩

end LateralTheory.E.LeafOneLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPicCut
section
noncomputable section
open nonZeroDivisors

namespace LateralTheory.E.LeafPicCut

def sel (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (FractionRing B)ˣ :=
  (powMonoidHom q : (FractionalIdeal B⁰ (FractionRing B))ˣ →* _).range.comap (toPrincipalIdeal B (FractionRing B))

abbrev selPow (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (sel B q) :=
  (powMonoidHom q : (FractionRing B)ˣ →* (FractionRing B)ˣ).range.subgroupOf (sel B q)

abbrev selQ (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Type := sel B q ⧸ selPow B q

def LeafSelPic : Prop := ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (q : ℕ) [NeZero q],
  Finite (selQ B q) → Finite {c : ClassGroup B // c ^ q = 1}

end LateralTheory.E.LeafPicCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafPrimCoverPf

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = 1 := by
  obtain ⟨h, hh⟩ : cyclotomic q A ∣ X ^ q - 1 := cyclotomic.dvd_X_pow_sub_one q A
  have hd := congrArg derivative hh
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd
  obtain ⟨u, hu⟩ := hq.exists_left_inv
  refine ⟨C u * (h * X), C u * (derivative h * X - C (q : A) * h), ?_⟩
  have hq0 : 0 < q := Nat.pos_of_neZero q
  have e1 : (X : A[X]) ^ q = X ^ (q - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel hq0]
  have hc : (C (q : A) : A[X]) = (q : A[X]) := map_natCast C q
  have hcu : C u * C (q : A) = 1 := by rw [← C_mul, hu, C_1]
  rw [e1] at hh
  linear_combination (-(C u * X)) * hd + (C u * C (q:A)) * hh + hcu

def cycPair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := by
    obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq
    exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem etale_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  let P := cycPair A q hq
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := by
    rw [show P.g = 1 from rfl, map_one]; exact isUnit_one
  let e2 : AdjoinRoot P.f ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.mk P.f P.g) hu).restrictScalars A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

theorem ff_adjoin (A : Type) [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Module.FaithfullyFlat A (AdjoinRoot (cyclotomic q A)) := by
  let b := AdjoinRoot.powerBasisAux' (cyclotomic.monic q A)
  have hpos : 0 < (cyclotomic q A).natDegree := by
    rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_neZero q)
  have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hpos⟩⟩
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

theorem prim_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Nonempty (Prim q (AdjoinRoot (cyclotomic q A))) := by
  refine ⟨⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), ?_⟩⟩
  have h0 : aeval (AdjoinRoot.root (cyclotomic q A)) (cyclotomic q A) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← aeval_map_algebraMap A, map_cyclotomic]
  exact h0

theorem spec_surj (A B : CommRingCat.{0}) (φ : A ⟶ B) (hA : Subsingleton A) : Surjective (Spec.map φ) := by
  constructor
  intro x
  exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

theorem leafPrimCover_pf : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := by
  intro q _ U hq
  let A : Type := Γ(U, ⊤)
  let B : Type := AdjoinRoot (cyclotomic q A)
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hEt : Etale (Spec.map φ) := by
    have := etale_adjoin A q hq
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr this)
  have hSu : Surjective (Spec.map φ) := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact spec_surj _ _ φ h
    · have := ff_adjoin A q
      exact ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2
  let f := pullback.fst U.toSpecΓ (Spec.map φ)
  refine ⟨Sieve.generate (Presieve.singleton f), ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    exact (Scheme.singleton_mem_precoverage_iff (P := @Etale) f).2 ⟨Surjective.surj, inferInstance⟩
  · rintro V g ⟨W, h, k, hk, rfl⟩
    cases hk
    obtain ⟨ζ⟩ := prim_adjoin A q hq
    exact ⟨Prim.map (h.appTop.hom.comp ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) ζ⟩

theorem LeafPrimCover_of : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := leafPrimCover_pf

end LateralTheory.E.LeafPrimCoverPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHSectionPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHSectionPf

def SHAlgSec : Prop := ∀ (A R : CommRingCat.{0}) (f : A ⟶ R), SH A → f.hom.Etale →
  (∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal) → ∃ σ : R ⟶ A, f ≫ σ = 𝟙 A

def EtAffNbhd : Prop := ∀ (A : CommRingCat.{0}) [Nontrivial A] {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ (R : CommRingCat.{0}) (f : A ⟶ R) (ι : Spec R ⟶ V), f.hom.Etale ∧ ι ≫ g = Spec.map f ∧
    ∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal

theorem SHSection_of (h1 : SHAlgSec) (h2 : EtAffNbhd) : LateralTheory.E.t_E3Cut.SHSection := by
  intro A hA V g _ _
  have : Nontrivial A := by obtain ⟨hH, -⟩ := hA; infer_instance
  obtain ⟨R, f, ι, hf, hι, hQ⟩ := h2 A g
  obtain ⟨σ, hσ⟩ := h1 A R f hA hf hQ
  refine ⟨Spec.map σ ≫ ι, ?_⟩
  rw [Category.assoc, hι, ← Spec.map_comp, hσ, Spec.map_id]

end LateralTheory.E.SHSectionPf
end
end

