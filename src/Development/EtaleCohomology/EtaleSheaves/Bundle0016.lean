module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.LineHigh

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem resGen_res' {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  have h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) :
        (twF q i).obj Γ(U, ⊤)))
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold resGen
  rw [← h1]
  exact congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm

def UnitPairLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → ν.mul U 0 t t (zero_add t) a b = b

theorem sec_eq_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  have hsh := (F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor
  let fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  let fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have hxy : fx = fy := by
    refine hsh.ext (fun V g hg => ?_)
    change fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)
    simpa [fx, fy] using hP V g hg
  have := congrArg (fun f => f.hom 1) hxy
  simpa [fx, fy] using this

def LeafUnitPairG : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U),
    ν.mul U 0 t t (zero_add t) (resGen 0 ζ) b = b

theorem unitPairLoc_of (h : LeafUnitPairG) : UnitPairLoc := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  refine ⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩
  obtain ⟨S, hS, hP⟩ := ha
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ, hζ⟩ := hP V g hg
  rw [ν.nat g 0 t t (zero_add t) a b, hζ, hν]

theorem leafUnitPair_of_loc (h : UnitPairLoc) : LeafUnitPair := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  have key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)),
      ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b) := by
    rintro k rfl
    exact ⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩
  obtain ⟨μ, hμ⟩ := key (0 + i) (zero_add i).symm
  have gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b,
      HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b) := by
    intro U t w w' h1 h2 e a b
    subst e
    rfl
  have hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ) := by
    rintro k rfl U ζ
    rfl
  refine ⟨μ, ?_, ?_⟩
  · intro U ζ
    have hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ') :=
      ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩
    exact eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))
  · intro U t w hw a b ha
    exact (hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))

theorem LeafUnitPair_of (h : LeafUnitPairG) : LeafUnitPair := leafUnitPair_of_loc (unitPairLoc_of h)

end LateralTheory.E.LeafUnitPairPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfA
section
namespace LateralTheory.E.E4

def LeafUnitsFG : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Group.FG (Bˣ ⧸ (Units.map (algebraMap k B).toMonoidHom).range)

theorem units_range_le_pow (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] :
    (Units.map (algebraMap k B).toMonoidHom).range ≤ (powMonoidHom q : Bˣ →* Bˣ).range := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne q)] at hz
    exact a.ne_zero hz.symm
  refine ⟨Units.map (algebraMap k B).toMonoidHom (Units.mk0 z hz0), ?_⟩
  ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
  rw [← map_pow, hz]

theorem LeafUnits_of (hFG : LeafUnitsFG) : LeafUnits := by
  intro q _ k B _ _ _ _ _ _
  have hle := units_range_le_pow q k B
  let N := (powMonoidHom q : Bˣ →* Bˣ).range
  let M := (Units.map (algebraMap k B).toMonoidHom).range
  have : Group.FG (Bˣ ⧸ M) := hFG k B
  let φ : Bˣ ⧸ M →* Bˣ ⧸ N := QuotientGroup.map M N (MonoidHom.id _) hle
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk u, rfl⟩
  have : Group.FG (Bˣ ⧸ N) := Group.fg_of_surjective hφ
  apply CommGroup.finite_of_fg_isMulTorsion
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨q, Nat.pos_of_ne_zero (NeZero.ne q), ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafWhitneyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.WhitneyPf

theorem alg {A : Type*} [CommRing A] (C D : ℕ → A) (x : A) (a b : ℕ) (hC : ∀ i, a < i → C i = 0)
    (hD : ∀ j, b < j → D j = 0) :
    ∑ k ∈ Finset.range (a + b + 1), (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      (∑ i ∈ Finset.range (a + 1), C i * x ^ (a - i)) * (∑ j ∈ Finset.range (b + 1), D j * x ^ (b - j)) := by
  set f : ℕ → ℕ → A := fun i j => C i * D j * x ^ (a + b - (i + j)) with hf
  have h1 : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      ∑ i ∈ Finset.range (k + 1), f i (k - i) := by
    intro k
    rw [Finset.sum_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ f k]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hf, hp]
  simp_rw [h1]
  rw [Finset.sum_range_diag_flip (a + b + 1) f, Finset.sum_mul_sum]
  have h2 : ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i * x ^ (a - i) * (D j * x ^ (b - j)) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hi hj
    simp only [hf]
    rw [show a + b - (i + j) = (a - i) + (b - j) by omega, pow_add]; ring
  rw [h2]
  symm
  calc ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_subset ?_ ?_
        · simp only [Finset.mem_range] at hi
          intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j _ hnj
          simp only [Finset.mem_range] at hnj
          simp only [hf]; rw [hD j (by omega)]; ring
    _ = ∑ i ∈ Finset.range (a + b + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_subset ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i _ hni
          simp only [Finset.mem_range] at hni
          refine Finset.sum_eq_zero fun j _ => ?_
          simp only [hf]; rw [hC i (by omega)]; ring

variable {q : ℕ}

def ccup {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j) (hk : i + j = k) : Ht q E (2 * k) k :=
  (cup q a b).cast (by subst hk; push_cast; ring) (by subst hk; push_cast; ring)

theorem ι_ccup (P : Collected q) {E : Spc} (h : Inv q E) {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j)
    (hk : i + j = k) : P.ι h k (ccup a b hk) = P.ι h i a * P.ι h j b := by
  subst hk; exact P.ι_mul h i j a b

theorem cast_zero {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem pull_cast {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem ccup_zero_left {E : Spc} {i j k : ℕ} (b : Ht q E (2 * j) j) (hk : i + j = k) :
    ccup (0 : Ht q E (2 * i) i) b hk = 0 := by
  unfold ccup; rw [map_zero, AddMonoidHom.zero_apply, cast_zero]

theorem ccup_zero_right {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (hk : i + j = k) :
    ccup a (0 : Ht q E (2 * j) j) hk = 0 := by
  unfold ccup; rw [map_zero, cast_zero]

section
variable [NeZero q]

theorem pull_ccup (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') {i j k : ℕ} (a : Ht q E' (2 * i) i)
    (b : Ht q E' (2 * j) j) (hk : i + j = k) : pull _ f _ _ (ccup a b hk) = ccup (pull _ f _ _ a) (pull _ f _ _ b) hk := by
  subst hk; unfold ccup; rw [pull_cast, (hA q).1]

theorem pull_cpow (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hA q).1, ih]

def yExpr {E E' : Spc} (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    Ht q E' (2 * a) a :=
  ∑ j : Fin (a + 1), ccup (pull _ g _ _ (c j)) (cpow q (c1 q L) (a - j)) (by have := j.isLt; omega)

theorem ι_yExpr (P : Collected q) {E E' : Spc} (hE : Inv q E) (hE' : Inv q E') (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    P.ι hE' a (yExpr g L c a) = ∑ j ∈ Finset.range (a + 1), P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j) := by
  unfold yExpr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun j => P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ι_ccup, P.map_ι, P.ι_cpow]

theorem pull_yExpr (hA : DivisorNaturality) {E E' E'' : Spc} (f : E'' ⟶ E') (hE' : Inv q E') (g : E' ⟶ E)
    (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    pull _ f _ _ (yExpr g L c a) = yExpr (f ≫ g) (f ≫ L) c a := by
  unfold yExpr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_ccup hA, pull_cpow hA f hE', (hA q).2.2.1 f L hE', pull_comp]

theorem yExpr_eq_zero (P : Collected q) {E : Spc} (h : Inv q E) {a : ℕ} (V : E ⟶ ofCat (glCat a))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (hc : IsChern P h V c) : yExpr (PB.pr V) (PB.line V) c a = 0 := by
  have := ι_yExpr P h (inv_of (PB.pr V) h) (PB.pr V) (PB.line V) c a
  rw [hc.2.2] at this
  rw [← P.π_ι (inv_of (PB.pr V) h) a (yExpr (PB.pr V) (PB.line V) c a), this, map_zero]

end

def eExpr {E : Spc} (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) : Ht q E (2 * k) k :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).attach,
    ccup (c p.1.1) (d p.1.2) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)

theorem ι_eExpr (P : Collected q) {E : Spc} (h : Inv q E) (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) :
    P.ι h k (eExpr c d k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2) := by
  unfold eExpr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k)
    (fun p => P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2))]
  exact Finset.sum_congr rfl fun p _ => ι_ccup P h _ _ _

end LateralTheory.E.D2.WhitneyPf

namespace LateralTheory.E.D2
open WhitneyPf

theorem LeafWhitney_of (hG : LeafGeom) (hC2 : LeafCover2) (hS : LeafA6supp) (hA : LeafA6nat) : LeafWhitney := by
  intro q _ P E h a b V W c d hc hd
  classical
  have he := ι_eExpr P h c d
  refine ⟨eExpr c d, ⟨?_, ?_, ?_⟩, he⟩
  · rw [he]; simp [hc.1, hd.1]
  · intro j hj
    unfold eExpr
    refine Finset.sum_eq_zero fun p _ => ?_
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    by_cases ha : a < p.1.1
    · rw [hc.2.1 _ ha, ccup_zero_left]
    · rw [hd.2.1 _ (by omega), ccup_zero_right]
  · have hX := inv_of (PB.pr (bsumOf V W)) h
    obtain ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, lc, e1, e2, e3, e4⟩ := hG V W
    have hcov := hC2 (ZMod q) f₁ f₂ m₁ m₂ lc
    have hy : pull _ f₁ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a) = 0 := by
      rw [pull_yExpr hA f₁ hX, ← e1, ← e2, ← pull_yExpr hA p₁ (inv_of (PB.pr V) h), yExpr_eq_zero P h V c hc,
        map_zero]
    have hz : pull _ f₂ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) = 0 := by
      rw [pull_yExpr hA f₂ hX, ← e3, ← e4, ← pull_yExpr hA p₂ (inv_of (PB.pr W) h), yExpr_eq_zero P h W d hd,
        map_zero]
    have h0 := hS q f₁ f₂ hcov _ _ hy hz
    have key : P.ι hX (a + b) (ccup (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a)
        (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) rfl) = 0 := by
      unfold ccup; rw [h0, cast_zero, map_zero]
    rw [ι_ccup, ι_yExpr P h hX, ι_yExpr P h hX,
      ← alg (fun i => P.map (PB.pr (bsumOf V W)) hX h (P.ι h i (c i)))
        (fun j => P.map (PB.pr (bsumOf V W)) hX h (P.ι h j (d j))) _ a b
        (fun i hi => by simp only [hc.2.1 i hi, map_zero])
        (fun j hj => by simp only [hd.2.1 j hj, map_zero])] at key
    refine Eq.trans ?_ key
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    simp only [map_mul]

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LevelIdentPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LevelIdentPf

def FreeSingleHomotopyEquivDiscreteChains : Prop := ∀ (R : Type) [CommRing R], ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)),
  (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧
  ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
    (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp _ x _) = CohomologyClass.mk (zcomp _ x _)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, n.negOnePow • (Cochain.ofHomotopy h).comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (by omega) 0 (n + 1) n (by omega) (by omega) (by omega), δ_ofHomotopy]
  simp [zcomp, Cocycle.δ_eq_zero, Cochain.sub_comp, smul_smul, Int.units_mul_self]

theorem cpull_iso_bij {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, cpull_homotopy e.homotopyInvHomId, cpull_id]
  · rw [← cpull_comp, cpull_homotopy e.homotopyHomInvId, cpull_id]

theorem sq_iff {A B C D : Type*} {a : B → D} {b : A → B} {c : C → D} {d : A → C}
    (w : ∀ x, a (b x) = c (d x)) (ha : Function.Bijective a) (hd : Function.Bijective d) :
    (Function.Bijective b ↔ Function.Bijective c) ∧ (Function.Injective b ↔ Function.Injective c) := by
  have w' : a ∘ b = c ∘ d := funext w
  obtain ⟨d', hd1, hd2⟩ := Function.bijective_iff_has_inverse.1 hd
  have hc : c = a ∘ b ∘ d' := by
    funext y; simp only [Function.comp_apply, w, hd2 y]
  have hd'b : Function.Bijective d' := Function.bijective_iff_has_inverse.2 ⟨d, hd2, hd1⟩
  refine ⟨⟨fun hb => hc ▸ ha.comp (hb.comp hd'b), fun hc' => ?_⟩, ⟨fun hb => hc ▸ ha.1.comp (hb.comp hd'b.1), fun hc' => ?_⟩⟩
  · have : a ∘ b = c ∘ d := w'
    have hab : Function.Bijective (a ∘ b) := this ▸ hc'.comp hd
    obtain ⟨a', ha1, ha2⟩ := Function.bijective_iff_has_inverse.1 ha
    have : b = a' ∘ (a ∘ b) := by funext x; simp [ha1 (b x)]
    rw [this]; exact (Function.bijective_iff_has_inverse.2 ⟨a, ha2, ha1⟩).comp hab
  · intro x y hxy
    apply hd.1; apply hc'
    rw [← w, ← w, hxy]

theorem chains_f {E E' : Spc} (f : E ⟶ E') (n : ℕ) : ((chains R).map f).f (-(n : ℤ)) =
    (chainsXIso R E n).hom ≫ (free R).map (f.app (op (SimplexCategory.mk n))) ≫ (chainsXIso R E' n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem cpull_isoHom_bij {K L : Cx R} (i : K ≅ L) (I : Cx R) (n : ℤ) : Function.Bijective (cpull i.hom I n) :=
  cpull_iso_bij (HomotopyEquiv.ofIso i) I n

theorem pull_eq {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R f F n x = cpull ((chains R).map f) (res R F) n x := rfl

theorem LevelIdent_of (hS : FreeSingleHomotopyEquivDiscreteChains) : LateralTheory.E.DescStepPf.LevelIdent := by
  intro R _ F E E' f p j
  obtain ⟨e, -, he⟩ := hS R
  let S := CochainComplex.singleFunctor (Shv R) 0
  let g := f.app (op (SimplexCategory.mk p))
  have sq1 : S.map (((chains R).map f).f (-(p : ℤ))) ≫ S.map (chainsXIso R E' p).hom =
      S.map (chainsXIso R E p).hom ≫ S.map ((free R).map g) := by
    rw [← S.map_comp, ← S.map_comp, chains_f]; simp [g]
  have w1 : ∀ x, cpull (S.map (chainsXIso R E p).hom) (res R F) j (cpull (S.map ((free R).map g)) (res R F) j x) =
      cpull (S.map (((chains R).map f).f (-(p : ℤ)))) (res R F) j (cpull (S.map (chainsXIso R E' p).hom) (res R F) j x) := by
    intro x; rw [← cpull_comp, ← cpull_comp, sq1]
  have w2 : ∀ x, cpull (e (E.obj (op (SimplexCategory.mk p)))).hom (res R F) j (pull R (disc.map g) F j x) =
      cpull (S.map ((free R).map g)) (res R F) j (cpull (e (E'.obj (op (SimplexCategory.mk p)))).hom (res R F) j x) := by
    intro x; rw [pull_eq, ← cpull_comp, ← cpull_comp, he g]
  obtain ⟨b1, i1⟩ := sq_iff w1 (cpull_isoHom_bij (S.mapIso (chainsXIso R E p)) _ _)
    (cpull_isoHom_bij (S.mapIso (chainsXIso R E' p)) _ _)
  obtain ⟨b2, i2⟩ := sq_iff w2 (cpull_iso_bij _ _ _) (cpull_iso_bij _ _ _)
  exact ⟨b2.trans b1, i2.trans i1⟩

end LateralTheory.E.LevelIdentPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LineHighPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LineHighPf

open LateralTheory.E.t_E2Cut

def QAIC (q : ℕ) (W : Scheme.{0}) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (I : Ideal B), AIC B ∧ IsUnit (q : B) ∧
    Nonempty (W ≅ Spec (CommRingCat.of (B ⧸ I)))

def Cover2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem acyc_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : Acyc q (sch.obj W')) : Acyc q (sch.obj W) := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have hs : ∀ z : Ht q (sch.obj W) n i,
      pull _ (sch.map e.hom) (tw q i) n (pull _ (sch.map e.inv) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← hs x, ← hs y, Subsingleton.elim (pull _ (sch.map e.inv) (tw q i) n x) (pull _ (sch.map e.inv) (tw q i) n y)]

theorem acyc_of_QAIC (H : Hyp) (hQ : QuotAcyc) {q : ℕ} {W : Scheme.{0}} (h : QAIC q W) : Acyc q (sch.obj W) := by
  obtain ⟨B, _, _, I, hB, hq, ⟨e⟩⟩ := h
  exact acyc_of_iso e (hQ H q B I hB hq)

theorem high_of_cover (H : Hyp) (hM : MV) {q : ℕ} {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
    [IsOpenImmersion g] (hc : Set.range f ∪ Set.range g = Set.univ) (hU : Acyc q (sch.obj U)) (hV : Acyc q (sch.obj V))
    (hW : Acyc q (sch.obj (pullback f g))) (i n : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨δ, hδ, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have key : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 := by
    intro x
    have h3 := ((hδ f g hc m).2.2 x).1
    have := hU (m + 1) i (by omega)
    have := hV (m + 1) i (by omega)
    have := hW m i (by omega)
    obtain ⟨w, hw⟩ := h3 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem LineHigh_of (hQ : QuotAcyc) (hM : MV) (hC : Cover2) : LineHigh := by
  intro H q i A _ _ hq Z p hp hZ n hn
  obtain ⟨U, V, f, g, hf, hg, hc, hU, hV, hW⟩ := hC q A hq p hp hZ
  exact high_of_cover H hM f g hc (acyc_of_QAIC H hQ hU) (acyc_of_QAIC H hQ hV) (acyc_of_QAIC H hQ hW) i n hn

theorem fibre_affine (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] :
    Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (cpt A) ≅
      Spec (CommRingCat.of (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))) := by
  refine ⟨pullbackSpecIso A B (IsLocalRing.ResidueField A) ≪≫ ?_⟩
  exact Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv).op

def Good {A : Type} [CommRing A] {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) : Prop :=
  IsEmpty W ∨ ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B), AIC B ∧
    ∃ e : W ≅ Spec (CommRingCat.of B), e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = w

def ZCov : Prop := ∀ (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ Z) (g : V ⟶ Z), IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    Good (f ≫ p) ∧ Good (g ≫ p) ∧ Good (pullback.fst f g ≫ f ≫ p)

def FibCov : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ {U V : Scheme.{0}} (f : U ⟶ Z) (g : V ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g],
  Set.range f ∪ Set.range g = Set.univ → Good (f ≫ p) → Good (g ≫ p) → Good (pullback.fst f g ≫ f ≫ p) →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem Cover2_of (hZ : ZCov) (hF : FibCov) : Cover2 := by
  intro q A _ _ hq Z p hp hZA
  obtain ⟨U, V, f, g, hf, hg, hc, h1, h2, h3⟩ := hZ A p hp hZA
  exact hF q A hq p hZA f g hc h1 h2 h3

end LateralTheory.E.LineHighPf
end
end

