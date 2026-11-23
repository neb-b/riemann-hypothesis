module

public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0008

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafChernPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.ChernPf

theorem cast_rfl {q : ℕ} {E : Spc} {n i : ℤ} (x : Ht q E n i) (h1 : n = n) (h2 : i = i) : x.cast h1 h2 = x := rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h1 : n = n') (h2 : i = i')
    (h3 : n' = n'') (h4 : i' = i'') : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem term {q : ℕ} (P : Collected q) {E F : Spc} (f : F ⟶ E) (h : Inv q E) (h' : Inv q F) (y : Ht q F 2 1)
    {n' i' : ℤ} (u : Ht q E n' i') (k m N : ℕ) (hN : k + m = N) (hn : n' = 2 * (k : ℤ)) (hi : i' = k)
    (h1 : n' + 2 * (m : ℤ) = 2 * (N : ℤ)) (h2 : i' + (m : ℤ) = N) :
    P.ι h' N ((cup q (pull _ f _ _ u) (cpow q y m)).cast h1 h2) =
      P.map f h' h (P.ι h k (u.cast hn hi)) * P.ι h' m (cpow q y m) := by
  subst hN hn hi
  rw [cast_rfl, P.map_ι]
  exact P.ι_mul h' k m _ _

variable {q : ℕ} {E : Spc} {N : ℕ}

def Phi (V : E ⟶ ofCat (glCat N)) (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    Ht q (PB V) (2 * (N : ℤ)) N :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ (2 * (N : ℤ)) N)

def ac (c : ∀ j : ℕ, Ht q E (2 * j) j) : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ)) :=
  fun j => (c (N - j)).cast (by have := j.isLt; omega) (by have := j.isLt; omega)

theorem phi_ι (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N))
    (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    P.ι (inv_of (PB.pr V) h) N (Phi V a) = ∑ j : Fin N, P.map (PB.pr V) (inv_of (PB.pr V) h) h
      (P.ι h (N - j) ((a j).cast (by have := j.isLt; omega) (by have := j.isLt; omega))) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (j : ℕ) := by
  unfold Phi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [term P (PB.pr V) h (inv_of (PB.pr V) h) _ (a j) (N - j) j N (by have := j.isLt; omega)
    (by have := j.isLt; omega) (by have := j.isLt; omega), P.ι_cpow]

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2.ChernPf
variable {q : ℕ} {E : Spc} {N : ℕ}

theorem cast_inj {n i n' i' : ℤ} {x y : Ht q E n i} (h1 : n = n') (h2 : i = i') (e : x.cast h1 h2 = y.cast h1 h2) : x = y := by
  subst h1 h2; exact e

theorem cast_idx {n i : Fin N → ℤ} (a : ∀ j, Ht q E (n j) (i j)) (j j' : Fin N) (e : j = j')
    (h1 : n j = n j') (h2 : i j = i j') : (a j).cast h1 h2 = a j' := by
  subst e; rfl

theorem sum_eq (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j)
    (h0 : P.ι h 0 (c 0) = 1) :
    ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) =
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ N + P.ι (inv_of (PB.pr V) h) N (Phi V (ac c)) := by
  have key : ∀ g : ℕ → P.R (PB V) (inv_of (PB.pr V) h),
      ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range N, g (N - j) + g 0 := by
    intro g
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp
  rw [key, phi_ι P h V, h0, map_one, one_mul, Nat.sub_zero, add_comm, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.sub_sub_self j.isLt.le]
  dsimp only [ac]
  rw [ChernPf.cast_cast, cast_rfl]

def mkc (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) : ∀ j : ℕ, Ht q E (2 * j) j :=
  fun j => if h0 : j = 0 then (one q E).cast (by simp [h0]) (by simp [h0])
    else if hj : j ≤ N then (a ⟨N - j, by omega⟩).cast (by simp; omega) (by simp; omega) else 0

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2
open ChernPf

theorem LeafChern_of : LeafChern := by
  intro hD1 q _ P E h N V
  have hB : Function.Bijective (Phi (q := q) V) := hD1 q V h (2 * (N : ℤ)) N
  have hι : ∀ {F : Spc} (h : Inv q F) k, Function.Injective (P.ι h k) := fun h k a b e => by
    simpa [P.π_ι] using congrArg (P.π h k) e
  have char : ∀ c, P.ι h 0 (c 0) = 1 → (IsChern P h V c ↔
      (∀ j, N < j → c j = 0) ∧ Phi V (ac c) = -cpow q (c1 q (PB.line V)) N) := by
    intro c h0
    unfold IsChern
    rw [sum_eq P h V c h0, ← P.ι_cpow, ← map_add (f := _), map_eq_zero_iff _ (hι _ _), add_eq_zero_iff_neg_eq, eq_comm]
    simp only [h0, true_and]
    exact and_congr_right fun _ => eq_comm
  have uniq : ∀ c c', IsChern P h V c → IsChern P h V c' → c = c' := by
    intro c c' hc hc'
    have hA : ac c = ac c' := hB.1 (((char c hc.1).1 hc).2.trans ((char c' hc'.1).1 hc').2.symm)
    funext j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hι h 0 (hc.1.trans hc'.1.symm)
    by_cases hjN : N < j
    · rw [hc.2.1 j hjN, hc'.2.1 j hjN]
    have := cast_inj _ _ (congrFun hA ⟨N - j, by omega⟩)
    have e : N - ((⟨N - j, by omega⟩ : Fin N) : ℕ) = j := by simp; omega
    rw [e] at this
    exact this
  obtain ⟨a, ha⟩ := hB.2 (-cpow q (c1 q (PB.line V)) N)
  have hc0 : P.ι h 0 (mkc a 0) = 1 := by
    dsimp only [mkc]
    rw [dite_eq_left rfl]
    exact P.ι_one h
  have hac : ac (mkc a) = a := by
    funext j
    dsimp only [ac, mkc]
    rw [dite_eq_right (by omega), dite_eq_left (by omega), ChernPf.cast_cast]
    exact cast_idx a _ _ (Fin.ext (by simp; omega)) _ _
  have hC : IsChern P h V (mkc a) := (char _ hc0).2 ⟨fun j hj => by
    dsimp only [mkc]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)], by rw [hac]; exact ha⟩
  exact ⟨mkc a, hC, fun c' hc' => uniq _ _ hc' hC⟩

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut

open LateralTheory.E.E4

def LeafMV : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens), U ⊔ V = ⊤ →
  ∀ n : ℤ, ∃ δ : H R (sch.obj (U ⊓ V).toScheme) F n →+ H R (sch.obj X) F (n + 1),
    ∀ x : H R (sch.obj X) F (n + 1),
      (pull R (sch.map U.ι) F (n + 1) x = 0 ∧ pull R (sch.map V.ι) F (n + 1) x = 0) ↔ x ∈ δ.range

def isoH (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (e : X ≅ Y) (n : ℤ) :
    H R (sch.obj Y) F n ≃ H R (sch.obj X) F n where
  toFun := pull R (sch.map e.hom) F n
  invFun := pull R (sch.map e.inv) F n
  left_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  right_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem finite_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Finite (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Finite (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Finite (H R (sch.obj V.toScheme) F (n + 1))) :
    Finite (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  let φ := (pull R (sch.map U.ι) F (n + 1)).prod (pull R (sch.map V.ι) F (n + 1))
  have hker : φ.ker = δ.range := by
    ext x
    rw [← hδ x, AddMonoidHom.mem_ker]
    simp [φ, Prod.ext_iff]
  have : Finite φ.ker := by
    rw [hker]
    exact Set.finite_range δ |>.to_subtype
  have : Finite (H R (sch.obj X) F (n + 1) ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_addSubgroup_quotient φ.ker

theorem subsingleton_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Subsingleton (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Subsingleton (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Subsingleton (H R (sch.obj V.toScheme) F (n + 1))) :
    Subsingleton (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj X) F (n + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hδ z).1 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  rw [hx x, hx y]

end LateralTheory.E.E4.CurveCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeoCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoCut

def FamilyV {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeoV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → FamilyV (k := k) X c0 γ1 γ2

def LeafClosed : Prop := ∀ (B : Scheme.{0}) (V : B.Opens),
  ∃ (W : Scheme.{0}) (ι : W ⟶ B), IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ

def LeafBdry : Prop := ∀ {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), IsClosedImmersion ι → IrreducibleSpace Y →
  topologicalKrullDim Y < ⊤ → (p ⁻¹' (Set.range ι)ᶜ).Nonempty →
  topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim Y

theorem goal_of (hV : LeafGeoV) (hC : LeafClosed) (hB : LeafBdry) : LateralTheory.E.E4.LeafGeo := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, hc0, hall⟩ := hV k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, f2, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨W, ι, hι, hWV⟩ := hC B V
  exact ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hι, hWV, hs, m0, m1, m2, f1, f2, dB,
    lt_of_lt_of_le (hB π ι hι irr fin (hWV ▸ ne)) dY, P0, P1, P2, w1, w2⟩

end LateralTheory.E.LeafGeoCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeomPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2

namespace LateralTheory.E.LeafGeomPf

def vec0 {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Fin (a + b) → Scheme.Γ.obj (op X) :=
  ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
    ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).1

def First {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin a => vec0 V W x (Fin.castAdd b i)) = ⊤

def Second {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin b => vec0 V W x (Fin.natAdd a i)) = ⊤

def LeafHalf1 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V), Mono f₁ ∧
    p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), First V W x → ∃ y : Sx U₁ n X, (f₁.app _).app _ y = x

def LeafHalf2 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₂ : Spc) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₂ : U₂ ⟶ PB W), Mono f₂ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), Second V W x → ∃ y : Sx U₂ n X, (f₂.app _).app _ y = x

def LeafLocal : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) (n : ℕ) (X : Scheme.{0})
  (x : Sx (PB (bsumOf V W)) n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    First V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) ∨
    Second V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) (hL : LeafLocal) : LateralTheory.E.D2.LeafGeom := by
  intro E a b V W
  obtain ⟨U₁, f₁, p₁, m₁, e₁, l₁, s₁⟩ := h1 V W
  obtain ⟨U₂, f₂, p₂, m₂, e₂, l₂, s₂⟩ := h2 V W
  refine ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, ?_, e₁, l₁, e₂, l₂⟩
  intro n X x
  obtain ⟨S, hS, hk⟩ := hL V W n X x
  refine ⟨S, hS, fun Y k hk' => ?_⟩
  rcases hk Y k hk' with h | h
  · exact Or.inl (s₁ n Y _ h)
  · exact Or.inr (s₂ n Y _ h)

end LateralTheory.E.LeafGeomPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostCut
open LateralTheory.E.E4

def rmap (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) : mappingCone ((chains R).map f') ⟶ mappingCone ((chains R).map f) :=
  mappingCone.map _ _ ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])

abbrev fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

abbrev rpull (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (F : Shv R) (n : ℤ) : Hrel R f F n →+ Hrel R f' F n :=
  HK.pull R (rmap R f f' u e comm) F n

abbrev rpl (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (n : ℤ) : Hrel (ZMod q) (sch.map f) (tw q i) n →+ Hrel (ZMod q) (sch.map f') (tw q i) n :=
  rpull (ZMod q) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (tw q i) n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x

def LeafRelNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n),
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y)

def LeafGhostRel : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (y : Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n),
    ∃ c : Hrel (ZMod q) (sch.map ι) (tw q i) n,
      rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y =
        rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p) pullback.condition n c

open CochainComplex.HomComplex in
theorem relExact : LeafRelExact := by
  intro R _ F U E f n x hx
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, β, hβ⟩ := hx
  refine ⟨CohomologyClass.mk (mappingCone.descCocycle _ (n.negOnePow • β) z hm ?_), ?_⟩
  · rw [δ_units_smul, hβ]
    simp [zcomp]
  · refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp [zcomp]

open CochainComplex.HomComplex in
theorem relNat : LeafRelNat := by
  intro R _ F U E U' E' f f' u e comm n y
  have key : mappingCone.inr ((chains R).map f') ≫ rmap R f f' u e comm =
      (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [rmap, mappingCone.map]
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, key, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

theorem goal_of_all (hEx : LeafRelExact) (hNat : LeafRelNat) (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n a ha
  obtain ⟨y, rfl⟩ := hEx (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) n a ha
  obtain ⟨c, hc⟩ := hCore hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA n y
  refine ⟨fgt (ZMod q) (sch.map ι) (tw q i) n c, ?_⟩
  have e1 := hNat (ZMod q) (tw q i) (sch.map ι) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.snd (g2 ≫ g1 ≫ p) ι)) (sch.map (g2 ≫ g1 ≫ p))
    (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]) n c
  have hsq : pullback.fst (g2 ≫ g1 ≫ p) ι ≫ (g2 ≫ g1) =
      pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm
  have e2 := hNat (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp))) (sch.map (g2 ≫ g1))
    (by rw [← Functor.map_comp, ← Functor.map_comp, hsq]) n y
  change pull _ _ _ _ _ = pull _ _ _ _ _
  rw [← e1, ← e2]
  exact congrArg _ hc.symm

theorem goal_of (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := goal_of_all relExact relNat hCore

end LateralTheory.E.LeafGhostCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafHAWBounds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafHtpyAWPf

abbrev HFam (R : Type) [CommRing R] (I J K : Cx R) : Type 1 :=
  ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U

def IsHAW {R : Type} [CommRing R] {I J K : Cx R} (h : HFam R I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (η : Cochain ((chains R).obj E) K (k - 1)) :
    Prop :=
  ∀ (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + (k - 1) = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w hw U x =
    ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))

def LeafHAWExists : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (h : HFam R I J K),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α β η

def LeafHAWBounds : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) (h : HFam R I J K),
  (∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
        h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    ∀ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α.1 β.1 η → δ (k - 1) k η = γ.1 - γ'.1

end LateralTheory.E.LeafHtpyAWPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKillCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKillCut

open LateralTheory.E.E4

def LeafOne : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → ∀ x : Ht q (sch.obj C) m i,
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m x = 0

theorem goal_of (hOne : LeafOne) : LateralTheory.E.E4.LeafKill := by
  intro hy q _ Ω _ _ hq C c hc m i hm hfin
  classical
  have key : ∀ s : Finset (Ht q (sch.obj C) m i), ∃ (C' : Scheme.{0}) (γ : C' ⟶ C),
      IsCurve (γ ≫ c) ∧ Surjective γ ∧ ∀ x ∈ s, pl q i γ m x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C, 𝟙 C, by simpa using hc, inferInstance, by simp⟩
    | insert a s ha IH =>
      obtain ⟨C1, γ1, h1, s1, k1⟩ := IH
      obtain ⟨C2, γ2, h2, s2, k2⟩ := hOne hy q Ω hq (γ1 ≫ c) h1 m i hm (pl q i γ1 m a)
      have := s1
      have := s2
      refine ⟨C2, γ2 ≫ γ1, by simpa [Category.assoc] using h2, inferInstance, ?_⟩
      intro x hx
      rw [pl_comp]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact k2
      · rw [k1 x hx, map_zero]
  have := Fintype.ofFinite (Ht q (sch.obj C) m i)
  obtain ⟨C', γ, h1, h2, h3⟩ := key Finset.univ
  exact ⟨C', γ, h1, h2, AddMonoidHom.ext fun x => by simpa using h3 x (Finset.mem_univ x)⟩

end LateralTheory.E.LeafKillCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKumSpecPf

section Basic
variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

end Basic

section Kum
variable (q : ℕ) [NeZero q]

end Kum

end LateralTheory.E.LeafKumSpecPf
end
end

