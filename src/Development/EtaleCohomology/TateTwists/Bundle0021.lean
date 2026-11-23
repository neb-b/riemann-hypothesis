module

public import Development.EtaleCohomology.TateTwists.Bundle0008
public import Development.EtaleCohomology.TateTwists.Bundle0009

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.KumExistsPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def L_kumT_ex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def L_prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def L_sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def L_sch_cls : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def L_res_sec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)

section Basic
variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  show (F.obj.map (k ≫ g).op).hom x = (F.obj.map k.op).hom ((F.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp]
  rfl

theorem sec_res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := LinearMap.map_add _ _ _

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  simp [Sec.map]

end Basic

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

theorem prim_isUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 :=
  IsUnit.of_pow_eq_one (prim_pow ζ) (NeZero.ne q)

theorem units_root {q : ℕ} {X U V : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ)
    (h : w ^ q = Units.map x.appTop.hom.toMonoidHom u) :
    (Units.map g.appTop.hom.toMonoidHom w) ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  rw [← map_pow, h]
  ext
  simp
  rfl

section Kum
variable (q : ℕ) [NeZero q]

theorem d_resGen (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (resGen 1 ζ) = 0 :=
  ((hR (ZMod q) (tw q 1) U).1 _).2 ⟨twGen 1 ζ, rfl⟩

theorem dt_pow (hK : L_kumT_ex) (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U v) := by
  induction a with
  | zero =>
    intro v w h
    have : w = v := Units.ext (by simpa using h)
    subst this; rfl
  | succ a ih =>
    intro v w h
    let m : (Γ(U, ⊤))ˣ := (prim_isUnit ζ).unit ^ a * v
    have hm : (m : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp [m]
    have hw : (w : Γ(U, ⊤)) = ζ.1 * m := by rw [h, hm, pow_succ]; ring
    rw [(hK q).2 U ζ m w hw, sec_map_add, d_resGen q hR, add_zero]
    exact ih v m hm

theorem dt_root (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hR : L_res_sec) {W : Scheme.{0}}
    (hqW : IsUnit (q : Γ(W, ⊤))) (w1 w2 : (Γ(W, ⊤))ˣ) (h : w1 ^ q = w2 ^ q) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w2) := by
  let ρ : (Γ(W, ⊤))ˣ := w2 * w1⁻¹
  have hρ : ρ ^ q = 1 := by
    simp only [ρ]; rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  apply (hG (ZMod q) _ W).1
  obtain ⟨S, hS, hPS⟩ := (hP q W).1 hqW
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hPS V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hqW.map g.appTop.hom
  have hr : (g.appTop.hom (ρ : Γ(W, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_one, map_one]
  rw [sec_res_map, sec_res_map, (hK q).1 V W g w1 hqW, (hK q).1 V W g w2 hqW]
  apply (hG (ZMod q) _ V).1
  obtain ⟨T, hT, hPT⟩ := (hP q V).2.2.1 ζ _ hr
  refine ⟨T, hT, fun V' k hk => ?_⟩
  dsimp only
  obtain ⟨a, ha⟩ := hPT V' k hk
  rw [sec_res_map, sec_res_map, (hK q).1 V' V k _ hqV, (hK q).1 V' V k _ hqV]
  symm
  apply dt_pow q hK hR (Prim.map k.appTop.hom ζ) a
  have e : (w2 : Γ(W, ⊤)) = (ρ : Γ(W, ⊤)) * w1 := by simp [ρ]
  change k.appTop.hom (g.appTop.hom (w2 : Γ(W, ⊤))) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (g.appTop.hom (w1 : Γ(W, ⊤)))
  rw [e, map_mul, map_mul, ha]

end Kum

theorem kum_exists_of (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hC : L_sch_cls) (hR : L_res_sec) :
    kum_exists := by
  intro q _ X u hq
  have hqU : ∀ {U : Scheme.{0}} (x : U ⟶ X), IsUnit (q : Γ(U, ⊤)) := fun x => by simpa using hq.map x.appTop.hom
  have key : ∀ {U : Scheme.{0}} (x : U ⟶ X) (w1 w2 : (Γ(U, ⊤))ˣ), w1 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      w2 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w2) :=
    fun x w1 w2 h1 h2 => dt_root q hK hP hG hR (hqU x) w1 w2 (h1.trans h2.symm)
  obtain ⟨S, hS, hroot⟩ := (hP q X).2.2.2 hq u
  choose v hv using hroot
  obtain ⟨z, hz⟩ := (hG (ZMod q) ((res (ZMod q) (tw q 1)).X 1) X).2 S hS
    (fun V g hg => Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V (v V g hg))) (by
      intro V W g k hg
      rw [sec_res_map, (hK q).1 W V k _ (hqU g)]
      exact key (k ≫ g) _ _ (units_root u g k _ (hv V g hg)) (hv W (k ≫ g) _))
  have hdz : Sec.map ((res (ZMod q) (tw q 1)).d 1 2) z = 0 := by
    apply (hG (ZMod q) _ X).1
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [sec_res_map, hz V g hg, sec_res_zero, ← sec_map_comp, HomologicalComplex.d_comp_d, sec_map_zero]
  obtain ⟨α, hα0, hα1⟩ := (hC (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).1 z hdz
  refine ⟨α, fun U x => hα1 0 0 _ U x, fun U x w hw => ?_⟩
  rw [hα0 U x]
  apply (hG (ZMod q) _ U).1
  refine ⟨S.pullback x, (Scheme.etaleTopology).pullback_stable x hS, fun V g hg => ?_⟩
  dsimp only
  rw [← sec_res_comp, hz V (g ≫ x) hg, sec_res_map, (hK q).1 V U g w (hqU x)]
  exact key (g ≫ x) _ _ (hv V (g ≫ x) hg) (units_root u x g w hw)

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.LeafAcycPf
section
open CategoryTheory GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.AcycPf

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun i => Fin.cases 0 (fun j => a.toOrderHom j) i, by
    intro i j h
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j => simpa using a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 h)⟩

def v0 {N : ℕ} : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

lemma δ0_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext j
  simp [SimplexCategory.δ, cone]

lemma δsucc_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.δ, cone]
  | succ j => simp [SimplexCategory.δ, cone, Fin.succ_succAbove_succ]

lemma δ1_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 := by
  ext j
  fin_cases j
  simp [SimplexCategory.δ, cone, v0]
  rfl

abbrev X {N : ℕ} (p r : ℕ) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨p, r, a, b⟩ : Pr N) 1

def Hg {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  X (z.1 + 1) z.2.1 (cone z.2.2.1) z.2.2.2 + if z.1 = 0 then X 0 (z.2.1 + 1) v0 (cone z.2.2.2) else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ Hg

lemma d_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d N (X p r a b) = Pr.d₁ (⟨p, r, a, b⟩ : Pr N) + (-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N) := by
  simp [Pr.d, X]

lemma H_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    H N (X p r a b) = Hg (⟨p, r, a, b⟩ : Pr N) := by
  simp [H, X]

lemma Hg_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨0, r, a, b⟩ : Pr N) = X 1 r (cone a) b + X 0 (r + 1) v0 (cone b) := by
  simp [Hg]

lemma Hg_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨p + 1, r, a, b⟩ : Pr N) = X (p + 2) r (cone a) b := by
  simp [Hg]

lemma diffOne_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_second_face_of_vertex_eq_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_first_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X p r (SimplexCategory.δ i ≫ a) b := by
  simp [Pr.d₁, X]

lemma simplex_pair_second_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) = ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p r a (SimplexCategory.δ i ≫ b) := by
  simp [Pr.d₂, X]

lemma simplex_pair_first_face_cone_vertex_formula {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨1, r, cone a, b⟩ : Pr N) = X 0 r a b - X 0 r v0 b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_two]
  have h1 : SimplexCategory.δ (1 : Fin 2) ≫ cone a = v0 := δ1_cone a
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, δ0_cone, h1, neg_smul, sub_eq_add_neg]

lemma simplex_pair_first_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 2, r, cone a, b⟩ : Pr N) = X (p + 1) r a b - ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X (p + 1) r (cone (SimplexCategory.δ i ≫ a)) b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma simplex_pair_second_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1 + 1, a, cone b⟩ : Pr N) = X p (r + 1) a b - ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p (r + 1) a (cone (SimplexCategory.δ i ≫ b)) := by
  rw [simplex_pair_second_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma alt_const {N : ℕ} (p : ℕ) (Y : Pr N →₀ ℤ) :
    ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (if p = 0 then Y else 0) = 0 := by
  cases p with
  | zero => simp [Fin.sum_univ_two]
  | succ p => simp

lemma key {N : ℕ} (z : Pr N) (hz : z.1 + z.2.1 ≠ 0) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  obtain ⟨p, r, a, b⟩ := z
  change Pr.d N (H N (X p r a b)) + H N (Pr.d N (X p r a b)) = X p r a b
  cases p with
  | zero =>
    cases r with
    | zero => simp at hz
    | succ r =>
      rw [H_X, Hg_zero, map_add (f := _), d_X, d_X, d_X, simplex_pair_first_face_cone_vertex_formula, diffOne_zero, diffOne_zero, simplex_pair_second_face_cone_succ_formula, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, map_zsmul, H_X, Hg_zero, smul_add, Finset.sum_add_distrib, zero_add,
        pow_zero, pow_one, one_smul, neg_smul, map_zero]
      abel
  | succ p =>
    cases r with
    | zero =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_of_vertex_eq_zero, simplex_pair_second_face_of_vertex_eq_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, map_zsmul, H_X, smul_zero, add_zero, map_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      abel
    | succ r =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, map_zsmul, H_X, Hg_succ, map_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      have e : (-1 : ℤ) ^ (p + 2) = -(-1) ^ (p + 1) := by ring
      rw [e, neg_smul]
      abel

lemma deg_H {N k : ℕ} {c : Pr N →₀ ℤ} (hdeg : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz
  have e : H N c = ∑ y ∈ c.support, c y • Hg y := by
    simp [H, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [e] at hz
  obtain ⟨y, hy, hz2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have hz3 := Finsupp.support_smul hz2
  have hy' := hdeg y hy
  obtain ⟨p, r, a, b⟩ := y
  simp only [Hg] at hz3
  rcases Finset.mem_union.1 (Finsupp.support_add hz3) with h | h
  · have := Finsupp.support_single_subset h
    rw [Finset.mem_singleton] at this
    subst this
    change p + r = k + 1 at hy'
    change p + 1 + r = k + 2
    omega
  · split_ifs at h with hp
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      subst this
      change p + r = k + 1 at hy'
      change 0 + (r + 1) = k + 2
      omega
    · simp at h

end LateralTheory.EtaleFoundations.AcycPf


open LateralTheory.EtaleFoundations.AcycPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  intro N k c hdeg hcyc
  refine ⟨LateralTheory.EtaleFoundations.AcycPf.H N c, LateralTheory.EtaleFoundations.AcycPf.deg_H hdeg, ?_⟩
  have h : ∀ y ∈ c.support, Pr.d N (LateralTheory.EtaleFoundations.AcycPf.H N (Finsupp.single y (c y))) + LateralTheory.EtaleFoundations.AcycPf.H N (Pr.d N (Finsupp.single y (c y))) =
      Finsupp.single y (c y) := by
    intro y hy
    have hy' := hdeg y hy
    rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← smul_add, LateralTheory.EtaleFoundations.AcycPf.key y (by omega)]
  have e : Pr.d N (LateralTheory.EtaleFoundations.AcycPf.H N c) + LateralTheory.EtaleFoundations.AcycPf.H N (Pr.d N c) = c := by
    conv_rhs => rw [← Finsupp.sum_single c]
    conv_lhs => rw [← Finsupp.sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl h
  rw [hcyc, map_zero, add_zero] at e
  exact e

end
end

-- bundled from Development.EtaleCohomology.TateTwists.LeafWaPf
section
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf.WaPf

def swap {N : ℕ} (z : Pr N) : Pr N := ⟨z.2.1, z.1, z.2.2.2, z.2.2.1⟩

noncomputable def tau (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z => Finsupp.single (swap z) ((-1 : ℤ) ^ (z.1 * z.2.1))

lemma tau_single {N : ℕ} (z : Pr N) (n : ℤ) :
    tau N (Finsupp.single z n) = Finsupp.single (swap z) (n * (-1 : ℤ) ^ (z.1 * z.2.1)) := by
  simp [tau, Finsupp.linearCombination_single, Finsupp.smul_single]

lemma d_single {N : ℕ} (z : Pr N) (n : ℤ) :
    Pr.d N (Finsupp.single z n) = n • (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  simp [Pr.d, Finsupp.linearCombination_single]

lemma d_tau_single {N : ℕ} (z : Pr N) :
    Pr.d N (tau N (Finsupp.single z 1)) = tau N (Pr.d N (Finsupp.single z 1)) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [tau_single, d_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp [swap, Pr.d₁, Pr.d₂]
    | succ r =>
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_smul, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul]
      simp
  | succ p =>
    cases r with
    | zero =>
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_smul, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul]
      simp
    | succ r =>
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul, smul_add]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)

lemma d_tau {N : ℕ} (c : Pr N →₀ ℤ) : Pr.d N (tau N c) = tau N (Pr.d N c) := by
  have : (Pr.d N).comp (tau N) = (tau N).comp (Pr.d N) := by
    refine Finsupp.lhom_ext' fun z => LinearMap.ext_ring ?_
    exact d_tau_single z
  exact LinearMap.congr_fun this c

lemma tau_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    tau M (Pr.push θ c) = Pr.push θ (tau N c) := by
  have : (tau M).comp (Pr.push θ) = (Pr.push θ).comp (tau N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tau_single]
    rfl
  exact LinearMap.congr_fun this c

lemma tau_bd {N : ℕ} (c : Pr N →₀ ℤ) : tau (N + 1) (Pr.bd c) = Pr.bd (tau N c) := by
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, tau_push]

lemma wa_eq (N : ℕ) : Pr.wa N = tau N (Pr.aw N) := by
  unfold Pr.wa Pr.aw
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, tau_single, swap, one_mul]

end LateralTheory.EtaleFoundations.SteenPf.WaPf


open LateralTheory.EtaleFoundations.SteenPf LateralTheory.EtaleFoundations.SteenPf.WaPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of_aw (hAW : leaf_aw) : leaf_wa := by
  intro N
  rw [wa_eq, wa_eq, d_tau, hAW, tau_bd]


open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of (hAW : leaf_aw) : leaf_wa := leaf_wa_of_aw hAW
end

-- bundled from Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds
section
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_push {N M K : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M)
    (θ' : SimplexCategory.mk M ⟶ SimplexCategory.mk K) (c : Pr N →₀ ℤ) :
    Pr.push θ' (Pr.push θ c) = Pr.push (θ ≫ θ') c := by
  simp only [Pr.push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  rfl

def inv {N : ℕ} (p : Fin (N + 3) × Fin (N + 2)) : Fin (N + 3) × Fin (N + 2) :=
  if h : (p.2 : ℕ) < p.1 then (p.2.castSucc, p.1.pred (by intro e; rw [e] at h; simp at h))
  else (p.2.succ, p.1.castPred (fun e => by have := congrArg Fin.val e; have := p.2.isLt; simp at this; simp at *; omega))

theorem prism_boundary_map_square_zero_holds : leaf_bdbd := by
  intro N c
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product' (f := fun (i : Fin (N + 3)) (j : Fin (N + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • Pr.push (SimplexCategory.δ j ≫ SimplexCategory.δ i) c)]
  refine Finset.sum_involution (fun p _ => inv p) ?_ ?_ (fun p _ => by simp) ?_
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h
    · have hj : j ≤ i.pred (fun e => by subst e; simp at h) := by
        rw [Fin.le_def, Fin.val_pred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      have hi : (i.pred (fun e => by subst e; simp at h)).succ = i := Fin.succ_pred _ _
      rw [hi] at e
      simp only [Fin.val_castSucc, Fin.val_pred]
      rw [e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]; ring
    · push Not at h
      have hne : i ≠ Fin.last (N + 2) := fun e => by have := congrArg Fin.val e; have := j.isLt; simp at this; simp at *; omega
      have hj : i.castPred hne ≤ j := by rw [Fin.le_def, Fin.coe_castPred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      rw [Fin.castSucc_castPred] at e
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [← e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      rw [pow_succ]; ring
  · rintro ⟨i, j⟩ - -
    simp only [inv]
    split_ifs with h <;> intro e <;> simp [Prod.ext_iff, Fin.ext_iff] at e <;> omega
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h h2 h2
    · exfalso; simp at h2; omega
    · simp [Prod.ext_iff, Fin.ext_iff]
    · simp [Prod.ext_iff, Fin.ext_iff]
    · exfalso; simp at h2; omega

end LateralTheory.EtaleFoundations.SteenPf
end

