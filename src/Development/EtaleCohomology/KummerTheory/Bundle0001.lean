module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.CupAWCutEv
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AW
variable {R : Type} [CommRing R]

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
  have h2 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up x))) h
  refine h2.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (P.map g.op)) (ULift.up x))

theorem map_freeGen {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have h := toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)
  have h2 := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) h
  refine h2.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (f.app (op U))) (ULift.up x))

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext Scheme.etaleTopology _ _ F.property ?_
  ext U : 2
  exact ModuleCat.free_hom_ext (fun x => h U.unop x.down)

theorem sec_map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h2 := congrArg (fun φ => φ.hom x) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

variable {E : Spc} {I : Cx R} {n : ℤ}

theorem ev_eq (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl

theorem ev_res (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sx E p U) : Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g) := by
  rw [ev_eq, ev_eq, sec_map_res, freeGen_res]; rfl

theorem ev_add (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x := by
  rw [ev_eq, Cochain.add_v, Preadditive.comp_add]; rfl

theorem sec_map_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem sec_map_zsmul {F G : Shv R} (c : ℤ) (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (c • φ) x = c • Sec.map φ x :=
  map_zsmul (AddMonoidHom.mk' (fun φ : F ⟶ G => Sec.map φ x) (fun _ _ => rfl)) c φ

theorem sec_map_sum {F G : Shv R} {ι : Type*} (s : Finset ι) (φ : ι → (F ⟶ G)) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (∑ i ∈ s, φ i) x = ∑ i ∈ s, Sec.map (φ i) x :=
  map_sum (AddMonoidHom.mk' (fun φ : F ⟶ G => Sec.map φ x) (fun _ _ => rfl)) φ s

theorem ev_units_smul (c : ℤˣ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x := by
  rw [ev_eq, Cochain.units_smul_v, Linear.comp_units_smul, Units.smul_def, sec_map_zsmul]; rfl

theorem isZero_pos (E : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj E).X i) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun j hj => by
    change -(j : ℤ) = i at hj
    omega)

theorem ev_ext (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) : α = β := by
  ext i j hij : 1
  by_cases hi : 0 < i
  · exact (isZero_pos E i hi).eq_of_src _ _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ (fun U x => h p j hij U x)

theorem chains_d (E : Spc) (p : ℕ) : (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl
  have h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p
  rw [h2] at h
  rw [Iso.inv_comp_eq]
  exact h

theorem ev_delta_zero {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (s t : ℤ) (hs : -((0 : ℕ) : ℤ) + n = s)
    (ht : -((0 : ℕ) : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E 0 U) :
    ev (R := R) (δ n m α) 0 t ht U x = Sec.map (I.d s t) (ev (R := R) α 0 s hs U x) := by
  rw [ev_eq, δ_v n m hm α _ _ ht s 1 (by omega) (by simp), (isZero_pos E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0]
  simp only [zero_comp, smul_zero, add_zero]
  rfl

theorem ev_delta_succ {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E (p + 1) U) :
    ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i) := by
  rw [ev_eq, δ_v n m hm α _ _ ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Linear.comp_units_smul,
    reassoc_of% (chains_d (R := R) E p), Preadditive.sum_comp]
  refine (sec_map_add _ _ _).trans ?_
  congr 1
  rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, sec_map_zsmul, ev_eq]
  congr 1
  exact congrArg (Sec.map ((chainsXIso R E p).inv ≫ α.v (-(p : ℤ)) t (by omega))) (map_freeGen (E.δ i) U x)

theorem along_comp {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  simp [Sx.along]

theorem val_succAbove {N : ℕ} (i : Fin (N + 1)) (a : Fin N) :
    (i.succAbove a).val = if a.val < i.val then a.val else a.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h h2 h2 <;> simp [Fin.lt_def] at h h2 ⊢ <;> omega

theorem face_sub_le {U : Scheme.{0}} {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)
    (hi : (i : ℕ) ≤ j) : (x.face i).sub j l h = x.sub (j + 1) l (by omega) := by
  refine (along_comp x _ _).trans (congrArg x.along ?_)
  ext a
  refine (val_succAbove i ⟨a.1 + j, _⟩).trans ?_
  change (if a.1 + j < i.1 then a.1 + j else a.1 + j + 1) = a.1 + (j + 1)
  split_ifs <;> omega

theorem face_sub_gt {U : Scheme.{0}} {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)
    (hi : j + l < (i : ℕ)) : (x.face i).sub j l h = x.sub j l (by omega) := by
  refine (along_comp x _ _).trans (congrArg x.along ?_)
  ext a
  have : a.1 < l + 1 := a.2
  refine (val_succAbove i ⟨a.1 + j, _⟩).trans ?_
  change (if a.1 + j < i.1 then a.1 + j else a.1 + j + 1) = a.1 + j
  split_ifs <;> omega

theorem face_sub_mid {U : Scheme.{0}} {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)
    (i' : Fin (l + 2)) (hi : (i : ℕ) = j + i') : (x.face i).sub j l h = (x.sub j (l + 1) (by omega)).face i' := by
  refine (along_comp x _ _).trans (Eq.trans (congrArg x.along ?_) (along_comp x _ _).symm)
  ext a
  refine (val_succAbove i ⟨a.1 + j, _⟩).trans ?_
  change (if a.1 + j < i.1 then a.1 + j else a.1 + j + 1) = (i'.succAbove a).1 + j
  rw [val_succAbove]
  split_ifs <;> omega

section Comb
variable {U : Scheme.{0}} {G : Type*} [AddCommGroup G]

def bd (f : ∀ p : ℕ, Sx E p U → G) : ∀ p : ℕ, Sx E p U → G
  | 0, _ => 0
  | p + 1, y => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • f p (y.face i)

theorem bd_congr {f g : ∀ p : ℕ, Sx E p U → G} {M : ℕ} (h : ∀ N y, N + 1 = M → f N y = g N y) (x : Sx E M U) :
    bd f M x = bd g M x := by
  cases M with
  | zero => rfl
  | succ N => exact Finset.sum_congr rfl fun i _ => by rw [h N _ rfl]

theorem face_split {N : ℕ} (x : Sx E (N + 1) U) (p q : ℕ) (h : p + q = N) (f : Sx E p U → Sx E q U → G) :
    ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • f ((x.face i).sub 0 p (by omega)) ((x.face i).sub p q (by omega)) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • f ((x.sub 0 (p + 1) (by omega)).face i) (x.sub (p + 1) q (by omega)) +
      (-1 : ℤ) ^ p • ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • f (x.sub 0 p (by omega)) ((x.sub p (q + 1) (by omega)).face j) := by
  rw [← Fin.sum_congr' _ (show (p + 1) + (q + 1) = N + 2 by omega), Fin.sum_univ_add, Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1), smul_add, Finset.smul_sum]
  have e1 : (x.sub 0 (p + 1) (by omega)).face (Fin.last (p + 1)) = x.sub 0 p (by omega) :=
    (face_sub_mid x ⟨p + 1, by omega⟩ 0 p (by omega) _ (by simp)).symm.trans (face_sub_gt x _ 0 p _ (by simp))
  have e2 : (x.sub p (q + 1) (by omega)).face 0 = x.sub (p + 1) q (by omega) :=
    (face_sub_mid x ⟨p, by omega⟩ p q (by omega) _ (by simp)).symm.trans (face_sub_le x _ p q _ (by simp))
  rw [e1, e2]
  have c : ∀ a b c d : G, b + c = 0 → a + d = a + b + (c + d) := fun a b c d h => by
    rw [add_assoc, ← add_assoc b, h, zero_add]
  refine Eq.trans ?_ (c _ _ _ _ (by simp [pow_succ]))
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := i.2
    rw [face_sub_mid x _ 0 p _ i.castSucc (by simp), face_sub_le x _ p q _ (by simp; omega)]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [face_sub_mid x _ p q _ j.succ (by simp; omega), face_sub_gt x _ 0 p _ (by simp; omega), smul_smul, ← pow_add]
    congr 2
    simp; omega

theorem sub_congr {A : Type*} {N : ℕ} (x : Sx E N U) (F : ∀ q : ℕ, Sx E q U → A) (p : ℕ) {q q' : ℕ} (e : q = q')
    (h : p + q ≤ N) : F q (x.sub p q h) = F q' (x.sub p q' (e ▸ h)) := by
  subst e; rfl

theorem bd_aw (F : ∀ p q : ℕ, Sx E p U → Sx E q U → G) (c c' : ℕ → ℤ) (hc : ∀ p, c' (p + 1) = c p) (M : ℕ) (x : Sx E M U) :
    bd (fun N y => ∑ p : Fin (N + 1), c p • F p (N - p) (y.sub 0 p (by omega)) (y.sub p (N - p) (by omega))) M x =
      ∑ p : Fin (M + 1), (c' p • bd (fun a y => F a (M - p) y (x.sub p (M - p) (by omega))) p (x.sub 0 p (by omega)) +
        c p • (-1 : ℤ) ^ (p : ℕ) • bd (fun b z => F p b (x.sub 0 p (by omega)) z) (M - p) (x.sub p (M - p) (by omega))) := by
  cases M with
  | zero => simp [bd]
  | succ N =>
    rw [Finset.sum_add_distrib, Fin.sum_univ_succ (n := N + 1), Fin.sum_univ_castSucc (n := N + 1),
      sub_congr x (bd _) _ (show N + 1 - (Fin.last (N + 1) : ℕ) = 0 by simp)]
    change ∑ i : Fin (N + 2), _ = (_ • (0 : G) + _) + (_ + _ • _ • (0 : G))
    simp only [smul_zero, zero_add, add_zero, Finset.smul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := p.2
    simp only [smul_comm _ (c p)]
    rw [← Finset.smul_sum, face_split x p (N - p) (by omega) (F p (N - p)), smul_add]
    congr 1
    · rw [← hc]
      exact congrArg _ (sub_congr x (fun q z => bd (fun a y => F a q y z) (p + 1) (x.sub 0 (p + 1) (by omega))) (p + 1)
        (show N - p = N + 1 - (p + 1) by omega) _)
    · exact congrArg _ (congrArg _ (sub_congr x (bd (fun b z => F p b (x.sub 0 p (by omega)) z)) p
        (show N - p + 1 = N + 1 - p by omega) _))

end Comb

end LateralTheory.KummerTheory.AW
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.InjSlice
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def IsoUpTo {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N : ℕ) (f : A → B) : Prop :=
  (∀ a, f a = 0 → N • a = 0) ∧ ∀ b, ∃ a, f a = N • b

def ext (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (y : Ht q (sch.obj Y) (n - a) 0) : Ht q (sch.obj (pullback pX pY)) n i :=
  (cup q (pull _ (sch.map (pullback.fst pX pY)) _ _ x) (pull _ (sch.map (pullback.snd pX pY)) _ _ y)).cast
    (by ring) (by ring)

def lh (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) : Ht q (sch.obj (pullback pX pY)) n i :=
  ∑ a : Fin (M + 1), ∑ s : Fin (r a), ext q pX pY ((a : ℕ) : ℤ) n i (c a s) (y a s)

def comb (q : ℕ) {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Ht q E n i) (t : Fin r → ZMod q) : Ht q E n i := ∑ s, t s • c s

def lev (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} (x : Hl l E n i) (k : ℕ) : Ht (l ^ k) E n i := x.1 k

def QBasis (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Hl l E n i) : Prop :=
  LinearIndependent ℚ_[l] (fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : HQ l E n i)) ∧
    Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : HQ l E n i)) = ⊤

def KunIso (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) : Prop :=
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0), ∃ z : Hl l (sch.obj (pullback pX pY)) n i,
      (∀ k, lev l z k = ext (l ^ k) pX pY a n i (lev l x k) (lev l y k)) ∧
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] z

def GOAL : Prop := A2 → DivisorNaturality → DivisorRingCompatibility → A7 → A8 → A9 → A10 → A11 → B1 → B2 → B3 → E2 → E3 → E4 →
  ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ {X Y : Scheme.{0}}
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k)) [IsProper pX] [Smooth pX] [IsProper pY]
    (n i : ℤ), KunIso l pX pY n i

def IsCls {R : Type} [CommRing R] {X : Scheme.{0}} {I : Cx R} {n : ℤ}
    (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) (a : Sec (I.X n) X) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, CohomologyClass.mk α = x ∧
    ev (R := R) α.1 0 n (by simp) X (𝟙 X) = a ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U),
      ev (R := R) α.1 (p + 1) s h U y = 0

def tot {X S : Scheme.{0}} (p : X ⟶ S) : Over S ⥤ Scheme.{0} := Over.pullback p ⋙ Over.forget X

def bcMap {X : Scheme.{0}} {R A B : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (h : A ⟶ B) (e : f ≫ h = g) :
    pullback p (Spec.map g) ⟶ pullback p (Spec.map f) :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map h) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp, e])

def Dict : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ),
  (∀ a : Sec (I.X n) X, Sec.map (I.d n (n + 1)) a = 0 → ∃ x, IsCls x a) ∧
  (∀ x : CohomologyClass ((chains R).obj (sch.obj X)) I n, ∃ a, IsCls x a) ∧
  (∀ x (a : Sec (I.X n) X), IsCls x a → Sec.map (I.d n (n + 1)) a = 0 ∧
    (x = 0 ↔ ∃ b : Sec (I.X (n - 1)) X, Sec.map (I.d (n - 1) n) b = a)) ∧
  (∀ x x' (a a' : Sec (I.X n) X), IsCls x a → IsCls x' a' → IsCls (x + x') (a + a') ∧ IsCls (-x) (-a)) ∧
  ∀ {Y : Scheme.{0}} (f : Y ⟶ X) x (a : Sec (I.X n) X), IsCls x a →
    IsCls (cpre (Cocycle.ofHom ((chains R).map (sch.map f))) I n n (zero_add n) x) (Sec.res f a)

def CupAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
  ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 ∧
    μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def CupSch : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (X : Scheme.{0}) {n m k : ℤ} (hk : n + m = k)
  x y (a : Sec (I.X n) X) (b : Sec (J.X m) X), IsCls x a → IsCls y b →
  IsCls (μ.cup (sch.obj X) hk x y) (μ.mul X n m k hk a b)

def Ghost : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [EnoughInjectives A] (C : CochainComplex A ℤ)
  [C.IsStrictlyGE (-1)], (∀ j, Injective (C.X j)) → ∀ (N : ℕ) (m : ℕ), (∀ j : ℤ, j < m → N • 𝟙 (C.homology j) = 0) →
  ∀ j : ℤ, j < m → ∀ (P : A) (f : P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 →
    ∃ g : P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = N ^ (m + 1) • f

def InjSlice : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] {X S : Scheme.{0}} (p : X ⟶ S),
  (∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((tot p).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))) ∧
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

def StrictHenselization : Prop := ∀ (R : CommRingCat.{0}) (𝔭 : PrimeSpectrum R), ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c) (u : (Functor.const J).obj R ⟶ D),
  SH c.pt ∧ ∀ j, (u.app j).hom.Etale ∧ ∃ 𝔮 : PrimeSpectrum (D.obj j), 𝔮.asIdeal.comap (u.app j).hom = 𝔭.asIdeal

def Cont : Prop := A2 → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R) [QuasiCompact p]
  [IsSeparated p], IsUnit (q : R) → ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
  IsColimit c → ∀ (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j k} (f : j ⟶ k), u j ≫ D.map f = u k) (v : R ⟶ c.pt)
    (hv : ∀ j, u j ≫ c.ι.app j = v) (n i : ℤ),
  (∀ x : Ht q (sch.obj (pullback p (Spec.map v))) n i, ∃ j y, pull _ (sch.map (bcMap p (u j) v (c.ι.app j) (hv j))) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (pullback p (Spec.map (u j)))) n i),
    pull _ (sch.map (bcMap p (u j) v (c.ι.app j) (hv j))) _ _ y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull _ (sch.map (bcMap p (u j) (u k) (D.map f) (hu f))) _ _ y = 0

def LH : Prop := A2 → DivisorNaturality → B1 → ∃ e : ℕ → ℕ, ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (M N : ℕ), (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → ∀ n : ℤ, n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)) →
  ∀ {Y : Scheme.{0}} (pY : Y ⟶ Spec R) (n : ℤ), n < M → IsoUpTo (N ^ e M) (lh q p pY i r c M n)

def TwSec : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  Nonempty (Prim q Γ(Spec (CommRingCat.of A), ⊤)) ∧ ∀ (i : ℤ) (ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤)),
    Function.Bijective fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ

def H0 : Prop := A9 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  Function.Bijective fun t : ZMod q => t • one q (sp A)

def Place : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K],
  ∃ (T : ValuationSubring K) (σ : k →+* T), (∀ x, (σ x : K) = algebraMap k K x) ∧
    Function.Bijective ((IsLocalRing.residue T).comp σ) ∧ AIC T ∧ SH T

def AlgExt : Prop := E2 → E3 → ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
  (f : k →+* K), IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom f)))) (tw q i)

def SHInsep : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A] [Algebra κ A],
  SH A → SH (A ⊗[κ] K)

def Insep : Prop := A9 → B2 → B3 → ∀ (q : ℕ) [NeZero q] (κ K : Type) [Field κ] [Field K] [Algebra κ K]
  [IsPurelyInseparable κ K], IsUnit (q : κ) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of κ)) (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap κ K))))) (tw q i)

def SHInv : Prop := A9 → B2 → B3 → E2 → E3 → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] [Smooth p] (A : CommRingCat.{0})
    (s : CommRingCat.of k ⟶ A), SH A → ∀ i : ℤ, Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i)

def Stalk : Prop := DivisorNaturality → DivisorRingCompatibility → A9 → B2 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ), Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i) →
  (∀ a ≤ M, IsoUpTo N (comb q (c a))) → ∀ n : ℤ, n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)

def BockData (l b : ℕ) (E : Spc) (i : ℤ) : Prop :=
  ∃ (u : ∀ (a : ℕ) (n : ℤ), Ht (l ^ a) E n i →+ Ht (l ^ (b + a)) E n i)
    (d : ∀ (a : ℕ) (n : ℤ), Ht (l ^ b) E n i →+ Ht (l ^ a) E (n + 1) i), ∀ (a : ℕ) (n : ℤ),
    Function.Exact (u a n) (red (l ^ (b + a)) (l ^ b) E n i) ∧
    Function.Exact (red (l ^ (b + a)) (l ^ b) E n i) (d a n) ∧
    Function.Exact (d a n) (u a (n + 1)) ∧
    (∀ x, u a n (red (l ^ (b + a)) (l ^ a) E n i x) = l ^ b • x) ∧
    (∀ x, red (l ^ (a + 1)) (l ^ a) E (n + 1) i (d (a + 1) n x) = d a n x) ∧
    ∀ x, red (l ^ (b + (a + 1))) (l ^ (b + a)) E n i (u (a + 1) n x) = u a n (red (l ^ (a + 1)) (l ^ a) E n i x)

def Bock : Prop := A7 → A8 → A10 → A11 → ∀ (l : ℕ) [Fact l.Prime] (b : ℕ) (E : Spc) (i : ℤ), Inv l E → BockData l b E i

def AdicDeg : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, ∃ (r : ℕ) (c : Fin r → Hl l E n i) (N : ℕ), 0 < N ∧ QBasis l c ∧
    ∀ k, IsoUpTo N (comb (l ^ k) fun s => lev l (c s) k)

def Limit : Prop := A9 → A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → 0 < N → (∀ a ≤ M, QBasis l (c a)) →
  (∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0)) →
  (∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n)) → KunIso l pX pY n i

end LateralTheory.KummerTheory

end
end

