module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows

namespace GlobalTheory.CompanionTheory.Dict

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def L0 : Cn F 0 →ₗ[R] C0 F where
  toFun f T := f (mk₀ T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L1 : Cn F 1 →ₗ[R] C1 F where
  toFun f _ _ φ := f (mk₁ φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L2 : Cn F 2 →ₗ[R] C2 F where
  toFun f _ _ _ φ ψ := f (mk₂ φ ψ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L3 : Cn F 3 →ₗ[R] C3 F where
  toFun f _ _ _ _ φ ψ χ := f (mk₃ φ ψ χ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem L0_bijective_cochain : Function.Bijective (L0 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj (Fin.last 0)), rfl⟩⟩
  obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact congr_fun h X

theorem L1_bijective_cochain : Function.Bijective (L1 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj (Fin.last 1))
    (c.map (homOfLE (Fin.zero_le _))), rfl⟩⟩
  obtain ⟨X₀, X₁, φ, rfl⟩ := ComposableArrows.mk₁_surjective c
  exact congr_fun (congr_fun (congr_fun h X₀) X₁) φ

theorem L2_bijective_cochain : Function.Bijective (L2 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj (Fin.last 2))
    (c.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, φ, ψ, rfl⟩ := ComposableArrows.mk₂_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) φ) ψ

theorem L3_bijective_cochain : Function.Bijective (L3 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj 2)
    (c.obj (Fin.last 3)) (c.map (homOfLE (show (0 : Fin 4) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 4) ≤ 2 by decide)))
    (c.map (homOfLE (show (2 : Fin 4) ≤ Fin.last 3 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, X₃, φ, ψ, χ, rfl⟩ := ComposableArrows.mk₃_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) X₃) φ) ψ) χ

theorem cof_eq {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ C) (c' : Fin (n + 1) ⥤ C)
    (h : face i c = c') (u : c'.obj (Fin.last n) ⟶ c.obj (Fin.last (n + 1)))
    (hu : HEq (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) u) (f : Cn F n) :
    cof F n i f c = mp F u (f c') := by
  subst h
  obtain rfl := eq_of_heq hu
  rfl

theorem dn0 (f : Cn F 0) (c : Fin 2 ⥤ C) : dn F 0 f c = cof F 0 0 f c - cof F 0 1 f c := by
  simp [dn, Fin.sum_univ_two, sub_eq_add_neg]

theorem dn1 (f : Cn F 1) (c : Fin 3 ⥤ C) :
    dn F 1 f c = cof F 1 0 f c - cof F 1 1 f c + cof F 1 2 f c := by
  simp [dn, Fin.sum_univ_three, pow_succ, sub_eq_add_neg]

theorem dn2 (f : Cn F 2) (c : Fin 4 ⥤ C) :
    dn F 2 f c = cof F 2 0 f c - cof F 2 1 f c + cof F 2 2 f c - cof F 2 3 f c := by
  simp [dn, Fin.sum_univ_four, pow_succ, sub_eq_add_neg]

theorem eq_mk₁ (c : ComposableArrows C 1) (x : c.left ⟶ c.right) (h : c.hom = x) : c = mk₁ x := by
  obtain ⟨X₀, X₁, g, rfl⟩ := ComposableArrows.mk₁_surjective c
  subst h
  rfl

theorem eq_mk₂ (c : ComposableArrows C 2) (x : c.obj' 0 ⟶ c.obj' 1) (y : c.obj' 1 ⟶ c.obj' 2)
    (hx : map' c 0 1 = x) (hy : map' c 1 2 = y) : c = mk₂ x y := by
  obtain ⟨X₀, X₁, X₂, g₀, g₁, rfl⟩ := ComposableArrows.mk₂_surjective c
  subst hx hy
  rfl

section Faces

variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')

theorem cech_nerve_face_one_zero : face 0 (mk₁ φ) = mk₀ T' := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_one_one : face 1 (mk₁ φ) = mk₀ T := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_two_zero : face 0 (mk₂ φ ψ) = mk₁ ψ := by
  exact eq_mk₁ (face 0 (mk₂ φ ψ)) ψ rfl
theorem cech_nerve_face_two_one : face 1 (mk₂ φ ψ) = mk₁ (φ ≫ ψ) := by
  exact eq_mk₁ (face 1 (mk₂ φ ψ)) (φ ≫ ψ) rfl
theorem cech_nerve_face_two_two : face 2 (mk₂ φ ψ) = mk₁ φ := by
  exact eq_mk₁ (face 2 (mk₂ φ ψ)) φ rfl
theorem face_zero_mk3 : face 0 (mk₃ φ ψ χ) = mk₂ ψ χ := by
  exact eq_mk₂ (face 0 (mk₃ φ ψ χ)) ψ χ rfl rfl
theorem face_one_mk3 : face 1 (mk₃ φ ψ χ) = mk₂ (φ ≫ ψ) χ := by
  exact eq_mk₂ (face 1 (mk₃ φ ψ χ)) (φ ≫ ψ) χ rfl rfl
theorem face_two_mk3 : face 2 (mk₃ φ ψ χ) = mk₂ φ (ψ ≫ χ) := by
  exact eq_mk₂ (face 2 (mk₃ φ ψ χ)) φ (ψ ≫ χ) rfl rfl
theorem face_three_mk3 : face 3 (mk₃ φ ψ χ) = mk₂ φ ψ := by
  exact eq_mk₂ (face 3 (mk₃ φ ψ χ)) φ ψ rfl rfl

end Faces

private theorem mp_id_apply (X : C) (x : F.obj X) : mp F (𝟙 X) x = x := by
  rw [mp, CategoryTheory.Functor.map_id]
  rfl

theorem L1_dn_zero_eq_d0_L0 (f : Cn F 0) : L1 F (dn F 0 f) = d0 F (L0 F f) := by
  funext T T' φ
  show dn F 0 f (mk₁ φ) = L0 F f T' - mp F φ (L0 F f T)
  rw [dn0, cof_eq F (n := 0) 0 (mk₁ φ) (mk₀ T') (cech_nerve_face_one_zero φ) (𝟙 T') HEq.rfl f,
    cof_eq F (n := 0) 1 (mk₁ φ) (mk₀ T) (cech_nerve_face_one_one φ) φ HEq.rfl f]
  show mp F (𝟙 T') (f (mk₀ T')) - mp F φ (f (mk₀ T)) = _
  rw [mp_id_apply F T' (f (mk₀ T'))]
  rfl

theorem L2_dn_one_eq_d1_L1 (f : Cn F 1) : L2 F (dn F 1 f) = d1 F (L1 F f) := by
  funext T T' T'' φ ψ
  show dn F 1 f (mk₂ φ ψ) = mp F ψ (L1 F f T T' φ) - L1 F f T T'' (φ ≫ ψ) + L1 F f T' T'' ψ
  rw [dn1, cof_eq F (n := 1) 0 (mk₂ φ ψ) (mk₁ ψ) (cech_nerve_face_two_zero φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 1 (mk₂ φ ψ) (mk₁ (φ ≫ ψ)) (cech_nerve_face_two_one φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 2 (mk₂ φ ψ) (mk₁ φ) (cech_nerve_face_two_two φ ψ) ψ HEq.rfl f]
  conv_lhs => rw [sub_add_comm]
  show mp F ψ (f (mk₁ φ)) - mp F (𝟙 T'') (f (mk₁ (φ ≫ ψ))) + mp F (𝟙 T'') (f (mk₁ ψ)) = _
  rw [mp_id_apply F T'' (f (mk₁ (φ ≫ ψ))), mp_id_apply F T'' (f (mk₁ ψ))]
  rfl

theorem L3_dn_two_eq_d2_L2 (f : Cn F 2) : L3 F (dn F 2 f) = d2 F (L2 F f) := by
  funext T T' T'' T''' φ ψ χ
  show dn F 2 f (mk₃ φ ψ χ) = L2 F f T' T'' T''' ψ χ - L2 F f T T'' T''' (φ ≫ ψ) χ +
    L2 F f T T' T''' φ (ψ ≫ χ) - mp F χ (L2 F f T T' T'' φ ψ)
  rw [dn2, cof_eq F (n := 2) 0 (mk₃ φ ψ χ) (mk₂ ψ χ) (face_zero_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 1 (mk₃ φ ψ χ) (mk₂ (φ ≫ ψ) χ) (face_one_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 2 (mk₃ φ ψ χ) (mk₂ φ (ψ ≫ χ)) (face_two_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 3 (mk₃ φ ψ χ) (mk₂ φ ψ) (face_three_mk3 φ ψ χ) χ HEq.rfl f]
  show mp F (𝟙 T''') (f (mk₂ ψ χ)) - mp F (𝟙 T''') (f (mk₂ (φ ≫ ψ) χ)) +
    mp F (𝟙 T''') (f (mk₂ φ (ψ ≫ χ))) - mp F χ (f (mk₂ φ ψ)) = _
  rw [mp_id_apply F T''' (f (mk₂ ψ χ)), mp_id_apply F T''' (f (mk₂ (φ ≫ ψ) χ)),
    mp_id_apply F T''' (f (mk₂ φ (ψ ≫ χ)))]
  rfl

theorem dictSt : DictSt := by
  intro R _ C _ F
  refine ⟨LinearEquiv.ofBijective (L0 F) (L0_bijective_cochain F), LinearEquiv.ofBijective (L1 F) (L1_bijective_cochain F),
    LinearEquiv.ofBijective (L2 F) (L2_bijective_cochain F), LinearEquiv.ofBijective (L3 F) (L3_bijective_cochain F),
    fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
    fun f => ?_, fun f => ?_, fun f => ?_⟩ <;> simp only [LinearEquiv.ofBijective_apply]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact L1_dn_zero_eq_d0_L0 F f
  · exact L2_dn_one_eq_d1_L1 F f
  · exact L3_dn_two_eq_d2_L2 F f

end GlobalTheory.CompanionTheory.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveMV

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def Cob (W : ObjectProperty C) : ∀ j : ℕ, CrystallineSemistableComparison.CH.Cn F j → Prop
  | 0, x => ∀ s : ComposableArrows C 0, W (s.obj 0) → x s = 0
  | j + 1, x => ∃ y : CrystallineSemistableComparison.CH.Cn F j, ∀ s : ComposableArrows C (j + 1), W (s.obj 0) → x s = CrystallineSemistableComparison.CH.d F j y s

def Van (W : ObjectProperty C) (j : ℕ) : Prop :=
  ∀ x : CrystallineSemistableComparison.CH.Cn F j, (∀ s : ComposableArrows C (j + 1), W (s.obj 0) → CrystallineSemistableComparison.CH.d F j x s = 0) → Cob F W j x

variable {F}

theorem face_start {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (i : Fin (n + 2))
    (s : ComposableArrows C (n + 1)) (h : W (s.obj 0)) : W ((face i s).obj 0) :=
  hW (s.map (homOfLE (Fin.zero_le _))) h

theorem d_congr {n : ℕ} (x y : CrystallineSemistableComparison.CH.Cn F n) (s : ComposableArrows C (n + 1))
    (h : ∀ i, x (face i s) = y (face i s)) : CrystallineSemistableComparison.CH.d F n x s = CrystallineSemistableComparison.CH.d F n y s := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (x (face i s)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (y (face i s))
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

def liftCh {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (s : ComposableArrows C n) (h : W (s.obj 0)) :
    ComposableArrows W.FullSubcategory n :=
  W.lift s fun i => hW (s.map (homOfLE (Fin.zero_le i))) h


open Classical in
def extZ {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (y : CrystallineSemistableComparison.CH.Cn (W.ι ⋙ F) n) : CrystallineSemistableComparison.CH.Cn F n :=
  fun s => if h : W (s.obj 0) then y (liftCh hW s h) else 0

theorem pull_extZ {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (y : CrystallineSemistableComparison.CH.Cn (W.ι ⋙ F) n) :
    (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC n (extZ hW y) = y := by
  funext t
  have h : W ((t ⋙ W.ι).obj 0) := (t.obj 0).property
  change extZ hW y (t ⋙ W.ι) = y t
  unfold extZ
  rw [dite_eq_left h]
  rfl

theorem van_of_subsingleton {W : ObjectProperty C} (hW : Cosieve W) (j : ℕ)
    (hs : Subsingleton (HU F W j)) : Van F W j := by
  intro x hx
  have hz : CrystallineSemistableComparison.CH.d (W.ι ⋙ F) j ((CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC j x) = 0 := by
    rw [CrystallineSemistableComparison.CH.Mor.d_pullC]
    funext t
    exact hx (t ⋙ W.ι) (t.obj 0).property
  have hB := ((CrystallineSemistableComparison.P.cls_surj (CrystallineSemistableComparison.CH.cx (W.ι ⋙ F)) j).2.1 _ hz).1 (Subsingleton.elim _ _)
  cases j with
  | zero =>
    intro s h
    have e : (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC 0 x = 0 := hB
    exact congrFun e (liftCh hW s h)
  | succ j =>
    obtain ⟨y, hy⟩ := hB
    refine ⟨extZ hW y, fun s h => ?_⟩
    have e : (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC (j + 1) x =
        (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC (j + 1) (CrystallineSemistableComparison.CH.d F j (extZ hW y)) := by
      rw [← CrystallineSemistableComparison.CH.Mor.d_pullC, pull_extZ]
      exact hy.symm
    exact congrFun e (liftCh hW s h)

theorem van_sup {U V : ObjectProperty C} (hU : Cosieve U) (hV : Cosieve V) {j : ℕ}
    (h1 : Van F U j) (h2 : Van F V j) (h3 : ∀ i, j = i + 1 → Van F (fun T => U T ∧ V T) i) :
    Van F (fun T => U T ∨ V T) j := by
  intro x hx
  have ca := h1 x fun s h => hx s (Or.inl h)
  have cb := h2 x fun s h => hx s (Or.inr h)
  cases j with
  | zero =>
    rintro s (h | h)
    · exact ca s h
    · exact cb s h
  | succ n =>
    obtain ⟨a, ha⟩ := ca
    obtain ⟨b, hb⟩ := cb
    have hz : ∀ s : ComposableArrows C (n + 1), (U (s.obj 0) ∧ V (s.obj 0)) →
        CrystallineSemistableComparison.CH.d F n (a - b) s = 0 := by
      intro s hs
      rw [map_sub, Pi.sub_apply, ← ha s hs.1, ← hb s hs.2, sub_self]
    have hc := h3 n rfl (a - b) hz
    obtain ⟨a', ha', hab⟩ : ∃ a' : CrystallineSemistableComparison.CH.Cn F n,
        (∀ s : ComposableArrows C (n + 1), U (s.obj 0) → x s = CrystallineSemistableComparison.CH.d F n a' s) ∧
        ∀ s : ComposableArrows C n, U (s.obj 0) → V (s.obj 0) → a' s = b s := by
      cases n with
      | zero => exact ⟨a, ha, fun s h h' => sub_eq_zero.1 (hc s ⟨h, h'⟩)⟩
      | succ m =>
        obtain ⟨c, hc⟩ := hc
        refine ⟨a - CrystallineSemistableComparison.CH.d F m c, fun s h => ?_, fun s h h' => ?_⟩
        · rw [map_sub, CrystallineSemistableComparison.CH.d_d, sub_zero]
          exact ha s h
        · have e := hc s ⟨h, h'⟩
          rw [Pi.sub_apply] at e ⊢
          rw [← e]
          abel
    classical
    refine ⟨fun s => if U (s.obj 0) then a' s else b s, fun s hs => ?_⟩
    by_cases hu : U (s.obj 0)
    · rw [ha' s hu]
      exact d_congr _ _ s fun i => (if_pos (face_start hU i s hu)).symm
    · have hv : V (s.obj 0) := hs.resolve_left hu
      rw [hb s hv]
      refine d_congr _ _ s fun i => ?_
      by_cases hui : U ((face i s).obj 0)
      · exact (hab _ hui (face_start hV i s hv)).symm.trans (if_pos hui).symm
      · exact (if_neg hui).symm

theorem van_congr {W W' : ObjectProperty C} (h : ∀ T, W T ↔ W' T) {j : ℕ} (hv : Van F W j) : Van F W' j := by
  obtain rfl : W = W' := funext fun T => propext (h T)
  exact hv

theorem van_empty {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Van F W j := by
  intro x _
  cases j with
  | zero => exact fun s hs => (h _ hs).elim
  | succ j => exact ⟨0, fun s hs => (h _ hs).elim⟩

def Wc {ι : Type} (U : ι → ObjectProperty C) (A S : Finset ι) : ObjectProperty C :=
  fun T => (∃ α ∈ A, U α T) ∧ capS U S T

theorem cosieve_capS {ι : Type} {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α)) (S : Finset ι) :
    Cosieve (capS U S) :=
  fun _ _ f h α hα => hU α f (h α hα)

theorem cosieve_Wc {ι : Type} {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α)) (A S : Finset ι) :
    Cosieve (Wc U A S) := by
  rintro T T' f ⟨⟨α, hα, hT⟩, hS⟩
  exact ⟨⟨α, hα, hU α f hT⟩, cosieve_capS hU S f hS⟩

theorem van_Wc {ι : Type} [DecidableEq ι] {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α))
    (D : ℕ → ℕ → Prop) (E : ℕ → Prop) (hD : ∀ n j, D (n + 1) j → D n j ∧ E j ∧ ∀ i, j = i + 1 → D n i)
    (hcap : ∀ S : Finset ι, S.Nonempty → ∀ j, E j → Van F (capS U S) j) (A : Finset ι) :
    ∀ (S : Finset ι) (j : ℕ), D A.card j → Van F (Wc U A S) j := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j _
    exact van_empty (fun T hT => by simpa using hT.1) j
  | insert a A ha ih =>
    intro S j hj
    rw [Finset.card_insert_of_notMem ha] at hj
    obtain ⟨d1, d2, d3⟩ := hD _ _ hj
    have key := van_sup (cosieve_Wc hU A S) (cosieve_capS hU (insert a S)) (ih S j d1)
      (hcap _ (Finset.insert_nonempty _ _) j d2) fun i hi => van_congr (fun T => ⟨fun h =>
        ⟨⟨h.1, fun α hα => h.2 α (Finset.mem_insert_of_mem hα)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩)
        (ih (insert a S) i (d3 i hi))
    refine van_congr (fun T => ⟨?_, ?_⟩) key
    · rintro (⟨⟨α, hα, hT⟩, hS⟩ | h)
      · exact ⟨⟨α, Finset.mem_insert_of_mem hα, hT⟩, hS⟩
      · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
          fun α hα => h α (Finset.mem_insert_of_mem hα)⟩
    · rintro ⟨⟨α, hα, hT⟩, hS⟩
      rcases Finset.mem_insert.1 hα with rfl | h
      · refine Or.inr fun β hβ => ?_
        rcases Finset.mem_insert.1 hβ with rfl | h'
        · exact hT
        · exact hS β h'
      · exact Or.inl ⟨⟨α, h, hT⟩, hS⟩

theorem subsingleton_of_van {W : ObjectProperty C} (hW : ∀ T, W T) {j : ℕ} (h : Van F W j) :
    Subsingleton (CrystallineSemistableComparison.CH.H F j) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
  refine ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 a ha).2 ?_
  have hc := h a fun s _ => congrFun ha s
  cases j with
  | zero => exact funext fun s => hc s (hW _)
  | succ j =>
    obtain ⟨y, hy⟩ := hc
    exact ⟨y, funext fun s => (hy s (hW _)).symm⟩

theorem vanishing_of_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  intro R _ C _ F ι _ U hU hc s
  classical
  have key : ∀ (D : ℕ → ℕ → Prop) (E : ℕ → Prop),
      (∀ n j, D (n + 1) j → D n j ∧ E j ∧ ∀ i, j = i + 1 → D n i) →
      (∀ S : Finset ι, S.Nonempty → ∀ j, E j → Subsingleton (HU F (capS U S) j)) →
      ∀ j, D (Fintype.card ι) j → Subsingleton (CrystallineSemistableComparison.CH.H F j) := by
    intro D E hD h j hj
    refine subsingleton_of_van (W := Wc U Finset.univ ∅) (fun T => ?_)
      (van_Wc hU D E hD (fun S hS j hE => van_of_subsingleton (cosieve_capS hU S) j (h S hS j hE))
        Finset.univ ∅ j (by simpa using hj))
    obtain ⟨α, hα⟩ := hc T
    exact ⟨⟨α, Finset.mem_univ _, hα⟩, fun β hβ => by simp at hβ⟩
  refine ⟨fun h j hj => key (fun _ j => j < s) (fun j => j < s) ?_ (fun S hS j hE => h S hS j hE) j hj,
    fun h j => key (fun _ _ => True) (fun _ => True) ?_ (fun S hS j _ => h S hS j) j trivial,
    fun h j hj => key (fun n j => s + n ≤ j) (fun j => j > s) ?_ (fun S hS j hE => h S hS j hE) j hj⟩
  · intro n j hj
    exact ⟨hj, hj, fun i hi => by omega⟩
  · intro n j _
    exact ⟨trivial, trivial, fun _ _ => trivial⟩
  · intro n j hj
    exact ⟨by omega, by omega, fun i hi => by omega⟩

end GlobalTheory.CompanionTheory.CosieveMV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CoordRes

theorem etale_rs {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    (rs h).Etale := by
  have key := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ h
  have e : Scheme.Hom.appLE (𝟙 X) V W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE] <;> rfl
  rw [e] at key
  exact key

theorem rs_comp_strV {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : W ≤ V) : (rs h).comp (strV q V) = strV q W := by
  simp only [rs, strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem main : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  intro O _ X q V W d c h hW
  refine ⟨⟨hW, fun i => rs h (c.t i), ?_⟩, fun i => rfl⟩
  have e1 : MvPolynomial.eval₂Hom (strV q W) (fun i => rs h (c.t i)) =
      (rs h).comp (MvPolynomial.eval₂Hom (strV q V) c.t) := by
    rw [MvPolynomial.comp_eval₂Hom, rs_comp_strV]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ c.etale (etale_rs h c.affine hW)

end GlobalTheory.CompanionTheory.CoordRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordsOfEtaleBasicOpen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCoord

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) :
        MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  letI := (strV q W).toAlgebra
  intro h
  haveI := hW.isLocalization_basicOpen g
  let φ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hφ : ∀ x, φ (algebraMap Γ(X, W) (Localization.Away g) x) = resO (X.basicOpen_le g) x :=
    fun x => φ.commutes x
  refine ⟨⟨hW.basicOpen g, fun k => resO (X.basicOpen_le g) (s k), ?_⟩, fun _ => rfl⟩
  have h2 := RingHom.Etale.stableUnderComposition _ _ h
    (RingHom.Etale.of_bijective (f := (φ : Localization.Away g →+* Γ(X, X.basicOpen g))) φ.bijective)
  have e : (MvPolynomial.eval₂Hom (strV q (X.basicOpen g)) (fun k => resO (X.basicOpen_le g) (s k)) :
        MvPolynomial (Fin d) K →+* Γ(X, X.basicOpen g)) =
      (φ : Localization.Away g →+* Γ(X, X.basicOpen g)).comp
        (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
          (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
      rw [strV_res q (X.basicOpen_le g), RingHom.comp_apply, IsScalarTower.algebraMap_apply K Γ(X, W) (Localization.Away g)]
      exact (hφ _).symm
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]
      exact (hφ _).symm
  rw [e]
  exact h2

end GlobalTheory.CompanionTheory.GeoCoord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalizationExactStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_cohomology_localization_exact : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ hμ : μ.comp (toGS Ω _) = cycMod F Ω l r, LocalTateDuality → 0 < r → ∀ inv : InvFam F Ω l r, (∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Function.Bijective (inv A)) → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)) ∧ Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)).flip := by
  first | exact @GlobalTheory.CompanionTheory.LocalPerfect.locPerfect | exact GlobalTheory.CompanionTheory.LocalPerfect.locPerfect | (intros; apply GlobalTheory.CompanionTheory.LocalPerfect.locPerfect <;> assumption)
end

