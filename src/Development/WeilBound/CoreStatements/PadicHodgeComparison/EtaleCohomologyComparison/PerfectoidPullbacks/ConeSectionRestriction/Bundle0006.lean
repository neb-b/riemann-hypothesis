module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) : T.B :=
  Classical.choose (Ideal.Quotient.mk_surjective (ev T h g))

def dlogC (Q : ObjectProperty (Thick (smFun X q))) (s : ℕ) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) :
    CH.Cn (CH.modF (sP Q).A) 1 :=
  fun σ => (show (σ.obj (Fin.last 1)).obj.B from
    plogK (σ.obj (Fin.last 1)).obj.δ s (ĝ (σ.obj (Fin.last 1)) *
      Ring.inverse ((σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (ĝ (σ.obj 0))) - 1))

def jacSpan {V V' : X.Opens} (h : V ≤ V') {A : Type} [CommRing A] (ι : Γ(X, V) →+* A) {d m : ℕ}
    (D : Fin d → Γ(X, V) → A) (κ : Fin m → Fin d) : AddSubgroup A :=
  AddSubgroup.closure {y | ∃ (b : Γ(X, V')) (bs : Fin m → Γ(X, V')),
    y = ι (rs h b) * (Matrix.of fun k l => D (κ k) (rs h (bs l))).det}

section KS
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V V' : X.Opens} (h : V ≤ V') {T : Thick (smFun X q)} (hT : InU V T) : InU V' T :=
  fun x hx => h (hT hx)

theorem ks_le (s : ℕ) {V V' : X.Opens} (h : V ≤ V') : KS q s {V} ≤ KS q s {V'} := by
  rintro T ⟨hT, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  subst hW
  exact ⟨hT, V', rfl, inU_mono q h hTW⟩

theorem ks_in (s : ℕ) (V : X.Opens) : ∀ T, KS q s {V} T → InU V T := by
  rintro T ⟨-, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  exact hW ▸ hTW

def resKS (s : ℕ) {V V' : X.Opens} (h : V ≤ V') (r r' : ℤ) (j : ℕ) :
    HQ (KS q s {V'}) r r' j →ₗ[K] HQ (KS q s {V}) r r' j :=
  ((incl (ks_le q s h)).sq (incl_fil _ r) (incl_fil _ r')).pull j

end KS

end CrystallineSemistableComparison.Pb
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactA
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

theorem range_sub_awayι {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Set.range z ⊆ Set.range (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd) := by
  rintro _ ⟨x, rfl⟩
  have hx : z x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f := h (Set.mem_univ x)
  rw [← Proj.opensRange_awayι _ f hf hd] at hx
  exact hx

def liftA {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A :=
  (Spec.preimage (IsOpenImmersion.lift (Proj.awayι _ f hf hd) z (range_sub_awayι z hf hd h))).hom

theorem liftA_spec {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z := by
  unfold liftA
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem liftA_unique {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ f hf hd = z) : φ = liftA z hf hd h := by
  have h1 : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (liftA z hf hd h)) := by
    rw [← cancel_mono (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd), hφ, liftA_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem liftA_comp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ) ≫ z) ⁻¹ᵁ Proj.basicOpen _ f) :
    liftA (Spec.map (CommRingCat.ofHom ρ) ≫ z) hf hd h' = ρ.comp (liftA z hf hd h) := by
  symm
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, liftA_spec]

theorem liftA_awayMap {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d d' : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (d + d')) (hdd : 0 < d + d')
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x) :
    (liftA z hxd hdd h').comp (HomogeneousLocalization.awayMap _ hg hx) = liftA z hf hd h := by
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
  exact liftA_spec z hxd hdd h'

theorem awayToSection_appLE {A : CommRingCat.{0}}
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d)
    (φ : CommRingCat.of (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) ⟶ A)
    (h : ⊤ ≤ (Spec.map φ ≫ Proj.awayι _ f hf hd) ⁻¹ᵁ Proj.basicOpen _ f) :
    Proj.awayToSection _ f ≫ (Spec.map φ ≫ Proj.awayι _ f hf hd).appLE (Proj.basicOpen _ f) ⊤ h ≫
      (Scheme.ΓSpecIso A).hom = φ := by
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.map φ ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd).inv := ⟨_, rfl⟩
  have e1 : Spec.map φ ≫ Proj.awayι _ f hf hd = w ≫ (Proj.basicOpen _ f).ι := by
    rw [hw, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have e2 : w ≫ Proj.basicOpenToSpec _ f = Spec.map φ := by
    rw [hw, ← Proj.basicOpenIsoSpec_hom _ f hf hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have e3 : ∀ (z : Spec A ⟶ PSpace K N) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hz : z = w ≫ (Proj.basicOpen _ f).ι),
      z.appLE (Proj.basicOpen _ f) ⊤ h = (Proj.basicOpen _ f).topIso.inv ≫ w.appTop := by
    intro z h hz
    subst hz
    rw [← Scheme.Hom.appLE_comp_appLE w _ _ ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [e3 _ h e1]
  have e4 := Scheme.ΓSpecIso_naturality φ
  rw [← e2, Scheme.Hom.comp_appTop] at e4
  have e5 := Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f
  change (Proj.basicOpenToSpec _ f).appTop = _ at e5
  rw [e5] at e4
  simp only [Category.assoc] at e4
  simpa only [Category.assoc] using (cancel_epi _).1 e4

theorem liftA_eval {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) = liftA z hf hd h a := by
  have key : ∀ (z' : Spec (CommRingCat.of A) ⟶ PSpace K N) (h' : ⊤ ≤ z' ⁻¹ᵁ Proj.basicOpen _ f)
      (hz : Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z'),
      Proj.awayToSection _ f ≫ z'.appLE (Proj.basicOpen _ f) ⊤ h' ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (liftA z hf hd h) := by
    intro z' h' hz
    subst hz
    exact awayToSection_appLE hf hd _ h'
  exact congrArg (fun ψ => CommRingCat.Hom.hom ψ a) (key z h (liftA_spec z hf hd h))

theorem le_basicOpen_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g : MvPolynomial (Fin (N + 1)) K}
    (hf : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hg : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ g) :
    ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (f * g) := by
  rw [Proj.basicOpen_mul]
  intro p hp
  exact ⟨hf hp, hg hp⟩

theorem liftA_eval_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d' n : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K n) (hn : 0 < n)
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) =
      liftA z hxd hn h' (HomogeneousLocalization.awayMap _ hg hx a) := by
  rw [← liftA_eval]
  have e : Proj.awayToSection _ f ≫ z.appLE (Proj.basicOpen _ f) ⊤ h =
      CommRingCat.ofHom (HomogeneousLocalization.awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        z.appLE (Proj.basicOpen _ x) ⊤ h' := by
    rw [← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (CommRingCat.Hom.hom ψ a)) e

def yx {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1))
    (k : Fin m) : ChartR K N j :=
  HomogeneousLocalization.Away.mk _ (X_mem K N j) e (y k)
    (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k))

theorem liftA_yx_isUnit {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k)) :
    IsUnit (liftA z (X_mem K N j) one_pos hj (yx y hy j k)) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have hxd : MvPolynomial.X j * y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk
  rw [← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx, RingHom.comp_apply]
  apply IsUnit.map
  have hX : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ^ (1 + e) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • (1 + e)) := by
    simpa using SetLike.pow_mem_graded (1 + e) (X_mem K N j)
  refine IsUnit.of_mul_eq_one (HomogeneousLocalization.Away.mk _ hxd 1 _ hX) ?_
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  ring

theorem liftA_yx_change {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j j' : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hj' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j') one_pos hj' (yx y hy j' k) * liftA z (X_mem K N j) one_pos hj (ratio K N j j') ^ e := by
  have hxd : (MvPolynomial.X j * MvPolynomial.X j' : MvPolynomial (Fin (N + 1)) K) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + 1) :=
    SetLike.mul_mem_graded (X_mem K N j) (X_mem K N j')
  have hx := le_basicOpen_mul z hj hj'
  rw [← liftA_awayMap z (X_mem K N j) one_pos (X_mem K N j') rfl hxd (by omega) hj hx,
    ← liftA_awayMap z (X_mem K N j') one_pos (X_mem K N j) (mul_comm _ _) hxd (by omega) hj' hx]
  simp only [RingHom.comp_apply]
  rw [← map_pow, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx ratio
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

theorem liftA_yx_quot {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k k' : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j) one_pos hj (yx y hy j k') *
        GlobalTheory.Cris.evalAt z (Proj.basicOpen _ (y k')) hk'
          ((Proj.awayToSection _ (y k')).hom
            (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
              (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hxd : MvPolynomial.X j * y k' ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk'
  rw [liftA_eval_mul z (X_mem K N j) (mul_comm _ _) hxd (by omega) hk' hx,
    ← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx]
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

end CrystallineSemistableComparison.Pb.LX
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def CLiftK.precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) : CLiftK (h ⋙ g) D where
  p c := Λ.p (h.obj c)
  hp c := Λ.hp (h.obj c)
  w φ := Λ.w (h.map φ)
  hw φ hh := Λ.hw (h.map φ) hh

def zK {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ) :
    CH.Cn (g ⋙ O (smFun X q)) 2 :=
  fun σ => (show (g.obj (σ.obj (Fin.last 2))).B from
    plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1))

def 𝒱D (D : E.LineData X) : Set X.Opens := {V | ∃ σ : (V : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = V.ι}

end CrystallineSemistableComparison.Pb
end
end

