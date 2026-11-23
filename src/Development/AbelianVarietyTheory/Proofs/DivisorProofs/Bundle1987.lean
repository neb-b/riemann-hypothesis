module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetUniq

open GlobalTheory.MBLow.ScaleJet

theorem tr_unique {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) {m : ℕ} (hm : Odd m) {T : Over S}
    {th th' : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} (hth : ∀ j, th.f j = th'.f j) {x : T ⟶ P.A} {U U' t t'}
    (hU : SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U) (hU' : SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U')
    (H : Tr P ρ m th U t) (H' : Tr P ρ m th' U' t') (j) : t.f j = t'.f j := by
  have hL := P.isLB
  obtain ⟨α, s, hα, hn, h₁, h₂⟩ := H
  obtain ⟨α', s', hα', hn', h₁', h₂'⟩ := H'
  have hc := SymLiftOdd.symLift_unique globalFns_holds P.isAb hL hm.pow _ _ hU hU'
  have ha := gen_unique' hL (fun _ _ _ => rfl) (fst T P.A).left (ptSecT P.A (1 : T ⟶ P.A)).left
    (congrArg (fun q => q.left) (lift_fst _ _ : lift (𝟙 T) (1 : T ⟶ P.A) ≫ _ = _))
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_fst globalFns_holds P.isAb T) hα hα' (fun w I hI => by
      have q := val_corr hI hn (𝟙 _)
      have q' := val_corr hI hn' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at q q'
      exact q.trans q'.symm)
  obtain ⟨p, φ, hφ⟩ := U
  obtain ⟨p', φ', hφ'⟩ := U'
  obtain rfl : p = x := hU.pt_eq
  obtain rfl : p' = p := hU'.pt_eq
  refine sec_ext_val (φ := fun _ : Fin 1 => (snd T P.A).left) hL (fun y J hJ => ?_) j
  refine (twist_val h₂ _ y hJ).trans (Eq.trans ?_ (twist_val h₂' _ y hJ).symm)
  refine congrArg₂ (· * ·) (congrArg Units.val (val_corr hJ hc _)) ?_
  refine (twist_val h₁ _ y hJ).trans (Eq.trans ?_ (twist_val h₁' _ y hJ).symm)
  exact congrArg₂ (· * ·) (congrArg Units.val (ha _ _ y J hJ)) (congrArg (gs _ y _) (hth _))

section Germ

variable {B : Type} [CommRing B] {X : Scheme.{0}}

def germAt (z : Sp B) : B →+* (Sp B).presheaf.stalk z :=
  ((Sp B).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

theorem germAt_valR (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (z : Sp B) :
    germAt z (valR x U f) = gs x z U f := by
  rw [valR, dite_eq_left h, gs_eq x z U (h trivial), germAt, RingHom.comp_apply, Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp B).presheaf (homOfLE h) z trivial _

theorem germAt_ext {a b : B} (h : ∀ z : Sp B, germAt z a = germAt z b) : a = b := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b :=
    TopCat.Presheaf.section_ext (Sp B).sheaf ⊤ _ _ fun z _ => h z
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1 e

theorem isUnit_valR (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : IsUnit (valR x U u.val) := by
  rw [valR, dite_eq_left h]
  exact (u.isUnit.map _).map _

theorem valR_sec_chart {Y : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (n : ℤ)))) (y : Sp B ⟶ Y) {i i' : L.ι}
    (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i') :
    valR y (LB.wchart L (fun _ : Fin 1 => φ) fun _ => i') (s.f fun _ => i') =
      valR (y ≫ φ) (L.U i' ⊓ L.U i) (L.g i' i).val ^ n * valR y (LB.wchart L (fun _ : Fin 1 => φ) fun _ => i) (s.f fun _ => i) := by
  have a : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) fun _ => i := fun z hz => Set.mem_iInter.2 fun _ => h hz
  have a' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) fun _ => i' := fun z hz => Set.mem_iInter.2 fun _ => h' hz
  have b : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ (L.U i' ⊓ L.U i) := fun z hz => ⟨h' hz, h hz⟩
  refine germAt_ext fun z => ?_
  have q := sec_trans s y z (a' trivial) (a trivial)
  rw [trF, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val] at q
  rw [map_mul, map_pow, germAt_valR _ _ b, gs_unit (y ≫ φ) z (L.U i' ⊓ L.U i) (b trivial)]
  exact (germAt_valR _ _ a' _ z).trans (q.trans (congrArg _ (germAt_valR _ _ a _ z).symm))

theorem valR_gen_chart {Y : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) {ρ : LB.Gen (L.pull φ)} (hρ : ρ.IsGen) (y : Sp B ⟶ Y)
    {i i' : L.ι} (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i') :
    valR y ((L.pull φ).U fun _ => i') (ρ.s fun _ => i').val =
      valR (y ≫ φ) (L.U i' ⊓ L.U i) (L.g i' i).val * valR y ((L.pull φ).U fun _ => i) (ρ.s fun _ => i).val := by
  have a : ⊤ ≤ y ⁻¹ᵁ (L.pull φ).U fun _ => i := fun z hz => Set.mem_iInter.2 fun _ => h hz
  have a' : ⊤ ≤ y ⁻¹ᵁ (L.pull φ).U fun _ => i' := fun z hz => Set.mem_iInter.2 fun _ => h' hz
  have b : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ (L.U i' ⊓ L.U i) := fun z hz => ⟨h' hz, h hz⟩
  refine germAt_ext fun z => ?_
  have q := congrArg Units.val (gen_trans (φ := fun _ : PUnit => φ) (ε := fun _ => 1) hρ y z (a' trivial) (a trivial))
  rw [trF, Fintype.prod_unique, zpow_one, Units.val_mul] at q
  rw [map_mul, germAt_valR _ _ b, gs_unit (y ≫ φ) z (L.U i' ⊓ L.U i) (b trivial)]
  exact ((germAt_valR _ _ a' _ z).trans (gs_unit y z _ (a' trivial) _)).trans
    (q.trans (congrArg _ ((germAt_valR _ _ a _ z).trans (gs_unit y z _ (a trivial) _)).symm))

end Germ

section Tangent

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def toProd (A : Over (Sp R)) : A.left ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk A.hom (by simp) : A ⟶ baseOver (Sp R)) (𝟙 A)).left

omit [GrpObj A] in
theorem epsLift_eq (v : epsR R ⟶ A) : epsLift v = v.left ≫ toProd A := by
  rw [epsLift, toProd, ← Over.comp_left, comp_lift, Category.comp_id]
  congr 2
  exact Over.OverMorphism.ext (Over.w v).symm

omit [GrpObj A] in
theorem epsLift_snd (v : epsR R ⟶ A) : epsLift v ≫ (snd (baseOver (Sp R)) A).left = v.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem grpPullback_id : IsGrpPullback A A (𝟙 (Sp R)) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 (Sp R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

theorem tan_le {v : epsR R ⟶ A} (hv : IsTangent v) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) : ⊤ ≤ v.left ⁻¹ᵁ V := by
  rw [GlobalTheory.ArcLie.le_iff_fst, hv]
  exact hV

theorem fst_valR {v : epsR R ⟶ A} (hv : IsTangent v) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) (f : Γ(A.left, V)) :
    (valR (A := DualNumber R) v.left V f).fst = valR (A := R) (eSec A) V f := by
  have e := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom R R R).toRingHom v.left V (tan_le hv hV) f
  rw [hv] at e
  exact e.symm

theorem snd_valR [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : ∀ k, IsTangent (v k)) {c : Fin n → R}
    {w : epsR R ⟶ A} (hc : IsLieComb c v w) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) (f : Γ(A.left, V)) :
    (valR (A := DualNumber R) w.left V f).snd = ∑ k, c k * (valR (A := DualNumber R) (v k).left V f).snd := by
  have e := GlobalTheory.ArcLieCoord.comb_snd grpPullback_id v hv c w hc V (by rw [Category.comp_id]; exact hV) f
  simpa only [Category.comp_id] using e

omit [GrpObj A] in
theorem toProd_snd : toProd A ≫ (snd (baseOver (Sp R)) A).left = 𝟙 A.left := by
  rw [toProd, ← Over.comp_left, lift_snd]; rfl

theorem le_toProd {L : LB A.left} {i : L.ι} (h : ⊤ ≤ eSec A ⁻¹ᵁ L.U i) :
    ⊤ ≤ eSec A ⁻¹ᵁ toProd A ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd (baseOver (Sp R)) A).left) fun _ => i := by
  intro z hz
  refine Set.mem_iInter.2 fun _ => ?_
  have e : (toProd A ≫ (snd (baseOver (Sp R)) A).left) (eSec A z) ∈ L.U i := by
    rw [toProd_snd]; exact h hz
  exact e

end Tangent

theorem thJet_change : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (hp rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → ∀ (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ P.A)) (ϑ ϑ' : I → K) (J J' : I → Fin P.g → K), ThJet ⟨P, hp, rig, hr, th, hth, v, hv⟩ rfl m pt ϑ J → ThJet ⟨P, hp, rig, hr, th', hth', v', hv'⟩ rfl m pt ϑ' J' → (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin P.g → K, ∀ i j, J' i j = a * ∑ l, M j l * J i l + c j * ϑ i := by
  intro K _ P hp rig hr th hth v hv th' hth' v' hv' a M hs hM m hm _ I pt ϑ ϑ' J J'
  rintro ⟨θ, hθ, U, t, i₀, c, hU, hi, H⟩ ⟨θ', hθ', U', t', i₁, c', hU', hi', H'⟩
  have := P.isAb.comm
  dsimp only at hθ hθ' hU hU' hi hi' H H'
  have k₀ : ⊤ ≤ eSec P.A ⁻¹ᵁ P.L.U i₀ := fun z hz => hi hz
  have k₁ : ⊤ ≤ eSec P.A ⁻¹ᵁ P.L.U i₁ := fun z hz => hi' hz
  have hθ₁ : ∀ j, θ'.f j = (cMul (baseOver (Sp K) ⊗ P.A).hom a θ).f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    have h := LB.wchart_le P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) (fun _ => i) 0
    exact (hθ' i h).trans ((congrArg _ (hs i)).trans (polAVSectionInverseImage_mulConstant P _ th θ a hθ i h).symm)
  have ht : ∀ i j, (t' i).f j = constFn (baseOver (Sp K) ⊗ P.A).hom _ a * (t i).f j := fun i j => by
    obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
    exact tr_unique P rig hm hθ₁ (hU' i).1 (hU i).1 (hU' i).2 (t' := cMul _ a (t i))
      ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩ j

  let V := LB.wchart P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) fun _ => i₀
  let D : I → (epsR K ⟶ P.A) → DualNumber K := fun i w => valR (epsLift w) V ((t i).f fun _ => i₀)
  let r : K := valR (𝟙 (Sp K)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (rig.s fun _ => i₀).val
  let G : K := valR (A := K) (eSec P.A) (P.L.U i₁ ⊓ P.L.U i₀) (P.L.g i₁ i₀).val
  let u : Fin P.g → DualNumber K := fun j =>
    valR (A := DualNumber K) (v' j).left (P.L.U i₁ ⊓ P.L.U i₀) (P.L.g i₁ i₀).val ^ (m ^ 2)
  have k₂ : ⊤ ≤ eSec P.A ⁻¹ᵁ (P.L.U i₁ ⊓ P.L.U i₀) := fun z hz => ⟨k₁ hz, k₀ hz⟩
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((P.L.pull (eSec P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hG₀ : G ≠ 0 := (isUnit_valR (B := K) _ _ k₂ _).ne_zero
  have hu : ∀ j, (u j).fst = G ^ (m ^ 2) := fun j => by
    rw [TrivSqZeroExt.fst_pow, fst_valR (hv'.1 j) k₂]
  have hD : ∀ i l, D i (v l) = TrivSqZeroExt.inl (r ^ (m ^ 2)) *
      (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i l + c l * ϑ i)) := H
  have hD' : ∀ i w, D i w = valR (A := DualNumber K) w.left (toProd P.A ⁻¹ᵁ V)
      (((toProd P.A).app V).hom ((t i).f fun _ => i₀)) := fun i w => by
    simp only [D]
    rw [epsLift_eq]
    exact GlobalTheory.HolHom.valR_comp _ _ _ _
  have f₁ : ∀ i j, (D i (v' j)).fst = r ^ (m ^ 2) * ϑ i := fun i j => by
    have e := congrArg TrivSqZeroExt.fst (hD i j)
    rw [hD', fst_valR (hv.1 j) (le_toProd k₀)] at e
    rw [hD', fst_valR (hv'.1 j) (le_toProd k₀), e]
    simp
  have f₂ : ∀ i j, (D i (v' j)).snd = r ^ (m ^ 2) * (∑ l, M j l * J i l + (∑ l, M j l * c l) * ϑ i) := fun i j => by
    rw [hD', snd_valR hv.1 (hM j) (le_toProd k₀), Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hD', hD]
    simp
    ring
  have main : ∀ i j, algebraMap K (DualNumber K) a * (u j * D i (v' j)) = TrivSqZeroExt.inl ((G * r) ^ (m ^ 2)) *
      (TrivSqZeroExt.inl (ϑ' i) + TrivSqZeroExt.inr (J' i j + c' j * ϑ' i)) := fun i j => by
    have e₁ := valR_gen_chart (eSec P.A) hr (𝟙 (Sp K)) hi hi'
    have e₂ := valR_sec_chart (snd (baseOver (Sp K)) P.A).left (m ^ 2) (t i) (epsLift (v' j)) (i := i₀) (i' := i₁)
      (by rw [epsLift_snd]; exact tan_le (hv'.1 j) k₀) (by rw [epsLift_snd]; exact tan_le (hv'.1 j) k₁)
    rw [epsLift_snd] at e₂
    have hx : epsLift (v' j) ≫ (baseOver (Sp K) ⊗ P.A).hom = spMap (algebraMap K (DualNumber K)) := Over.w _
    have e₃ := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₁)
    have e₄ := H' i j
    rw [e₁] at e₄
    exact (congrArg _ e₂).symm.trans (e₃.symm.trans ((congrArg (valR _ _) (ht i _)).symm.trans e₄))
  have hϑ : ∀ i, ϑ' i = a * ϑ i := fun i => by
    have e := congrArg TrivSqZeroExt.fst (main i ⟨0, hp⟩)
    simp only [TrivSqZeroExt.fst_mul, hu, f₁, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero, mul_pow] at e
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (m ^ 2) hG₀) (pow_ne_zero (m ^ 2) hr₀)) ?_
    linear_combination -e
  refine ⟨hϑ, fun j => a * (∑ l, M j l * c l + (u j).snd / G ^ (m ^ 2) - c' j), fun i j => ?_⟩
  have e := congrArg TrivSqZeroExt.snd (main i j)
  simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hu, f₁, f₂, hϑ, TrivSqZeroExt.algebraMap_eq_inl,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, zero_add, zero_mul,
    add_zero, mul_pow] at e
  have hG₁ := pow_ne_zero (m ^ 2) hG₀
  refine mul_left_cancel₀ (mul_ne_zero hG₁ (pow_ne_zero (m ^ 2) hr₀)) ?_
  linear_combination -e - r ^ (m ^ 2) * a * ϑ i * div_mul_cancel₀ (u j).snd hG₁

end GlobalTheory.MBLow.JetUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem isFreeGen_formMap_of_formallyEtale {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} {D : ℕ} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β)
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formOrd_ratPull (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ)
    (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p]
    (hn : topologicalKrullDim W = n) (E : DivOver p) (E' : DivOver (f ≫ p))
    (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring)
    (hρ : ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale)
    (hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g)
    (η : RatForms p n) (hη : η ≠ 0) :
    (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  set φ := functionFieldMap f with hφ
  set ρ := φ.restrict E.ring E'.ring h with hρdef
  obtain ⟨ω, hω, g, hη', hg⟩ := E.isFormOrd_formOrd hn hη
  have hc : ρ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun (functionFieldMap_comp_constFn p f) a
  have hω' : IsFreeGen E'.ring (TopForm.formMap n ρ hc ω) := isFreeGen_formMap_of_formallyEtale hρ hc hω
  have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ρ := by
    ext x
    rfl
  have hτ : (E'.ring.subtype.comp ρ).comp E.const = Cartier.constFn (f ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ρ hc ω) := by
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl
      (functionFieldMap_comp_constFn p f) hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ρ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hpull : ratPull p f n η = φ (g : W.functionField) • E'.toRat n (TopForm.formMap n ρ hc ω) := by
    rw [hη', map_smulₛₗ, key]
  have hne : ratPull p f n η ≠ 0 := by
    rw [hpull]
    intro h0
    have hinj := (E'.isFreeGen_toRat hω').1
    have : φ (g : W.functionField) = 0 := hinj (by simpa using h0)
    exact (g.map φ.toMonoidHom).ne_zero this
  change E'.formOrd (ratPull p f n η) = E.formOrd η
  rw [← hg]
  refine DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', Units.map φ.toMonoidHom g, hpull, hord g⟩

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

def trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι) (n : ℤ) : A :=
  valR y (L.U a ⊓ L.U b) ((L.g a b) ^ n).val

def pickJ {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) : Ix :=
  jf (Classical.epsilon fun i' => φs i' = φs i)

theorem pickJ_congr {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) {i₁ i₂ : Fin 4}
    (h : φs i₁ = φs i₂) : pickJ φs jf i₁ = pickJ φs jf i₂ := by
  unfold pickJ; rw [h]

theorem pickJ_spec {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) :
    ∃ i', φs i' = φs i ∧ pickJ φs jf i = jf i' :=
  ⟨_, Classical.epsilon_spec (p := fun i' => φs i' = φs i) ⟨i, rfl⟩, rfl⟩

theorem trV_add {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n m : ℤ) : trV L y a b n * trV L y a b m = trV L y a b (n + m) := by
  unfold trV
  rw [zpow_add, Units.val_mul, GlobalTheory.ZH.CrdCalc.valR_mul y _ h]

theorem isUnit_trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) : IsUnit (trV L y a b n) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h]
  exact (Units.isUnit _).map _

theorem top_le_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j :=
  fun q _ => Set.mem_iInter.2 fun k => h k (x := q) trivial

theorem wchart_top_le {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j) (k : K) : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  fun q _ => Set.mem_iInter.1 (h (x := q) trivial) k

theorem trV_zero {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) : trV L y a b 0 = 1 := by
  unfold trV
  rw [zpow_zero, Units.val_one, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, map_one]

theorem trV_pow {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) (m : ℕ) : trV L y a b n ^ m = trV L y a b (n * m) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, ← map_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul]

end GlobalTheory.MBLow.TanGauge

namespace GlobalTheory.MBLow.TanGauge

theorem gl_corr : ∀ {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')),
    LB.Gen.Corr L φ ε φ' ε' t t' → ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
    (∀ k k', φ k = φ' k' → j k = j' k') → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ' j' →
    valR y (LB.wchart L φ j) (t.s j).val = valR y (LB.wchart L φ' j') (t'.s j').val := by
  intro X Y L K K' _ _ φ ε φ' ε' t t' hc j j' hj hj' hx A _ y h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun q hq => ⟨h hq, h' hq⟩
  have e := congrArg Units.val (hc j j' hj hj' hx)
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') hh (t'.s j').val
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact congrArg (valR y _) e

theorem gl_pullGen : ∀ {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι) {A : Type} [CommRing A] (y : Sp A ⟶ Z),
    ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ j →
    valR y (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val = valR (y ≫ h) (LB.wchart L φ j) (c.s j).val := by
  intro X Y Z L K _ φ ε c h j A _ y hy
  have hy' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j :=
    top_le_wchart L _ _ _ fun k => by rw [← Category.assoc]; exact wchart_top_le L _ _ _ hy k
  have e := GlobalTheory.ZH.CrdCalc.valR_res y ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j) hy' (pullU h _ (c.s j)).val
  refine e.trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ j) (fun q hq => hy hq) _

theorem gl_gtφT_pull : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T T' : Over (Sp R)) (h : T'.left ⟶ T.left),
    h ≫ T.hom = T'.hom → ∀ (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A), b'.left = h ≫ b.left → ∀ (α : D.X) (i : Fin 4),
    DegPre.gtφT D T' b' α i = h ≫ DegPre.gtφT D T b α i := by
  intro R _ _ D T T' h hh b b' hb α i
  have hb' : b' = Over.homMk h hh ≫ b := by
    ext; simpa using hb
  subst hb'
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T' α) (Over.homMk h hh ≫ b)).left = (Over.homMk h hh : T' ⟶ T).left ≫
      (padd D.P.A (DegPre.cT D T α) b).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T' ≫ D.c α).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (Over.homMk h hh ≫ b).left = h ≫ b.left
    simp
  · change (toUnit T' ≫ η[D.P.A]).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_gtφT_famφB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (b : T ⟶ D.P.A) (α : D.X) (i : Fin 4),
    DegPre.gtφT D T b α i = b.left ≫ D.famφB α (![1, 2, 0, 3] i) := by
  intro R _ _ D T b α i
  have pc : ∀ (x y : T ⟶ D.P.A), padd D.P.A x y = padd D.P.A y x := fun x y => by
    show x * y = y * x
    exact mul_comm x y
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T α) b).left = b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left, pc]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T ≫ D.c α).left = b.left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · exact (Category.comp_id _).symm
  · change (toUnit T ≫ η[D.P.A]).left = b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB' : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ (DegPre.prB D C).left =
      b.left := by
  intro R _ _ D C _ _ b
  rw [← Over.comp_left, lift_snd]

theorem gl_scal : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (c : C),
    valR (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ⊤
      (scal (fst (TF (R := R) C) D.P.A).left c) = TrivSqZeroExt.inl c := by
  intro R _ _ D C _ _ b c
  have hq : (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫
      (fst (TF (R := R) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h := GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) _ _ hq ⊤ (fun _ _ => trivial) c
  have e : resTop ⊤ (scal (fst (TF (R := R) C) D.P.A).left c) = scal (fst (TF (R := R) C) D.P.A).left c := by
    simp [resTop]
  rw [e] at h
  rw [h, TrivSqZeroExt.algebraMap_eq_inl]

theorem gl_tan : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (gm₀ : GtPt D (epsR R)), GtTan gm₀ →
    redE R ≫ gm₀.b.left = eSec D.P.A := by
  intro R _ _ D gm₀ hT
  obtain ⟨o, ⟨hb, -⟩, h1, -⟩ := hT
  rw [← h1, hb]
  have hw := Over.w (toUnit (baseOver (Sp R)))
  have e : (toUnit (baseOver (Sp R))).left = 𝟙 _ := by simpa using hw
  simp only [DegPre.zeroT, Over.comp_left, e, Category.id_comp]
  rfl

theorem gl_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    (TF (R := R) C).hom = spMap (toF R C) := by
  intro R _ _ C _ _
  simp only [TF, jFK, jK, Over.mk_hom, spMap, toF, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gl_redE : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    redE C ≫ spMap (dualMap (toF R C)) = spMap (toF R C) ≫ redE R := by
  intro R _ _ C _ _
  simp only [redE, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  simp [dualMap, toF]

theorem gl_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    spMap (dualMap (toF R C)) ≫ (epsR R).hom = (TE R C).hom := by
  intro R _ _ C _ _
  simp only [TE, epsR, Over.mk_hom, gl_TF, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.MBLow.TanGauge

end
end

