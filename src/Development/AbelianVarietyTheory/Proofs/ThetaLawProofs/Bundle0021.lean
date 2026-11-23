module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulExactOfGradedRegular
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsSquareDetComparisonScaleSec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero

noncomputable section

namespace GlobalTheory.KaScale

section Lin

variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))}

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

def der (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U)) : K :=
  TrivSqZeroExt.snd (valT (T := DualNumber K) v.left U f)

theorem der_pos (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = (pullFn v U h f).snd := congrArg _ (dif_pos h)

theorem der_neg (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ¬ ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = 0 := congrArg _ (dif_neg h)

theorem der_scale (v : sp (R₀ := K) (DualNumber K) ⟶ A) (c : K) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (Chart.spMap (scaleD c) ≫ v) U f = c * der v U f := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  by_cases h : ⊤ ≤ v.left ⁻¹ᵁ U
  · have h' := le_preimage_comp (scaleD c) v _ rfl U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h', pullFn_comp (scaleD c) v _ rfl U h h' f, scaleD_eq]
    simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_preimage_of_comp (scaleD c) v _ rfl U h')), mul_zero]

variable [GrpObj A]

theorem le_of_isTan {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ v'.left ⁻¹ᵁ U := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  exact le_preimage_of_comp (fstD K) v' 1 hv'.symm U (le_preimage_comp (fstD K) v 1 hv.symm U h)

theorem der_mul {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (f : Γ(A.left, U)) : der (v * v') U f = der v U f + der v' U f := by
  by_cases h : ⊤ ≤ (v * v').left ⁻¹ᵁ U
  · obtain ⟨h₁, h₂, e⟩ := snd_pullFn_mul hv hv' U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h₁, der_pos _ _ _ h₂, e]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_of_isTan hv (isTan_mul hv hv') U h')),
      der_neg _ _ _ (fun h' => h (le_of_isTan hv' (isTan_mul hv hv') U h')), add_zero]

theorem der_one (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (1 : sp (R₀ := K) (DualNumber K) ⟶ A) U f = 0 := by
  rw [← comp_one' (Chart.spMap (scaleD (0 : K))), der_scale, zero_mul]

theorem der_prod (U : A.left.Opens) (f : Γ(A.left, U)) :
    ∀ {n : ℕ} (v : Fin n → (sp (R₀ := K) (DualNumber K) ⟶ A)), (∀ i, Chart.IsTan (v i)) →
      Chart.IsTan (List.ofFn v).prod ∧ der (List.ofFn v).prod U f = ∑ i, der (v i) U f := by
  intro n
  induction n with
  | zero =>
    intro v _
    rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨isTan_one, der_one U f⟩
  | succ n ih =>
    intro v hv
    obtain ⟨h₁, h₂⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, der_mul (hv 0) h₁, h₂]
    exact ⟨isTan_mul (hv 0) h₁, rfl⟩

theorem der_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der w U f = ∑ i, c i * der (v i) U f := by
  rw [(isLieComb_iff c v w).1 hw]
  refine (der_prod U f _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))).2.trans ?_
  exact Finset.sum_congr rfl fun i _ => der_scale _ _ _ _

theorem translate_left (z : 𝟙_ (Over (Sp K)) ⟶ A) (v : epsR K ⟶ A) :
    ((toUnit (epsR K) ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem snd_valT_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (z : 𝟙_ (Over (Sp K)) ⟶ A)
    (U : A.left.Opens) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * w).left U f) =
      ∑ i, c i * TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v i).left U f) := by
  simp only [translate_left]
  exact (congrArg _ (valT_comp _ _ _ _)).trans ((der_comb hv hw _ _).trans
    (Finset.sum_congr rfl fun i _ => congrArg (fun t => c i * TrivSqZeroExt.snd t) (valT_comp _ _ _ _).symm))

end Lin

def cS {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) : K →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem gs_constFn' {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) (r : Y ⟶ X)
    (y : Y) (hy : r y ∈ W) (a : K) : gs r y W (constFn p W a) = cS (r ≫ p) y a :=
  ((gs_res r y (fun _ _ => trivial : W ≤ p ⁻¹ᵁ ⊤) hy _).trans (gs_pull r p y ⊤ trivial _)).trans
    (gs_eq (r ≫ p) y ⊤ trivial _)

theorem gs_cst' {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) (a : K) :
    gs (𝟙 Y) y ⊤ (AbLaw.cst p ⊤ a) = cS p y a :=
  (gs_constFn' p ⊤ (𝟙 Y) y trivial a).trans (by rw [Category.id_comp])

variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}

theorem isSquareDetComparison_scale_sec (a : Kˣ) (hth₀ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b) (lam : Kˣ)
    (h : IsSquareDeterminantComparison ⟨P, hg, rig, hr, th, hth, v, hv⟩ m al b lam) :
    IsSquareDeterminantComparison ⟨P, hg, rig, hr, th', hth', v', hv'⟩ m al b (lam * a ^ (8 * m ^ (4 * P.g + 2))) := by
  obtain ⟨ξ, mu, w, Q, rho, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨ξ, mu, w, (a : K) ^ 4 • Q, rho, h₁, h₂, h₃, h₄, h₅, fun I y J hJ => ?_, ?_⟩
  · have e := h₆ I y J hJ
    simp only [gs_cst'] at e ⊢
    have e₂ : ∀ r : Fin 4, gs (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left y _
        (LB.Sec.f th' (J (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left)) =
        cS (Out.powObj P.A 4).hom y a * gs (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left y _
        (LB.Sec.f th (J (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left)) := fun r => by
      rw [hth₀, gs_mul _ _ _ (hJ _), gs_constFn' _ _ _ _ (hJ _), Over.w]
      rfl
    refine (Finset.prod_congr rfl fun r _ => e₂ r).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg _ e).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, _root_.mul_assoc]
  · rw [Units.val_mul, h₇, Matrix.det_smul, Units.val_pow_eq_pow_val]
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

theorem jac_scale (M : Matrix (Fin P.g) (Fin P.g) K) (hM : ∀ i, IsLieComb (M i) v (v' i)) {n : ℕ}
    (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (z) (c) :
    jac ⟨P, hg, rig, hr, th', hth', v', hv'⟩ s z c = jac ⟨P, hg, rig, hr, th, hth, v, hv⟩ s z c * M.det := by
  unfold jac
  rw [← Matrix.det_transpose M, ← Matrix.det_mul]
  congr 1
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine (snd_valT_comb hv.1 (hM k) z _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact mul_comm _ _

theorem kaVal_scale : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (κ : Kˣ), admitted P.g n l l' al → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → KaVal ⟨P, hg, rig, hr, th, hth, v, hv⟩ n l l' al s κ → ∃ κ' : Kˣ, KaVal ⟨P, hg, rig, hr, th', hth', v', hv'⟩ n l l' al s κ' ∧ a ^ (8 * kaExp P.g n l l') * (κ' : K) = M.det ^ (4 * kaExp P.g n l l') * κ := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M n l l' al s κ hadm hth₀ hM hκ
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hth₀, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have : IsCommMonObj P.A := P.isAb.comm
  have hdet : IsUnit M.det := ((LieComb.lieComb_algebra K P.A P.g v hv.1).2.2.2.2 M v' hv hM).1 hv'
  lift a to Kˣ using ha.isUnit
  obtain ⟨D, hD⟩ := hdet
  obtain ⟨z, ch, b, b', t, t', J, lam, lam', ⟨e₁, e₂, e₃, e₄, e₅⟩, hJ, hb, hb', ht, ht', rfl⟩ := hκ
  refine ⟨_, ⟨z, ch, b, b', t, t', J * D ^ (P.g.factorial * n ^ P.g),
    fun j => lam j * a ^ (8 * (l - j * n) ^ (4 * P.g + 2)),
    fun j => lam' j * a ^ (8 * (l' - j * n) ^ (4 * P.g + 2)), ⟨e₁, e₂, fun k => ?_, e₄, e₅⟩, ?_,
    fun j hj => ⟨(hb j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb j hj).2⟩,
    fun j hj => ⟨(hb' j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb' j hj).2⟩, ht, ht', rfl⟩, ?_⟩
  · rw [jac_scale (th := th) (hth := hth) (hv := hv) M hM, ← hD]
    exact (e₃ k).mul D.isUnit
  · rw [Units.val_mul, hJ, Units.val_pow_eq_pow_val, hD]
    simp only [jac_scale (th := th) (hth := hth) (hv := hv) (th' := th') (hth' := hth') (hv' := hv') M hM]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have key := kaForm_homogeneous K P.g n l l' t t' J 1 a 1 lam lam' (fun _ => 1) (fun _ => 1)
      hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at key
    rw [← hD]
    norm_cast
    rw [← key]
    unfold kaForm kaExp
    generalize tComb P.g n l _ t _ = X
    generalize tComb P.g n l' _ t' _ = X'
    generalize degProd P.g n l l' ^ (3 * P.g + 2) = N
    generalize P.g.factorial * n ^ P.g = F
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
    push_cast [Nat.cast_sub hadm.2.2.1.le]
    module

end GlobalTheory.KaScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulExactOfRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]

abbrev lf (x : KeyIn K) {l : ℕ} (s : RR x l) (c : x.P.L.ι) : Γ(x.P.A.left, x.P.L.U c) := s.f c

def phi (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) (c : x.P.L.ι) :
    Γ(x.P.A.left, x.P.L.U c) := ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * lf x (b k) c

theorem phi_add (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v w : Fin N → K) (c) :
    phi x b (v + w) c = phi x b v c + phi x b w c := by
  simp only [phi, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem phi_zero (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (c) : phi x b 0 c = 0 := by
  simp only [phi, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem phi_sum (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) {A : Type} (S : Finset A)
    (v : A → Fin N → K) (c) : phi x b (∑ i ∈ S, v i) c = ∑ i ∈ S, phi x b (v i) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, phi_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phi_add, ih]

def sec (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) : RR x l where
  f := fun c => phi x b v c
  compat := fun i j => by
    obtain ⟨u, hu⟩ : ∃ u : Γ(x.P.A.left, x.P.L.U i ⊓ x.P.L.U j), u = ((pw x.P.L (l : ℤ)).g i j).val :=
      ⟨_, rfl⟩
    have h : ∀ k, rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) j) :=
      fun k => hu ▸ (b k).compat i j
    have h' : rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [phi, map_sum, map_mul, rs_cst, h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    subst hu
    exact h'

theorem phi_inj (x : KeyIn K) {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) {v w : Fin N → K}
    (h : ∀ c, phi x b v c = phi x b w c) : v = w :=
  (hb (sec x b v)).unique (fun _ => rfl) h

theorem phi_surj (x : KeyIn K) {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) (y : RR x l) :
    ∃ v, ∀ c, lf x y c = phi x b v c := (hb y).exists

theorem phi_mulVec (x : KeyIn K) {n l : ℕ} {s : Fin x.P.g → RR x n}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m)
    (i : Fin x.P.g) {j : ℕ} (hj : j < x.P.g) (v) (c) :
    phi x (b j) ((m i j (j + 1)).mulVec v) c = lf x (s i) c * phi x (b (j + 1)) v c := by
  have h : ∀ k, lf x (s i) c * lf x (b (j + 1) k) c =
      ∑ k', cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c :=
    fun k => hm i j hj k c
  calc phi x (b j) ((m i j (j + 1)).mulVec v) c
      = ∑ k', ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) *
          (cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [phi, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * (lf x (s i) c * lf x (b (j + 1) k) c) := by
        rw [Finset.sum_comm]
        simp only [h, Finset.mul_sum]
    _ = _ := by
        simp only [phi, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff {g : ℕ} {a b : ℕ} (i : Fin g) (M : Fin g → Matrix (Fin a) (Fin b) K) (y : Fin a → K) :
    y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (M i').mulVecLin) ↔
      ∃ t : Fin g → Fin b → K, y = ∑ i' ∈ Finset.univ.filter (· < i), (M i').mulVec (t i') := by
  have e : (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (M i').mulVecLin) =
      ⨆ i' ∈ Finset.univ.filter (· < i), LinearMap.range (M i').mulVecLin := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e, Submodule.mem_iSup_finset_iff_exists_sum]
  constructor
  · rintro ⟨q, h⟩
    choose t ht using fun i' => (q i').2
    refine ⟨t, h.symm.trans (Finset.sum_congr rfl fun i' _ => (ht i').symm)⟩
  · rintro ⟨t, h⟩
    exact ⟨fun i' => ⟨(M i').mulVec (t i'), t i', rfl⟩, h.symm⟩

theorem koszul_exact_of_regular : ∀ (K : Type) [CommRing K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ (i : Fin x.P.g) (j : ℕ), j + 1 + i ≤ x.P.g → ∀ (y : RR x (l - (j + 1) * n)) (ta : Fin x.P.g → RR x (l - (j + 1) * n)), (∀ c, (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) * (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (ta i').f c)) → ∃ tb : Fin x.P.g → RR x (l - (j + 2) * n), ∀ c, (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (tb i').f c)) → ∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  intro K _ x n l s b m _ hb hm hreg
  refine _root_.GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular K x.P.g (fun j => (l - j * n) ^ x.P.g) m ?_ ?_
  · intro i i' j hj
    refine Matrix.ext_of_mulVec_single fun k => ?_
    refine phi_inj x (hb j (by omega)) fun c => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, phi_mulVec x hm i (by omega),
      phi_mulVec x hm i' (by omega), phi_mulVec x hm i' (by omega), phi_mulVec x hm i (by omega)]
    ring
  · intro i j y hj hy
    have hjg : j < x.P.g := by omega
    obtain ⟨t, ht⟩ := (mem_iff i (fun i' => m i' j (j + 1)) _).1 hy
    refine (mem_iff i (fun i' => m i' (j + 1) (j + 2)) _).2 ?_
    obtain ⟨tb, htb⟩ := hreg i j hj (sec x (b (j + 1)) y) (fun i' => sec x (b (j + 1)) (t i')) (fun c => by
      change lf x (s i) c * phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * phi x (b (j + 1)) (t i') c
      rw [← phi_mulVec x hm i hjg, ht, phi_sum]
      exact Finset.sum_congr rfl fun i' _ => phi_mulVec x hm i' hjg _ _)
    have htb' : ∀ c, phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * lf x (tb i') c := htb
    by_cases h2 : j + 2 ≤ x.P.g
    · choose u hu using fun i' => phi_surj x (hb (j + 2) h2) (tb i')
      refine ⟨u, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', phi_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hu]
      exact (phi_mulVec x hm i' (j := j + 1) (by omega) _ _).symm
    · have he : Finset.univ.filter (· < i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun i' _ h => ?_
        have : (i' : ℕ) < i := h
        omega
      refine ⟨0, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', he, Finset.sum_empty, Finset.sum_empty, phi_zero]

end GlobalTheory.KeyKa.KosBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemSpanOfForallGermMemSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory

private theorem gs_id_eq_germ (X : Scheme.{0}) (V : X.Opens) (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = X.presheaf.germ V y hy a := by
  rw [gs_eq (𝟙 X) y V hy a]
  rfl

theorem mem_span_of_forall_germ_mem_span : ∀ (X : Scheme.{0}) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (r : Γ(X, V)), IsAffineOpen V → (∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i))) → r ∈ Ideal.span (Set.range f) := by
  intro X V J f r hV h
  rw [hV.mem_ideal_iff]
  intro y hy
  rw [Ideal.map_span, ← Set.range_comp]
  by_cases hz : ∀ i, y ∉ X.basicOpen (f i)
  · have hr := h y hy hz
    simp only [gs_id_eq_germ X V y hy] at hr
    exact hr
  · simp only [not_forall, not_not] at hz
    obtain ⟨i, hi⟩ := hz
    rw [X.mem_basicOpen (f i) y hy] at hi
    have hmem : X.presheaf.germ V y hy (f i) ∈ Ideal.span (Set.range (⇑(X.presheaf.germ V y hy).hom ∘ f)) :=
      Ideal.subset_span ⟨i, rfl⟩
    rw [Ideal.eq_top_of_isUnit_mem _ hmem hi]
    trivial

end GlobalTheory
end

