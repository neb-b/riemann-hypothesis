module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertDataEqOfLbIsoPowPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

private lemma mul_mul_pow_mul_inv_pow_eq {A B G G' c c' : ℂ} (m n : ℕ) (h : A * G' ^ m = G ^ n * B)
    (hGc : G * c ≠ 0) : A * (G' * c') ^ m * ((G * c) ^ n)⁻¹ = B * c' ^ m * (c ^ n)⁻¹ := by
  have hGn : G ^ n ≠ 0 := pow_ne_zero n (left_ne_zero_of_mul hGc)
  rw [mul_pow, mul_pow, mul_inv,
    show A * (G' ^ m * c' ^ m) * ((G ^ n)⁻¹ * (c ^ n)⁻¹) = A * G' ^ m * (G ^ n)⁻¹ * (c' ^ m * (c ^ n)⁻¹) by ring,
    h, mul_comm (G ^ n) B, mul_inv_cancel_right₀ hGn]
  ring

private lemma mul_pow_mul_inv_pow_eq_of_factor {s a b a' b' x x' E E' : ℂ} (m n : ℕ) (ha : a = x * E * b)
    (ha' : a' = x' * E' * b') (hE : E' ^ m = E ^ n) (hx : x ≠ 0) (hx' : x' ≠ 0) (hEne : E ≠ 0)
    (hb : b ≠ 0) (hb' : b' ≠ 0) :
    s * b' ^ m * (b ^ n)⁻¹ = x ^ n * (x' ^ m)⁻¹ * (s * a' ^ m * (a ^ n)⁻¹) := by
  subst ha ha'
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hE]
  field_simp


open PullHermitian in
theorem semicharacter_pull_eq_of_lbIso_pow :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ₀ : ∀ l ∈ u.Λ, F l ∈ u'.Λ), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hΛ₀ l l.2⟩ ^ m := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hΛ₀ hex m n hiso

  have hH := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex m n hiso
  obtain ⟨w, hw⟩ := hiso
  unfold HolUnif.IsAH at hu hu'
  have := u.discrete
  have hxf : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by rw [hex z]; rfl

  let φ : L.ι × L'.ι → (Fin g → ℂ) → ℂ := fun p z =>
    valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val * u'.fr p.2 (F z) ^ m * (u.fr p.1 z ^ n)⁻¹
  let V : L.ι × L'.ι → Set (Fin g → ℂ) := fun p =>
    {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1 ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U p.2}
  have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  have hV : ∀ p, IsOpen (V p) := fun p =>
    (u.hol (L.U p.1) 0).1.inter ((u'.hol (L'.U p.2) 0).1.preimage hFc)
  have hcov : ∀ z, ∃ p, z ∈ V p := fun z => by
    obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
    obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
    exact ⟨(i, j), hi, hj⟩
  have hdiv : ∀ i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f.left) m)).U (idx f.left m n i j) :=
    fun i j z hi hj => idx_chart _ f.left m n i j hi (by rw [← hxf]; exact hj)
  have hφd : ∀ p, DifferentiableOn ℂ (φ p) (V p) := fun p => by
    have h1 := ((u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2).mono
      (fun z (hz : z ∈ V p) => hdiv p.1 p.2 z hz.1 hz.2)
    have h2 : DifferentiableOn ℂ (fun z => u'.fr p.2 (F z)) (V p) :=
      (u'.fr_hol p.2).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn
        (fun z hz => hz.2)
    have h3 : DifferentiableOn ℂ (fun z => u.fr p.1 z) (V p) := (u.fr_hol p.1).mono (fun z hz => hz.1)
    exact (h1.mul (h2.pow m)).mul ((h3.pow n).inv fun z hz => pow_ne_zero _ (u.fr_ne _ z hz.1))
  have hagree : ∀ p q z, z ∈ V p → z ∈ V q → φ p z = φ q z := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hi, hj⟩ ⟨hi', hj'⟩
    have hj₁ : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j := by rw [← hxf]; exact hj
    have hj₁' : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j' := by rw [← hxf]; exact hj'
    have hval := val_iso_pow (u.ex z).left f.left m n w hw i i' j j' hi hi' hj₁ hj₁'
    have hc := u.fr_compat i i' z (inf_of _ hi hi')
    have hc' := u'.fr_compat j j' (F z) (inf_of _ hj hj')
    rw [hxf] at hc'
    have hne : u.fr i z ≠ 0 := u.fr_ne i z hi
    simp only [φ]
    rw [hc] at hne ⊢
    rw [hc']
    exact mul_mul_pow_mul_inv_pow_eq m n hval hne
  obtain ⟨r, hr, hrφ⟩ := exists_glue V hV hcov φ hφd hagree
  have hφne : ∀ i j z, z ∈ V (i, j) → φ (i, j) z ≠ 0 := by
    intro i j z hz
    have hd := hdiv i j z hz.1 hz.2
    simp only [φ]
    rw [valAt'_eq_unitVal _ hd]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne j _ hz.2)))
      (inv_ne_zero (pow_ne_zero _ (u.fr_ne i z hz.1)))
  have hr_ne : ∀ z, r z ≠ 0 := fun z => by
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    rw [hrφ _ z hp]
    exact hφne i j z hp
  have hexl : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have hexl' : ∀ (l : u.Λ) z, u'.ex (F (z + l)) = u'.ex (F z) := fun l z => by
    rw [map_add (f := _), u'.ex_add, (u'.ker _).2 (hΛ₀ _ l.2), _root_.mul_one]
  have hχne : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using hu.2.2.1 l
  have hχne' : ∀ l, χ' l ≠ 0 := fun l h0 => by simpa [h0] using hu'.2.2.1 l
  let c : u.Λ → ℂ := fun l => χ l ^ n * (χ' ⟨F l, hΛ₀ l l.2⟩ ^ m)⁻¹
  have h0 : ∀ a b : Fin g → ℂ, hermForm (0 : Matrix (Fin g) (Fin g) ℂ) a b = 0 := fun a b => by
    simp [hermForm]
  have hper : ∀ (l : u.Λ) z, r (z + l) =
      c l * Complex.exp (Real.pi * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z (l : Fin g → ℂ) +
        Real.pi / 2 * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℂ) (l : Fin g → ℂ)) * r z := by
    intro l z
    simp only [h0, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one]
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    have hzl : z + l ∈ V (i, j) := ⟨by rw [hexl]; exact hp.1, by rw [hexl']; exact hp.2⟩
    rw [hrφ _ _ hzl, hrφ _ _ hp]
    have ha := hu.2.2.2 l i z hp.1
    have ha' := hu'.2.2.2 ⟨F l, hΛ₀ l l.2⟩ j (F z) hp.2
    dsimp only at ha'
    have hb : u.fr i (z + l) ≠ 0 := u.fr_ne i _ hzl.1
    have hb' : u'.fr j (F z + F l) ≠ 0 := u'.fr_ne j _ (by rw [← map_add (f := _)]; exact hzl.2)
    simp only [φ, c]
    rw [hexl l z, map_add (f := _)]
    refine mul_pow_mul_inv_pow_eq_of_factor m n ha ha' ?_ (hχne l) (hχne' _) (Complex.exp_ne_zero _) hb hb'
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have e1 := hH z l
    have e2 := hH l l
    simp only [hermForm] at e1 e2
    linear_combination (Real.pi : ℂ) * e1 + ((Real.pi : ℂ) / 2) * e2
  have hcn : ∀ l, ‖c l‖ = 1 := fun l => by
    simp only [c, norm_mul, norm_inv, norm_pow, hu.2.2.1 l, hu'.2.2.1, one_pow, inv_one, _root_.mul_one]
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 c r
    Matrix.isHermitian_zero hcn hr hr_ne hper).2.1
  intro l
  have hl := key l
  simp only [c] at hl
  exact (mul_inv_eq_one₀ (pow_ne_zero _ (hχne' _))).1 hl

theorem appellHumbert_data_eq_of_lbIso_pow_pull :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ) (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (n : ℕ), 0 < n → L.IsLB → L'.IsLB → u.IsAH Hm χ → u'.IsAH Hm' χ' → (∀ z, u'.ex (F z) = u.ex z ≫ f) → LBIso (lbPow L n) (lbPow (L'.pull f.left) n) → (∀ z w, hermForm Hm z w = hermForm Hm' (F z) (F w)) ∧ ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hF l l.2⟩ ^ n := by
  intro A A' _ _ L L' g g' u u' Hm Hm' χ χ' f F hF n hn hL hL' hu hu' hex hiso
  have hiso' := hiso.symm
  refine ⟨fun z w => ?_,
    semicharacter_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF hex n n hiso'⟩
  have h := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex n n hiso' z w
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_left_cancel₀ hn' h).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CechPrimitive
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Primitive

open GlobalTheory.KuennethOne

variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}

theorem rsT_eq_rs {O₀ O : A.Opens} (s : Γ(A, O₀)) (h : O ≤ O₀) : rsT s O = rs h s := by
  rw [rsT, dif_pos h]
  rfl

theorem pbT_eq (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀) :
    pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  exact dif_pos h

theorem rs_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀)
    (h' : O' ≤ O) : rs h' (pbT f s O) = pbT f s O' := by
  rw [pbT_eq f s h, pbT_eq f s (h'.trans h)]
  show (T.presheaf.map (homOfLE h').op).hom ((f.appLE O₀ O h).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem app_pbT (r : T ⟶ Z) (f : Z ⟶ A) (g : T ⟶ A) (e : r ≫ f = g) {O₀ : A.Opens} (s : Γ(A, O₀))
    {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : (r.app O).hom (pbT f s O) = pbT g s (r ⁻¹ᵁ O) := by
  subst e
  rw [pbT_eq f s h, pbT_eq (r ≫ f) s (r.preimage_mono h)]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem le_pre_inf (f : T ⟶ A) {N : T.Opens} {V W : A.Opens} (h : N ≤ f ⁻¹ᵁ V) (h' : N ≤ f ⁻¹ᵁ W) :
    N ≤ f ⁻¹ᵁ (V ⊓ W) :=
  fun _ hx => ⟨h hx, h' hx⟩

private lemma pbT_add' (f : T ⟶ A) {O₀ : A.Opens} (s s' : Γ(A, O₀)) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O₀) : pbT f (s + s') N = pbT f s N + pbT f s' N := by
  simp only [pbT_eq f _ hN, map_add (f := _)]

private lemma pbT_rsT' (f : T ⟶ A) {O₀ O : A.Opens} (s : Γ(A, O₀)) (hO : O ≤ O₀) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O) : pbT f (rsT s O) N = pbT f s N := by
  rw [rsT_eq_rs s hO, pbT_eq f _ hN, pbT_eq f s (hN.trans (f.preimage_mono hO))]
  show (f.appLE O N hN).hom ((A.presheaf.map (homOfLE hO).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem pbT_coc (hc : IsCoc U c) (f : T ⟶ A) (i j k : I) {N : T.Opens} (hi : N ≤ f ⁻¹ᵁ U i)
    (hj : N ≤ f ⁻¹ᵁ U j) (hk : N ≤ f ⁻¹ᵁ U k) :
    pbT f (c i j) N + pbT f (c j k) N = pbT f (c i k) N := by
  have hN : N ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := le_pre_inf f (le_pre_inf f hi hj) hk
  have l1 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have l2 : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l3 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [← pbT_rsT' f (c i j) l1 hN, ← pbT_rsT' f (c j k) l2 hN, ← pbT_rsT' f (c i k) l3 hN,
    ← pbT_add' f _ _ hN, hc i j k]

theorem exists_split (hc : IsCoc U c) (f g : T ⟶ A) {i₀ : I} (hg : ⊤ ≤ g ⁻¹ᵁ U i₀) {J : Type}
    (i₁ i₂ i₃ : J → I) (N : J → T.Opens) (h₁ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₁ a))
    (h₂ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₂ a)) (h₃ : ∀ a, N a ≤ g ⁻¹ᵁ U (i₃ a)) :
    ∃ ψ : ∀ a, Γ(T, N a), ∀ a b (M : T.Opens) (ha : M ≤ N a) (hb : M ≤ N b),
      pbT f (c (i₁ a) (i₁ b)) M - pbT f (c (i₂ a) (i₂ b)) M - pbT g (c (i₃ a) (i₃ b)) M =
        rs ha (ψ a) - rs hb (ψ b) := by
  refine ⟨fun a => pbT f (c (i₁ a) (i₂ a)) (N a) - pbT g (c (i₃ a) i₀) (N a), ?_⟩
  intro a b M ha hb
  have hg' : M ≤ g ⁻¹ᵁ U i₀ := le_top.trans hg
  have e1 := pbT_coc hc f (i₁ a) (i₂ a) (i₁ b) (ha.trans (h₁ a)) (ha.trans (h₂ a)) (hb.trans (h₁ b))
  have e2 := pbT_coc hc f (i₂ a) (i₁ b) (i₂ b) (ha.trans (h₂ a)) (hb.trans (h₁ b)) (hb.trans (h₂ b))
  have e3 := pbT_coc hc g (i₃ a) i₀ (i₃ b) (ha.trans (h₃ a)) hg' (hb.trans (h₃ b))
  have e4 := pbT_coc hc g (i₃ b) i₀ (i₃ b) (hb.trans (h₃ b)) hg' (hb.trans (h₃ b))
  have e5 := pbT_coc hc g (i₃ b) (i₃ b) (i₃ b) (hb.trans (h₃ b)) (hb.trans (h₃ b)) (hb.trans (h₃ b))
  have r1 := rs_pbT f (c (i₁ a) (i₂ a)) (le_pre_inf f (h₁ a) (h₂ a)) ha
  have r2 := rs_pbT f (c (i₁ b) (i₂ b)) (le_pre_inf f (h₁ b) (h₂ b)) hb
  have r3 := rs_pbT g (c (i₃ a) i₀) (le_pre_inf g (h₃ a) (le_top.trans hg)) ha
  have r4 := rs_pbT g (c (i₃ b) i₀) (le_pre_inf g (h₃ b) (le_top.trans hg)) hb
  simp only [map_sub, r1, r2, r3, r4]
  linear_combination e2 - e1 + e3 - e4 - e5

theorem iSup_triple (hU : ⨆ i, U i = ⊤) (m p q : Z ⟶ A) :
    ⨆ α : I × I × I, m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2 = ⊤ := by
  have cov : ∀ y : A, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨i, hi⟩ := cov (m x)
  obtain ⟨j, hj⟩ := cov (p x)
  obtain ⟨k, hk⟩ := cov (q x)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩

private lemma preimage_le_preimage_of_comp_eq {X₁ X₂ X₃ : Scheme.{0}} (s : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (g : X₁ ⟶ X₃)
    (e : s ≫ m = g) {W : X₂.Opens} {O : X₃.Opens} (h : W ≤ m ⁻¹ᵁ O) : s ⁻¹ᵁ W ≤ g ⁻¹ᵁ O := by
  subst e
  intro x hx
  show (s ≫ m) x ∈ O
  rw [Scheme.Hom.comp_apply]
  exact h hx

private lemma presheaf_map_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) :
    (T.presheaf.map (homOfLE h').op).hom (pbT f s O) = pbT f s O' :=
  rs_pbT f s h h'

set_option maxHeartbeats 1600000 in
private theorem cech_coboundary_mul_sub_fst_sub_snd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) := by
  intro hL _ _ K _ P₀ I U c hU hc
  have : IsProper P₀.A.hom := P₀.isAb.proper
  have hsub : Subsingleton (𝟙_ (Over (Sp K))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let _ : Inhabited (𝟙_ (Over (Sp K))).left := inferInstanceAs (Inhabited (Spec (CommRingCat.of K)))
  have hbij : Function.Bijective P₀.A.hom.appTop.hom := hL.globalFns _ P₀.A P₀.isAb
  let e : 𝟙_ (Over (Sp K)) ⟶ P₀.A := MonObj.one
  let g₀ : P₀.A.left ⟶ P₀.A.left := (toUnit P₀.A ≫ e).left
  let m := (fst P₀.A P₀.A * snd P₀.A P₀.A).left
  let p := (fst P₀.A P₀.A).left
  let q := (snd P₀.A P₀.A).left

  have hpt : ∀ x : P₀.A.left, g₀ x = e.left default := by
    intro x
    show ((toUnit P₀.A).left ≫ e.left) x = _
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have cov : ∀ y : P₀.A.left, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨i₀, hi₀⟩ := cov (e.left default)
  have hg : ⊤ ≤ g₀ ⁻¹ᵁ U i₀ := fun x _ => by
    show g₀ x ∈ U i₀
    rw [hpt x]
    exact hi₀

  have es_m : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (mul_one (𝟙 P₀.A))
  have es_p : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ p = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have es_q : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ q = g₀ := by
    rw [← Over.comp_left, lift_snd]
  have et_m : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (one_mul (𝟙 P₀.A))
  have et_p : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ p = g₀ := by
    rw [← Over.comp_left, lift_fst]
  have et_q : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ q = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  let V : I × I × I → (P₀.A ⊗ P₀.A).left.Opens := fun α =>
    m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2
  have hVm : ∀ α, V α ≤ m ⁻¹ᵁ U α.1 := fun α => inf_le_left.trans inf_le_left
  have hVp : ∀ α, V α ≤ p ⁻¹ᵁ U α.2.1 := fun α => inf_le_left.trans inf_le_right
  have hVq : ∀ α, V α ≤ q ⁻¹ᵁ U α.2.2 := fun α => inf_le_right
  obtain ⟨ψ, hK⟩ := kuenneth_injective K P₀.A P₀.A e e inferInstance inferInstance inferInstance
    inferInstance hbij hbij (I × I × I) V (iSup_triple hU m p q)
    (fun a b => pbT m (c a.1 b.1) (V a ⊓ V b) - pbT p (c a.2.1 b.2.1) (V a ⊓ V b) -
      pbT q (c a.2.2 b.2.2) (V a ⊓ V b))
    (by
      intro a b d
      have w1 : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
      have w2 : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
      have w3 : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
      simp only [map_sub]
      rw [presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm b)) (inf_le_right.trans (hVm d))),
        presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp b)) (inf_le_right.trans (hVp d))), presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq b)) (inf_le_right.trans (hVq d))),
        presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm d))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp d))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq d)))]
      have cm := pbT_coc hc m a.1 b.1 d.1 (w1.trans (hVm a)) (w2.trans (hVm b)) (w3.trans (hVm d))
      have cp := pbT_coc hc p a.2.1 b.2.1 d.2.1 (w1.trans (hVp a)) (w2.trans (hVp b)) (w3.trans (hVp d))
      have cq := pbT_coc hc q a.2.2 b.2.2 d.2.2 (w1.trans (hVq a)) (w2.trans (hVq b)) (w3.trans (hVq d))
      linear_combination cm - cp - cq)
    (by
      let s := (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.1)
        (fun α => α.2.2) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ es_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s p _ es_p (hVp α)) (fun α => preimage_le_preimage_of_comp_eq s q _ es_q (hVq α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) es_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p (𝟙 _) es_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q g₀ es_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b)))]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
    (by
      let s := (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.2)
        (fun α => α.2.1) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ et_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s q _ et_q (hVq α)) (fun α => preimage_le_preimage_of_comp_eq s p _ et_p (hVp α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) et_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p g₀ et_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q (𝟙 _) et_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), sub_right_comm]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
  unfold IsCob
  refine ⟨fun a => -ψ a, fun a b => (hK a b).trans ?_⟩
  rw [rsT_eq_rs _ inf_le_right, rsT_eq_rs _ inf_le_left, map_neg, map_neg]
  exact (neg_sub_neg _ _).symm

theorem cech_primitive : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) :=
  cech_coboundary_mul_sub_fst_sub_snd

end GlobalTheory.KS.Primitive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChiEqOneOrOfSym
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaUnifCompare

open GlobalTheory.FrameValue CubeValues SymmetricSemicharacter EigenNorm

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem chi_neg_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨U, hU, s, hs⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    rintro x -
    refine ⟨⟨x, ?_⟩, rfl⟩
    have e : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    show A.hom x ∈ U
    rw [e]; exact hU
  obtain ⟨p, hp⟩ : ∃ p : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, p ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hz : ∀ w, IsLift u (K := Fin 2) ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι]
      ((u.ex w).left ≫ p) ![-w, w] := fun w k => by
    fin_cases k
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-w)).left
      rw [Category.assoc, reassoc_of% hp]
      exact ex_neg_left u w
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι = (u.ex w).left
      rw [Category.assoc, hp, Category.comp_id]
  have hd : Differentiable ℂ fun w => genVal u hL s ((u.ex w).left ≫ p) ![-w, w] :=
    differentiable_genVal hL hs p (q := id) differentiable_id (z := fun w => ![-w, w])
      (fun k => by fin_cases k <;> simp <;> fun_prop) hz
  have hper : ∀ (l : u.Λ) w, genVal u hL s ((u.ex (w + l)).left ≫ p) ![-(w + l), w + l] =
      χ (-l) / χ l * genVal u hL s ((u.ex w).left ≫ p) ![-w, w] := fun l w => by
    have e₂ : ![-(w + l), w + l] = fun k => ![-w, w] k + ((![-l, l] : Fin 2 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [add_comm]
    rw [ex_add_period u w l l.2, e₂, genVal_add_period hL h s (hz w)]
    congr 1
    have n := chi_ne_zero h l
    simp [ahFactor, hermForm_neg_left, hermForm_neg_right]
    field_simp
  have hc := const_of_norm_periodic u hd (fun l w => by
    rw [hper, norm_mul, norm_div, h.2.2.1, h.2.2.1, div_one, _root_.one_mul])
  have e := hper l 0
  rw [hc _ 0] at e
  exact (div_eq_one_iff_eq (chi_ne_zero h l)).1
    (mul_right_cancel₀ (genVal_ne_zero hL s (hz 0)) (e.symm.trans (_root_.one_mul _).symm))

theorem chi_eq_one_or_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ l = 1 ∨ χ l = -1 := by
  have e := chi_add hL h l (-l)
  have hi : (hermForm Hm l l).im = 0 := Complex.conj_eq_iff_im.1 (hermForm_conj Hm h.1 l l).symm
  rw [add_neg_cancel, chi_zero hL h, chi_neg_of_sym hL hs h, Submodule.coe_neg, hermForm_neg_right, Complex.neg_im,
    hi] at e
  exact mul_self_eq_one_iff.1 (by simpa using e.symm)

end GlobalTheory.ThetaUnifCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmGeneratorSqQuadraticEq
section
namespace GlobalTheory.CMGeneratorSquareModuli

open NumberField

theorem cm_generator_sq_quadratic_eq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ k : ℤ, H.w0 * H.w0 = H.w0 - (k : NumberField.RingOfIntegers E) := by
  have hm := H.d_mod
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (H.d : ℤ) + 1 = 4 * k := ⟨((H.d : ℤ) + 1) / 4, by omega⟩
  refine ⟨k, ?_⟩
  have hkc : (H.d : NumberField.RingOfIntegers E) + 1 = 4 * (k : NumberField.RingOfIntegers E) := by
    have := congrArg (fun z : ℤ => (z : NumberField.RingOfIntegers E)) hk
    push_cast at this
    exact this
  have h4 : (4 : NumberField.RingOfIntegers E) * (H.w0 * H.w0 - (H.w0 - (k : NumberField.RingOfIntegers E))) = 0 := by
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hkc
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · exact sub_eq_zero.mp h

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E},
    a ∈ Algebra.adjoin ℤ ({ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H} : Set (NumberField.RingOfIntegers E)) →
    ∃ u v : ℤ, a = (u : NumberField.RingOfIntegers E) + (v : NumberField.RingOfIntegers E) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  obtain ⟨k, hk⟩ := cm_generator_sq_quadratic_eq H
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    exact ⟨u1 + u2, v1 + v2, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    refine ⟨u1 * u2 - v1 * v2 * k, u1 * v2 + u2 * v1 + v1 * v2, ?_⟩
    push_cast
    linear_combination ((v1 : NumberField.RingOfIntegers E) * v2) * hk

end GlobalTheory.CMGeneratorSquareModuli
end

