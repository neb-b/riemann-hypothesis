module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PGFine
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem diag_comp' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · have h1 := hs.1
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (fst A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := hs.2
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (snd A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

private theorem diag_lbIso' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂)
    {P' : LB (G2 A').left} {P : LB (G2 A).left} (hP' : P'.IsLB) (hP : P.IsLB) (hpol : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  have h₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp hpol _ (diag_comp' hs).symm
  have h₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP _)) φ rfl
  exact LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) h₁ h₂.symm

theorem gFine_of : GFine := by
  intro p _ D b gb N M X ρ h hL f hf hG hpts hfine
  obtain ⟨φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ := hG
  have hX : SmoothOfRelativeDimension D.g X.univ.A.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} D.g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.g) hcart.1 h
  have hL' : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB := pull_isLB X.univ.isLB _
  have hB := diag_lbIso' hsq X.univ.isLB M.univ.isLB hpol
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap, Sp]
  have key := fun (D' : PLat D.O D.inv) (t : D.La → D'.La) P (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ)) =>
    _root_.GlobalTheory.unifAt_correspond_of_cartesian D.O D.inv D.g ρ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) D.La (M.univ.fam h hL) (gfam X.univ hX hL') N f φA
      hcart hact hB heta D' t P y hy (by
        show (y ≫ f) ≫ M.s = _
        rw [Category.assoc, hf, hy])
  refine ⟨hX, hL', ?_, ?_, ?_⟩
  · intro (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ))
    have hy' : (y ≫ f) ≫ M.s = spMap (RingHom.id ℂ) := by rw [Category.assoc, hf, hy]
    obtain ⟨D', t, P, e, hC, hU⟩ := hfine.pts (y ≫ f) hy'
    obtain ⟨e', he', -⟩ := (key D' t P y hy).2 e hU
    exact ⟨D', t, P, e', hC, he'⟩
  · intro D' t P hC hP
    obtain ⟨y', e, hU⟩ := hfine.occ D' t P hC hP
    obtain ⟨y, ⟨hy, rfl⟩, -⟩ := hpts y' (hU.1)
    obtain ⟨e', he', -⟩ := (key D' t P y (hy.trans hid.symm)).2 e hU
    exact ⟨y, e', he'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w u hw hQ
    obtain ⟨e₁, he₁, -⟩ := (key D' t P y hU.1).1 e hU
    obtain ⟨e₂, he₂, -⟩ := (key D'' t' P' y' hU'.1).1 e' hU'
    have hyy := hfine.sep D' D'' t t' P P' (y ≫ f) (y' ≫ f) e₁ e₂ he₁ he₂ w u hw hQ
    obtain ⟨z, -, huniq⟩ := hpts (y ≫ f) he₁.1
    have a₁ : y = z := huniq y ⟨hU.1.trans hid, rfl⟩
    have a₂ : y' = z := huniq y' ⟨hU'.1.trans hid, hyy.symm⟩
    rw [a₁, a₂]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PInvMin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem aeval_inv_reverse_eq_zero_iff {K A : Type} [Field K] [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) :
    Polynomial.aeval (↑u⁻¹ : A) f.reverse = 0 ↔ Polynomial.aeval (u : A) f = 0 := by
  let S : Subalgebra K A := Algebra.adjoin K {(u : A), ↑u⁻¹}
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin K (by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
  letI : CommRing S := { mul_comm := isMulCommutative_iff.mp inferInstance }
  let x : S := ⟨u, Algebra.subset_adjoin (by simp)⟩
  let y : S := ⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩
  letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩
  have key := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f
  have h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse) :=
    Polynomial.aeval_algHom_apply S.val y f.reverse
  have h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f) :=
    Polynomial.aeval_algHom_apply S.val x f
  rw [h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective,
    Polynomial.aeval_def, Polynomial.aeval_def]
  exact key

private theorem squarefree_mirror {F : Type} [Field F] (f : F[X]) (h : Squarefree f) :
    Squarefree f.mirror := by
  intro r hr
  obtain ⟨s, hs⟩ := hr
  have hf : f = r.mirror * r.mirror * s.mirror := by
    rw [← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs,
      Polynomial.mirror_mirror]
  have hu : IsUnit r.mirror := h _ ⟨_, hf⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.mirror_zero] at hu
    exact not_isUnit_zero hu
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rw [Polynomial.degree_eq_natDegree hr0]
  rw [Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0),
    Polynomial.mirror_natDegree] at hu
  exact hu

private theorem separable_reverse_of_coeff_zero_ne_zero {K : Type} [Field K] (f : K[X]) (h0 : f.coeff 0 ≠ 0)
    (hs : f.Separable) : f.reverse.Separable := by
  rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]
  have hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) =
      (f.map (algebraMap K (AlgebraicClosure K))).mirror := by
    have htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0 :=
      Polynomial.natTrailingDegree_eq_zero.mpr
        (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))
    rw [Polynomial.mirror, htd, pow_zero, _root_.mul_one]
    simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]
  rw [hm, PerfectField.separable_iff_squarefree]
  exact squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree

theorem UpperTheory.Gal.W2.invMin_of :
    UpperTheory.Gal.W2.InvMin := by
  intro K A _ _ _ _ _ u
  have hint : ∀ v : Aˣ, IsIntegral K (v : A) := fun v => .of_finite K _
  have hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0 := by
    intro v h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hne := minpoly.ne_zero (hint v)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hne hq
    have hev : Polynomial.aeval (v : A) q = 0 := by
      have := minpoly.aeval K (v : A)
      rw [hq, map_mul, Polynomial.aeval_X] at this
      simpa using congrArg (fun z => (↑v⁻¹ : A) * z) this
    have hdeg := minpoly.degree_le_of_ne_zero K (v : A) hq0 hev
    have h2 := Polynomial.natDegree_le_natDegree hdeg
    rw [hq, Polynomial.natDegree_X_mul hq0] at h2
    omega
  set p := minpoly K (u : A) with hp
  have htd : p.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))
  have hdegrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htd, Nat.sub_zero]
  have hinvMonic : (invPoly p).Monic := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]
  have hinvDeg : (invPoly p).natDegree = p.natDegree := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]
  have hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0 := by
    show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0
    rw [map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]
  have heq : minpoly K (↑u⁻¹ : A) = invPoly p := by
    refine (minpoly.unique K _ hinvMonic hinvEval ?_).symm
    intro q hqm hqe
    have hq0 : q ≠ 0 := hqm.ne_zero
    have h1 : Polynomial.aeval (u : A) q.reverse = 0 := by
      have := (aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe
      simpa using this
    have h2 := minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1
    have h3 := Polynomial.natDegree_le_natDegree h2
    have h4 := Polynomial.reverse_natDegree_le q
    rw [Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]
    exact_mod_cast h3.trans h4
  refine ⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩
  rw [heq]
  have hrev : p.reverse.Separable := separable_reverse_of_coeff_zero_ne_zero p (hc u) hs
  refine hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩
  show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)
  rw [_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u),
    Polynomial.C_1, _root_.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (x a b : Fin g → ℂ) :
    hermForm M x (a + b) = hermForm M x a + hermForm M x b := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

private theorem herm_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (a b y : Fin g → ℂ) :
    hermForm M (a + b) y = hermForm M a y + hermForm M b y := by
  simp [hermForm, add_dotProduct]

private theorem herm_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x a : Fin g → ℂ) :
    hermForm M x (c • a) = star c * hermForm M x a := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (a y : Fin g → ℂ) :
    hermForm M (c • a) y = c * hermForm M a y := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

private theorem herm_sub_smul {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x y : Fin g → ℂ) :
    hermForm (H₁ - t • H₂) x y = hermForm H₁ x y - t * hermForm H₂ x y := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

private theorem real_smul_eq {g : ℕ} (c : ℝ) (a : Fin g → ℂ) : c • a = (c : ℂ) • a := by
  ext i; simp

private theorem herm_im_zero {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm M x y).im = 0) (z w : Fin g → ℂ) :
    (hermForm M z w).im = 0 := by
  have key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0 := by
    intro w hw z
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [herm_add_left]; simp [ha, hb]
    | smul c a _ ha => rw [real_smul_eq, herm_smul_left]; simp [ha]
  have hw : w ∈ Submodule.span ℝ s := by rw [hs]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy => exact key y hy z
  | zero => simp [hermForm]
  | add a b _ _ ha hb => rw [herm_add_right]; simp [ha, hb]
  | smul c a _ ha => rw [real_smul_eq, herm_smul_right]; simp [ha]

private theorem bil_dvd {M : Type} [AddCommGroup M] (Bf : LinearMap.BilinForm ℤ M) (n : ℕ) (x y e e' : M) :
    (n : ℤ) ∣ Bf (x + n • e) (y + n • e') - Bf x y := by
  refine ⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩
  simp [map_add (f := _), map_nsmul, LinearMap.add_apply, nsmul_eq_mul]
  ring

private theorem form_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf) (n : ℕ)
    {a a' b b' : D.La} {w w' : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) (hw' : w' ∈ LaHat D)
    (e : L.actG h (inAf D a) = inAf D b + n • w) (e' : L.actG h (inAf D a') = inAf D b' + n • w') :
    ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
  have h1 := MultScale.EFA_actG L h (inAf D a) (inAf D a')
  rw [e, e', MultScale.EFA_inAf] at h1
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    MultScale.EFA_inAf] at h1
  have hn : IsIntAf (n : AfP p) := by
    have := MultScale.isIntAf_intCast (p := p) (n : ℤ)
    simpa using this
  refine ⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') +
    (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩
  · exact MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add
      (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw')
      (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b')))
      (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))
  · linear_combination h1

private theorem cross_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (n : ℤ) ∣ D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  unfold IsWit at hf hf''
  have hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La,
      (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧
      (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧
      ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
        ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
    intro x x'
    obtain ⟨a, e, rfl⟩ := (hf.2 n hn hc).2.2.2.1 x
    obtain ⟨a', e', rfl⟩ := (hf.2 n hn hc).2.2.2.1 x'
    obtain ⟨b, E, hb⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a))
    obtain ⟨b', E', hb'⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a'))
    obtain ⟨w, hw, hwe⟩ := (hyp n hn hc a b).1 ⟨E, hb⟩
    obtain ⟨w', hw', hwe'⟩ := (hyp n hn hc a' b').1 ⟨E', hb'⟩
    refine ⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩
    · have h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e) := by
        rw [map_add (f := _), map_nsmul, hb, smul_add, add_assoc]
      have h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e') := by
        rw [map_add (f := _), map_nsmul, hb', smul_add, add_assoc]
      rw [h1, h2]
      exact (Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm
    · exact (Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm
  obtain ⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩ := hX u₁ u₂
  obtain ⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩ := hX u₃ u₄
  have hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2 := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _
      (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))
    · rw [sub_eq_add_neg]
      exact MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _))
        (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))
    · rw [map_intCast]
      push_cast
      linear_combination ((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34
  have h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) -
      nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hZ
    exact ⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩
  exact Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)

private theorem cross {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) :
    D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ = D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd
  suffices hz : d = 0 by exact sub_eq_zero.mp hz
  have hn : 0 < p * d.natAbs + 1 := Nat.succ_pos _
  have hc : (p * d.natAbs + 1).Coprime p :=
    ((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm
  have hdvd := cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  rw [Int.abs_eq_natAbs]
  push_cast
  nlinarith [Int.natCast_nonneg d.natAbs]

theorem UpperTheory.Gal.W2.isogForm_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.IsogForm := by
  intro _ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp
  by_cases hall : ∀ u u' : D'.La, D'.EF u u' = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have h0 : ∀ x : D'.La, x = 0 := fun x => D'.nondeg x (hall x)
    rw [h0 u]
    simp
  push_neg at hall
  obtain ⟨u₃, u₄, hne⟩ := hall
  have hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) =
      ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ) := by
    intro u u'
    have hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
    rw [div_mul_eq_mul_div, eq_div_iff hcq]
    exact_mod_cast cross L h inc hf hf'' hyp u u' u₃ u₄
  refine ⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩
  unfold PELU.IsPeriod at hP hP''
  obtain ⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩ := hP
  obtain ⟨-, -, -, -, H2, -, hpos2, him2⟩ := hP''
  set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq
  have hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0 := by
    apply herm_im_zero _ (Set.range P) hspan
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]
    have hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)
      simpa [hq] using this
    rw [hr]
    ring
  have hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0 := by
    intro z w
    apply Complex.ext
    · have := hzero (Complex.I • z) w
      rw [herm_smul_left] at this
      simpa using this
    · simpa using hzero z w
  have hu3 : P u₃ ≠ 0 := by
    intro h0
    have hu : u₃ = 0 := hPinj (by rw [h0, map_zero])
    apply hne
    rw [hu]
    simp
  have e := hM (P u₃) (P u₃)
  rw [herm_sub_smul, sub_eq_zero] at e
  have p1 := hpos1 _ hu3
  have p2 := hpos2 _ hu3
  rw [e, Complex.re_ofReal_mul] at p2
  have hpos : (0 : ℝ) < (q : ℝ) := lt_of_not_ge (fun hle => by nlinarith)
  exact Rat.cast_pos.mp hpos
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMinBridge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.minBridge_of :
    UpperTheory.Gal.W2.MinBridge := by
  intro p _ D G L β D' j hP ga c hga
  obtain ⟨hinj, hsmul, hspan, -⟩ := hP
  set f : 𝓞 D.F →+* G.F := (L.e : D.F →+* G.F).comp (algebraMap (𝓞 D.F) D.F) with hf
  have hpow : ∀ (n : ℕ) (u : D'.La), j ((ga ^ n) u) = (L.rep c ^ n) (j u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, hga, pow_succ, Module.End.mul_apply]
  have key : ∀ (q : (𝓞 D.F)[X]) (u : D'.La),
      j (q.sum fun i b => algebraMap (𝓞 D.F) D.O b • (ga ^ i) u) =
        L.rep (aeval c (q.map f)) (j u) := by
    intro q u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.sum_def, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hpow, map_mul, map_pow, Module.End.mul_apply, ← L.rep_F]
    rfl
  have hK : ∀ q : (𝓞 D.F)[X], Kills (algebraMap (𝓞 D.F) D.O) ga q ↔ aeval c (q.map f) = 0 := by
    intro q
    constructor
    · intro h
      apply L.rep_inj
      rw [map_zero]
      refine LinearMap.ext fun w => ?_
      obtain ⟨m, u, hm, hmu⟩ := hspan w
      have h1 : L.rep (aeval c (q.map f)) (j u) = 0 := by rw [← key, h u, map_zero]
      have h2 : m • L.rep (aeval c (q.map f)) w = 0 := by
        rw [← LinearMap.map_smul_of_tower, hmu, h1]
      rw [← Nat.cast_smul_eq_nsmul ℚ] at h2
      rw [LinearMap.zero_apply]
      exact (smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm)
    · intro h x
      apply hinj
      rw [key, h, map_zero, LinearMap.zero_apply, map_zero]
  refine ⟨(minpoly.monic (Algebra.IsIntegral.isIntegral c)).map _, fun q => ?_⟩
  have hcomp : (L.e.symm : G.F →+* D.F).comp f = algebraMap (𝓞 D.F) D.F := by
    ext b
    simp [hf]
  rw [hK, ← minpoly.dvd_iff, ← map_dvd_iff (Polynomial.mapEquiv L.e.symm),
    Polynomial.mapEquiv_apply, Polynomial.mapEquiv_apply, Polynomial.map_map, hcomp]
end

