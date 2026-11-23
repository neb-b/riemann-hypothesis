module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearActInt
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearActAlg
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTripleAlg
section
noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix
open GlobalTheory.WeilM

section Forms

variable {k : Type} [Field k] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}

theorem map_mul_c {a b d : Type} [Fintype b] (A : Matrix a b K) (B : Matrix b d K) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem map_one_c {a : Type} [DecidableEq a] : (1 : Matrix a a K).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)

theorem exists_left_inv (hK : IsField K) {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (C : Matrix a b K)
    (h : ∀ t, C *ᵥ t = 0 → t = 0) : ∃ L : Matrix b a K, L * C = 1 := by
  letI := hK.toField
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot'.2 fun t ht => h t ht)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

theorem isLagr_of_free [Invertible (2 : k)] (hK : IsField K) (hc : ∀ x, c (c x) = x) {N m : ℕ} (hN : N = 2 * m)
    {J : Matrix (Fin N) (Fin N) K} (hJ : IsSkewM c J) {Y : Matrix (Fin N) (Fin m) K} (hY : Yᵀ * J * Y.map c = 0)
    (hf : ∀ t, Y *ᵥ t = 0 → t = 0) : IsLagr c J Y := by
  obtain ⟨L, hL⟩ := exists_left_inv hK Y hf
  have cc : ∀ {a b : Type} (A : Matrix a b K), (A.map c).map c = A := fun A => Matrix.ext fun i j => hc _
  have hJ' : (J.map c)ᵀ = -J := Matrix.ext fun i j => hJ.1 i j
  have sk : ∀ {a b : Type} (A : Matrix (Fin N) a K) (B : Matrix (Fin N) b K),
      Bᵀ * J * A.map c = -((Aᵀ * J * B.map c).map c)ᵀ := fun A B => by
    rw [map_mul_c, map_mul_c, cc, Matrix.transpose_mul, Matrix.transpose_mul, hJ', Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin N) (Fin m) K, Yᵀ * J * Z.map c = 1 := ⟨(J⁻¹ * Lᵀ).map c, by
    rw [cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.2, ← Matrix.transpose_mul, hL, Matrix.transpose_one]⟩
  have hZ' : Zᵀ * J * Y.map c = -1 := by rw [sk, hZ, map_one_c, Matrix.transpose_one]
  set S := Zᵀ * J * Z.map c with hS
  have hS' : (S.map c)ᵀ = -S := by rw [hS, neg_eq_iff_eq_neg.2 (sk Z Z)]
  let t : Matrix (Fin m) (Fin m) K := -(⅟(2 : k) • Sᵀ)
  have ht : t.map c = ⅟(2 : k) • S := by
    ext i j
    have : c (S j i) = -S i j := congrFun (congrFun hS' i) j
    simp [t, this]
  have a1 : ∀ A B : Matrix (Fin N) (Fin m) K, (A + B).map c = A.map c + B.map c := fun A B =>
    Matrix.map_add _ (map_add c) _ _
  have e1 : Yᵀ * J * (Z + Y * t).map c = 1 := by
    rw [a1, map_mul_c, Matrix.mul_add, hZ, ← Matrix.mul_assoc, hY, Matrix.zero_mul, add_zero]
  have e2 : (Z + Y * t)ᵀ * J * Y.map c = -1 := by rw [sk, e1, map_one_c, Matrix.transpose_one]
  have e3 : (Z + Y * t)ᵀ * J * (Z + Y * t).map c = 0 := by
    rw [a1, map_mul_c, Matrix.mul_add, ← Matrix.mul_assoc, e2, ht, Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.transpose_mul, Matrix.mul_assoc tᵀ, Matrix.mul_assoc tᵀ, hZ, ← hS]
    simp only [t, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul]
    rw [add_assoc, ← neg_add, ← add_smul, invOf_two_add_invOf_two, one_smul, add_neg_cancel]
  set X := Z + Y * t
  have g : (Matrix.fromCols Y X)ᵀ * J * (Matrix.fromCols Y X).map c = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_map, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hY, e1, e2, e3]
  have g' : ((Matrix.fromBlocks 0 (-1) 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (((Matrix.fromCols Y X)ᵀ).map c * J.map c)) * Matrix.fromCols Y X = 1 := by
    have := congrArg (fun M => M.map c) g
    simp only [map_mul_c, cc] at this
    rw [Matrix.mul_assoc, this, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one_c, Matrix.map_neg _ (map_neg c),
      map_one_c, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp
  exact ⟨hY, X, _, e3, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp; omega))).1 g', g'⟩


end Forms

end PositivityTheory.ThK.PT
end
end

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InducedVanishOfVanishOnIntegral
section
open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.ThK.SplitLoc

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a a' : ℕ}

abbrev stdE (a a' : ℕ) : Fin a ⊕ Fin a' ≃ Fin (a + a') := stdSum (rfl : a + a' = a + a')

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isBlockUpper_iff (b : GL (Fin (a + a')) k) : IsBlockUpper b ↔ b ∈ parab k (two (stdE a a')) :=
  (mem_parab_two k).symm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blkA (p : parab k (two (stdE a a'))) :
    ((GeneralLinearGroup.det (leviProj k (two (stdE a a')) p false) : kˣ) : k) = (blkA (p : GL (Fin (a + a')) k)).det := by
  rw [GeneralLinearGroup.val_det_apply]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blkD (p : parab k (two (stdE a a'))) :
    ((GeneralLinearGroup.det (leviProj k (two (stdE a a')) p true) : kˣ) : k) = (blkD (p : GL (Fin (a + a')) k)).det := by
  rw [GeneralLinearGroup.val_det_apply]
  congr 1

theorem law_parab {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β)
    (p : parab k (two (stdE a a'))) (h : GL (Fin (a + a')) k) :
    F (p * h) = indFac a a' α β (GeneralLinearGroup.det (leviProj k (two (stdE a a')) p false))
      (GeneralLinearGroup.det (leviProj k (two (stdE a a')) p true)) * F h :=
  hF.2 _ h ((isBlockUpper_iff _).2 p.2) _ _ (det_blkA p) (det_blkD p)

abbrev rhoD (a a' : ℕ) (α β : kˣ →* ℂˣ) : Representation ℂ (Levi k (Two (Fin a) (Fin a'))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin a) α) (detRep (Fin a') β)).comp (leviTwo k (Fin a) (Fin a')).symm.toMonoidHom

theorem twist_rhoD (α β : kˣ →* ℂˣ) (g : Levi k (Two (Fin a) (Fin a'))) (x : ℂ ⊗[ℂ] ℂ) :
    twist (rhoD a a' α β) (deltaHalf k (Two (Fin a) (Fin a'))) g x =
      indFac a a' α β (GeneralLinearGroup.det (g false)) (GeneralLinearGroup.det (g true)) • x := by
  obtain ⟨g, rfl⟩ := (leviTwo k (Fin a) (Fin a')).surjective g
  rw [twist_apply, deltaHalf_two]
  have h : ∀ x, rhoD a a' α β (leviTwo k (Fin a) (Fin a') g) x =
      ((α (GeneralLinearGroup.det g.1) : ℂ) * β (GeneralLinearGroup.det g.2)) • x := by
    intro x
    show extTensor _ _ ((leviTwo k (Fin a) (Fin a')).symm (leviTwo k (Fin a) (Fin a') g)) x = _
    rw [MulEquiv.symm_apply_apply]
    induction x with
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
    | tmul v w =>
      rw [extTensor_tmul]
      simp only [detRep, ofChar_apply, detChar_apply, ← smul_eq_mul, TensorProduct.smul_tmul_smul]
  rw [h, smul_smul]
  congr 1
  simp only [Fintype.card_fin, Units.val_mul]
  show apow (GeneralLinearGroup.det g.1) ((a' : ℂ) / 2) * apow (GeneralLinearGroup.det g.2) (-(a : ℂ) / 2) * _ =
    indFac a a' α β (GeneralLinearGroup.det g.1) (GeneralLinearGroup.det g.2)
  unfold indFac
  ring

def toFn (a a' : ℕ) (α β : kˣ →* ℂˣ) : IndSp (two (stdE a a')) (rhoD a a' α β) →ₗ[ℂ] (GL (Fin (a + a')) k → ℂ) where
  toFun f := fun g => TensorProduct.lid ℂ ℂ (f.1.1 g)
  map_add' f f' := funext fun g => map_add (TensorProduct.lid ℂ ℂ) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := funext fun g => map_smul (TensorProduct.lid ℂ ℂ) c (f.1.1 g)

theorem exists_toFn {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β) :
    ∃ f, toFn a a' α β f = F := by
  obtain ⟨U, hU, hUF⟩ := hF.1
  refine ⟨⟨⟨fun g => (TensorProduct.lid ℂ ℂ).symm (F g), fun p g => ?_⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hU.mem_nhds U.one_mem) fun u hu => ?_)⟩, funext fun g => ?_⟩
  · refine Eq.trans ?_ (twist_rhoD α β (leviProj k (two (stdE a a')) p) _).symm
    rw [← map_smul, smul_eq_mul]
    exact congrArg _ (law_parab hF p g)
  · exact Subtype.ext (funext fun x => congrArg (TensorProduct.lid ℂ ℂ).symm (hUF u hu x))
  · exact (TensorProduct.lid ℂ ℂ).apply_symm_apply _

end PositivityTheory.ThK.SplitLoc

namespace PositivityTheory.ThK.SplitDict

open PositivityTheory.ThK.SplitLoc GlobalTheory.SplitWeil GlobalTheory.SmGL

theorem induced_vanish_of_vanish_on_integral : IndIwasawa := by
  intro k _ _ _ _ a a' α β F hF h0
  funext g
  obtain ⟨p, hp, c, hc, rfl⟩ := iwasawa_blockTriangular k _ (fun i => (blk (two (stdE a a')) i).toNat) g
  have hp' : p ∈ parab k (two (stdE a a')) := fun i j hij => hp (by
    revert hij
    dsimp only
    cases blk (two (stdE a a')) i <;> cases blk (two (stdE a a')) j <;> simp)
  exact (law_parab hF ⟨p, hp'⟩ c).trans (by rw [h0 c hc, mul_zero]; rfl)

end PositivityTheory.ThK.SplitDict
end
end

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
section
noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory PositivityTheory.ThKH.Evl

namespace PositivityTheory.ThK

namespace LinAct

variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {K : Type} [CommRing K] [Nontrivial K] [Algebra k K] {c : K →ₐ[k] K} {ψ : AddChar k ℂ} {ξ₀ ξ : K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  {JA : Matrix α α K} {JB : Matrix β β K} {Cy : Matrix β ν K}

theorem dbl_fix (hc : Continuous ψ) (h1 : ψ ≠ 1) (hq : IsQuad c ξ₀) (hA : IsHerm c JA) (hL : IsLagr c JB Cy)
    (dd : Darboux (symp (R := k) c ξ JB (dbl JA)) κ) (om : UG c (dbl JA) →* Module.End ℂ ((κ → k) → ℂ))
    (hs : IsSplitting (sbClass k) ψ dd (actB c) om) (hr : SiegelRule c (sbClass k) ψ ξ JB (dbl JA) dd 1 (diagCols α) om)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ lagY dd Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) : ∀ g, ∀ φ ∈ SB (κ → k), l (om g φ) = l φ := by
  have hiso := lagY_iso dd hL.1
  have hdim := lagY_dim hq dd hL
  have hcard := card_lagr hL
  have hn := norm_char hc
  have key : ∀ g, ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l (om g φ) = a * l φ := fun g =>
    line hc hn h1 _ hiso hdim l (l ∘ₗ om g) hl (by
      rintro _ ⟨z, rfl⟩ φ hφ
      refine (congrArg l (hs.impl g (Cy * z) φ hφ)).trans (hl _ ?_ _ (hs.pres g φ hφ))
      exact mem_lagY.2 ⟨_, by rw [actB, Matrix.mul_assoc]⟩) hne
  choose a ha using key
  obtain ⟨φ₀, hφ₀, hl₀⟩ := hne
  let A : UG c (dbl JA) →* ℂ :=
    { toFun := a
      map_one' := by
        have := ha 1 φ₀ hφ₀
        rw [map_one, Module.End.one_apply] at this
        exact (mul_eq_right₀ hl₀).1 this.symm
      map_mul' := fun g h => by
        have := ha (g * h) φ₀ hφ₀
        rw [map_mul, Module.End.mul_apply, ha g _ (hs.pres h _ hφ₀), ha h _ hφ₀, ← mul_assoc] at this
        exact (mul_right_cancel₀ hl₀ this).symm }
  obtain ⟨-, Cx, M, -, hM1, hM2⟩ := id hL
  obtain ⟨r, e, he⟩ := exists_coord hq ν α
  have hD := isLagr_diagCols (R := k) c JA
  have hisoD : ∀ z z' : Matrix β α K, (dd.e (z * (diagCols (E := K) α)ᵀ)).1 ⬝ᵥ (dd.e (z' * (diagCols (E := K) α)ᵀ)).2 =
      (dd.e (z' * (diagCols (E := K) α)ᵀ)).1 ⬝ᵥ (dd.e (z * (diagCols (E := K) α)ᵀ)).2 := fun z z' => by
    have h := dd.form (z * (diagCols (E := K) α)ᵀ) (z' * (diagCols (E := K) α)ᵀ)
    rw [symp, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JB hD.1, mul_zero, map_zero] at h
    exact sub_eq_zero.mp h.symm
  let X₀ : Matrix ν α K →ₗ[k] Matrix β (α ⊕ α) K :=
    { toFun := fun z => Cx * z * (diagCols (E := K) α)ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun t z => by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let X : (Fin r → k) →ₗ[k] (κ → k) × (κ → k) := dd.e.toLinearMap ∘ₗ X₀ ∘ₗ e.toLinearMap
  have hX : ∀ x, X x = dd.e (Cx * e x * (diagCols (E := K) α)ᵀ) := fun _ => rfl
  obtain ⟨L, ⟨φ₁, hφ₁, hL₁⟩, hLX, hLY, hLT⟩ := exists_avg hc h1 _ hiso hdim l hl ⟨φ₀, hφ₀, hl₀⟩ X
    (fun x x' => hisoD _ _) (fun x hx => by
      obtain ⟨z, hz⟩ := mem_lagY.1 hx
      have h2 := dd.e.injective (hz.trans (hX x))
      have h3 := (indep hM2 (z := -z) (z' := e x * (diagCols (E := K) α)ᵀ) (by
        rw [Matrix.mul_neg, h2, Matrix.mul_assoc, neg_add_cancel])).2
      rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one, ← fromCols_zero] at h3
      exact e.map_eq_zero_iff.1 (fromCols_ext_iff .. |>.1 h3).1)
  have hinv : ∀ z : Matrix β α K, ∀ φ ∈ SB (κ → k), L (dd.rho ψ (z * (diagCols (E := K) α)ᵀ) φ) = L φ := fun z φ hφ => by
    obtain ⟨x, hx⟩ := e.surjective (M * z).toRows₂
    have hz : z = Cy * (M * z).toRows₁ + Cx * e x := by
      rw [hx, ← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hM1, Matrix.one_mul]
    rw [Darboux.rho, hz, Matrix.add_mul, map_add (f := _), ← schr_add (hisoD _ _), hLY _ (mem_lagY.2 ⟨_, by rw [Matrix.mul_assoc]⟩)
      (fun x => hisoD _ _) _ (schr_mem hc _ hφ), ← hX, hLX _ _ hφ]
  have hA1 := _root_.GlobalTheory.CompanionTheory.SiegelChar.char_trivial k K c ξ₀ _ _ _ _ hq (GlobalTheory.CompanionTheory.WeilOneMember.isHerm_dbl hA) hD A.toHomUnits fun p t hp => by
    obtain ⟨g, hg, hdet⟩ := he t
    have e1 := hr L trivial hinv p t hp φ₁ hφ₁
    have e2 := hLT (om p) g (a p) (hs.pres p) (fun x φ hφ => by
      refine (hs.impl p (Cx * e x * (diagCols (E := K) α)ᵀ) φ hφ).trans ?_
      rw [hX, hg, actB, Darboux.rho, Matrix.mul_assoc _ (diagCols (E := K) α)ᵀ, ← transpose_mul, hp, transpose_mul]
      simp only [Matrix.mul_assoc]) (ha p) φ₁ hφ₁
    have e3 := mul_right_cancel₀ hL₁ (e1.symm.trans e2)
    have e4 : (Fintype.card β : ℝ) / 2 = (Fintype.card ν : ℕ) := by rw [hcard]; push_cast; ring
    rw [hdet, map_pow, e4, Real.rpow_natCast, MonoidHom.one_apply, Circle.coe_one, one_mul, NNReal.coe_pow] at e3
    refine Units.ext ((mul_eq_left₀ ?_).1 e3.symm)
    exact_mod_cast pow_ne_zero _ distribHaarChar_pos.ne'
  intro g φ hφ
  have : a g = 1 := congrArg Units.val (DFunLike.congr_fun hA1 g)
  rw [ha g φ hφ, this, one_mul]

theorem weilB_fix (hc : Continuous ψ) (h1 : ψ ≠ 1) (hq : IsQuad c ξ₀) (hA : IsHerm c JA) (hL : IsLagr c JB Cy)
    (d : Darboux (symp (R := k) c ξ JB JA) κ) (om : UG c JA →* Module.End ℂ ((κ → k) → ℂ))
    (hW : IsWeilB c (sbClass k) ψ ξ JB JA d 1 om)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ lagY d Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) : ∀ g, ∀ φ ∈ SB (κ → k), l (om g φ) = l φ := by
  obtain ⟨hs₀, dd, omd, hdd, hs, hr, hb⟩ := hW
  have hn := norm_char hc
  obtain ⟨l₂, hne₂, hl₂⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form k _ ψ hc h1 _ (lagY_iso dd hL.1)
  have hfix := dbl_fix hc h1 hq hA hL dd omd hs hr l₂ hl₂ hne₂
  obtain ⟨φ₁, h₁, φ₂, h₂, h₁₂⟩ : ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), l₂ (boxFun φ₁ φ₂) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨φ₀, h₀, hl₀⟩ := hne
    obtain ⟨φ, hφ, hφ0⟩ := hne₂
    obtain ⟨y, hy⟩ := Function.ne_iff.mp fun h : φ₀ = 0 => hl₀ (by rw [h, map_zero])
    refine hφ0 (cyc hc hn h1 (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem h₀ h₀) (fun h => ?_) l₂ (fun w => ?_) φ hφ)
    · exact mul_ne_zero hy hy (congrFun h (Sum.elim y y))
    · rw [schr_box]
      exact hcon _ (schr_mem hc _ h₀) _ (schr_mem hc _ h₀)
  let Bx : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    { toFun := fun φ => boxFun φ φ₂
      map_add' := fun a b => funext fun x => add_mul _ _ _
      map_smul' := fun t a => funext fun x => mul_assoc _ _ _ }
  obtain ⟨a, ha⟩ := line hc hn h1 _ (lagY_iso d hL.1) (lagY_dim hq d hL) l (l₂ ∘ₗ Bx) hl (by
    rintro _ ⟨z, rfl⟩ φ hφ
    have e := hl₂ _ (mem_lagY.2 ⟨fromCols z 0, rfl⟩) _ (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ h₂)
    have e0 : schr ψ (0, 0) φ₂ = φ₂ := by funext x; simp [schr]
    rw [mul_fromCols, hdd, Matrix.mul_zero, map_zero, schr_box] at e
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.fst_zero, Prod.snd_zero, neg_zero, e0] at e
    exact e) hne
  have ha0 : a ≠ 0 := fun h => h₁₂ ((ha φ₁ h₁).trans (by rw [h, zero_mul]))
  intro g φ hφ
  obtain ⟨gd, hgd⟩ := GlobalTheory.CompanionTheory.WeilOneMember.exists_embed g
  have e := hfix gd _ (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ h₂)
  rw [hb g gd hgd φ hφ φ₂ h₂] at e
  exact mul_left_cancel₀ ha0 ((ha _ (hs₀.pres g φ hφ)).symm.trans (e.trans (ha φ hφ)))

end LinAct

theorem split_character_fixes_evaluation : LinearAct := by
  intro k _ _ _ _ _ _ K _ _ _ _ c ψ hK ⟨ξ₀, hq⟩ hc h1 m n N κ _ JA JB d χ Cy om l hA _ hL ⟨_, d', hd', hW⟩ hev g φ hφ
  have := hK.nontrivial
  refine LinAct.weilB_fix hc h1 hq hA hL d' _ hW l ?_ hev.1 g φ hφ
  rintro _ ⟨z, rfl⟩ φ hφ
  have e := hev.2 zᵀ φ hφ
  rw [Darboux.rho, ← hd', transpose_mul, transpose_transpose, transpose_transpose] at e
  exact e

end PositivityTheory.ThK
end
end

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransport
section
noncomputable section

namespace PositivityTheory.ThK

open Matrix GlobalTheory.WeilM SiegelT

theorem siegel_transport : SiegelTransport := by
  intro k _ _ _ _ _ _ K _ _ _ _ c ψ _ hq hψ _ m n N κ _ JA JB d χ Cy om _ hsk hL hW
  obtain ⟨ξ, hq⟩ := hq
  obtain ⟨hs0, dd, omd, hdd, hs, hrule, hres⟩ := hW
  obtain ⟨γ, s, s', h1, h2, hγ⟩ := exists_gamma hq.invol hsk.1 hsk.2 hL
  have hr := rule_of_conj hs γ s s' h1 h2 hγ hrule
  intro l _ hinv p t hp φ hφ
  by_cases h0 : ∀ φ ∈ SB (κ → k), l φ = 0
  · rw [h0 φ hφ, h0 _ (hs0.pres p φ hφ), mul_zero]
  push Not at h0
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  obtain ⟨gd, hgd⟩ := exists_UG (c := c) (J := dbl JB)
    (g := fromBlocks ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) 0 0 1) (by
      rw [dbl, det_fromBlocks_zero₂₁, det_neg]
      exact hsk.2.mul ((isUnit_one.neg.pow _).mul hsk.2)) (by
      have hp' : ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * JB *
        ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map c = JB := p.2
      simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one', fromBlocks_multiply]
      simp [hp'])
  let td : GL (Fin n ⊕ Fin n) K := ⟨fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 1,
    fromBlocks ((t⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0 1,
    by rw [fromBlocks_multiply, Units.mul_inv]; simp, by rw [fromBlocks_multiply, Units.inv_mul]; simp⟩
  have hdet : Matrix.GeneralLinearGroup.det td = Matrix.GeneralLinearGroup.det t :=
    Units.ext (by
      show (fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin n) (Fin n) K)).det = (t : Matrix (Fin n) (Fin n) K).det
      rw [det_fromBlocks_zero₂₁, det_one, mul_one])
  have key := hr (boxL l (conjL l)) (Set.mem_univ _) (fun z Φ hΦ => by
    have e : z * (fromBlocks Cy 0 0 Cy)ᵀ = fromCols (z.toCols₁ * Cyᵀ) (z.toCols₂ * Cyᵀ) := by
      conv_lhs => rw [← fromCols_toCols z]
      rw [fromBlocks_transpose, fromCols_mul_fromBlocks]
      simp
    rw [Darboux.rho, e, hdd]
    exact boxL_inv (norm_psi hψ) (hinv _) (hinv _) hΦ) gd td (by
      rw [hgd]
      show _ = fromBlocks Cy 0 0 Cy * fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin n) (Fin n) K)
      rw [fromBlocks_multiply, fromBlocks_multiply]
      simp [hp]) (boxFun φ (star φ₀)) (box_mem hφ (star_mem hφ₀))
  rw [hres p gd hgd φ hφ _ (star_mem hφ₀), hdet] at key
  have b : ∀ φ₁, boxL l (conjL l) (boxFun φ₁ (star φ₀)) = l φ₁ * star (l φ₀) := fun φ₁ => by
    have := boxL_box l (conjL l) φ₁ (star φ₀)
    rw [show conjL l (star φ₀) = star (l φ₀) from congrArg (fun f => star (l f)) (star_star φ₀)] at this
    exact this
  rw [b, b, ← mul_assoc] at key
  exact mul_right_cancel₀ (star_ne_zero.mpr hne) key

end PositivityTheory.ThK
end
end

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitAsm
section
noncomputable section

namespace PositivityTheory.ThK.SplitAsm

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ChrFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Base F E) (X : Chars F E)
    (a a' : ℕ) (v : Pl F) (τ : E →ₐ[F] Fv F v), Chars.IsGood B X a a' →
    (∀ x, ‖(chrW X.α τ x : ℂ)‖ = 1) ∧ (∀ x, ‖(chrW X.β τ x : ℂ)‖ = 1) ∧ chrW X.ν τ = chrW X.α τ / chrW X.β τ ∧
    (∃ e : ℕ, CondLE (unifAt v) e (chrW X.α τ) ∧ CondLE (unifAt v) e (chrW X.β τ)) ∧
    (v ∈ X.T → ¬ GlobalTheory.SplitWeil.IsUnram (chrW X.ν τ)) ∧
    (v ∉ X.T → GlobalTheory.SplitWeil.IsUnram (chrW X.α τ) ∧ GlobalTheory.SplitWeil.IsUnram (chrW X.β τ))

theorem extendOn {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ V)
    (g : V → W) (hg : ∀ x ∈ S, ∀ y ∈ S, ∀ c : ℂ, g (x + c • y) = g x + c • g y) :
    ∃ p : V →ₗ[ℂ] W, ∀ x ∈ S, p x = g x := by
  have h0 : g 0 = 0 := by
    have h1 := hg 0 S.zero_mem 0 S.zero_mem 1
    rw [smul_zero, add_zero, one_smul] at h1
    have h2 : g 0 + g 0 = g 0 + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  let gS : S →ₗ[ℂ] W :=
    { toFun := fun x => g x
      map_add' := fun x y => by
        have h3 := hg x x.2 y y.2 1
        rw [one_smul, one_smul] at h3
        simpa using h3
      map_smul' := fun c x => by
        have h3 := hg 0 S.zero_mem x x.2 c
        rw [zero_add, h0, zero_add] at h3
        simpa using h3 }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend gS
  refine ⟨p, fun x hx => ?_⟩
  have h4 := LinearMap.congr_fun hp ⟨x, hx⟩
  simpa [gS] using h4

theorem mk_p {D M P : Type} [AddCommGroup P] [Module ℂ P] (SD : Submodule ℂ (D → ℂ)) (SM : Submodule ℂ (M → ℂ))
    (ι : (D → ℂ) →ₗ[ℂ] (M → ℂ)) (hι : Set.BijOn ι SD SM) (N : Submodule ℂ P) (f : (M → ℂ) → P)
    (hlin : ∀ Φ ∈ SM, ∀ Φ₁ ∈ SM, ∀ c : ℂ, f (Φ + c • Φ₁) = f Φ + c • f Φ₁) (hmem : ∀ Φ ∈ SM, f Φ ∈ N)
    (hon : ∀ y ∈ N, ∃ Φ ∈ SM, f Φ = y) :
    ∃ p : (D → ℂ) →ₗ[ℂ] N, (∀ φ ∈ SD, (p φ : P) = f (ι φ)) ∧ SD.map p = ⊤ := by
  classical
  let g : (D → ℂ) → N := fun φ => if h : ι φ ∈ SM then ⟨f (ι φ), hmem _ h⟩ else 0
  have hgS : ∀ φ ∈ SD, (g φ : P) = f (ι φ) := by
    intro φ hφ
    show ((if h : ι φ ∈ SM then (⟨f (ι φ), hmem _ h⟩ : N) else 0 : N) : P) = f (ι φ)
    rw [dite_eq_left (show ι φ ∈ SM from hι.mapsTo hφ)]
  obtain ⟨p, hp⟩ := extendOn SD g (by
    intro x hx y hy c
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hgS _ (SD.add_mem hx (SD.smul_mem c hy)), hgS _ hx, hgS _ hy,
      map_add, map_smul]
    exact hlin _ (hι.mapsTo hx) _ (hι.mapsTo hy) c)
  refine ⟨p, fun φ hφ => by rw [hp φ hφ]; exact hgS φ hφ, ?_⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨Φ, hΦ, hfΦ⟩ := hon y.1 y.2
  obtain ⟨φ, hφ, hιφ⟩ := hι.surjOn hΦ
  refine ⟨φ, hφ, ?_⟩
  apply Subtype.ext
  rw [hp φ hφ, hgS φ hφ, hιφ, hfΦ]

end PositivityTheory.ThK.SplitAsm
end
end

