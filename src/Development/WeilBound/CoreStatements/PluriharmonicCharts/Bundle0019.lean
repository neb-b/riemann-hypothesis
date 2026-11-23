module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.LeMCoordIdealOfTorus
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

section HomogIdeal

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : K → Ω) (f : MRing J) :
    MvPolynomial.eval c (mConeMap y f) = MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) f := by
  have h : (MvPolynomial.eval c).comp (mConeMap y).toRingHom =
      (MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) : MRing J →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp [mConeMap]
  exact congrArg (fun φ : MRing J →+* Ω => φ f) h

theorem aeval_eq_eval_map (w : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem aeval_eq_zero_of_mem {w : (Σ k, J k) → ℂ} {f : MRing J} (hf : f ∈ mCoordIdeal w) :
    MvPolynomial.aeval w f = 0 := by
  have hf' : mConeMap w f = 0 := hf
  have h := eval_mConeMap w (fun _ => 1) f
  rw [hf', map_zero] at h
  simpa using h.symm

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} (c : (k : K) → J k) {f : MRing J}
    (hf : f ∈ mCoordIdeal x) : MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f = 0 := by
  have hf' : mConeMap x f = 0 := hf
  have h := eval_mConeMap x (fun k => (x ⟨k, c k⟩)⁻¹) f
  rw [hf', map_zero] at h
  simpa [div_eq_mul_inv] using h.symm

theorem eq_zero_of_eval_torus {F : MvPolynomial K ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → MvPolynomial.eval c F = 0) : F = 0 := by
  have h2 : F * ∏ k, (MvPolynomial.X k : MvPolynomial K ℂ) = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_mul, map_zero, map_prod]
    by_cases hc : ∀ k, c k ≠ 0
    · rw [h c hc, zero_mul]
    · push_neg at hc
      obtain ⟨k, hk⟩ := hc
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), mul_zero]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 (Finset.prod_ne_zero_iff.2 fun k _ => MvPolynomial.X_ne_zero k)

theorem le_mCoordIdeal_of_torus {bd : Ideal (MRing J)} {z : (Σ k, J k) → ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ f ∈ bd, MvPolynomial.aeval (fun p : Σ k, J k => z p * c p.1) f = 0) :
    bd ≤ mCoordIdeal z := by
  intro f hf
  show mConeMap z f = 0
  refine eq_zero_of_eval_torus fun c hc => ?_
  rw [eval_mConeMap]
  exact h c hc f hf

theorem exists_algHom_ker_eq {S : Type} [CommRing S] [Algebra ℚ S] [Algebra.FiniteType ℚ S] (m : Ideal S)
    [m.IsMaximal] : ∃ ev : S →ₐ[ℚ] ℂ, RingHom.ker ev = m := by
  let _ : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) (Ideal.Quotient.mkₐ_surjective ℚ m)
  haveI : Module.Finite ℚ (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (S ⧸ m)
  haveI : Algebra.IsAlgebraic ℚ (S ⧸ m) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (S ⧸ m) →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.comp (Ideal.Quotient.mkₐ ℚ m), ?_⟩
  ext s
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff φ φ.toRingHom.injective,
    Ideal.Quotient.eq_zero_iff_mem]

theorem cond_of_bd {Ω : Type} [Field Ω] [CharZero Ω] {x : (Σ k, J k) → Ω} {bd : Ideal (MRing J)}
    {c : (k : K) → J k} (hc : ∀ k, x ⟨k, c k⟩ ≠ 0) {S : Subalgebra ℚ Ω} [Algebra.FiniteType ℚ S]
    (hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c p.1⟩ ∈ S) (q : Ideal S) (hq : q.IsPrime)
    (hbd : ∀ g ∈ bd, ∀ s : S, (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q) :
    ∀ g ∈ (⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z), ∀ s : S,
      (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q := by
  intro g hg s hs
  haveI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := ℚ)
  have hjac : q.jacobson = q := isJacobsonRing_iff_prime_eq.mp inferInstance q hq
  rw [← hjac]
  refine Ideal.mem_sInf.2 ?_
  rintro m ⟨hqm, hm⟩
  obtain ⟨ev, hev⟩ := exists_algHom_ker_eq m
  let ρS : (Σ k, J k) → S := fun p => ⟨_, hρ p⟩
  let w : (Σ k, J k) → ℂ := fun p => ev (ρS p)
  have hval : ∀ f : MRing J, ev (MvPolynomial.aeval ρS f) = MvPolynomial.aeval w f := fun f => by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← AlgHom.coe_toRingHom, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hsub : ∀ f : MRing J, ((MvPolynomial.aeval ρS f : S) : Ω) =
      MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f := fun f => by
    show S.val.toRingHom (MvPolynomial.aeval ρS f) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hwP : w ∈ mcPts (mCoordIdeal x) := by
    refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
    · have h1 : ρS ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
      simp only [w, h1, map_one]
      exact one_ne_zero
    · rw [← aeval_eq_eval_map, ← hval]
      have h1 : MvPolynomial.aeval ρS f = 0 := Subtype.ext (by rw [hsub]; exact aeval_ratio_eq_zero c hf)
      rw [h1, map_zero]
  have hwbd : w ∈ mcPts bd := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    rw [← aeval_eq_eval_map, ← hval, ← RingHom.mem_ker, hev]
    exact hqm (hbd f hf _ (hsub f))
  have hg' : g ∈ mCoordIdeal w := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hg w) ⟨hwP, hwbd⟩
  have hs' : s = MvPolynomial.aeval ρS g := Subtype.ext (hs.trans (hsub g).symm)
  rw [← hev, RingHom.mem_ker, hs', hval]
  exact aeval_eq_zero_of_mem hg'

end HomogIdeal

theorem exists_homogIdeal {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (hs : Cmp.IsSncModel x n bd)
    (ha : IsArithVar (mCoordIdeal x) (n + 1))
    (ht : ∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) :
    ∃ I : Ideal (MRing J), IsMultiHomogIdeal I ∧ ¬ I ≤ mCoordIdeal x ∧ Cmp.IsSncModel x n I ∧
      mcPts (mCoordIdeal x) ∩ mcPts I = mcPts (mCoordIdeal x) ∩ mcPts bd := by
  classical
  set I : Ideal (MRing J) := ⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z with hIdef
  have hle : bd ≤ I := by
    intro f hf
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    refine le_mCoordIdeal_of_torus (fun c hc g hg => ?_) hf
    have e : (fun p : Σ k, J k => z p * c p.1) = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z :=
      funext fun p => mul_comm _ _
    rw [e, aeval_eq_eval_map]
    exact (ht z hz c hc).2.2 g hg
  have hhom : IsMultiHomogIdeal I := by
    refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff I).mp ?_
    intro f hf b
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.component_mem z f
      ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) hz) b

  have hrel := ha.2.1.2.2
  have hc0 : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap x (MvPolynomial.X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hc0
  refine ⟨I, hhom, ?_, ?_, ?_⟩
  · intro hIP
    obtain ⟨m, f, a, -, -, hsum, hl⟩ := hs c hc
    obtain ⟨l, hfl⟩ : ∃ l, f l ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero fun l _ => by rw [h l, mul_zero]] at hsum
      exact zero_ne_one hsum
    obtain ⟨-, z, n', -, hli, -, hq⟩ := hl l hfl _ rfl
    have hbot := hq ⊥ Ideal.isPrime_bot
    have hR : ¬ ∃ i : Fin n, (i : ℕ) < n' ∧ z i ∈ (⊥ : Ideal _) := by
      rintro ⟨i, -, hzi⟩
      rw [Ideal.mem_bot] at hzi
      exact hli.ne_zero i (by rw [hzi, map_zero])
    rw [← hbot] at hR
    push_neg at hR
    obtain ⟨g, hg, s, hs1, hs2⟩ := hR
    have hs3 : (s : Ω) ≠ 0 := fun h0 => hs2 ((Ideal.mem_bot).2 (Subtype.ext h0))
    rw [hs1] at hs3
    exact hs3 (aeval_ratio_eq_zero c (hIP (hle hg)))
  · intro c' hc'
    obtain ⟨m, f, a, hf, ha', hsum, hl⟩ := hs c' hc'
    refine ⟨m, f, a, hf, ha', hsum, fun l hfl S hS => ?_⟩
    obtain ⟨hsm, z, n', hn', hli, hsp, hq⟩ := hl l hfl S hS
    refine ⟨hsm, z, n', hn', hli, hsp, fun q hqp => ?_⟩
    rw [← hq q hqp]
    constructor
    · intro h g hg s hs'
      exact h g (hle hg) s hs'
    · intro h
      have hfin : (insert (f l)⁻¹ (Set.range fun p : Σ k, J k => x p / x ⟨p.1, c' p.1⟩)).Finite :=
        (Set.finite_range _).insert _
      haveI : Algebra.FiniteType ℚ S := by
        rw [← Subalgebra.fg_iff_finiteType, hS, ← hfin.coe_toFinset]
        exact Subalgebra.fg_adjoin_finset _
      have hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c' p.1⟩ ∈ S := fun p => by
        rw [hS]
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_range_self p))
      exact cond_of_bd hc' hρ q hqp h
  · ext z
    constructor
    · rintro ⟨hzP, hzI⟩
      exact ⟨hzP, hzI.1, fun f hf => hzI.2 f (hle hf)⟩
    · rintro ⟨hzP, hzb⟩
      refine ⟨hzP, hzP.1, fun f hf => ?_⟩
      rw [← aeval_eq_eval_map]
      exact aeval_eq_zero_of_mem ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) ⟨hzP, hzb⟩)

end PositivityTheory.Xgp.c_bm_exists_boundary
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.PeriodGramConj
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem det_head {p q k : ℕ} {I : Type} [Fintype I] [DecidableEq I] (M : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
    (f : I → Fin q ⊕ Fin p) (hf : Function.Injective f)
    (hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x) :
    (M.submatrix (Subtype.val : {a : Fin (p + q) // (a : ℕ) < k} → _) Subtype.val).det =
      ((M.submatrix (blockEquiv p q) (blockEquiv p q)).submatrix f f).det := by
  let e : I ≃ {a : Fin (p + q) // (a : ℕ) < k} := Equiv.ofBijective
    (fun i => ⟨blockEquiv p q (f i), (hr _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf ((blockEquiv p q).injective (congrArg Subtype.val h)), fun ⟨a, ha⟩ => by
      obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
      obtain ⟨i, rfl⟩ := (hr x).1 ha
      exact ⟨i, rfl⟩⟩
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem sub_conj {m I : Type} [Fintype m] (H Y : Matrix m m ℂ) (f : I → m) :
    (Hᴴ * Y * H).submatrix f f = (H.submatrix id f)ᴴ * Y * H.submatrix id f := by
  ext a b
  simp [Matrix.mul_apply]

theorem periodGram_of {p q : ℕ} (Pi : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ)
    (Gw : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin q) (Fin p) ℂ) (hGo : Go.PosDef) (hdet : IsUnit Pi.det)
    (h : (gramOf (sigForm (p + q) p) Pi).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) :
    IsPeriodGram p Pi ((fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  classical
  refine ⟨⟨hdet, ?_⟩, fun h' hb k => ?_⟩
  · let f : {a : Fin (p + q) // (a : ℕ) < p + q - p} → Fin q := fun a => ⟨a.1, by have := a.2; omega⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (Fin.ext (congrArg Fin.val e :))
    convert hGo.submatrix hf using 1
    ext a b
    have := congrFun (congrFun h (.inl (f a))) (.inl (f b))
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply] at this
    simp at this
    simp only [gramHead, Matrix.neg_apply, Matrix.submatrix_apply]
    rw [neg_eq_iff_eq_neg]
    exact this
  have e1 : (gramOf (sigForm (p + q) p) (Pi * h')).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← h, ← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e2 : (h'ᴴ * (fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm * h').submatrix
      (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q),
      ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q)]
    simp
  unfold gramHead
  by_cases hk : q ≤ k
  · let f : Fin q ⊕ {b : Fin p // q + (b : ℕ) < k} → Fin q ⊕ Fin p := Sum.map id Subtype.val
    have hf : Function.Injective f := Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · exact ⟨fun _ => ⟨.inl a, rfl⟩, fun _ => by show (a : ℕ) < k; omega⟩
      · refine ⟨fun h => ⟨.inr ⟨b, h⟩, rfl⟩, ?_⟩
        rintro ⟨a | a, ha⟩
        · simp [f] at ha
        · obtain rfl : a.1 = b := by simpa [f] using ha
          exact a.2
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₂ : Matrix (Fin p) {b : Fin p // q + (b : ℕ) < k} ℂ := (wBlock h').submatrix id Subtype.val
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromBlocks (omBlock h') 0 0 h₂ := by
      ext (a | a) (b | b) <;> rfl
    rw [e3]
    have e4 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') (Z * h₂) 0 1)ᴴ * fromBlocks (-Go) 0 0 (h₂ᴴ * Gw * h₂) *
          fromBlocks (omBlock h') (Z * h₂) 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    have e5 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') 0 0 1)ᴴ * fromBlocks Go 0 0 (h₂ᴴ * Gw * h₂) * fromBlocks (omBlock h') 0 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc]
    rw [e4, e5]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · let f : {a : Fin q // (a : ℕ) < k} → Fin q ⊕ Fin p := fun a => .inl a.1
    have hf : Function.Injective f := fun a b e => Subtype.ext (Sum.inl_injective e)
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · refine ⟨fun h => ⟨⟨a, h⟩, rfl⟩, ?_⟩
        rintro ⟨b, hb⟩
        obtain rfl : b.1 = a := Sum.inl_injective hb
        exact b.2
      · refine ⟨fun h => absurd h (by show ¬ q + (b : ℕ) < k; omega), ?_⟩
        rintro ⟨a, ha⟩
        simp [f] at ha
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₁ : Matrix (Fin q) {a : Fin q // (a : ℕ) < k} ℂ := (omBlock h').submatrix id Subtype.val
    set O : Matrix (Fin p) {a : Fin q // (a : ℕ) < k} ℂ := 0 with hO
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromRows h₁ O := by
      ext (a | a) b <;> rfl
    rw [e3]
    have e4 : (fromRows h₁ O)ᴴ * ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromRows h₁ O = -((fromRows h₁ O)ᴴ * fromBlocks Go 0 0 Gw * fromRows h₁ O) := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [hO]
    rw [e4, Matrix.det_neg]
    simp

theorem periodGram_conj {N j : ℕ} {Pi G : Matrix (Fin N) (Fin N) ℂ} (h : IsPeriodGram j Pi G) :
    IsPeriodGram j (Pi.map (starRingEnd ℂ)) (G.map (starRingEnd ℂ)) := by
  classical
  have g : ∀ (k : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), gramHead (sigForm N j) k (X.map (starRingEnd ℂ)) =
      (gramHead (sigForm N j) k X).map (starRingEnd ℂ) := fun k X => by
    ext a b
    simp [gramHead, gramOf, Matrix.mul_apply, Matrix.diagonal_apply, apply_ite]
  have dm : ∀ {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ),
      (X.map (starRingEnd ℂ)).det = starRingEnd ℂ X.det := fun X => (RingHom.map_det _ X).symm
  refine ⟨⟨?_, ?_⟩, fun h' hb k => ?_⟩
  · rw [dm]; exact h.1.1.map _
  · rw [g]
    suffices e : -(gramHead (sigForm N j) (N - j) Pi).map (starRingEnd ℂ) = (-gramHead (sigForm N j) (N - j) Pi)ᵀ by
      rw [e]; exact h.1.2.transpose
    ext a b
    have := h.1.2.isHermitian.apply a b
    simp only [Matrix.neg_apply, star_neg, neg_inj] at this
    simp only [Matrix.neg_apply, Matrix.map_apply, Matrix.transpose_apply, neg_inj]
    rw [← this]; simp
  · have := h.2 (h'.map (starRingEnd ℂ)) (fun a b hab => by simp [hb a b hab]) k
    have e1 : Pi.map (starRingEnd ℂ) * h' = (Pi * h'.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    have e2 : (h'ᴴ * G.map (starRingEnd ℂ) * h').submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) = (((h'.map (starRingEnd ℂ))ᴴ * G * h'.map (starRingEnd ℂ)).submatrix
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    rw [e1, g, e2, dm, dm, Complex.norm_conj, Complex.norm_conj, this]

theorem blockG_conj {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    have e1 : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ = (omBlock Γ)ᴴ := rfl
    rw [e1, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.transpose_nonsing_inv]
    rfl
  ext a b
  simp only [blockG, e, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (blockEquiv p q).symm a with a | a <;> rcases (blockEquiv p q).symm b with b | b <;>
    simp [wBlock]

end PositivityTheory.Xgp.c_bm_exists_period
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsArith
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_arith

open KaehlerDifferential

open Algebra in
theorem trdeg_int_eq_rat (L : Type) [Field L] [Algebra ℚ L] : Algebra.trdeg ℤ L = Algebra.trdeg ℚ L := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

end PositivityTheory.Xgp.c_bm_exists_arith

theorem PositivityTheory.Xgp.t_c_bm_exists_arith : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  intro X Ω _ _ ξ K _ J _ x n bd hn T hs
  classical

  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hc0 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨m, f, a, hf, ha, hsum, hmain⟩ := hs c hc0
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  set R : Set Ω := Set.range fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩ with hR
  set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ R) with hS
  obtain ⟨hsm, z, n', -, hli, hspan, -⟩ := hmain l hl S rfl

  have hRS : R ⊆ S := fun r hr => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hr)
  have hmono : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ≤ S.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩ ∈ S
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => hRS ⟨⟨k, j k⟩, rfl⟩
  have hfr : IsFractionRing S Ω := by
    refine IsFractionRing.of_field S Ω fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
    exact ⟨⟨g, hmono hg⟩, ⟨h, hmono hh⟩, e⟩
  have hfin : Module.finrank Ω (KaehlerDifferential ℚ Ω) = n :=
    GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis ℚ S ℚ Ω n z hli hspan

  have hK : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have hall : ∀ a : Ω, a ∈ Set.range (algebraMap ℚ Ω) := by
      intro a
      obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
      have h1 : (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ⊆ {1} := by
        rintro _ ⟨j, rfl⟩
        simp
      have hbot : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
          (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩), ∃ q : ℤ, b = q := by
        intro b hb
        have := Algebra.adjoin_mono h1 hb
        rw [Algebra.adjoin_singleton_one, Algebra.mem_bot] at this
        obtain ⟨q, rfl⟩ := this
        exact ⟨q, by simp⟩
      obtain ⟨q1, rfl⟩ := hbot g hg
      obtain ⟨q2, rfl⟩ := hbot h hh
      exact ⟨(q1 : ℚ) / q2, by rw [e]; simp⟩
    have hsub : Subsingleton (KaehlerDifferential ℚ Ω) := by
      have htop := KaehlerDifferential.span_range_derivation ℚ Ω
      refine subsingleton_of_forall_eq 0 fun w => ?_
      have hw : w ∈ (⊤ : Submodule Ω (KaehlerDifferential ℚ Ω)) := trivial
      rw [← htop] at hw
      have hle : Submodule.span Ω (Set.range (KaehlerDifferential.D ℚ Ω)) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨q, rfl⟩ := hall b
        exact (KaehlerDifferential.D ℚ Ω).map_algebraMap q
      simpa using hle hw
    have := Module.finrank_zero_of_subsingleton (R := Ω) (M := KaehlerDifferential ℚ Ω)
    omega

  have : Algebra.EssFiniteType S Ω := .of_isLocalization Ω (nonZeroDivisors S)
  have : Algebra.EssFiniteType ℚ Ω := .comp ℚ S Ω
  have hfd : Module.Finite Ω (KaehlerDifferential ℚ Ω) := Module.finite_of_finrank_pos (by omega)
  have htr : Algebra.trdeg ℚ Ω = n := by
    rw [← GlobalTheory.rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank, hfin]
  have htr' : Algebra.trdeg ℤ Ω = n := (PositivityTheory.Xgp.c_bm_exists_arith.trdeg_int_eq_rat Ω).trans htr
  exact (GlobalTheory.T.birational_of_transcendence_degree X Ω ξ K J x n T htr').2
end

