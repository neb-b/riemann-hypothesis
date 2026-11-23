module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStE
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem fnTrace_coe (x : ι → Ω) (e : Fin (D + 1) → ι) (s : Lx x e) :
    fnTrace x e (s : Ω) =
      ((Algebra.trace (fnField (x ∘ e)) (Lx x e) s : fnField (x ∘ e)) : Ω) := by
  have hs : (s : Ω) ∈ fnField x := (IntermediateField.mem_extendScalars _).mp s.2
  unfold fnTrace
  rw [dite_eq_left hs]

theorem exists_gen (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ G : Gen x e, G.P.natDegree = projDeg x e ∧
      (∀ H, fnTrace x e (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) =
        deh (x ∘ e) 0 (G.TrP H)) ∧
      (∀ m F, fnTrace x e (deh (x ∘ e) 0 m * deh x (e 0) F) =
        deh (x ∘ e) 0 m * fnTrace x e (deh x (e 0) F)) := by
  classical
  set y := x ∘ e with hy
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero y h.free 0
  have hfin := Lx_finite x e h
  obtain ⟨c, hc⟩ := exists_primitive x e h
  set θL : Lx x e := ∑ i, (c i : Lx x e) * gL x e i with hθLdef
  let Θ : MvPolynomial ι ℤ := ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i
  have hθ : deh x (e 0) Θ = (θL : Ω) := by
    simp [Θ, θL, gL, deh_X]
  obtain ⟨θ, hθdef⟩ : ∃ θ : Ω, θ = deh x (e 0) Θ := ⟨_, rfl⟩
  have hθθ : θ = (θL : Ω) := hθdef.trans hθ

  have hfrac := chartRing_frac y h.free
  have hclosed := chartRing_closed y h.free
  have hθA : IsIntegral (chartRing y) θ := by
    have : (θL : Ω) = ∑ i, (c i : Ω) * (x i / x (e 0)) := by simp [θL, gL]
    rw [hθθ, this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (coord_div_isIntegral x e h i)
    simpa using isIntegral_algebraMap (R := chartRing y) (A := Ω) (x := ((c i : ℤ) : chartRing y))
  have hθK : IsIntegral (fnField y) θ := hθA.tower_top
  have hPK : minpoly (fnField y) θ = (minpoly (chartRing y) θ).map (algebraMap (chartRing y) (fnField y)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (fnField y) hθA
  have hθL : minpoly (fnField y) θ = minpoly (fnField y) θL := by
    rw [hθθ]
    exact minpoly.algebraMap_eq (algebraMap (Lx x e) Ω).injective θL
  have hδ : (minpoly (fnField y) θL).natDegree = projDeg x e := by
    rw [projDeg, relfinrank_eq_finrank_of_le (fnField_comp_le x e), ← IntermediateField.finrank_top',
      ← hc, IntermediateField.adjoin.finrank (.of_finite _ _)]

  have hind := chartGen_indep y h.free
  let r : chartRing y →+* MvPolynomial (Fin (D + 1)) ℤ :=
    (MvPolynomial.rename Subtype.val).toRingHom.comp hind.aevalEquiv.symm.toRingHom
  have hr : ∀ a : chartRing y, deh y 0 (r a) = algebraMap (chartRing y) Ω a := by
    intro a
    obtain ⟨g, rfl⟩ := hind.aevalEquiv.surjective a
    have h1 : r (hind.aevalEquiv g) = MvPolynomial.rename Subtype.val g := by
      show MvPolynomial.rename Subtype.val (hind.aevalEquiv.symm (hind.aevalEquiv g)) = _
      rw [AlgEquiv.symm_apply_apply]
    have h2 : ((hind.aevalEquiv g : Algebra.adjoin ℤ (Set.range (chartGen y))) : fnField y) =
        MvPolynomial.aeval (chartGen y) g := hind.algebraMap_aevalEquiv g
    rw [h1, ← aeval_chartGen, ← h2]
    rfl
  have hrc : (deh y 0).comp r = algebraMap (chartRing y) Ω := RingHom.ext hr
  have hrK : (dehK y).comp r = algebraMap (chartRing y) (fnField y) := by
    ext a
    rw [RingHom.comp_apply, coe_dehK, hr, IsScalarTower.algebraMap_apply (chartRing y) (fnField y) Ω]
    rfl
  have hev : ∀ (p : (chartRing y)[X]) (t : Ω),
      (p.map r).eval₂ (deh y 0) t = aeval t (p.map (algebraMap (chartRing y) (fnField y))) := by
    intro p t
    rw [eval₂_map, hrc, IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω, ← eval₂_map,
      aeval_def]
  have hdehK : (algebraMap (fnField y) Ω).comp (dehK y) = deh y 0 := RingHom.ext fun _ => rfl
  set Pa := minpoly (chartRing y) θ with hPa
  have hPa_deg : (Pa.map r).natDegree = (minpoly (fnField y) θL).natDegree := by
    rw [(minpoly.monic hθA).natDegree_map, ← hθL, hPK, (minpoly.monic hθA).natDegree_map]

  have hq : ∀ i, ∃ q : (fnField y)[X], aeval θL q = gL x e i := by
    intro i
    have htop : Algebra.adjoin (fnField y) {θL} = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.of_finite _ θL).isAlgebraic, hc,
        top_toSubalgebra]
    have hm : gL x e i ∈ Algebra.adjoin (fnField y) {θL} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨q, hq⟩ := hm
    exact ⟨q, hq⟩
  choose q hq using hq
  have hqΩ : ∀ i, aeval θ (q i) = x i / x (e 0) := by
    intro i
    have : (θL : Ω) = algebraMap (Lx x e) Ω θL := rfl
    rw [hθθ, this, aeval_algebraMap_apply, hq i]
    rfl
  obtain ⟨b, Qa, hb0, hQa⟩ := exists_clear (A := chartRing y) (K := fnField y) q
  have hsep : (minpoly (fnField y) θ).Separable := (minpoly.irreducible hθK).separable
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨b', UV, hb'0, hUV⟩ := exists_clear (A := chartRing y) (K := fnField y) ![u, v]
  have hinjA : Function.Injective (algebraMap (chartRing y) Ω) := by
    rw [IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω]
    exact (algebraMap (fnField y) Ω).injective.comp (IsFractionRing.injective _ _)
  have hne : ∀ a : chartRing y, a ≠ 0 → deh y 0 (r a) ≠ 0 := fun a ha => by
    rw [hr]; exact (map_ne_zero_iff _ hinjA).mpr ha
  let G : Gen x e :=
    { Θ := Θ
      P := Pa.map r
      monic := (minpoly.monic hθA).map r
      root := by rw [← hθdef, hev, ← hPK]; exact minpoly.aeval _ _
      min := by
        intro H hH h0 j
        have hm : H.map (dehK y) = 0 := by
          by_contra hne'
          have h1 : aeval θ (H.map (dehK y)) = 0 := by
            rw [aeval_def, eval₂_map, hdehK, hθdef]; exact h0
          have h2 := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (fnField y) θ hne' h1)
          have h3 := natDegree_map_le (f := dehK y) (p := H)
          rw [hθL] at h2
          rw [hPa_deg] at hH
          omega
        have := congrArg (fun p => p.coeff j) hm
        simp only [coeff_map, coeff_zero] at this
        rw [← coe_dehK, this]
        simp
      dd := r b
      dd_ne := hne b hb0
      Q := fun i => (Qa i).map r
      hQ := by
        intro i
        rw [← hθdef, hev, hQa i, map_mul, aeval_C, hqΩ i, deh_X, hr,
          IsScalarTower.algebraMap_apply (chartRing y) (fnField y) Ω]
      cc := r b'
      cc_ne := hne b' hb'0
      U := (UV 0).map r
      V := (UV 1).map r
      hUV := by
        have e1 : (UV 0).map r * Pa.map r + (UV 1).map r * derivative (Pa.map r) - C (r b') =
            (UV 0 * Pa + UV 1 * derivative Pa - C b').map r := by
          rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul,
            Polynomial.derivative_map, Polynomial.map_C]
        have e2 : (UV 0 * Pa + UV 1 * derivative Pa - C b').map
            (algebraMap (chartRing y) (fnField y)) = 0 := by
          rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul,
            ← Polynomial.derivative_map, Polynomial.map_C, hUV 0, hUV 1, ← hPK]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination (C (algebraMap (chartRing y) (fnField y) b')) * huv
        rw [e1, Polynomial.map_map, hrc, IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω, ← Polynomial.map_map,
          e2, Polynomial.map_zero] }
  refine ⟨G, ?_, ?_, ?_⟩
  · show (Pa.map r).natDegree = _
    rw [hPa_deg, hδ]
  · intro H
    have hS : ∀ j, (dehK y (G.S j) : fnField y) =
        psumC (minpoly (fnField y) θL) (minpoly (fnField y) θL).natDegree j := by
      intro j
      show dehK y (psumC (Pa.map r) (Pa.map r).natDegree j) = _
      rw [map_psumC, Polynomial.map_map, hrK, ← hPK, hθL, hPa_deg]
    set s : Lx x e := ∑ j ∈ Finset.range (H.natDegree + 1), dehK y (H.coeff j) • θL ^ j with hsdef
    have hs : (s : Ω) = H.eval₂ (deh y 0) (deh x (e 0) G.Θ) := by
      show _ = H.eval₂ (deh y 0) (deh x (e 0) Θ)
      rw [eval₂_eq_sum_range, hθ, hsdef]
      simp [Algebra.smul_def]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hs, fnTrace_coe, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, trace_pow_eq_psumC hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Gen.TrP, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← coe_dehK y (G.S j), hS j]
    rfl
  · intro m F
    let t : Lx x e := ⟨deh x (e 0) F, deh_mem_fnField x (e 0) F⟩
    have h1 : deh y 0 m * deh x (e 0) F = ((dehK y m • t : Lx x e) : Ω) := by
      rw [Algebra.smul_def]; rfl
    rw [h1, fnTrace_coe, show deh x (e 0) F = (t : Ω) from rfl, fnTrace_coe, LinearMap.map_smul,
      smul_eq_mul]
    push_cast
    rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def lexDeg (a : K → ℕ) : Lex (Fin (Fintype.card K) → ℕ) := toLex (a ∘ (Fintype.equivFin K).symm)

theorem lexDeg_add (a b : K → ℕ) : lexDeg (a + b) = lexDeg a + lexDeg b := rfl


variable (ι) in
abbrev grL : Lex (Fin (Fintype.card K) → ℕ) → Submodule ℤ (MRing ι) :=
  weightedHomogeneousSubmodule ℤ (lexW (ι := ι) (Fintype.equivFin K))

theorem mem_grL_iff (f : MRing ι) (a : K → ℕ) : f ∈ grL ι (lexDeg a) ↔ IsMultiHomog f a := by
  constructor
  · intro h
    have := isMultiHomog_of_mem_lex _ h
    convert this using 1
    funext k
    simp [lexDeg]
  · exact mem_lex_of_isMultiHomog _

theorem mHom_eq (a : K → ℕ) : mHom ι a = grL ι (lexDeg a) := by
  rw [mHom]
  have : {s : MRing ι | IsMultiHomog s a} = (grL ι (lexDeg a) : Set (MRing ι)) := by
    ext s
    exact (mem_grL_iff s a).symm
  rw [this, Submodule.span_eq]

theorem mem_mHom_iff_via_grL (f : MRing ι) (a : K → ℕ) : f ∈ mHom ι a ↔ IsMultiHomog f a := by
  rw [mHom_eq, mem_grL_iff]

theorem isHomogeneous_grL {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) :
    J.IsHomogeneous (grL ι) := (isHomogeneous_lex_iff _ J).mpr hJ

def pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) : mHom ι a →ₗ[ℤ] MRing ι ⧸ J :=
  (Ideal.Quotient.mkₐ ℤ J).toLinearMap ∘ₗ (mHom ι a).subtype

theorem range_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) :
    LinearMap.range (pieceMap J a) = mPiece J a := by
  rw [pieceMap, LinearMap.range_comp, Submodule.range_subtype]
  rfl

theorem mem_ker_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) (x : mHom ι a) :
    x ∈ LinearMap.ker (pieceMap J a) ↔ (x : MRing ι) ∈ J := by
  simp [pieceMap, Ideal.Quotient.eq_zero_iff_mem]

theorem card_mPiece_eq (J : Ideal (MRing ι)) (a : K → ℕ) :
    Nat.card (mPiece J a) = Nat.card (mHom ι a ⧸ LinearMap.ker (pieceMap J a)) := by
  rw [← range_pieceMap]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem card_quot_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (h : A ≤ B) :
    Nat.card (V ⧸ A) = Nat.card (V ⧸ B) * Nat.card (B ⧸ A.comap B.subtype) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (B.map A.mkQ)
  have e1 : Nat.card ((V ⧸ A) ⧸ B.map A.mkQ) = Nat.card (V ⧸ B) :=
    Nat.card_congr (Submodule.quotientQuotientEquivQuotient A B h).toEquiv
  let φ : B →ₗ[R] V ⧸ A := A.mkQ ∘ₗ B.subtype
  have hr : LinearMap.range φ = B.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker φ = A.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e2 : Nat.card (B.map A.mkQ) = Nat.card (B ⧸ A.comap B.subtype) := by
    rw [← hr, ← hk]
    exact Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv.symm
  rw [h1, e1, e2]
  ring

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  rw [← mem_grL_iff] at hf hg ⊢
  rw [lexDeg_add]
  exact SetLike.GradedMul.mul_mem hf hg

theorem card_mPiece_step {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) :
    Nat.card (mPiece J a) = Nat.card (mPiece (J ⊔ Ideal.span {f}) a) * Nat.card (mPiece q (a - c)) := by
  classical
  set J' := J ⊔ Ideal.span {f}
  have hJJ' : J ≤ J' := le_sup_left
  set A := LinearMap.ker (pieceMap J a)
  set B := LinearMap.ker (pieceMap J' a)
  have hAB : A ≤ B := fun x hx => by
    rw [mem_ker_pieceMap] at hx ⊢
    exact hJJ' hx
  rw [card_mPiece_eq, card_mPiece_eq, card_mPiece_eq, card_quot_chain A B hAB]
  congr 1
  have hac : a - c + c = a := funext fun k => Nat.sub_add_cancel (hca k)
  have hmul : ∀ g : mHom ι (a - c), (g : MRing ι) * f ∈ mHom ι a := fun g => by
    rw [mem_mHom_iff]
    have := isMultiHomog_mul ((mem_mHom_iff_via_grL _ _).mp g.2) hf
    rwa [hac] at this
  let χ' : mHom ι (a - c) →ₗ[ℤ] B :=
    { toFun := fun g => ⟨⟨(g : MRing ι) * f, hmul g⟩, by
        rw [mem_ker_pieceMap]
        exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))⟩
      map_add' := fun g h => by ext; simp [add_mul]
      map_smul' := fun r g => by ext; simp [mul_assoc] }
  let χ := (A.comap B.subtype).mkQ ∘ₗ χ'
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨⟨⟨x, hxa⟩, hxB⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    have hxJ' : x ∈ J' := (mem_ker_pieceMap J' a ⟨x, hxa⟩).mp hxB
    obtain ⟨j, hj, y, hy, hjx⟩ := Submodule.mem_sup.mp hxJ'
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hf' : f ∈ grL ι (lexDeg c) := (mem_grL_iff f c).mpr hf
    set g := (DirectSum.decompose (grL ι) h (lexDeg (a - c)) : MRing ι)
    have hg : g ∈ mHom ι (a - c) := by
      rw [mHom_eq]
      exact SetLike.coe_mem _
    refine ⟨⟨g, hg⟩, ?_⟩
    have hx : x = (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f := by
      have h1 : x ∈ grL ι (lexDeg a) := by rw [← mHom_eq]; exact hxa
      conv_lhs => rw [← DirectSum.decompose_of_mem_same (grL ι) h1, ← hjx]
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      congr 1
      rw [← hac, lexDeg_add, DirectSum.coe_decompose_mul_add_of_right_mem (grL ι) hf']
    have hjc : (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) ∈ J := isHomogeneous_grL hJ _ hj
    show (A.comap B.subtype).mkQ (χ' ⟨g, hg⟩) = (A.comap B.subtype).mkQ ⟨⟨x, hxa⟩, hxB⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.coe_subtype, mem_ker_pieceMap]
    have : (((χ' ⟨g, hg⟩ - ⟨⟨x, hxa⟩, hxB⟩ : B) : mHom ι a) : MRing ι) = g * f - x := rfl
    rw [this, hx, show g * f - ((DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f) =
      -(DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) by ring]
    exact J.neg_mem hjc
  have hker : LinearMap.ker χ = LinearMap.ker (pieceMap q (a - c)) := by
    ext g
    rw [LinearMap.mem_ker, mem_ker_pieceMap, hq]
    show (A.comap B.subtype).mkQ (χ' g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      mem_ker_pieceMap]
    rfl
  rw [← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective χ hsurj).toEquiv.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

