module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CommAll
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.commAll :
    ∀ (n : ℕ) (Ξ : Pre n) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), (∀ y, IsUnit y → Ξ.mat y * Z = Z * Ξ.mat y) →
      ∀ y, Ξ.mat y * Z = Z * Ξ.mat y := by
  intro n Ξ Z hZ y
  choose P hP using Ξ.poly
  let Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ := fun i j =>
    ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j
  have hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j,
      (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j) := by
    intro g i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Q, Matrix.mul_apply, hP, map_sum, mul_comm]
  rw [← sub_eq_zero]
  ext i j
  rw [hent, Matrix.zero_apply]
  have hQ : Q i j = 0 := MvPolynomial.eq_of_eval_eq_on_gl (fun g => by
    rw [← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply, map_zero])
  rw [hQ, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.curve :
    ∀ (n : ℕ) (Ξ : Pre n) (c : ℂ → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ), c 0 = 1 →
      (∀ a b, HasDerivAt (fun t => c t a b) (X a b) 0) → ∀ i j, HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.D X i j) 0 := by
  intro n Ξ c X h0 hd i j
  have hγ : HasDerivAt (fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) (of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro a
    rw [hasDerivAt_pi]
    intro b
    exact hd a b
  have hγ0 : (of.symm (c 0) : Fin n → Fin n → ℂ) = oneM n := by
    rw [h0]
  have hf : HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n))
      ((fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) 0) := by
    show HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n)) (of.symm (c 0))
    rw [hγ0]
    exact ((coefDiff n Ξ i j) (oneM n)).hasFDerivAt
  exact hf.comp_hasDerivAt (0 : ℂ) hγ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IrrSub
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.irrSub :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        0 < d' ∧ d' ≤ d ∧ B * A = 1 ∧ (∀ y, ρ' y = B * ρ y * A) ∧ (∀ y, ρ y * A = A * ρ' y) ∧
        ∀ W : Submodule ℂ (Fin d' → ℂ), (∀ y, ∀ v ∈ W, ρ' y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G _ d ρ hd
  classical
  have hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank ℂ S = m := by
    refine ⟨_, ⊤, fun y v _ => Submodule.mem_top, ?_, rfl⟩
    intro h
    have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0 := by
      rw [h]; exact finrank_bot ℂ (Fin d → ℂ)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨S, hSinv, hSne, hSrank⟩ := Nat.find_spec hex
  obtain ⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩ := subMat G d ρ S hSinv
  have hSpos : Module.finrank ℂ S ≠ 0 := fun h => hSne (Submodule.finrank_eq_zero.mp h)
  refine ⟨d', A, B, ρ', ?_, ?_, hBA, hρ', hint, ?_⟩
  · omega
  · have hle := Submodule.finrank_le S
    rw [Module.finrank_fin_fun] at hle
    omega
  · intro W hW
    by_cases hWb : W = ⊥
    · exact Or.inl hWb
    right
    have hinj : Function.Injective A.mulVecLin := by
      intro v w h
      have h2 := congrArg (fun u => B *ᵥ u) h
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA] using h2
    have hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
    have hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin := by
      intro y v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]
    have hW'ne : W.map A.mulVecLin ≠ ⊥ := by
      intro h
      apply hWb
      rw [← Submodule.finrank_eq_zero, ← hrank, h]
      exact finrank_bot ℂ (Fin d → ℂ)
    have hmin := Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le W
    rw [Module.finrank_fin_fun] at hle ⊢
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.PolPre
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.polPre :
    ∀ (n N : ℕ), ∃ (Ξ : Pre n) (e : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N ≃ₗ[ℂ] (Fin Ξ.d → ℂ)),
      ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N),
        (f' : Pol n) = rtr g f → Ξ.mat g *ᵥ e f = e f' := by
  intro n N
  let V := MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N
  have mem : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : V), rtr g (f : Pol n) ∈ V := by
    intro g f
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact (rtrDeg n g f).trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 f.2)
  let R : Matrix (Fin n) (Fin n) ℂ → V →ₗ[ℂ] V := fun g =>
    LinearMap.codRestrict V ((rtr g).toLinearMap.comp V.subtype) (mem g)
  have hR : ∀ g (f : V), ((R g f : V) : Pol n) = rtr g (f : Pol n) := fun g f => rfl
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (R g)
  have hR1 : R 1 = LinearMap.id := by
    ext f
    rw [hR, (rtrMul n).1]
    rfl
  have hRm : ∀ g h, R (g * h) = R g ∘ₗ R h := by
    intro g h
    ext f
    rw [hR, (rtrMul n).2]
    rfl
  let mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := M
      map_one' := by
        show LinearMap.toMatrix b b (R 1) = 1
        rw [hR1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        show LinearMap.toMatrix b b (R (g * h)) = LinearMap.toMatrix b b (R g) * LinearMap.toMatrix b b (R h)
        rw [hRm]
        exact LinearMap.toMatrix_comp b b b (R g) (R h) }
  have poly : ∀ i j : Fin (Module.finrank ℂ V), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    intro i j
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
    obtain ⟨p, hp⟩ := rtrPoly n ((b j : V) : Pol n) φ
    refine ⟨p, fun g => ?_⟩
    rw [← hp]
    show LinearMap.toMatrix b b (R g) i j = _
    rw [LinearMap.toMatrix_apply, ← hR, ← b.coord_apply, ← hφ]
    rfl
  refine ⟨⟨Module.finrank ℂ V, mat, poly⟩, b.equivFun, ?_⟩
  intro g f f' hf
  show LinearMap.toMatrix b b (R g) *ᵥ b.repr f = b.repr f'
  rw [LinearMap.toMatrix_mulVec_repr]
  congr 2
  apply Subtype.ext
  rw [hR, hf]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetHW
section
open Matrix UpperTheory.V.Weyl

open Formalism.REAL in
private theorem UpperTheory.V.Weyl.map_quantum_determinant {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : φ (qdet X u) = qdet (fun a b => φ (X a b)) u := by
  have hT : ∀ v a b, φ (Tm X v a b) = Tm (fun a b => φ (X a b)) v a b := fun v a b => by
    unfold Tm
    split_ifs <;> simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem UpperTheory.V.Weyl.qdetHW :
    ∀ (n d : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (ν : Fin n → ℂ) (v : Fin d → ℂ), Formalism.REAL.GlRel E →
      (∀ a, E a a *ᵥ v = ν a • v) → (∀ a b, a < b → E a b *ᵥ v = 0) →
      ∀ u : ℂ, Formalism.REAL.qdet E u *ᵥ v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v := by
  intro n d E ν v hgl h1 h2 u
  let φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (Fin d → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have hφ : ∀ M w, φ M w = M *ᵥ w := fun M w => Matrix.toLinAlgEquiv'_apply M w
  have hgl' : Formalism.REAL.GlRel (fun a b => φ (E a b)) := by
    intro a b c e
    have := congrArg φ (hgl a b c e)
    simpa only [map_sub, map_mul, apply_ite φ, map_zero] using this
  have hw : Formalism.REAL.IsHW (fun a b => φ (E a b)) ν v :=
    ⟨fun a => (hφ _ _).trans (h1 a), fun a b hab => (hφ _ _).trans (h2 a b hab)⟩
  rw [← hφ, UpperTheory.V.Weyl.map_quantum_determinant]
  exact Formalism.REAL.qDetHW _ n _ ν v hgl' hw u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.TopPol
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.topPol :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) → ∃ f : Pol n, f ≠ 0 ∧ f.totalDegree ≤ n * H ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → rtr b f = (∏ k, b k k ^ ν k) • f := by
  intro n ν hν H hH
  classical
  have hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n),
      i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs := by
    intro h hs i
    constructor
    · intro hi
      exact Finset.le_max' _ _ hi
    · intro hi
      have hm := Finset.max'_mem _ hs
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h,
        rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by
    refine ⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then
      minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        exact (minorDeg n _).1
      · simp only [dite_eq_right hs]
        exact one_ne_zero
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        have h1 := (minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2
        have h2 := ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt
        omega
      · simp only [dite_eq_right hs, MvPolynomial.totalDegree_one]
        exact Nat.zero_le _
    · intro b hb h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        rw [minorRtr n _ b hb]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext i
        rw [hmem h hs i, Finset.mem_filter]
        simp
      · simp only [dite_eq_right hs]
        rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp
  refine ⟨∏ h ∈ Finset.range H, g h, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h)
  · calc (∏ h ∈ Finset.range H, g h).totalDegree ≤ ∑ h ∈ Finset.range H, (g h).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ h ∈ Finset.range H, n := Finset.sum_le_sum (fun h _ => hg2 h)
      _ = n * H := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  · intro b hb
    have key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i =
        ∏ k, b k k ^ ν k := by
      calc ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i
          = ∏ h ∈ Finset.range H, ∏ i, (if h < ν i then b i i else 1) := by
            refine Finset.prod_congr rfl (fun h _ => ?_)
            rw [Finset.prod_filter]
        _ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm
        _ = ∏ k, b k k ^ ν k := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1
            have hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i) := by
              ext h
              simp only [Finset.mem_filter, Finset.mem_range]
              have := hH i
              omega
            rw [hf, Finset.card_range]
    rw [map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]
    simp only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
end

