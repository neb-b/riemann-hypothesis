module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_mat {Γ S ι : Type} [TopologicalSpace Γ] [Fintype ι] (f : Γ → Matrix ι ι S)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (h i j).eventually_eq x
  exact this.mono fun y hy => Matrix.ext hy

theorem UpperTheory.V.Ws.sxAdicMat :
    ∀ {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (M : Γ → M4 R), (∀ i j, AdicCont I fun g => M g i j) → (∀ n, AdicCont I fun g => (M g).charpoly.coeff n) ∧ ∀ (U V : M4 R) i j, AdicCont I fun g => (U * M g * V) i j := by
  intro Γ R _ _ I M h
  have hl : ∀ N : ℕ, IsLocallyConstant fun g => (M g).map (Ideal.Quotient.mk (I ^ N)) :=
    fun N => lc_mat _ fun i j => h i j N
  refine ⟨fun n N => ?_, fun U V i j N => ?_⟩
  · have := (hl N).comp fun A => A.charpoly.coeff n
    convert this using 2 with g
    simp only [Function.comp, Matrix.charpoly_map, Polynomial.coeff_map]
  · have := (hl N).comp fun A =>
      (U.map (Ideal.Quotient.mk (I ^ N)) * A * V.map (Ideal.Quotient.mk (I ^ N))) i j
    convert this using 2 with g
    simp only [Function.comp, ← Matrix.map_mul, Matrix.map_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ChConj
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section
variable {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem ch_adj (g : R →+* R') (X : M4 R) : adj (X.map g) = (adj X).map g := by
  ext i j
  simp [adj]

private theorem ch_map (D : RD Φ R) (f : R →+* R') (g : R' →+* R'') : (D.map f).map g = D.map (g.comp f) := by
  apply RD.ext
  · ext s i j
    rfl
  · funext v i
    ext s
    rfl

private theorem ch_conj (D : RD Φ R) (g : R →+* R') (X : M4 R) (s : Γ) (i j : Fin 4) :
    (adj (X.map g) * (D.map g).r s * X.map g) i j = g ((adj X * D.r s * X) i j) := by
  rw [ch_adj]
  show ((adj X).map g * (D.r s).map g * X.map g) i j = _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rfl

private theorem ch_gsp (g : R →+* R') (X : M4 R) (i j : Fin 4) :
    (adj (X.map g) * X.map g - 1) i j = g ((adj X * X - 1) i j) := by
  rw [ch_adj, ← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private def chEq (D : RD Φ R) (n : Φ.ι → M4 R) : Set R :=
  {x | (∃ v i j, x = (adj (n v) * n v - 1) i j) ∨ (∃ v i, x = n v i i - 1) ∨ (∃ v i j, i < j ∧ x = n v i j) ∨
    (∃ v, ∃ s ∈ Φ.Gv v, ∃ i j, j < i ∧ x = (adj (n v) * D.r s * n v) i j) ∨
    (∃ v i, ∃ s : Φ.Gv v, x = (adj (n v) * D.r s * n v) i i - D.ψ v i s) ∨
    ∃ v i, ∃ s : Φ.Gv v, (s : Γ) ∈ Φ.Mu v ∧ x = D.ψ v i s - 1}

private theorem ch_iff (D : RD Φ R) (n : Φ.ι → M4 R) (g : R →+* R') :
    (D.map g).Flags (fun v => (n v).map g) ↔ ∀ x ∈ chEq D n, g x = 0 := by
  constructor
  · rintro ⟨hlow, hflag, hchar, hmu⟩ x hx
    rcases hx with ⟨v, i, j, rfl⟩ | ⟨v, i, rfl⟩ | ⟨v, i, j, hij, rfl⟩ | ⟨v, s, hs, i, j, hij, rfl⟩ |
      ⟨v, i, s, rfl⟩ | ⟨v, i, s, hs, rfl⟩
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow IsGSp at hl
      rw [← ch_gsp, hl.1]
      simp
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      rw [map_sub, map_one, sub_eq_zero]
      exact hl.2.1 i
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      exact hl.2.2 i j hij
    · rw [← ch_conj]
      exact hflag v s hs i j hij
    · rw [map_sub, sub_eq_zero, ← ch_conj]
      exact hchar v i s
    · rw [map_sub, map_one, sub_eq_zero]
      exact hmu v i s hs
  · intro h
    refine ⟨fun v => ?_, fun v s hs i j hij => ?_, fun v i s => ?_, fun v i s hs => ?_⟩
    · unfold IsLow IsGSp
      refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
      · ext i j
        have hx := h _ (Or.inl ⟨v, i, j, rfl⟩)
        rw [← ch_gsp, Matrix.sub_apply, sub_eq_zero] at hx
        rw [one_smul]
        exact hx
      · have hx := h _ (Or.inr (Or.inl ⟨v, i, rfl⟩))
        rw [map_sub, map_one, sub_eq_zero] at hx
        exact hx
      · exact h _ (Or.inr (Or.inr (Or.inl ⟨v, i, j, hij, rfl⟩)))
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, s, hs, i, j, hij, rfl⟩))))
      rw [← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, i, s, rfl⟩)))))
      rw [map_sub, sub_eq_zero, ← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, i, s, hs, rfl⟩)))))
      rw [map_sub, map_one, sub_eq_zero] at hx
      exact hx

end

theorem UpperTheory.V.Ws.sxChart :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {A₀ : Type} [CommRing A₀] (D : RD Φ A₀), ∃ (A : Type) (_ : CommRing A) (_ : Algebra A₀ A) (n : Φ.ι → M4 A), Algebra.FiniteType A₀ A ∧ Algebra.adjoin A₀ (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) = ⊤ ∧ (D.map (algebraMap A₀ A)).Flags n ∧ ∀ (R : Type) [CommRing R] (f : A₀ →+* R) (n' : Φ.ι → M4 R), (D.map f).Flags n' → ∃ F : A →+* R, F.comp (algebraMap A₀ A) = f ∧ ∀ v, (n v).map F = n' v := by
  intro O Γ _ _ Φ A₀ _ D
  classical
  let σ := Φ.ι × Fin 4 × Fin 4
  let N : Φ.ι → M4 (MvPolynomial σ A₀) := fun v => Matrix.of fun i j => MvPolynomial.X (v, i, j)
  let I : Ideal (MvPolynomial σ A₀) := Ideal.span (chEq (D.map MvPolynomial.C) N)
  let n : Φ.ι → M4 (MvPolynomial σ A₀ ⧸ I) := fun v => (N v).map (Ideal.Quotient.mk I)
  have hfac : algebraMap A₀ (MvPolynomial σ A₀ ⧸ I) = (Ideal.Quotient.mk I).comp MvPolynomial.C :=
    RingHom.ext fun _ => rfl
  refine ⟨MvPolynomial σ A₀ ⧸ I, inferInstance, inferInstance, n, ?_, ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A₀ I) (Ideal.Quotient.mkₐ_surjective A₀ I)
  · have hset : (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) =
        (Ideal.Quotient.mkₐ A₀ I) '' Set.range (MvPolynomial.X : σ → MvPolynomial σ A₀) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨MvPolynomial.X x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [hset, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A₀ I
  · rw [hfac, ← ch_map]
    exact (ch_iff _ _ _).2 fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
  · intro R _ f n' hn'
    let φ : MvPolynomial σ A₀ →+* R := MvPolynomial.eval₂Hom f fun x => n' x.1 x.2.1 x.2.2
    have hφC : φ.comp MvPolynomial.C = f := MvPolynomial.eval₂Hom_comp_C f _
    have hN : ∀ v, (N v).map φ = n' v := by
      intro v
      ext i j
      simp [φ, N]
    have hfl : ((D.map MvPolynomial.C).map φ).Flags (fun v => (N v).map φ) := by
      have hfun : (fun v => (N v).map φ) = n' := funext hN
      rw [ch_map, hφC, hfun]
      exact hn'
    have hker : I ≤ RingHom.ker φ :=
      Ideal.span_le.2 fun x hx => RingHom.mem_ker.2 ((ch_iff _ _ _).1 hfl x hx)
    refine ⟨Ideal.Quotient.lift I φ fun a ha => RingHom.mem_ker.1 (hker ha), ?_, ?_⟩
    · rw [hfac, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hφC]
    · intro v
      rw [← hN v]
      ext i j
      simp [n]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ContGr
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.sxContGr_pow {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (n : ℕ) :
    ∀ x ∈ Q ^ n, ∃ y ∈ J ^ n, e y = x := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_range] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨algebraMap Λ K a, by simp, e.commutes a⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := ih a ha
      obtain ⟨v, hv, rfl⟩ := hQ b hb
      exact ⟨u * v, by rw [pow_succ]; exact Ideal.mul_mem_mul hu hv, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_mul {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q P : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x)
    (hP : ∀ x ∈ P, ∃ y, e y = x) : ∀ x ∈ Q * P, ∃ y ∈ J, e y = x := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := hQ a ha
    obtain ⟨v, rfl⟩ := hP b hb
    exact ⟨u * v, J.mul_mem_right v hu, map_mul e u v⟩
  · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_cont {Λ K R Γ : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    [TopologicalSpace Γ] (e : K →ₐ[Λ] R) (he : Function.Injective e) (I : Ideal R) (J : Ideal K) (Q P P' : Submodule Λ R)
    (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (hP : ∀ x ∈ P, ∃ y, e y = x) (hP' : ∀ x ∈ P', ∃ y, e y = x)
    (h : ∀ n : ℕ, ∃ M : ℕ, P' ⊓ (I ^ M).restrictScalars Λ ≤ Q ^ n * P * P')
    (φ : Γ → K) (hφ : ∀ g, e (φ g) ∈ P') (hc : AdicCont I fun g => e (φ g)) : AdicCont J φ := by
  intro N
  obtain ⟨M, hM⟩ := h N
  have key : ∀ x ∈ Q ^ N * P * P', ∃ y ∈ J ^ N, e y = x := by
    intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := UpperTheory.V.Ws.sxContGr_mul e (J ^ N) (Q ^ N) P
        (UpperTheory.V.Ws.sxContGr_pow e J Q hQ N) hP a ha
      obtain ⟨v, rfl⟩ := hP' b hb
      exact ⟨u * v, (J ^ N).mul_mem_right v hu, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩
  have hcM : IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ M)) (e (φ g)) := hc M
  refine (IsLocallyConstant.iff_exists_open _).2 fun g0 => ?_
  refine ⟨{g | (Ideal.Quotient.mk (I ^ M)) (e (φ g)) = (Ideal.Quotient.mk (I ^ M)) (e (φ g0))},
    hcM.isOpen_fiber _, rfl, fun g hg => ?_⟩
  have hd : e (φ g) - e (φ g0) ∈ I ^ M := Ideal.Quotient.eq.1 hg
  have hd' : e (φ g) - e (φ g0) ∈ P' ⊓ (I ^ M).restrictScalars Λ :=
    Submodule.mem_inf.2 ⟨sub_mem (hφ g) (hφ g0), (Submodule.restrictScalars_mem _ _ _).2 hd⟩
  obtain ⟨y, hy, hye⟩ := key _ (hM hd')
  rw [← map_sub] at hye
  have : y = φ g - φ g0 := he hye
  exact Ideal.Quotient.eq.2 (this ▸ hy)

theorem UpperTheory.V.Ws.sxContGr :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] {Γ : Type} [TopologicalSpace Γ], (∀ (j : X) (φ : Γ → W.A), (∀ g, φ g ∈ W.gr j) → AdicCont (maximalIdeal R) (fun g => (φ g : R)) → AdicCont ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A)) φ) ∧ ∀ φ : Γ → W.gr 0, AdicCont (maximalIdeal R) (fun g => ((φ g : W.A) : R)) → AdicCont (maximalIdeal (W.gr 0)) φ := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ Γ _
  obtain ⟨hmax, -⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hfilt := part_filt Λ X R W hz
  have hb : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have ha : ∀ a : Λ, ((algebraMap Λ (W.gr 0) a : W.A) : R) = algebraMap Λ R a :=
    fun a => by first | rfl | simp
  refine ⟨fun j φ hφ hc => ?_, fun φ hc => ?_⟩
  · refine UpperTheory.V.Ws.sxContGr_cont W.A.val Subtype.val_injective (maximalIdeal R)
      ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part j) ?_ ?_ ?_
      (fun n => hfilt j n) φ (fun g => hφ g) hc
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      refine ⟨algebraMap (W.gr 0) W.A ⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        Ideal.mem_map_of_mem _ ((hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm)), ?_⟩
      rw [hb]
      rfl
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
  · let e : W.gr 0 →ₐ[Λ] R := AlgHom.mk ((W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A))
      (fun a => by
        show W.A.val (algebraMap (W.gr 0) W.A (algebraMap Λ (W.gr 0) a)) = _
        rw [hb]
        exact ha a)
    have he : ∀ b : W.gr 0, e b = ((b : W.A) : R) := fun b => by
      show W.A.val (algebraMap (W.gr 0) W.A b) = _
      rw [hb]
      rfl
    have hinj : Function.Injective e := by
      intro b c hbc
      rw [he, he] at hbc
      exact Subtype.ext (Subtype.ext hbc)
    have hc' : AdicCont (maximalIdeal R) fun g => e (φ g) := by
      have hfun : (fun g => e (φ g)) = fun g => ((φ g : W.A) : R) := funext fun g => he _
      rw [hfun]
      exact hc
    refine UpperTheory.V.Ws.sxContGr_cont e hinj (maximalIdeal R) (maximalIdeal (W.gr 0))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part 0) ?_ ?_ ?_
      (fun n => hfilt 0 n) φ (fun g => by rw [he]; exact (φ g).2) hc'
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      exact ⟨⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        (hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm), he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoreGen
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxCoreGen :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) = ⊤ := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W hD D' hmap
  have hr : ∀ g i j, D.r g i j = (D'.r g i j : R) := by
    subst hmap
    intro g i j
    first | rfl | simp [RD.map]
  have hψ : ∀ v i t, D.ψ v i t = (D'.ψ v i t : R) := by
    subst hmap
    intro v i t
    first | rfl | simp [RD.map]
  set S := Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) with hS
  have hbA : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have hgr : ∀ x : W.A, (x : R) ∈ W.part 0 → x ∈ S := by
    intro x hx
    have h := Subalgebra.algebraMap_mem S (⟨x, hx⟩ : W.gr 0)
    rwa [hbA] at h
  have hc : ∀ c : Λ, algebraMap Λ W.A c ∈ S := by
    intro c
    apply hgr
    have h0 : algebraMap Λ R c ∈ W.part 0 := by
      have := (algebraMap Λ (W.gr 0) c).2
      first
        | exact this
        | (have e : ((algebraMap Λ (W.gr 0) c : W.A) : R) = algebraMap Λ R c := by first | rfl | simp
           rw [← e]; exact this)
    first | exact h0 | simpa using h0
  have hr' : ∀ g i j, D'.r g i j ∈ S := fun g i j => Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
  have hz : ∀ s, W.zA s ∈ S := by
    intro s
    rcases hD.var s with ⟨g, i, j, c, hzs, -, -⟩ | ⟨v, i, t, c, hzs, -⟩
    · have e : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hr]
        rfl
      rw [e]
      exact sub_mem (hr' g i j) (hc c)
    · have e : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hψ]
        rfl
      rw [e]
      refine sub_mem (hgr _ ?_) (hc c)
      rw [← hψ]
      exact hD.chr v i t
  rw [eq_top_iff]
  intro a ha0
  clear ha0
  have ha : a ∈ Algebra.adjoin Λ (↑(W.gr 0) ∪ Set.range W.zA) := by
    rw [gr_gen Λ R (ℤ × ℤ) W]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨s, rfl⟩
    · exact hgr x hx
    · exact hz s
  | algebraMap c => exact hc c
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CpZero
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def cpZeroPol {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    (w : ℤ × ℤ) : AddSubgroup A[X] where
  carrier := {p | ∀ n, p.coeff n ∈ 𝒜 w}
  add_mem' := fun {p q} hp hq n => by rw [coeff_add]; exact add_mem (hp n) (hq n)
  zero_mem' := fun n => by rw [coeff_zero]; exact zero_mem _
  neg_mem' := fun {p} hp n => by rw [coeff_neg]; exact neg_mem (hp n)

private theorem cpZeroPol_graded {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (cpZeroPol 𝒜) := by
  refine { one_mem := ?_, mul_mem := ?_ }
  · change ∀ n, (1 : A[X]).coeff n ∈ 𝒜 0
    intro n
    rw [coeff_one]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  · intro i j p q hp hq
    change ∀ n, p.coeff n ∈ 𝒜 i at hp
    change ∀ n, q.coeff n ∈ 𝒜 j at hq
    change ∀ n, (p * q).coeff n ∈ 𝒜 (i + j)
    intro n
    rw [coeff_mul]
    exact Submodule.sum_mem _ fun x _ => SetLike.mul_mem_graded (hp x.1) (hq x.2)

theorem UpperTheory.V.Ws.sxCpZero :
    ∀ {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A) [SetLike.GradedMonoid 𝒜] (M : M4 A), (∀ i j, M i j ∈ 𝒜 (wt i j)) → ∀ n, M.charpoly.coeff n ∈ 𝒜 0 := by
  intro Λ A _ _ _ 𝒜 _ M hM
  have := cpZeroPol_graded 𝒜
  have hC : ∀ i j, C (M i j) ∈ cpZeroPol 𝒜 (wt i j) := fun i j n => by
    rw [coeff_C]
    split_ifs
    · exact hM i j
    · exact zero_mem _
  have hX : (X : A[X]) ∈ cpZeroPol 𝒜 0 := fun n => by
    rw [coeff_X]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  have hE : ∀ i j, M.charmatrix i j ∈ cpZeroPol 𝒜 (wt i j) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [Matrix.charmatrix_apply_eq]
      refine sub_mem ?_ (hC i i)
      have : wt i i = 0 := by simp [wt]
      rw [this]; exact hX
    · rw [Matrix.charmatrix_apply_ne _ _ _ h]
      exact neg_mem (hC i j)
  have key : M.charpoly ∈ cpZeroPol 𝒜 0 := by
    rw [Matrix.charpoly, Matrix.det_apply]
    refine AddSubgroup.sum_mem _ fun σ _ => ?_
    have h0 : ∑ i, wt (σ i) i = 0 := by
      have h1 := Equiv.sum_comp σ lamW
      have h2 := Equiv.sum_comp σ muW
      ext
      · simp only [wt, Prod.fst_sum, Finset.sum_sub_distrib, h1, sub_self, Prod.fst_zero]
      · simp only [wt, Prod.snd_sum, Finset.sum_sub_distrib, h2, sub_self, Prod.snd_zero]
    have hp : ∏ i, M.charmatrix (σ i) i ∈ cpZeroPol 𝒜 (∑ i, wt (σ i) i) :=
      SetLike.prod_mem_graded (cpZeroPol 𝒜) (fun i => wt (σ i) i) (fun i => M.charmatrix (σ i) i) fun i _ => hE (σ i) i
    rw [h0] at hp
    rw [Units.smul_def]
    exact AddSubgroup.zsmul_mem _ hp _
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurDesc
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLaurDesc :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {X : Type} [AddCommGroup X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] (W : WPres Λ X R) {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur (Λ := Λ) c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y) → ∃ f : W.A →ₐ[Λ] R', ∀ j, ∀ x ∈ W.gr j, e (F x) = HahnSeries.single (τ j) (f x) := by
  intro Λ _ _ X _ _ R _ _ W R' _ _ _ S _ _ _ c e hL τ F hF
  let φ : ∀ j, W.gr j →ₗ[Λ] R' := fun j =>
    { toFun := fun x => (e (F ((x : W.A) : R))).coeff (τ j)
      map_add' := fun x y => by
        simp only [Submodule.coe_add, Subalgebra.coe_add, map_add (f := _), HahnSeries.coeff_add]
      map_smul' := fun a x => by
        have h1 : (((a • x : W.gr j) : W.A) : R) = algebraMap Λ R a * ((x : W.A) : R) := by
          rw [← Algebra.smul_def]; rfl
        rw [h1, map_mul, AlgHom.commutes, map_mul, hL.alg, HahnSeries.coeff_single_zero_mul,
          RingHom.id_apply, Algebra.smul_def] }
  have key : ∀ j (x : W.gr j), e (F ((x : W.A) : R)) = HahnSeries.single (τ j) (φ j x) := by
    intro j x
    obtain ⟨y, hy⟩ := hF j ((x : W.A) : R) x.2
    have h2 : φ j x = y := by
      show (e (F ((x : W.A) : R))).coeff (τ j) = y
      rw [hy, HahnSeries.coeff_single_same]
    rw [h2, hy]
  have hone : φ 0 (GradedMonoid.GOne.one (A := fun j => W.gr j)) = 1 := by
    show (e (F 1)).coeff (τ 0) = 1
    rw [map_one, map_one, map_zero, HahnSeries.coeff_one, if_pos rfl]
  have hmul : ∀ {i j} (a : W.gr i) (b : W.gr j), φ _ (GradedMonoid.GMul.mul (A := fun j => W.gr j) a b) = φ i a * φ j b := by
    intro i j a b
    show (e (F (((a : W.A) : R) * ((b : W.A) : R)))).coeff (τ (i + j)) = _
    rw [map_mul, map_mul, key, key, HahnSeries.single_mul_single, map_add (f := _), HahnSeries.coeff_single_same]
  refine ⟨(DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
    (DirectSum.decomposeAlgEquiv W.gr).toAlgHom, fun j x hx => ?_⟩
  have h : DirectSum.decompose W.gr x = DirectSum.of (fun j => W.gr j) j ⟨x, hx⟩ :=
    DirectSum.decompose_of_mem W.gr hx
  have h3 : ((DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
      (DirectSum.decomposeAlgEquiv W.gr).toAlgHom) x = φ j ⟨x, hx⟩ := by
    show DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul (DirectSum.decompose W.gr x) = _
    rw [h]
    exact DirectSum.toSemiring_of (fun j => (φ j).toAddMonoidHom) hone hmul j _
  rw [h3]
  exact key j ⟨x, hx⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxLimPt
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLimPt :
    ∀ {Λ A R S : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing R] [Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R), (∀ N : ℕ, ∃ f : A →ₐ[Λ] R ⧸ I ^ (N + 1), ∀ s, f (e s) = Ideal.Quotient.mk _ (y s)) → (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + 1)), (∀ s, f (e s) = f' (e s)) → f = f') → ∃ f : A →ₐ[Λ] R, ∀ s, f (e s) = y s :=
  _root_.UpperTheory.Reformulated.B.Qg4.sxLimPt
end

