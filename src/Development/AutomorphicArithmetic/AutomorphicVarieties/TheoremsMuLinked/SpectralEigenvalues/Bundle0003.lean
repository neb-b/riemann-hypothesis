module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaLam
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.betaLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), ∀ a : abelian₂ O Empty D, A.β (algebraMap (abelian₂ O Empty D) A.R a) = b.lam a := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A a
  haveI hOO : IsCO O O :=
    { complete := IsCoef.complete
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Empty D) := co_mvps O O (Empty ⊕ Fin D)
  have hmax : ∀ s : Empty ⊕ Fin D, b.lam (MvPowerSeries.X s) ∈ maximalIdeal B := by
    intro s
    rw [← res_eq_zero_iff O B, res_map, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h0 := hu.map MvPowerSeries.constantCoeff
    simp at h0
  obtain ⟨F, _, huniq⟩ :=
    co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) hmax
  let F1 : abelian₂ O Empty D →ₐ[O] B :=
    A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have e1 : F1 = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => ?_⟩
    · rw [MvPowerSeries.c_eq_algebraMap]
      exact F1.commutes x
    · rcases s with e | k
      · exact e.elim
      · show A.β (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (Sum.inr k))) = _
        rw [A.segmentWeightExponent k, b.segmentWeightExponent k, map_sub, map_mul, map_one, AlgHom.commutes]
        congr 2
        have hp := congrArg (fun χ => ((χ (b.wt.γ k) : Bˣ) : B)) (A.β_pair.2 (b.wt.v k) (b.wt.i k))
        simpa [pushCh] using hp
  have e2 : b.lam = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => rfl⟩
    rw [MvPowerSeries.c_eq_algebraMap]
    exact b.lam.commutes x
  have := congrArg (fun φ : abelian₂ O Empty D →ₐ[O] B => φ a) (e1.trans e2.symm)
  simpa [F1] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaSurj
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C) (S : Set C) (hS : GenBy O S)
    (h1 : ∀ b ∈ S, b ∈ f.range) : Function.Surjective f := by
  apply co_surj O R C f
  intro x hx
  obtain ⟨a, ha, hxa⟩ := hS 2 x
  have hrange : Algebra.adjoin O S ≤ f.range := Algebra.adjoin_le (fun b hb => h1 b hb)
  obtain ⟨y, hy⟩ := hrange ha
  have hy' : f y = a := hy
  have hsq : maximalIdeal C ^ 2 ≤ maximalIdeal C := Ideal.pow_le_self (by norm_num)
  have haM : a ∈ maximalIdeal C := by
    have h2 : a = x - (x - a) := by ring
    rw [h2]
    exact sub_mem hx (hsq hxa)
  have hyM : y ∈ maximalIdeal R := by
    rw [← mem_iff f y, hy']
    exact haM
  have hx' : x = f y + (x - a) := by rw [hy']; ring
  rw [hx']
  exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem f hyM)) (Ideal.mem_sup_right hxa)

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  simp [GDet.lam, GDet.chi, GDet.comap, Finsupp.mapDomain_sub, MonoidAlgebra.mapDomain,
    Finsupp.mapDomain_single]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  simpa using h.2 i

private theorem surjective_levelChangeBaseGroupHom {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) :
    Function.Surjective h.p₀ := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := h.surj x
  refine ⟨⟨y, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker, ← h.η y]
  exact hx

theorem UpperTheory.V.Th.Sp.betaSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), GenBy O (pairVals u) → Function.Surjective A.β := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A hgen
  obtain ⟨hD, hψ⟩ := A.β_pair
  refine surj_of_gen A.β _ hgen ?_
  rintro b (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
  · obtain ⟨g, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    refine ⟨A.p.D.lam i (MonoidAlgebra.single g 1), ?_⟩
    have h := lam_map A.p.D A.β.toRingHom i g
    rw [hD, lam_comap] at h
    exact h.symm
  · exact ⟨(A.p.ψ v i g : A.R), congrArg (fun χ => ((χ g : _ˣ) : B)) (hψ v i)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Imports
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.chi :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] (q n m : ℕ) (a : Fin q → ℕ), (∀ j, m ≤ a j) → ∀ p : Fin q × Fin n, ∃ χ : Del l n a →* Multiplicative (Om O m), ∀ p', χ (Pi.mulSingle p' (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd (if p = p' then 1 else 0) := by
  intro l _ O _ _ _ _ q n m a ha p
  have hl : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have h0 : (zmultiplesHom (Om O m) 1) ((l ^ a p.1 : ℕ) : ℤ) = 0 := by
    have : ((l : O) ^ a p.1) ∈ maximalIdeal O ^ m :=
      Ideal.pow_le_pow_right (ha _) (Ideal.pow_mem_pow hl _)
    have h2 := Ideal.Quotient.eq_zero_iff_mem.mpr this
    simpa using h2
  let f : ZMod (l ^ a p.1) →+ Om O m := ZMod.lift _ ⟨zmultiplesHom (Om O m) 1, h0⟩
  have f1 : f 1 = 1 := by
    have := ZMod.lift_coe (l ^ a p.1) ⟨zmultiplesHom (Om O m) 1, h0⟩ 1
    simpa [f] using this
  refine ⟨(AddMonoidHom.toMultiplicative f).comp
    (Pi.evalMonoidHom (fun p : Fin q × Fin n => Multiplicative (ZMod (l ^ a p.1))) p), fun p' => ?_⟩
  by_cases h : p = p'
  · subst h
    simp [f1]
  · simp [h, Pi.mulSingle_eq_of_ne h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsFurther
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.trans :
    ∀ (R M W : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] (q n : ℕ) (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (tr : M →ₗ[R] W), Function.Surjective tr → LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) → (∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)) → (∀ τ m, tr (act1 τ m) = actw (MvPolynomial.aeval (Sum.elim MvPolynomial.X 0) τ) (tr m)) ∧ ∀ (I : Ideal R) m, tr m ∈ (I • ⊤ : Submodule R W) → m ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
  intro R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu
  have hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)
  refine ⟨fun τ => ?_, fun I m hm => ?_⟩
  · induction τ using MvPolynomial.induction_on with
    | C a =>
        intro m
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
        simp
    | add p r hp hr =>
        intro m
        simp [map_add (f := _), hp, hr]
    | mul_X p s hp =>
        intro m
        rcases s with ⟨j, i⟩ | ⟨j, i⟩
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply,
            MvPolynomial.aeval_X, Sum.elim_inl]
          exact congrArg _ (hu j i m)
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr,
            show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]
          simp
  · have htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [htop] at hm
    obtain ⟨m', hm', he⟩ := hm
    have hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, he, sub_self]
    have hmm : m = m' + (m - m') := by abel
    rw [hmm]
    exact Submodule.add_mem_sup hm' hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.LamW
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.lamW :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (lam : M →+ O) (m₀ : M), TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ (a : B) m, lam (a • m) = x a * lam m) → ∃ (lw : V →+ O) (v : V), (∀ τ w, lw (act τ w) = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) τ * lw w) ∧ lw v = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) f * lam m₀ := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α lam m₀ hT hP hlam
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hT
  letI : Algebra B O := (x : B →+* O).toAlgebra
  let ε : MSplitAlg P n →ₐ[B] O := MSplitAlg.lift P n (fun j i => α j i) (fun j => (hP j).symm)
  have hε : ∀ t : PU R q n, ε (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β.toRingHom t)) =
      MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) t := by
    intro t
    show MvPolynomial.aeval (fun p : Fin q × Fin n => α p.1 p.2) (MvPolynomial.map β.toRingHom t) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rfl
  let lamL : M →ₗ[B] O :=
    { toFun := lam
      map_add' := lam.map_add
      map_smul' := fun a m => hlam a m }
  let Λ : MSplitAlg P n ⊗[B] M →ₗ[B] O :=
    TensorProduct.lift ((LinearMap.mul B O).compl₁₂ ε.toLinearMap lamL)
  have hΛt : ∀ a m, Λ (a ⊗ₜ m) = ε a * lam m := by
    intro a m
    show TensorProduct.lift _ (a ⊗ₜ m) = _
    rw [TensorProduct.lift.tmul]
    rfl
  have hΛs : ∀ (a : MSplitAlg P n) z, Λ (a • z) = ε a * Λ z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul a' m => rw [TensorProduct.smul_tmul', smul_eq_mul, hΛt, hΛt, map_mul, mul_assoc]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  refine ⟨Λ.toAddMonoidHom.comp ψ, φ (1 ⊗ₜ m₀), ?_, ?_⟩
  · intro τ w
    show Λ (ψ (act τ w)) = _ * Λ (ψ w)
    rw [h2, hΛs, hε]
  · show Λ (ψ (φ (1 ⊗ₜ m₀))) = _
    rw [h4, hΛs, hε, hΛt, map_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Msp
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.msp :
    ∀ (O B κ : Type) [CommRing O] [CommRing B] [Algebra O B] [Fintype κ] (n : ℕ) (x : B →ₐ[O] O) (P : κ → Polynomial B) (α : κ → Fin n → O), (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → ∀ a : MvPolynomial (κ × Fin n) B, MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) a = 0 → Ideal.Quotient.mk (mSplitIdeal P n) ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) * a) ∈ (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) := by
  intro O B κ _ _ _ _ n x P α hP a ha
  classical
  set J : Ideal (MSplitAlg P n) := (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) with hJ
  let ψ : MvPolynomial (κ × Fin n) B →+* (MSplitAlg P n ⧸ J) :=
    (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (mSplitIdeal P n))
  let g : B →+* (MSplitAlg P n ⧸ J) := ψ.comp MvPolynomial.C
  let h : O →+* (MSplitAlg P n ⧸ J) := g.comp (algebraMap O B)
  have hg : ∀ b : B, g b = (Ideal.Quotient.mk J) (algebraMap B (MSplitAlg P n) b) := by
    intro b
    show (Ideal.Quotient.mk J) ((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b)) = _
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  have hgx : g = h.comp (x : B →+* O) := by
    ext b
    show g b = g (algebraMap O B (x b))
    rw [← sub_eq_zero, ← map_sub, hg, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker]
    simp
  have hg' : (Ideal.Quotient.mk J).comp (algebraMap B (MSplitAlg P n)) = h.comp (x : B →+* O) := by
    rw [← hgx]
    ext b
    exact (hg b).symm
  have hroot : ∀ j i, ∏ k, (ψ (MvPolynomial.X (j, i)) - h (α j k)) = 0 := by
    intro j i
    have e := MSplitAlg.prod_root P n j
    have e2 := congrArg (fun q => Polynomial.eval (ψ (MvPolynomial.X (j, i))) (q.map (Ideal.Quotient.mk J))) e
    rw [Polynomial.map_map, hg', ← Polynomial.map_map, hP j] at e2
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at e2
    rw [← e2]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hh : ∀ c : O, ψ (MvPolynomial.C (algebraMap O B c)) = h c := fun _ => rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ψ (_ * a) = 0
  rw [map_mul]
  set δ := ψ (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) with hδ
  have hδX : ∀ p : κ × Fin n, δ * (ψ (MvPolynomial.X p) - h (α p.1 p.2)) = 0 := by
    rintro ⟨j, i⟩
    obtain ⟨q, hq⟩ : (∏ k ∈ Finset.univ.erase i,
        (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) : MvPolynomial (κ × Fin n) B) ∣
        ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) :=
      (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ j))
    rw [hδ, hq, map_mul, mul_right_comm]
    simp only [map_prod, map_sub, hh]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i), hroot, zero_mul]
  have key : ∀ b : MvPolynomial (κ × Fin n) B,
      δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0 := by
    intro b
    refine MvPolynomial.induction_on
      (motive := fun b => δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0)
      b ?_ ?_ ?_
    · intro c
      have hc : ψ (MvPolynomial.C c) = h ((x : B →+* O) c) := by
        show g c = _
        rw [hgx]
        rfl
      rw [MvPolynomial.eval₂_C, hc, sub_self, mul_zero]
    · intro p q hp hq
      rw [map_add (f := _), MvPolynomial.eval₂_add, map_add (f := _)]
      linear_combination hp + hq
    · intro p v hp
      rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul]
      beta_reduce
      linear_combination (ψ (MvPolynomial.X v)) * hp +
        h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) p) * hδX v
  have hk := key a
  rw [ha, map_zero, sub_zero] at hk
  exact hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.PlNormal
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem core_ex {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem pl_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) :
    (PL l H).Normal := by
  refine ⟨fun a ha g => ?_⟩
  simp only [PL, Subgroup.mem_iInf] at ha ⊢
  intro U hU
  exact U.isNormal'.conj_mem a (ha U hU) g

private theorem pl_le (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : OpenNormalSubgroup Γ) :
    PL l H.toSubgroup ≤ H.toSubgroup := by
  intro a ha
  simp only [PL, Subgroup.mem_iInf] at ha
  exact ha H fun h hh => ⟨0, by rw [pow_zero, pow_one]; exact hh⟩

theorem UpperTheory.V.Th.Sp.close :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ K : ℕ, ∀ᶠ N in atTop, ∀ j a b, mat y.ρ ((T.h N).p₀ (T.ph N j)) a b - mat y.ρ (T.sg j) a b ∈ maximalIdeal O ^ K := by
  intro l _ L G0 T n O _ _ _ y hPL K
  haveI := pl_normal l T.H.toSubgroup
  have hle := pl_le l T.H
  let R : G0.G₀ →* Matrix (Fin n) (Fin n) (O ⧸ maximalIdeal O ^ K) :=
    (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix.toMonoidHom.comp (mat y.ρ)
  have hR : ∀ g i j, R g i j = Ideal.Quotient.mk (maximalIdeal O ^ K) (mat y.ρ g i j) := fun _ _ _ => rfl
  have h0 : IsLocallyConstant fun g : G0.G₀ => R g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have : ∀ᶠ g in nhds g0, ∀ i j, R g i j = R g0 i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        (y.cont i j K).eventually_eq g0
    filter_upwards [this] with g hg
    exact Matrix.ext hg
  have ho : IsOpen ((R.ker.map G0.η.ker.subtype : Subgroup G0.Γ) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ (h0.isOpen_fiber 1)
  have h1R : ∀ g, y.ρ g = 1 → R g = 1 := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix (Units.coeHom _ (y.ρ g)) = 1
    rw [h, map_one, map_one]
  obtain ⟨V, h1, h2⟩ := core_ex _ (PL l T.H.toSubgroup) ho fun g hg =>
    ⟨⟨g, T.H_η g (hle hg)⟩, h1R _ (hPL _ hg), rfl⟩
  filter_upwards [Filter.eventually_all.2 fun j => T.ph_lim V j h1] with N hN j a b
  obtain ⟨u, hu, e1⟩ := h2 (hN j)
  have e2 : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (by
    show (T.h N).p (T.ph N j) = (u : G0.Γ) * T.sg j
    rw [show (u : G0.Γ) = _ from e1, inv_mul_cancel_right])
  have e3 : R ((T.h N).p₀ (T.ph N j)) = R (T.sg j) := by
    rw [e2, map_mul, show R u = 1 from hu, one_mul]
  rw [← Ideal.Quotient.eq, ← hR, ← hR, e3]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.TracePartialCharpolySingle
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem UpperTheory.V.Th.Sp.trace_partial_charpoly_single {T G : Type} [CommRing T] [Group G] (t : MonoidAlgebra T G →ₗ[T] T)
    (g ta : G) (a y : T) :
    t (MonoidAlgebra.single g a * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y)) =
      a * (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) -
        y * (a * t (MonoidAlgebra.single g 1)) := by
  have h : ∀ (k : G) (b : T), t (MonoidAlgebra.single k b) = b * t (MonoidAlgebra.single k 1) := fun k b => by
    rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [mul_sub, mul_sub, mul_one, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one,
    map_sub, map_sub, h (g * ta) a, h g a, h g (a * y)]
  ring

theorem UpperTheory.V.Th.Sp.q2 :
    ∀ (O T G X : Type) [CommRing O] [CommRing T] [Algebra O T] [Group G] [AddCommGroup X] [Module O X] (n : ℕ) (D : GDet n T G) (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ta : G) (y : T) (Q : MonoidAlgebra T G), 1 ≤ n → IsDer x del → x y = 0 → (∀ g, x (D.tr (MonoidAlgebra.single (g * ta) 1)) = x (D.tr (MonoidAlgebra.single g 1))) → x (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = 0 ∧ del (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = del (D.tr (MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0))) - x (D.tr Q) • del y := by
  intro O T G X _ _ _ _ _ _ n D x del ta y Q hn hd hy hta
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  have ht' : ∀ z, D.tr z = t z := fun z => by rw [ht, (UpperTheory.V.CA.d_toDet D z).2.2.1]
  simp only [ht'] at hta ⊢
  induction Q using MonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    simp only [map_add (f := _), add_mul, hP.1, hQ.1, hP.2, hQ.2, add_zero, true_and, add_smul]
    abel
  | single g a =>
    have h : t (MonoidAlgebra.single g a) = a * t (MonoidAlgebra.single g 1) := by
      rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [MonoidAlgebra.mapRingHom_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, h]
    have h0 : x (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) = 0 := by
      rw [map_sub, hta, sub_self]
    refine ⟨by rw [map_sub, map_mul, map_mul, h0, hy, mul_zero, zero_mul, sub_zero], ?_⟩
    rw [map_sub, hd, hd, h0, hy, zero_smul, zero_smul, add_zero, zero_add, zero_mul, sub_zero, RingHom.comp_apply,
      ← Algebra.smul_def, map_smul]
    rfl
end

