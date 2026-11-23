module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ChiMapOfRep
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

section SlopeTestRemainingChoices

open Polynomial

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg, h]
  · simp [GDet.repAlg, h, hij]

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ A[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg]
  · simp [GDet.repAlg, hij]

private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  refine Polynomial.map_aeval_eq_aeval_map ?_ q M
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_eq_diagonal, h]

private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  have hp : ∀ k : ℕ, N ^ k * Y = Y * M ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mul, mul_add, hp, hq]
  | monomial k a => simp [aeval_monomial, ← Algebra.smul_def, hp]

private theorem key {n : ℕ} {A K : Type} [CommRing A] [IsDomain A] [Field K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) A)
    (hY : x • (M * Y) = Y * M) : Y = 0 := by
  have h1 := aeval_inter M (x • M) Y (by rw [← hY, ← Matrix.smul_mul]) M.charpoly
  rw [Matrix.aeval_self_charpoly, mul_zero] at h1
  have hn : IsNilpotent (f.mapMatrix M - algebraMap K _ c) := by
    refine ⟨n, ?_⟩
    have := aeval_mapM f M M.charpoly
    rw [Matrix.aeval_self_charpoly, map_zero, hM] at this
    simpa using this.symm
  have hu : IsUnit (f.mapMatrix (x • M) - algebraMap K _ c) := by
    have e : f.mapMatrix (x • M) - algebraMap K _ c =
        f x • (f.mapMatrix M - algebraMap K _ c) + algebraMap K _ ((f x - 1) * c) := by
      ext a b
      by_cases h : a = b <;> simp [Matrix.algebraMap_eq_diagonal, h]
      ring
    rw [e]
    refine IsNilpotent.isUnit_add_right_of_commute (hn.smul _) ?_ (Algebra.commute_algebraMap_right _ _)
    exact (IsUnit.mk0 _ (mul_ne_zero (sub_ne_zero.2 hx) hc)).map _
  have hd : (aeval (x • M) M.charpoly).det ≠ 0 := by
    intro h0
    have h2 := RingHom.map_det f (aeval (x • M) M.charpoly)
    rw [h0, map_zero, aeval_mapM, hM, map_pow, map_sub, aeval_X, aeval_C] at h2
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hu.pow n)).ne_zero h2.symm
  have h3 : (aeval (x • M) M.charpoly).det • Y = 0 := by
    have := congrArg (fun W => (aeval (x • M) M.charpoly).adjugate * W) h1
    simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero] using this
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  exact (mul_eq_zero.1 h4).resolve_left hd

end SlopeTestRemainingChoices

theorem UpperTheory.V.Th.Nm.n4 :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] (r : Resid F O n) (ρ : F.G₀ →* GL (Fin n) O), r.V0ok → (GDet.ofRep (mat ρ)).map (res O O : O →+* ResidueField O) = r.Dbar → ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ F.D0, ((F.eps O O g : Oˣ) : O) • (mat ρ g * Z) = Z * mat ρ g) → Z = 0 := by
  intro l _ n F O _ _ _ _ _ r ρ h hred Z hZ
  obtain ⟨-, h2, g, hg, h3⟩ := h
  ext i i'
  suffices H : Z = 0 by rw [H]
  refine key (res O O : O →+* ResidueField O) (mat ρ g) ((F.eps O O g : Oˣ) : O) (r.chib i g)
    (Units.ne_zero _) ?_ ?_ Z (hZ g hg)
  · intro h4
    apply h3
    apply Units.ext
    rw [Units.val_one, ← h4]
    exact ((res O O).commutes _).symm
  · have h := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) hred
    simp only [Resid.Dbar, chi_map_ofRep, chi_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp only [fun k => h2 g hg k i]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ConjAll
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.conjAll :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P Q P' : GL (Fin n) (Qbar l)), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q → (Continuous ρ → Continuous (cj Q ρ)) ∧ (Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) = ⊤) ∧ (F.IsForm c.O n ρ P → F.IsForm c.O n (cj Q ρ) P') ∧ GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) ∧ (∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly) ∧ (∀ S, DetQ F c.O ρ P S → DetQ F c.O (cj Q ρ) P' S) ∧ ∀ I ψ z, IsOrdCoc F ρ P I ψ z → IsOrdCoc F (cj Q ρ) P' I ψ fun g => ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * z g * Q := by
  intro l _ n F c ρ P Q P' hP
  have hm : ∀ g, mat (cj Q ρ) g = ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * mat ρ g * Q := by
    intro g
    change ((cj Q ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = _
    rw [cj_apply, Units.val_mul, Units.val_mul]; rfl
  have hch : ∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly := by
    intro g
    have := Matrix.charpoly_units_conj Q⁻¹ (mat ρ g)
    rw [hm, ← this, ← Matrix.coe_units_inv, inv_inv]
  have hinv : ∀ w : GL (Fin n) (Qbar l), (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * Q := by
    intro w; rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  have hmul : ∀ w : GL (Fin n) (Qbar l), ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * w := fun w => Units.val_mul _ _
  have hD : GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) :=
    (UpperTheory.V.AlgebraTools.Det.repApi (mat ρ)).2.2.2.2.2.2.2 _ Q fun g => by
      rw [hm, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h1 : (Q : Matrix (Fin n) (Fin n) (Qbar l)) * ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv Q
  have h2 : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (Q : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.inv_mul Q
  generalize hqi : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = qi at *
  generalize hq : (Q : Matrix (Fin n) (Fin n) (Qbar l)) = q at *
  have a1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), q * (qi * X) = X := fun X => by rw [← mul_assoc, h1, one_mul]
  have a2 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qi * (q * X) = X := fun X => by rw [← mul_assoc, h2, one_mul]
  have t1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qiᵀ * (qᵀ * X) = X := fun X => by
    rw [← mul_assoc, ← transpose_mul, h1, transpose_one, one_mul]
  refine ⟨fun h => ?_, fun h => ?_, fun h g => ?_, hD, hch, fun S h z hz hc hp ht => ?_, fun I ψ z h => ?_⟩
  · have : (cj Q ρ : F.G₀ → _) = fun g => Q⁻¹ * ρ g * Q := funext (cj_apply Q ρ)
    rw [this]
    exact (continuous_const.mul h).mul continuous_const
  · have key : ∀ Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)),
        qi * Z * q ∈ Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, hm g⟩
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
      | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    refine eq_top_iff.2 fun Z _ => ?_
    have := key (q * Z * qi) (h ▸ Submodule.mem_top)
    simpa only [mul_assoc, a2, h2, mul_one] using this
  · have := congrArg (fun X => qᵀ * X * q) (h g)
    simp only [mul_smul_comm, smul_mul_assoc] at this
    rw [hm, hm, hP, ← this]
    simp only [transpose_mul, mul_assoc, a1, t1]
  · obtain ⟨Y, hY⟩ := h (fun g => q * z g * qi) ((continuous_const.mul hz).mul continuous_const)
      (fun g g' => by
        simp only [hc g g', hm, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, h1, mul_one])
      (fun g => by
        have := congrArg (fun X => qiᵀ * X * qi) (hp g)
        simpa only [hP, transpose_mul, mul_assoc, t1, h1, mul_one] using this)
      (fun σ hσ k => by
        have := ht σ hσ k
        rw [← map_pow, hm, map_pow, ← mul_assoc, trace_mul_comm] at this
        simpa only [mul_assoc] using this)
    refine ⟨qi * Y * q, fun g => ?_⟩
    have := congrArg (fun X => qi * X * q) (hY g)
    simpa only [hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, a2, h2, mul_one] using this
  · refine ⟨(continuous_const.mul h.cont).mul continuous_const, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · simp only [h.coc g g', hm, mul_add, add_mul, mul_assoc, a1]
    · have := congrArg (fun X => qᵀ * X * q) (h.pol g)
      simpa only [hP, transpose_mul, mul_assoc, t1, a1, mul_neg, neg_mul] using this
    · simp [h.ine u g hg]
    · obtain ⟨w, Y, hw⟩ := h.ord v
      refine ⟨Q⁻¹ * w, qi * Y * q, fun g => ?_⟩
      have e1 : (Q⁻¹ * w)⁻¹ * cj Q ρ (F.φ v g) * (Q⁻¹ * w) = w⁻¹ * ρ (F.φ v g) * w := by
        rw [cj_apply]; group
      have e2 : (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (qi * z (F.φ v g) * q - dY F (mat (cj Q ρ)) (qi * Y * q) (F.φ v g)) *
          ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
          ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) (Qbar l)) := by
        simp only [hinv, hmul, dY, hm, mul_sub, sub_mul, mul_assoc, a1]
      rw [e1, e2]
      exact hw g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.DerOf
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.derOf :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) [IsCO O (DualNumber O)] (p : Pair r (DualNumber O)) (D : GDet n O F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Oˣ), p.Maps (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) D ψ → ∃ (x : B.B →ₐ[O] O) (δ : B.B →ₗ[O] O), IsDer x δ ∧ B.u.Maps x.toRingHom D ψ ∧ (∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = (p.D.tr (MonoidAlgebra.single g 1)).snd) ∧ ∀ v i g, δ (B.u.ψ v i g : B.Bˣ) = ((p.ψ v i g : (DualNumber O)ˣ) : DualNumber O).snd := by
  intro l _ n F O _ _ _ r B _ p D ψ hp
  obtain ⟨f, ⟨hD, hψ⟩, -⟩ := B.univ (DualNumber O) p
  refine ⟨(TrivSqZeroExt.fstHom O O O).comp f, (TrivSqZeroExt.sndHom O O).comp f.toLinearMap, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    change (f (a * b)).snd = (f a).fst • (f b).snd + (f b).fst • (f a).snd
    rw [map_mul, DualNumber.snd_mul, smul_eq_mul, smul_eq_mul]
    ring
  · rw [← hp.1, ← hD, (UpperTheory.V.CA.d_gmap B.u.D).2.1]
    rfl
  · intro v i
    rw [← hp.2 v i, ← hψ v i]
    rfl
  · intro g
    have h := ((UpperTheory.V.CA.d_gmap B.u.D).2.2.1 (f : B.B →+* DualNumber O) (MonoidAlgebra.single g 1)).2 1
    rw [hD, MonoidAlgebra.mapRingHom_single, map_one] at h
    change (f (B.u.D.lam 1 (MonoidAlgebra.single g 1))).snd = (p.D.lam 1 (MonoidAlgebra.single g 1)).snd
    rw [h]
    rfl
  · intro v i g
    rw [← hψ v i]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.HomMu
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.homMu :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : G → c.O), AdicCont (maximalIdeal c.O) d → (∀ g h, d (g * h) = d g + d h) → ∀ g ∈ muG l G, d g = 0 := by
  intro l _ c G _ _ _ d hd hadd g hg
  have hd1 : d 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    simpa using h
  let f : G →* Multiplicative c.O :=
    { toFun := fun x => Multiplicative.ofAdd (d x)
      map_one' := by simp [hd1]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (d (x * y)) = Multiplicative.ofAdd (d x) * Multiplicative.ofAdd (d y)
        rw [hadd]; rfl }
  have hcomm : ∀ x ∈ commutator G, d x = 0 := by
    intro x hx
    have := Abelianization.commutator_subset_ker f hx
    rw [MonoidHom.mem_ker] at this
    exact this
  have hcl : ∀ x ∈ (commutator G).topologicalClosure, d x = 0 := by
    intro x hx
    have hmemN : ∀ N : ℕ, d x ∈ (maximalIdeal c.O) ^ N := by
      intro N
      have hclosed := (hd N).isClosed_fiber 0
      have hsub : ((commutator G : Subgroup G) : Set G) ⊆
          {y | Ideal.Quotient.mk ((maximalIdeal c.O) ^ N) (d y) = 0} := by
        intro y hy
        simp only [Set.mem_setOf_eq]
        rw [hcomm y hy, map_zero]
      have hx' : x ∈ closure ((commutator G : Subgroup G) : Set G) := by
        rw [← Subgroup.topologicalClosure_coe]; exact hx
      have hfib := closure_minimal hsub hclosed hx'
      simp only [Set.mem_setOf_eq] at hfib
      exact Ideal.Quotient.eq_zero_iff_mem.mp hfib
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal c.O) (maximalIdeal.isMaximal c.O).ne_top
    have hin : d x ∈ ⨅ i, (maximalIdeal c.O) ^ i := (Submodule.mem_iInf _).mpr hmemN
    rw [hbot] at hin
    exact (Submodule.mem_bot _).mp hin
  have hg' : (QuotientGroup.mk' (commutator G).topologicalClosure g : TopologicalAbelianization G) ∈
      CommGroup.primaryComponent (TopologicalAbelianization G) l := hg
  obtain ⟨k, hk⟩ := hg'
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
  have h0 := hcl _ hk
  have hdp : d (g ^ (l ^ k)) = (l ^ k) • d g := map_pow f g (l ^ k)
  rw [hdp] at h0
  exact (smul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem inOf_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem inOf_div {l : ℕ} [Fact l.Prime] (c : Coef l) (a b : c.O) (hb : (b : PadicAlgCl l) ≠ 0)
    (h : ‖(a : PadicAlgCl l)‖ ≤ ‖(b : PadicAlgCl l)‖) : (a : PadicAlgCl l) / b ∈ c.O := by
  refine (coefSup l).2.2.2 c _ ((inOf_intIff _).2 ?_) ⟨a, b, hb, div_mul_cancel₀ _ hb⟩
  rw [norm_div]
  exact div_le_one_of_le₀ h (norm_nonneg _)

private theorem inOf_fin {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l)) (hs : ∀ x ∈ s, ‖x‖ ≤ 1) :
    ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x ∈ s, x ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨d, hd, hd'⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨e, he, he'⟩ := (coefSup l).2.2.1 d a ((inOf_intIff _).2 (hs a (Finset.mem_insert_self _ _)))
    refine ⟨e, hd.trans he, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact he'
    · exact he (hd' x hx)

theorem UpperTheory.V.Th.Nm.inOf :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l), (∀ (ι : Type) [Finite ι] (x : ι → Qbar l), (∀ i, ‖x i‖ ≤ 1) → ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ i, x i ∈ c'.O) ∧ (∀ x ∈ c.O, ‖x‖ ≤ 1) ∧ (∀ x ∈ c.O, ‖x‖ = 1 → ∀ h : x ∈ c.O, IsUnit (⟨x, h⟩ : c.O)) ∧ ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → c.O), (Continuous fun g => (f g : Qbar l)) → AdicCont (maximalIdeal c.O) f := by
  intro l _ c
  have hle : ∀ x ∈ c.O, ‖x‖ ≤ 1 := by
    intro x hx
    haveI := c.fin
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
    exact (inOf_intIff x).mp (hi.map c.O.val)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    have e := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at e
    rw [e, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hlO : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    haveI := c.dvr
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 : ((u : c.O) : PadicAlgCl l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hb := hle _ ((u⁻¹ : c.Oˣ) : c.O).2
    rw [hu] at h1
    have := congrArg norm h1
    rw [norm_mul, norm_one, SubringClass.coe_natCast] at this
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg ((l : ℕ) : PadicAlgCl l))
    linarith
  refine ⟨?_, hle, ?_, ?_⟩
  · intro ι _ x hx
    classical
    haveI := Fintype.ofFinite ι
    obtain ⟨c', hc', hs⟩ := inOf_fin c (Finset.univ.image x) (by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hx i)
    exact ⟨c', hc', fun i => hs _ (Finset.mem_image_of_mem x (Finset.mem_univ i))⟩
  · intro x _ hn h
    have hx0 : (x : PadicAlgCl l) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv := inOf_div c 1 ⟨x, h⟩ hx0 (by simp [hn])
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    simp [hx0]
  · intro Γ _ f hf N
    haveI := c.dvr
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hr : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ ^ N := by
      apply pow_pos
      rw [norm_pos_iff]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    filter_upwards [hf.continuousAt.eventually (Metric.ball_mem_nhds _ hr)] with g hg
    rw [dist_eq_norm] at hg
    rw [Ideal.Quotient.eq]
    set t : c.O := ((l : ℕ) : c.O) ^ N
    have ht0 : (t : PadicAlgCl l) ≠ 0 := by
      simp only [t, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
      exact pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hq := inOf_div c (f g - f g0) t ht0 (by
      simp only [t, SubmonoidClass.coe_pow, SubringClass.coe_natCast, AddSubgroupClass.coe_sub, norm_pow]
      exact hg.le)
    have he : f g - f g0 = (⟨_, hq⟩ : c.O) * t := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul]
      exact (div_mul_cancel₀ _ ht0).symm
    rw [he]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hlO N)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.OrdInt
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem ordInt_diag {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · simp

private theorem ordInt_conj {K : Type} [Field K] {n : ℕ} (b : GL (Fin n) K) {M : Matrix (Fin n) (Fin n) K}
    (hb : (b : Matrix (Fin n) (Fin n) K).BlockTriangular id) (hM : M.BlockTriangular id) :
    ((b : Matrix (Fin n) (Fin n) K) * M * ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).BlockTriangular id ∧
      ∀ i, ((b : Matrix (Fin n) (Fin n) K) * M * ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = M i i := by
  have hi : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    letI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨(hb.mul hM).mul hi, fun i => ?_⟩
  have h1 := ordInt_diag hb hi i
  rw [Units.mul_inv, Matrix.one_apply_eq] at h1
  rw [ordInt_diag (hb.mul hM) hi, ordInt_diag hb hM, mul_right_comm, ← h1, one_mul]

private def ordInt_V (l : ℕ) [Fact l.Prime] : ValuationSubring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rwa [norm_neg]
  mem_or_inv_mem' := fun a => by
    rcases le_total ‖a‖ 1 with h | h
    · exact Or.inl h
    · right
      show ‖a⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

theorem UpperTheory.V.Th.Nm.ordInt :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (v : F.Vl) (ψ : Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (w : GL (Fin n) (Qbar l)) (Y : Matrix (Fin n) (Fin n) (Qbar l)), OrdAt F ρ v ψ z w Y → ∃ w' : GL (Fin n) (Qbar l), IntM (w' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((w'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ OrdAt F ρ v ψ z w' Y := by
  intro l _ n F ρ v ψ z w Y h
  obtain ⟨k, hk⟩ := UpperTheory.V.Pr.T.iwasawaVal (ordInt_V l) n (w : Matrix (Fin n) (Fin n) (Qbar l))
  let k' : GL (Fin n) (Qbar l) := GeneralLinearGroup.map (ordInt_V l).subtype k
  have hb : ((k' * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id := hk
  refine ⟨k'⁻¹, fun i j => ?_, fun i j => ?_, fun g => ?_⟩
  · have : k'⁻¹ = GeneralLinearGroup.map (ordInt_V l).subtype k⁻¹ := (map_inv _ _).symm
    rw [this]
    exact ((k⁻¹ : GL (Fin n) (ordInt_V l)) i j).2
  · rw [inv_inv]
    exact (k i j).2
  · obtain ⟨h1, h2, h3, h4⟩ := h g
    have e : ∀ M : Matrix (Fin n) (Fin n) (Qbar l),
        ((k'⁻¹⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * M * (k'⁻¹ : GL (Fin n) (Qbar l)) =
        ((k' * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * M * (w : Matrix (Fin n) (Fin n) (Qbar l))) *
          (((k' * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
      intro M
      rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    have c1 := ordInt_conj (k' * w) hb
      (M := ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ (F.φ v g) : Matrix (Fin n) (Fin n) (Qbar l)) *
        (w : Matrix (Fin n) (Fin n) (Qbar l))) (fun i j hij => h1 i j hij)
    have c2 := ordInt_conj (k' * w) hb (fun i j hij => h3 i j hij)
    rw [← e] at c1 c2
    refine ⟨fun i j hij => c1.1 hij, fun i => (c1.2 i).trans (h2 i), fun i j hij => c2.1 hij,
      fun hg i => (c2.2 i).trans (h4 hg i)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SmithGen
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.smith_gen {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (P : GL (Fin n) K) : ∃ (U V : GL (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖(U : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((U⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖(V : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((V⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) K) = U * diagonal d * V :=
  _root_.UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen P

theorem UpperTheory.V.Th.Nm.smith :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (P : GL (Fin n) (Qbar l)), ∃ (U V : GL (Fin n) (Qbar l)) (d : Fin n → Qbar l), IntM (U : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((U⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM (V : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) (Qbar l)) = U * diagonal d * V := by
  intro l _ n P
  exact smith_gen P
end

