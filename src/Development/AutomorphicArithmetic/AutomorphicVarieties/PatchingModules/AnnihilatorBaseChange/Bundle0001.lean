module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChBarPush
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem gDet_chi_map_C_mapRingHom_gen {n : ℕ} {B B' G : Type} [CommRing B] [CommRing B'] [Group G] (g : B →+* B') (D : GDet n B G) (m : ℕ) (y : Fin m → MonoidAlgebra B G) : ((D.map g).map MvPolynomial.C).chi (MonoidAlgebra.mapRingHom G (MvPolynomial.map g) (GDet.gen y)) = Polynomial.map (MvPolynomial.map g) ((D.map MvPolynomial.C).chi (GDet.gen y)) := by
  letI i0 : Algebra B (Polynomial (MvPolynomial (Fin m) B)) := RingHom.toAlgebra ((algebraMap (MvPolynomial (Fin m) B) (Polynomial (MvPolynomial (Fin m) B))).comp MvPolynomial.C)
  letI i1 : Algebra B (Polynomial (MvPolynomial (Fin m) B')) := RingHom.toAlgebra (((algebraMap (MvPolynomial (Fin m) B') (Polynomial (MvPolynomial (Fin m) B'))).comp MvPolynomial.C).comp g)
  let φ : Polynomial (MvPolynomial (Fin m) B) →ₐ[B] Polynomial (MvPolynomial (Fin m) B') :=
    { Polynomial.mapRingHom (MvPolynomial.map g) with
      commutes' := fun b => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat _ _ φ (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y))
  have hx : MonoidAlgebra.mapRingHom G (φ : Polynomial (MvPolynomial (Fin m) B) →+* Polynomial (MvPolynomial (Fin m) B')) (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y)) = MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapRingHom G (MvPolynomial.map g) (GDet.gen y)) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    have hX : (φ : Polynomial (MvPolynomial (Fin m) B) →+* Polynomial (MvPolynomial (Fin m) B')) Polynomial.X = Polynomial.X := by
      change Polynomial.map (MvPolynomial.map g) Polynomial.X = _
      exact Polynomial.map_X _
    rw [hX]
    congr 1
    ext h a b
    simp only [MonoidAlgebra.coeff_mapRingHom]
    change ((Polynomial.map (MvPolynomial.map g) (Polynomial.C _)).coeff a).coeff b = _
    rw [Polynomial.map_C]
  rw [hx] at key
  exact key

private theorem gDet_mapRingHom_mem_ch_map_of_mem_ch {n : ℕ} {B B' G : Type} [CommRing B] [CommRing B'] [Group G] (g : B →+* B') (D : GDet n B G) (z : MonoidAlgebra B G) (hz : z ∈ D.CH) : MonoidAlgebra.mapRingHom G g z ∈ (D.map g).CH := by
  obtain ⟨m, y, β, hz⟩ := hz
  refine ⟨m, fun j => MonoidAlgebra.mapRingHom G g (y j), β, fun h => ?_⟩
  have hgen : GDet.gen (fun j => MonoidAlgebra.mapRingHom G g (y j)) = MonoidAlgebra.mapRingHom G (MvPolynomial.map g) (GDet.gen y) := by
    ext h
    simp [GDet.gen, Finsupp.finsetSum_apply, MonoidAlgebra.mapRingHom]
  have hcomm : (MonoidAlgebra.mapRingHom G (MvPolynomial.map g)).comp (algebraMap (MvPolynomial (Fin m) B) (MonoidAlgebra (MvPolynomial (Fin m) B) G)) = (algebraMap (MvPolynomial (Fin m) B') (MonoidAlgebra (MvPolynomial (Fin m) B') G)).comp (MvPolynomial.map g) := by
    refine RingHom.ext fun q => ?_
    simp [MonoidAlgebra.mapRingHom, MonoidAlgebra.coe_algebraMap, Finsupp.mapRange_single]
  rw [hgen, gDet_chi_map_C_mapRingHom_gen, Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomm, ← Polynomial.hom_eval₂]
  simp [MonoidAlgebra.mapRingHom, MvPolynomial.coeff_map, hz h, Polynomial.aeval_def]

private theorem monoidAlgebra_map_mapDomain_comm {R S G G' : Type} [Semiring R] [Semiring S] (F : R →+ S) (p : G → G') (x : MonoidAlgebra R G) : MonoidAlgebra.map F (MonoidAlgebra.mapDomain p x) = MonoidAlgebra.mapDomain p (MonoidAlgebra.map F x) := by
  ext h
  simp only [MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_mapDomain]
  rw [Finsupp.mapDomain_mapRange _ _ _ _ (map_add F)]

private theorem gDet_mapDomainRingHom_mem_ch_of_mem_ch_comap {n : ℕ} {B' G G' : Type} [CommRing B'] [Group G] [Group G'] (p : G →* G') (D' : GDet n B' G') (z : MonoidAlgebra B' G) (hz : z ∈ (D'.comap p).CH) : MonoidAlgebra.mapDomainRingHom B' p z ∈ D'.CH := by
  obtain ⟨m, y, β, hz⟩ := hz
  refine ⟨m, fun j => MonoidAlgebra.mapDomainRingHom B' p (y j), β, fun h => ?_⟩
  have hgen : GDet.gen (fun j => MonoidAlgebra.mapDomainRingHom B' p (y j)) = MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p (GDet.gen y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GDet.gen, map_sum, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom, Finsupp.mapDomain_smul, monoidAlgebra_map_mapDomain_comm]
  have hchi : ((D'.comap p).map MvPolynomial.C).chi (GDet.gen y) = (D'.map MvPolynomial.C).chi (MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p (GDet.gen y)) := by
    have e : MonoidAlgebra.mapDomainRingHom (Polynomial (MvPolynomial (Fin m) B')) p (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y)) = MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G' Polynomial.C (MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p (GDet.gen y)) := by
      rw [map_sub]
      simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom, monoidAlgebra_map_mapDomain_comm]
    calc ((D'.comap p).map MvPolynomial.C).chi (GDet.gen y) = (D'.map MvPolynomial.C).D (Polynomial (MvPolynomial (Fin m) B')) (MonoidAlgebra.mapDomainRingHom (Polynomial (MvPolynomial (Fin m) B')) p (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y))) := rfl
      _ = _ := by rw [e]; rfl
  have hcomm : (MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p).comp (algebraMap (MvPolynomial (Fin m) B') (MonoidAlgebra (MvPolynomial (Fin m) B') G)) = algebraMap (MvPolynomial (Fin m) B') (MonoidAlgebra (MvPolynomial (Fin m) B') G') := by
    refine RingHom.ext fun q => ?_
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coe_algebraMap]
  have hzW : z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) ((Polynomial.aeval (GDet.gen y)) (((D'.comap p).map MvPolynomial.C).chi (GDet.gen y))) := by
    ext g
    simp [hz g]
  rw [hgen, ← hchi, Polynomial.aeval_def, ← hcomm, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hzW, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply, ← monoidAlgebra_map_mapDomain_comm]
  simp

theorem UpperTheory.V.Pa.Core.chBarPush :
    ∀ (n : ℕ) (B B' G G' : Type) [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B'] [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (g : B →+* B') [IsLocalHom g] (p : G →* G') (D : GDet n B G) (D' : GDet n B' G') (Z : Set (MonoidAlgebra B G)), Continuous p → D.map g = D'.comap p → ∀ z ∈ D.chBar Z, MonoidAlgebra.mapDomainRingHom B' p (MonoidAlgebra.mapRingHom G g z) ∈ D'.chBar ((fun y => MonoidAlgebra.mapDomainRingHom B' p (MonoidAlgebra.mapRingHom G g y)) '' Z) := by
  intro n B B' G G' _ _ _ _ _ _ _ _ g _ p D D' Z hp hD z hz
  unfold GDet.chBar closureIdeal at hz ⊢
  simp only [TwoSidedIdeal.mem_iInf] at hz ⊢
  intro N H'
  let H : OpenNormalSubgroup G := ⟨H'.toOpenSubgroup.comap p hp, H'.isNormal'.comap p⟩
  have hzN := hz N H
  let φ : MonoidAlgebra B G →+* MonoidAlgebra B' G' := (MonoidAlgebra.mapDomainRingHom B' p).comp (MonoidAlgebra.mapRingHom G g)
  have hm : Ideal.map g (maximalIdeal B) ≤ maximalIdeal B' := Ideal.map_le_iff_le_comap.2 (fun x hx => (mem_maximalIdeal _).2 ((map_mem_nonunits_iff g x).2 ((mem_maximalIdeal _).1 hx)))
  refine (TwoSidedIdeal.mem_comap φ).1 ((TwoSidedIdeal.span_le.2 ?_) hzN)
  rintro x (((hx | hx) | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩) <;> rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] <;> apply TwoSidedIdeal.subset_span
  · refine Or.inl (Or.inl (Or.inl ?_))
    apply gDet_mapDomainRingHom_mem_ch_of_mem_ch_comap
    rw [← hD]
    exact gDet_mapRingHom_mem_ch_map_of_mem_ch g D x hx
  · exact Or.inl (Or.inl (Or.inr ⟨x, hx, rfl⟩))
  · refine Or.inl (Or.inr ⟨g a, Ideal.pow_right_mono hm N (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem g ha), ?_⟩)
    simp [φ, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
  · refine Or.inr ⟨p h, hh, ?_⟩
    show φ (MonoidAlgebra.single h 1 - 1) = _
    rw [map_sub, map_one]
    simp [φ, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChainAbs
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.chainAbs :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (h d : ℕ) (q : Fin (h + 1) → Ideal R) (o : PatchedSupportCompletions s ii ann q d) (St : Ideal (R ⧸ ii) → Prop) (Th : ∀ i, Ideal (o.B i) → Prop), (∀ i, (q i).IsPrime ∧ ii ≤ q i) → (∀ p p', p ≤ p' → St p' → St p) → (∀ i (Z Q : Ideal (o.B i)), Z.IsPrime → Q.IsPrime → St (Z.comap (algebraMap (R ⧸ ii) (o.B i))) → (d : WithBot ℕ∞) ≤ ringKrullDim (o.B i ⧸ Z) → St (Q.comap (algebraMap (R ⧸ ii) (o.B i))) ∨ Th i Q → Z ≤ Q) → ∀ E : Fin h → Ideal (R ⧸ ii), (∀ i, (E i).IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ E i) ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.castSucc ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.succ ∧ ∀ Q : Ideal (o.B i.castSucc), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = E i → Th _ Q) → (∃ p : Ideal (R ⧸ ii), p.IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) ∧ p.comap (Ideal.Quotient.mk ii) ≤ q 0 ∧ St p ∧ ann ≤ p.comap (Ideal.Quotient.mk ii)) → ∀ p : Ideal (R ⧸ ii), p.IsPrime → (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) → p.comap (Ideal.Quotient.mk ii) ≤ q (Fin.last h) → (St p ∨ ∀ Q : Ideal (o.B (Fin.last h)), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = p → Th _ Q) → ann ≤ p.comap (Ideal.Quotient.mk ii) := by
  intro Λ R σ _ _ _ _ s ii ann h d q o St Th hq hSt hkey E hE h0 p hp hpX hpq hpS
  have hOver : ∀ (j : Fin (h + 1)) (P : Ideal (R ⧸ ii)), P.IsPrime →
      P.comap (Ideal.Quotient.mk ii) ≤ q j →
      ∃ Q : Ideal (o.B j), Q.IsPrime ∧ Q.comap (algebraMap (R ⧸ ii) (o.B j)) = P := by
    intro j P hP hle
    apply (IsCplAt.exists_prime_over (R ⧸ ii) _ (o.B j) (o.cpl j)).1 P hP
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hle hx)
  have hInv : ∀ j : Fin (h + 1), ∃ Z : Ideal (o.B j), Z.IsPrime ∧ o.S j ≤ Z ∧
      St (Z.comap (algebraMap (R ⧸ ii) (o.B j))) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      obtain ⟨p0, hp0, hp0X, hp0q, hp0St, hp0ann⟩ := h0
      obtain ⟨Q, hQ, hQc⟩ := hOver 0 p0 hp0 hp0q
      refine ⟨Q, hQ, ?_, by rw [hQc]; exact hp0St⟩
      refine (o.fib 0 Q hQ ?_).mpr ?_
      · intro a
        have hx := hp0X a
        rw [← hQc] at hx
        exact hx
      · rw [hQc]
        exact hp0ann
    | succ i ih =>
      obtain ⟨Z, hZ, hSZ, hStZ⟩ := ih
      obtain ⟨hEp, hEX, hEc, hEs, hETh⟩ := hE i
      obtain ⟨Q, hQ, hQc⟩ := hOver i.castSucc (E i) hEp hEc
      have hThQ := hETh Q hQ hQc
      obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
      have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
      have hZ0Q := hkey i.castSucc Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) (Or.inr hThQ)
      have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B i.castSucc)
          (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
        intro a
        have hx := hEX a
        rw [← hQc] at hx
        exact hx
      obtain ⟨Z', hZ', hSZ', hZ'c⟩ := o.move i.castSucc i.succ Z0 Q hZ0.1.1 hQ hZ0.1.2 hZ0Q hQX
        (by rw [hQc]; exact hEs)
      exact ⟨Z', hZ', hSZ', by rw [hZ'c]; exact hStZ0⟩
  obtain ⟨Z, hZ, hSZ, hStZ⟩ := hInv (Fin.last h)
  obtain ⟨Q, hQ, hQc⟩ := hOver (Fin.last h) p hp hpq
  have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B (Fin.last h))
      (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
    intro a
    have hx := hpX a
    rw [← hQc] at hx
    exact hx
  obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
  have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
  have hQc' : St (Q.comap (algebraMap (R ⧸ ii) (o.B (Fin.last h)))) ∨ Th (Fin.last h) Q := by
    rcases hpS with h1 | h1
    · left
      rw [hQc]
      exact h1
    · right
      exact h1 Q hQ hQc
  have hZ0Q := hkey (Fin.last h) Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) hQc'
  have hann := (o.fib _ Q hQ hQX).mp (hZ0.1.2.trans hZ0Q)
  rw [hQc] at hann
  exact hann
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChiRes
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem chi_diag {n : ℕ} {k G : Type} [CommRing k] [Group G] (χ : Fin n → G →* kˣ) (g : G) :
    (GDet.ofRep (diagRep χ)).chi (MonoidAlgebra.single g 1) =
      ∏ i, (Polynomial.X - Polynomial.C (χ i g : k)) := by
  change (GDet.repAlg (diagRep χ) (Polynomial k) _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]

theorem UpperTheory.V.Pa.Core.chiRes :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (g : F.G₀) (ut : Fin n → O), (∀ i, residue O (ut i) = r.chib i g) → (u.D.chi (MonoidAlgebra.single g 1)).Monic ∧ (u.D.chi (MonoidAlgebra.single g 1)).natDegree = n ∧ (u.D.chi (MonoidAlgebra.single g 1)).map (residue B) = ∏ i, (Polynomial.X - Polynomial.C (residue B (algebraMap O B (ut i)))) := by
  intro l _ F n O _ _ _ r B _ _ _ u g ut hut
  have hm : (u.D.chi (MonoidAlgebra.single g 1)).Monic := by
    have hchi : u.D.toDet.chi (MonoidAlgebra.single g 1) = u.D.chi (MonoidAlgebra.single g 1) := by
      change u.D.D (Polynomial B) (ofT B F.G₀ (Polynomial B)
        (Polynomial.X ⊗ₜ 1 - 1 ⊗ₜ MonoidAlgebra.single g 1)) = _
      congr 1
      rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul,
        MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rfl
    rw [← hchi]
    exact (UpperTheory.V.CA.d_chi _ _).2.2.2.2.1
  have h1 : (u.D.chi (MonoidAlgebra.single g 1)).map (res O B : B →+* ResidueField O) =
      ∏ i, (Polynomial.X - Polynomial.C (residue O (ut i))) := by
    have hchi : (u.D.map (res O B : B →+* ResidueField O)).chi
        (MonoidAlgebra.mapRingHom F.G₀ (res O B : B →+* ResidueField O) (MonoidAlgebra.single g 1)) =
        (u.D.chi (MonoidAlgebra.single g 1)).map (res O B) := by
      let f : B →+* ResidueField O := res O B
      letI : Algebra B (Polynomial (ResidueField O)) := ((algebraMap _ _).comp f).toAlgebra
      let φ : Polynomial B →ₐ[B] Polynomial (ResidueField O) :=
        { Polynomial.mapRingHom f with
          commutes' := fun a => by
            change Polynomial.map f (Polynomial.C a) = Polynomial.C (f a)
            exact Polynomial.map_C f }
      have h := u.D.nat (Polynomial B) (Polynomial (ResidueField O)) φ
        (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom F.G₀ Polynomial.C (MonoidAlgebra.single g 1))
      refine Eq.trans ?_ h
      change u.D.D (Polynomial (ResidueField O)) _ = u.D.D (Polynomial (ResidueField O)) _
      congr 1
      have hφ : (φ : Polynomial B →+* Polynomial (ResidueField O)) = Polynomial.mapRingHom f := rfl
      rw [hφ]
      ext x : 2
      simp
    rw [← hchi, u.red, MonoidAlgebra.mapRingHom_single, map_one, Resid.Dbar,
      chi_diag]
    simp only [hut]
  have hc : (ResidueField.map (algebraMap O B)).comp (res O B : B →+* ResidueField O) = residue B := by
    ext x
    exact (RingEquiv.ofBijective _ (resMap_bijective O B)).apply_symm_apply (residue B x)
  have h2 : (u.D.chi (MonoidAlgebra.single g 1)).map (residue B) =
      ∏ i, (Polynomial.X - Polynomial.C (residue B (algebraMap O B (ut i)))) := by
    conv_lhs => rw [← hc, ← Polynomial.map_map, h1]
    simp [Polynomial.map_prod, ResidueField.map_residue]
  refine ⟨hm, ?_, h2⟩
  rw [← hm.natDegree_map (residue B), h2, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.closeLift :
    ∀ (Ph A B : Type) [Group Ph] [Group A] [Group B] (π : Ph →* A) (π' : Ph →* B) (V : Subgroup Ph) [V.Normal], π.ker ⊔ V = π'.ker ⊔ V → (∀ a b g, Close π π' V a b → π' g = b → ∃ g', π g' = a ∧ g⁻¹ * g' ∈ V) ∧ ∀ k, π' k = 1 → ∃ k', π k' = 1 ∧ k⁻¹ * k' ∈ V := by
  intro Ph A B _ _ _ π π' V _ hsup
  have hdec : ∀ x, π' x = 1 → ∃ k, π k = 1 ∧ ∃ v ∈ V, k * v = x := by
    intro x hx
    have hx' : x ∈ π.ker ⊔ V := by
      rw [hsup]
      exact Subgroup.mem_sup_left (MonoidHom.mem_ker.2 hx)
    obtain ⟨k, hk, v, hv, hkv⟩ := Subgroup.mem_sup_of_normal_right.1 hx'
    exact ⟨k, MonoidHom.mem_ker.1 hk, v, hv, hkv⟩
  refine ⟨fun a b g ⟨g0, g0', ha, hb, hV⟩ hg => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, v, hv, hkv⟩ := hdec (g0'⁻¹ * g) (by rw [map_mul, map_inv, hb, hg, inv_mul_cancel])
    refine ⟨g0 * k, by rw [map_mul, ha, hk, mul_one], ?_⟩
    have hg' : g = g0' * (k * v) := by rw [hkv, mul_inv_cancel_left]
    rw [hg']
    have hw : g0'⁻¹ * g0 ∈ V := by
      have := V.inv_mem hV
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have hconj : k⁻¹ * (g0'⁻¹ * g0) * k ∈ V := by
      have := (inferInstance : V.Normal).conj_mem _ hw k⁻¹
      rwa [inv_inv] at this
    have heq : (g0' * (k * v))⁻¹ * (g0 * k) = v⁻¹ * (k⁻¹ * (g0'⁻¹ * g0) * k) := by group
    rw [heq]
    exact V.mul_mem (V.inv_mem hv) hconj
  · obtain ⟨k', hk', v, hv, rfl⟩ := hdec k hk
    refine ⟨k', hk', ?_⟩
    have heq : (k' * v)⁻¹ * k' = v⁻¹ := by group
    rw [heq]
    exact V.inv_mem hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FibEquiv
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem fib_tmul_zero {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (t : S ⊗[R] X) : k • t = 0 := by
  have hI : Ideal.span (Set.range y) ≤ Module.annihilator R X := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact Module.mem_annihilator.mpr (hX a)
  have hmap : (Ideal.span (Set.range y)).map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] X) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hr' := Module.mem_annihilator.mp (hI hr)
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro u
    rw [algebraMap_smul]
    induction u using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | tmul a b => rw [← TensorProduct.tmul_smul, hr' b, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  exact Module.mem_annihilator.mp (hmap hk) t

private theorem fib_tmul_zero' {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (x : X) : k ⊗ₜ[R] x = 0 := by
  have := fib_tmul_zero y S X hX k hk (1 ⊗ₜ[R] x)
  rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this

private theorem fib_bij {R σ : Type} [CommRing R] (y : σ → R) (S BB : Type) [CommRing S] [Algebra R S]
    [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (hD : ∀ b : BB, ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB))
    (hS : ∀ s : S, algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) →
      s ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) :
    Function.Bijective (LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap) := by
  classical
  set IB := (Ideal.span (Set.range y)).map (algebraMap R BB) with hIB
  choose sel hsel using hD
  have hz : ∀ (s1 s2 : S) (x : X), algebraMap S BB s1 - algebraMap S BB s2 ∈ IB →
      s1 ⊗ₜ[R] x = s2 ⊗ₜ[R] x := by
    intro s1 s2 x h12
    have h0 := fib_tmul_zero' y S X hX (s1 - s2) (hS _ (by rwa [map_sub])) x
    rwa [TensorProduct.sub_tmul, sub_eq_zero] at h0
  have hrt : ∀ (s : S) (x : X), LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  let F : BB →ₗ[R] X →ₗ[R] S ⊗[R] X := LinearMap.mk₂ R (fun b x => sel b ⊗ₜ[R] x)
    (fun b1 b2 x => by
      rw [← TensorProduct.add_tmul]
      apply hz
      have e : algebraMap S BB (sel (b1 + b2)) - algebraMap S BB (sel b1 + sel b2) = (b1 - algebraMap S BB (sel b1)) + (b2 - algebraMap S BB (sel b2)) - (b1 + b2 - algebraMap S BB (sel (b1 + b2))) := by
        rw [map_add (f := _)]
        ring
      rw [e]
      exact sub_mem (add_mem (hsel b1) (hsel b2)) (hsel _))
    (fun r b x => by
      rw [TensorProduct.smul_tmul']
      apply hz
      have e : algebraMap S BB (sel (r • b)) - algebraMap S BB (r • sel b) = algebraMap R BB r * (b - algebraMap S BB (sel b)) - (r • b - algebraMap S BB (sel (r • b))) := by
        rw [Algebra.smul_def r (sel b), map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def r b]
        ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ (hsel b)) (hsel _))
    (fun b x1 x2 => TensorProduct.tmul_add _ _ _)
    (fun r b x => TensorProduct.tmul_smul _ _ _)
  let g := TensorProduct.lift F
  have hg : ∀ (b : BB) (x : X), g (b ⊗ₜ[R] x) = sel b ⊗ₜ[R] x := fun b x => by
    simp [g, F]
  constructor
  · apply Function.LeftInverse.injective (g := g)
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      rw [hrt, hg]
      apply hz
      have e : algebraMap S BB (sel (algebraMap S BB s)) - algebraMap S BB s = -(algebraMap S BB s - algebraMap S BB (sel (algebraMap S BB s))) := by ring
      rw [e]
      exact neg_mem (hsel _)
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b x =>
      refine ⟨sel b ⊗ₜ[R] x, ?_⟩
      rw [hrt]
      have h0 := fib_tmul_zero' y BB X hX (b - algebraMap S BB (sel b)) (hsel b) x
      rwa [TensorProduct.sub_tmul, sub_eq_zero, eq_comm] at h0
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨c, hc⟩ := hv
      exact ⟨a + c, by rw [map_add (f := _), ha, hc]⟩

private theorem fib_dense {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (b : BB) :
    ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) := by
  obtain ⟨k, r, hkr⟩ := h.dense 1 b
  rw [pow_one] at hkr
  set v := algebraMap S BB (IsLocalization.Away.invSelf (S := S) f) with hv
  have hvf : v * algebraMap R BB f = 1 := by
    rw [hv, IsScalarTower.algebraMap_apply R S BB f, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  refine ⟨algebraMap R S r * (IsLocalization.Away.invSelf (S := S) f) ^ k, ?_⟩
  have : b - algebraMap S BB (algebraMap R S r * IsLocalization.Away.invSelf (S := S) f ^ k) = v ^ k * (algebraMap R BB f ^ k * b - algebraMap R BB r) := by
    rw [map_mul, map_pow, ← hv, ← IsScalarTower.algebraMap_apply]
    calc b - algebraMap R BB r * v ^ k = (v * algebraMap R BB f) ^ k * b - algebraMap R BB r * v ^ k := by rw [hvf, one_pow, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hkr

private theorem fib_strict {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (s : S) (hs : algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB)) :
    s ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
  obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) s
  obtain ⟨k, hk⟩ := m.2
  simp only at hrm
  rw [← hk] at hrm
  have hB : algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ 1).map (algebraMap R BB) := by
    rw [pow_one, IsScalarTower.algebraMap_apply R S BB r, ← hrm, map_mul]
    exact Ideal.mul_mem_right _ _ hs
  obtain ⟨k', hk'⟩ := h.strict 1 r hB
  rw [pow_one] at hk'
  have hmem : s * algebraMap R S (f ^ (k' + k)) ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
    rw [pow_add, map_mul, mul_comm (algebraMap R S (f ^ k')), ← mul_assoc, hrm, ← map_mul, mul_comm]
    exact Ideal.mem_map_of_mem _ hk'
  have hu : IsUnit (algebraMap R S (f ^ (k' + k))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow _
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have : s = s * algebraMap R S (f ^ (k' + k)) * w := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hmem

theorem UpperTheory.V.Pa.Core.fibEquiv :
    ∀ (R σ : Type) [CommRing R] [Fintype σ] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB] (X : Type) [AddCommGroup X] [Module R X] (MM : Type) [AddCommGroup MM] [Module S MM] [Module BB MM] [IsScalarTower S BB MM] (q : MM →ₗ[S] S ⊗[R] X), IsYCpl y f BB → (∀ a (x : X), y a • x = 0) → Function.Surjective q → LinearMap.ker q = (Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ → Nonempty ((MM ⧸ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM)) ≃ₗ[BB] BB ⊗[R] X) := by
  intro R σ _ _ y f S BB _ _ _ _ _ _ _ X _ _ MM _ _ _ _ q hC hX hq hker
  have hbij := fib_bij y S BB X hX (fun b => fib_dense y f S BB hC b)
    (fun s hs => fib_strict y f S BB hC s hs)
  set rT := LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap with hrTdef
  have hrt : ∀ (s : S) (x : X), rT (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  have hrtS : ∀ (s : S) (t : S ⊗[R] X), rT (s • t) = algebraMap S BB s • rT t := by
    intro s t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hrt, hrt, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add u v hu hv => rw [smul_add, map_add (f := _), map_add (f := _), hu, hv, smul_add]
  have hJ : Ideal.span (Set.range fun a => algebraMap R BB (y a)) = (Ideal.span (Set.range y)).map (algebraMap R BB) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hL : ∀ i ∈ (Ideal.span (Set.range y)).map (algebraMap R BB), ∀ m : MM, q (i • m) = 0 := by
    intro i hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    · rintro _ ⟨r, hr, rfl⟩ m
      rw [IsScalarTower.algebraMap_apply R S BB, algebraMap_smul, ← LinearMap.mem_ker, hker]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    · intro m
      rw [zero_smul, map_zero]
    · intro a c _ _ ha hc m
      rw [add_smul, map_add (f := _), ha, hc, add_zero]
    · intro a c _ hc m
      rw [smul_eq_mul, mul_comm, mul_smul, hc]
  let φ : MM →ₗ[BB] BB ⊗[R] X :=
    { toFun := fun m => rT (q m)
      map_add' := fun a c => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun b m => by
        obtain ⟨s, hs⟩ := fib_dense y f S BB hC b
        have e : b • m = s • m + (b - algebraMap S BB s) • m := by
          rw [← algebraMap_smul BB s m, ← add_smul, add_sub_cancel]
        show rT (q (b • m)) = b • rT (q m)
        rw [e, map_add (f := _), map_smul, hL _ hs m, add_zero, hrtS]
        conv_rhs => rw [show b = algebraMap S BB s + (b - algebraMap S BB s) by ring, add_smul, fib_tmul_zero y BB X hX _ hs, add_zero] }
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨u, hu⟩ := hbij.2 t
    obtain ⟨m, hm⟩ := hq u
    refine ⟨m, ?_⟩
    show rT (q m) = t
    rw [hm, hu]
  have hK : LinearMap.ker φ = (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM) := by
    apply le_antisymm
    · intro m hm
      have h0 : q m = 0 := hbij.1 ((LinearMap.mem_ker.mp hm).trans (map_zero rT).symm)
      rw [← LinearMap.mem_ker, hker] at h0
      have hle : ((Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ : Submodule S MM) ≤ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM).restrictScalars S := by
        rw [Submodule.smul_le]
        intro s hs n _
        rw [Submodule.restrictScalars_mem, ← algebraMap_smul BB s n]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [hJ, IsScalarTower.algebraMap_eq R S BB, ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ hs
      exact hle h0
    · rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker]
      show rT (q (i • m)) = 0
      rw [hJ] at hi
      rw [hL i hi m, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hK.symm).trans (φ.quotKerEquivOfSurjective hφ)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.kjMap :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (k j : ℕ), (kjIdeal Λ σ k j).map s = Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j := by
  intro Λ R σ _ _ _ _ s k j
  rw [kjIdeal, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, ← Set.range_comp, Ideal.map_map, Ideal.map_pow]
  rfl
end

