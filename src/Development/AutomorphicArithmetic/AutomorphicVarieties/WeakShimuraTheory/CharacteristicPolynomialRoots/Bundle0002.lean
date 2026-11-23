module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.NoOmLift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Pu.noOm_rt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have h3 : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g), mul_inv_cancel_right]
  have e : Φ.rt (wt i j) g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (wt i j).1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (wt i j).2 := rfl
  rw [e]
  apply Additive.ofMul.injective
  have h4 := congrArg Additive.ofMul h3
  fin_cases i <;> fin_cases j <;>
    simp only [wt, lamW, muW, ofMul_mul, ofMul_inv, ofMul_zpow] at h4 ⊢ <;> simp [h4] <;> abel

private theorem UpperTheory.V.Ws.Pu.noOm_lift {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) (hg : g ∈ T.GalL) : ∃ g' : G T.L Ω, resQ T.L g' = resQ T.F g := by
  have h1 : resQ T.F g ∈ T.L.fixingSubgroup := by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩, hg⟩
  have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1
  exact ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => h2 x.1 x.2, rfl⟩

theorem UpperTheory.V.Ws.Pu.noOm :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h), D.Good → T.Ok → ∀ i j,
      (K.r.chib i).comp K.V.pr ≠ (K.r.chib j).comp K.V.pr * W.pushCh (residue c'.O) (chiO T.L Ω l c'.O) := by
  intro Ω _ _ _ l _ c D T c' h K hD hT i j hne
  haveI : IsLocalHom (inc h) := (UpperTheory.V.Ws.P1.coefRes c).2.2.1 c' h
  obtain ⟨g, hg, hw⟩ := hT.g2 (wt i j)
  obtain ⟨g', hg'⟩ := UpperTheory.V.Ws.Pu.noOm_lift T g hg
  apply hw
  have hχ : ∀ g, chi D T.pr 0 g * chi D T.pr 3 g = chi D T.pr 1 g * chi D T.pr 2 g := by
    intro g
    cases T.pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]
  have key : (T.fr ∅).rt (wt i j) g * chi D T.pr j (resQ T.F g) = chi D T.pr i (resQ T.F g) :=
    UpperTheory.V.Ws.Pu.noOm_rt (T.fr ∅) g (hχ _) i j
  have e0 : (K.r.chib i (K.V.pr g') : ResidueField c'.O) =
      (K.r.chib j (K.V.pr g') : ResidueField c'.O) * residue c'.O (chiO T.L Ω l c'.O g' : c'.O) :=
    congrArg (fun χ : G T.L Ω →* (ResidueField c'.O)ˣ => (χ g' : ResidueField c'.O)) hne
  have e1 : (chiO T.L Ω l c'.O g' : c'.O) = inc h (chiO ℚ Ω l c.O (resQ T.L g') : c.O) := rfl
  rw [K.chib, K.chib, e1, hg', ← key, Units.val_mul] at e0
  simp only [map_mul] at e0
  have u1 : residue c'.O (K.κ g' : c'.O) ≠ 0 := ((K.κ g').isUnit.map _).ne_zero
  have u2 : residue c'.O (inc h (chi D T.pr j (resQ T.F g) : c.O)) ≠ 0 := (((chi D T.pr j (resQ T.F g)).isUnit.map _).map _).ne_zero
  rw [mul_assoc, mul_right_inj' u1, mul_comm, mul_right_inj' u2] at e0
  rw [hD.om_bar]
  apply (ResidueField.map (inc h)).injective
  rw [ResidueField.map_residue, ResidueField.map_residue]
  exact e0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.RepChi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem chi_ofRep' {n : ℕ} {A Γ : Type} [CommRing A] [Group Γ] (ρ : Γ →* Matrix (Fin n) (Fin n) A) (g : Γ) :
    (W.GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  simp only [W.GDet.chi, W.GDet.ofRep, W.GDet.repAlg, MonoidHom.coe_comp, Function.comp_apply,
    map_sub, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, MonoidAlgebra.lift_single, Matrix.coe_detMonoidHom, map_one]
  rw [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.sub_apply]

private theorem chi_comap' {n : ℕ} {A Γ H : Type} [CommRing A] [Group Γ] [Group H] (D : W.GDet n A Γ) (φ : H →* Γ) (g : H) :
    (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem chi_map' {n : ℕ} {A A' Γ : Type} [CommRing A] [CommRing A'] [Group Γ] (D : W.GDet n A Γ) (f : A →+* A') (g : Γ) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] A'[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have h := D.nat A[X] A'[X] φ
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.single g 1))
  have e : (MonoidAlgebra.mapRingHom Γ (φ : A[X] →+* A'[X]))
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.single g 1)) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.single g 1) := by
    simp [φ, MonoidAlgebra.mapRingHom_single]
    change Polynomial.map f X = X
    exact Polynomial.map_X f
  rw [e] at h
  exact h

theorem UpperTheory.V.Ws.Pu.repChi :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → ∀ g, (W.mat ρ g).charpoly = (B.u.D.chi (MonoidAlgebra.single (V.pr g) 1)).map (x : B.B →+* PadicAlgCl l) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx g
  refine (chi_ofRep' (W.mat ρ) g).symm.trans ?_
  refine (congrArg (fun D => W.GDet.chi D (MonoidAlgebra.single g 1)) hx.symm).trans ?_
  exact (chi_comap' x.D V.pr g).trans (chi_map' B.u.D _ _)
end

