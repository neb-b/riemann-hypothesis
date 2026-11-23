module

public import Development.EtaleCohomology.WeilConjectures.AbsorbPf

@[expose] public section

-- bundled from Development.EtaleCohomology.WeilConjectures.EtaleAlgebrasHaveSmallModelSet
section
noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.EWeil.AbsorbPf3

theorem etaleAlgebras_have_small_model_set : LateralTheory.EWeil.AbsorbPf.Model := by
  intro A
  refine ⟨Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) A) // (algebraMap A (MvPolynomial (Fin n) A ⧸ I)).Etale},
    fun x => CommRingCat.of (MvPolynomial (Fin x.1) A ⧸ x.2.1),
    fun x => CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin x.1) A ⧸ x.2.1)), fun x => x.2.2, ?_⟩
  intro B g hg
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hg
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let eq : (MvPolynomial (Fin n) A ⧸ RingHom.ker f) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
  haveI : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) := Algebra.Etale.of_equiv eq.symm
  have hE : (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f)).Etale :=
    (RingHom.etale_algebraMap).mpr inferInstance
  refine ⟨⟨n, RingHom.ker f, hE⟩, (eq.symm.toRingEquiv).toCommRingCatIso, ?_⟩
  ext a
  exact eq.symm.commutes a

end LateralTheory.EWeil.AbsorbPf3
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.EtaleNeighborhoodsEqualizeParallelMaps
section
noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.EWeil.AbsorbPf4

theorem etaleNeighborhoods_equalize_parallel_maps : LateralTheory.EWeil.AbsorbPf.Coeq := by
  intro A B C Ω _ ι gB gC hB hC φB φC hφB hφC u v hu hv hφu hφv
  letI := gB.hom.toAlgebra
  letI := gC.hom.toAlgebra
  letI := ι.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hB
  let uA : B →ₐ[A] C := { u.hom with commutes' := fun a => RingHom.congr_fun (congrArg CommRingCat.Hom.hom hu) a }
  let vA : B →ₐ[A] C := { v.hom with commutes' := fun a => RingHom.congr_fun (congrArg CommRingCat.Hom.hom hv) a }
  let φB' : B →ₐ[A] Ω := { φB with commutes' := fun a => RingHom.congr_fun hφB a }
  let φC' : C →ₐ[A] Ω := { φC with commutes' := fun a => RingHom.congr_fun hφC a }
  let P : B ⊗[A] B →ₐ[A] C := Algebra.TensorProduct.lift uA vA (fun _ _ => Commute.all _ _)
  let t := Algebra.FormallyUnramified.elem A B
  let ε : C := P t
  have key : ∀ b : B, u.hom b * ε = v.hom b * ε := by
    intro b
    have h1 := congrArg P (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) (S := B) b)
    simp only [map_mul, P, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h1
    exact h1.symm
  have hPφ : φC'.comp P = φB'.comp (Algebra.TensorProduct.lmul' A) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, P, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
    show φC (u.hom x) * φC (v.hom y) = φB x * φB y
    rw [← RingHom.comp_apply, hφu, ← RingHom.comp_apply, hφv]
  have hε : φC ε = 1 := by
    have := congrArg (fun F : B ⊗[A] B →ₐ[A] Ω => F t) hPφ
    simp only [AlgHom.comp_apply] at this
    change φC ε = _
    rw [show φC ε = φC' (P t) from rfl, this, Algebra.FormallyUnramified.lmul_elem, map_one]
  have hεu : IsUnit (φC ε) := by rw [hε]; exact isUnit_one
  let w : C ⟶ CommRingCat.of (Localization.Away ε) := CommRingCat.ofHom (algebraMap C (Localization.Away ε))
  have hw : Et w := by
    change (algebraMap C (Localization.Away ε)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  refine ⟨CommRingCat.of (Localization.Away ε), gC ≫ w, IsLocalization.Away.lift ε hεu, w,
    LateralTheory.EWeil.AbsorbPf.et_comp hC hw, ?_, rfl, IsLocalization.Away.lift_comp ε hεu, ?_⟩
  · rw [CommRingCat.hom_comp, ← RingHom.comp_assoc]
    have e1 : (IsLocalization.Away.lift ε hεu).comp w.hom = φC := IsLocalization.Away.lift_comp ε hεu
    rw [e1, hφC]
  · ext b
    change algebraMap C (Localization.Away ε) (u.hom b) = algebraMap C (Localization.Away ε) (v.hom b)
    have hU := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ε) ε
    have := congrArg (algebraMap C (Localization.Away ε)) (key b)
    rw [map_mul, map_mul] at this
    exact (hU.mul_left_inj).mp this

end LateralTheory.EWeil.AbsorbPf4
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.EtaleNeighborhoodsHaveCommonRefinement
section
noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.EWeil.AbsorbPf2

theorem etaleNeighborhoods_have_common_refinement : LateralTheory.EWeil.AbsorbPf.Pair := by
  intro A B C Ω _ ι gB gC hB hC φB φC hφB hφC
  letI := gB.hom.toAlgebra
  letI := gC.hom.toAlgebra
  letI := ι.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hB
  haveI : Algebra.Etale A C := (RingHom.etale_algebraMap (R := A) (S := C)).mp hC
  let φB' : B →ₐ[A] Ω := { φB with commutes' := fun a => RingHom.congr_fun hφB a }
  let φC' : C →ₐ[A] Ω := { φC with commutes' := fun a => RingHom.congr_fun hφC a }
  let L := Algebra.TensorProduct.lift φB' φC' (fun _ _ => Commute.all _ _)
  refine ⟨CommRingCat.of (B ⊗[A] C), CommRingCat.ofHom (algebraMap A (B ⊗[A] C)), L.toRingHom,
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom,
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.Etale B (B ⊗[A] C) := inferInstance
    haveI : Algebra.Etale A (B ⊗[A] C) := Algebra.Etale.comp A B (B ⊗[A] C)
    exact (RingHom.etale_algebraMap (R := A) (S := B ⊗[A] C)).mpr inferInstance
  · ext a; exact L.commutes a
  · ext a
    show (gB.hom a) ⊗ₜ[A] (1 : C) = algebraMap A (B ⊗[A] C) a
    rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  · ext a
    show (1 : B) ⊗ₜ[A] (gC.hom a) = algebraMap A (B ⊗[A] C) a
    rw [Algebra.TensorProduct.algebraMap_apply]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := C) a).symm
  · ext b
    show L (b ⊗ₜ 1) = φB b
    simp [L, φB']
  · ext c
    show L (1 ⊗ₜ c) = φC c
    simp [L, φC']

end LateralTheory.EWeil.AbsorbPf2
end
end

