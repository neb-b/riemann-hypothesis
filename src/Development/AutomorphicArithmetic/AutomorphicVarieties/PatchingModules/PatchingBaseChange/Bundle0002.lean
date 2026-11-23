module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem gdet_ofRep_diagRep_map_eq_ofRep_pushCh {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G]
    (χ : Fin n → G →* Aˣ) (f : A →+* A') :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep (fun i => pushCh f (χ i))) := by
  refine GDet.ext fun B _ _ x => ?_
  simp only [GDet.map, GDet.ofRep, GDet.repAlg]
  congr 4
  apply congrArg
  refine MonoidHom.ext fun s => ?_
  ext i j
  simp [diagRep, pushCh, Matrix.diagonal_apply, RingHom.algebraMap_toAlgebra]
  split_ifs <;> simp

private theorem gdet_map_chi_mapRingHom_eq_map_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (x : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  letI : Algebra A (Polynomial A') := ((algebraMap A' (Polynomial A')).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial A' :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat (Polynomial A) (Polynomial A') φ
    (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
  have e : (MonoidAlgebra.mapRingHom G (φ : Polynomial A →+* Polynomial A'))
        (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
      = MonoidAlgebra.single 1 Polynomial.X
          - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.mapRingHom G f x) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · simp [φ, Polynomial.mapRingHom]
    · ext g
      simp [φ, Polynomial.mapRingHom, MonoidAlgebra.mapRingHom]
  rw [e] at key
  exact key

private theorem gdet_map_lam_mapRingHom_eq_lam {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (i : ℕ) (x : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f x) = f (D.lam i x) := by
  simp only [GDet.lam, gdet_map_chi_mapRingHom_eq_map_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

private theorem adicCont_maximalIdeal_comp_of_isLocalHom {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (g : R →+* R') [IsLocalHom g] {φ : Γ → R}
    (h : AdicCont (maximalIdeal R) φ) : AdicCont (maximalIdeal R') (fun x => g (φ x)) := by
  intro N
  have hm : (maximalIdeal R).map g ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit g x hx
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap g := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have := (h N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) g hle)
  convert this using 1
  funext x
  simp [Ideal.quotientMap_mk]

private theorem res_eq_zero_of_mem_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (x : R) (hx : x ∈ maximalIdeal R) : res O R x = 0 := by
  show ((RingEquiv.ofBijective _ _).symm.toRingHom.comp (residue R)) x = 0
  simp [(IsLocalRing.residue_eq_zero_iff x).mpr hx]

theorem UpperTheory.V.Pa.BC.pair_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n), RBC r r' → ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O' R'] [IsCO O' R'] (g : R →+* R') [IsLocalHom g], (∀ a, g (algebraMap O R a) = algebraMap O' R' (algebraMap O O' a)) → ∀ p : Pair r R, (∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x)) ∧ ∃ p' : Pair r' R', p.Maps g p'.D p'.ψ := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r r' hr R R' _ _ _ _ _ _ g _ hg p
  have hres : ∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have hx : x = algebraMap O R a + (x - algebraMap O R a) := by ring
    have h2 : g (x - algebraMap O R a) ∈ maximalIdeal R' := map_nonunit g _ ha
    rw [hx, map_add (f := _), map_add (f := _), map_add (f := _), hg, res_eq_zero_of_mem_maximalIdeal _ h2, res_eq_zero_of_mem_maximalIdeal _ ha, add_zero, add_zero,
      AlgHom.commutes, AlgHom.commutes, ResidueField.algebraMap_eq, ResidueField.algebraMap_eq,
      ResidueField.map_residue]
  have hs1 : ∀ h : F.G₀, (MonoidAlgebra.single h (1 : R') : MonoidAlgebra R' F.G₀)
      = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1) := by
    intro h
    simp [MonoidAlgebra.mapRingHom_single]
  refine ⟨hres, ⟨⟨p.D.map g, fun v i => pushCh g (p.ψ v i), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩⟩
  · intro i
    have key : (fun h : F.G₀ => (p.D.map g).lam i (MonoidAlgebra.single h 1))
        = fun h => g (p.D.lam i (MonoidAlgebra.single h 1)) := by
      funext h
      rw [hs1, gdet_map_lam_mapRingHom_eq_lam]
    show AdicCont _ _
    rw [key]
    exact adicCont_maximalIdeal_comp_of_isLocalHom g (p.cont i)
  · have hrg : ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O').comp g
        = (ResidueField.map (algebraMap O O')).comp ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) :=
      RingHom.ext hres
    have e1 : (p.D.map g).map ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O')
        = (p.D.map ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)).map
            (ResidueField.map (algebraMap O O')) := by
      refine GDet.ext fun B _ _ x => ?_
      simp only [GDet.map]
      congr 2
      congr 1
      refine RingHom.ext fun y => ?_
      show algebraMap (ResidueField O') B (res O' R' (g y)) = algebraMap (ResidueField O') B (ResidueField.map (algebraMap O O') (res O R y))
      rw [hres]
    rw [e1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (diagRep r'.chib)
    rw [gdet_ofRep_diagRep_map_eq_ofRep_pushCh]
    congr 2
    funext i
    exact (hr.1 i).symm
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · have := adicCont_maximalIdeal_comp_of_isLocalHom g (p.psi v i).cont
      simpa [pushCh] using this
    · intro x
      have h1 := (p.psi v i).red x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [hres, h1, hr.2.1 v i]
      simp [pushCh]
    · intro x
      have h1 := (p.psi v i).mu x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [h1, hg, hr.2.2 v i]
      simp [pushCh]
  · intro i h
    have he : ∀ y : F.G₀, Units.map (g : R →* R') (F.eps O R y) = F.eps O' R' y := by
      intro y
      ext
      simp [GFrame.eps, pushCh, hg, ← IsScalarTower.algebraMap_apply]
    have hs : F.star O' R' n (MonoidAlgebra.single h 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n (MonoidAlgebra.single h 1)) := by
      simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.mapRingHom_single, ← he]
      rw [← map_zpow]
      rfl
    rw [hs, hs1, gdet_map_lam_mapRingHom_eq_lam, gdet_map_lam_mapRingHom_eq_lam, p.P]
  · intro v gg h
    have e : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh g (p.ψ v i)) gg
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) gg) := by
      rw [map_mul, ← hs1]
      congr 1
      simp [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def, pushCh,
        MonoidAlgebra.mapRingHom_single]
    have h0 := p.Ord v gg h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
  · intro u x hx h
    have hx' : x ∈ r.Ip u := by
      simp only [Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx ⊢
      refine ⟨hx.1, fun i => ?_⟩
      have h2 := hx.2 i
      rw [hr.1 i] at h2
      ext
      have h3 := congrArg (fun u : (ResidueField O')ˣ => (u : ResidueField O')) h2
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3
      apply (ResidueField.map (algebraMap O O')).injective
      rw [h3, Units.val_one, map_one]
    have e : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single x 1 - 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * (MonoidAlgebra.single x 1 - 1)) := by
      simp [MonoidAlgebra.mapRingHom_single]
    have h0 := p.I u x hx' h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.QuotBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.quot_bc :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) (I' : Ideal R'), I' = I.map (algebraMap R R') → Nonempty (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] (R' ⊗[R] M) ⧸ (I' • ⊤ : Submodule R' (R' ⊗[R] M))) := by
  intro R R' _ _ _ M _ _ I I' hI
  subst hI
  have hker : ∀ i ∈ I, ∀ y : R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)), i • y = 0 := by
    intro i hi y
    induction y using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | tmul a q =>
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul,
          (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi Submodule.mem_top),
          TensorProduct.tmul_zero]
    | add y z hy hz => rw [smul_add, hy, hz, add_zero]
  have hann : I.map (algebraMap R R') ≤ Module.annihilator R' (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Ideal.map_le_iff_le_comap.2 fun i hi => Module.mem_annihilator.2 fun y => by
      rw [algebraMap_smul]
      exact hker i hi y
  let ψ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R]
      (R' ⊗[R] M) ⧸ (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)) :=
    (I • ⊤ : Submodule R M).liftQ
      (((I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).mkQ.restrictScalars R) ∘ₗ
        TensorProduct.mk R R' M 1) (by
      rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, TensorProduct.tmul_smul,
        ← algebraMap_smul R' i ((1 : R') ⊗ₜ[R] m)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top)
  let φ := ψ.liftBaseChange R'
  let χ := (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).liftQ
    (LinearMap.baseChange R' (I • ⊤ : Submodule R M).mkQ) (by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.1 (hann hr) _)
  refine ⟨LinearEquiv.ofLinear φ χ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp [φ, χ, ψ]
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro a q
    induction q using Submodule.Quotient.induction_on with
    | H m => simp [φ, χ, ψ, TensorProduct.smul_tmul']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ResidBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem star_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [CommRing O']
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] (B : Type) [CommRing B] [Algebra O B] [Algebra O' B]
    (h : ∀ a : ℤ_[l], algebraMap O B (algebraMap ℤ_[l] O a) = algebraMap O' B (algebraMap ℤ_[l] O' a))
    (n : ℕ) (y : MonoidAlgebra B F.G₀) : F.star O B n y = F.star O' B n y := by
  have he : F.eps O B = F.eps O' B := by
    ext g
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.coe_comp, Function.comp_apply]
    exact h _
  have hop : F.starOp O B n = F.starOp O' B n := by
    ext g
    simp [GFrame.starOp, he]
  unfold GFrame.star
  rw [hop]

private theorem diag_map {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (χ : Fin n → H →* Aˣ) :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep fun i => pushCh f (χ i)) := by
  rw [(UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep χ))).2.2.2 f (diagRep χ)]
  congr 1
  ext g a b
  by_cases hab : a = b
  · subst hab
    simp [diagRep]
  · simp [diagRep, hab]

private theorem push_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker :=
  MonoidHom.ker_comp_of_injective _ _ (Units.map_injective hf)

theorem UpperTheory.V.Pa.BC.resid_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n), (∃ r' : Resid F O' n, RBC r r') ∧ ∀ r' : Resid F O' n, RBC r r' → (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧ ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r
  let φ : ResidueField O →+* ResidueField O' := ResidueField.map (algebraMap O O')
  have hφ : Function.Injective φ := φ.injective
  have hker : ∀ {H : Type} [Group H] (χ : H →* (ResidueField O)ˣ), (pushCh φ χ).ker = χ.ker :=
    fun χ => push_ker φ hφ χ
  have hpolar : F.IsPolar O' (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))) := by
    intro B _ _ _ _ y
    letI : Algebra (ResidueField O) B := ((algebraMap (ResidueField O') B).comp φ).toAlgebra
    letI : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    haveI : IsScalarTower O (ResidueField O) B := IsScalarTower.of_algebraMap_eq (fun a => by
      show algebraMap O' B (algebraMap O O' a) = algebraMap (ResidueField O') B (φ (algebraMap O (ResidueField O) a))
      rw [ResidueField.algebraMap_eq, ResidueField.map_residue, ← ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply O' (ResidueField O') B])
    have hp := r.polar B y
    have hs := star_eq F O' O B (fun a => by
      show algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (algebraMap O O' (algebraMap ℤ_[l] O a))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] O O']) n y
    rw [hs]
    have hd : ∀ x, (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))).D B x =
        (GDet.ofRep (diagRep r.chib)).D B x := by
      intro x
      rw [← diag_map φ r.chib]
      rfl
    rw [hd, hd]
    exact hp
  have hmain : ∀ r' : Resid F O' n, RBC r r' →
      (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧
        ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
    intro r' ⟨hc, _, _⟩
    refine ⟨fun u => ?_, ?_, fun i g => ?_⟩
    · rw [Resid.Ip, Resid.Ip]
      congr 2
      funext i
      rw [hc i]
      exact hker _
    · have hfun : r'.chib = fun i => pushCh φ (r.chib i) := funext hc
      simp only [Resid.Dbar]
      rw [hfun, diag_map]
    · rw [hc i]
      show Units.map (φ : ResidueField O →* ResidueField O') (r.chib i g) = 1 ↔ _
      rw [← map_one (Units.map (φ : ResidueField O →* ResidueField O')),
        (Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ).eq_iff]
  refine ⟨⟨⟨fun i => pushCh φ (r.chib i), fun i => ?_, fun i j hij => ?_, hpolar,
    fun v i => pushCh φ (r.psib v i), fun v i => ?_, fun v i => pushCh (algebraMap O O') (r.th v i),
    fun v i g hg => ?_⟩, fun i => rfl, fun v i => rfl, fun v i => rfl⟩, hmain⟩
  · rw [hker]; exact r.chib_open i
  · apply r.chib_inj
    exact MonoidHom.ext fun g =>
      Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ (DFunLike.congr_fun hij g)
  · rw [hker]; exact r.psib_open v i
  · show Units.map (algebraMap O O' : O →* O') (r.th v i g) = 1
    rw [r.th_comm v i g hg, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
section
noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime]

structure SinfRel (l : ℕ) {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {D q n : ℕ}
    (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) :
    Prop where
  X : ∀ p, τS (Til.ι O O' _ (MvPowerSeries.X p)) = MvPowerSeries.X p
  C : ∀ a : abelian₂ O Empty D, τS (Til.ι O O' _ (MvPowerSeries.C a)) = MvPowerSeries.C (lamEmb O O' D a)
  cc : ∀ c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D, (∀ z, c z = MvPowerSeries.constantCoeff z) →
    ∀ z, MvPowerSeries.constantCoeff (τS z) = τ (Til.map O' c z)
  del : ∀ a : Fin q → ℕ, delIdeal l (abelian₂ O' Unit D) n a =
    (delIdeal l (abelian₂ O Empty D) n a).map ((τS.toRingEquiv : _ →+* Sinf O' Unit D q n).comp (Til.ι O O' _))

structure RingRel {L : Loc} {G0 G : Glob l L} {O O' : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CommRing O']
    [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] {n : ℕ} {r : Resid G0.frame O n} {r' : Resid G0.frame O' n}
    {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {B' : Type} [CommRing B'] [Algebra O' B'] [IsCO O' B']
    {u : Pair r B} {u' : Pair r' B'} {J : Ideal B} {J' : Ideal B'} {D : ℕ} {b : TWBase u J Empty D}
    {b' : TWBase u' J' Unit D} {h : G.Hom G0} {q : ℕ} {ut : Fin q → Fin n → O} {ut' : Fin q → Fin n → O'} {N : ℕ}
    (A : TWRing b h ut N) (A' : TWRing b' h ut' N)
    (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) where
  ρ : Til O O' A.R ≃ₐ[O'] A'.R
  maps : A.p.Maps ((ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)) A'.p.D A'.p.ψ
  s : ∀ z, A'.s (τS z) = ρ (Til.map O' A.s z)
  U : ∀ j i, A'.U j i = ρ (Til.ι O O' A.R (A.U j i))
  ν : Til O O' A.R ⊗[A.R] A.M ≃+ A'.M
  ν_smul : ∀ t m, ν (t • m) = ρ t • ν m

end UpperTheory.V.Pa
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SpFin
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem spf_nilp {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) (x : Q)
    (hx : ∀ y, IsUnit (x * y + 1)) (f : Polynomial k) (hf : f ≠ 0) (h : f.eval₂ φ x = 0) :
    IsNilpotent x := by
  obtain ⟨g, hg, hd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf 0
  rw [map_zero, sub_zero] at hg hd
  rw [Polynomial.X_dvd_iff] at hd
  have hu : IsUnit (g.eval₂ φ x) := by
    have e : g.eval₂ φ x = φ (g.coeff 0) * (x * (φ (g.coeff 0)⁻¹ * g.divX.eval₂ φ x) + 1) := by
      have e1 : φ (g.coeff 0) * φ (g.coeff 0)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hd, map_one]
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      linear_combination (-(x * g.divX.eval₂ φ x)) * e1
    rw [e]
    exact ((Ne.isUnit hd).map φ).mul (hx _)
  rw [hg, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
  exact ⟨_, hu.mul_left_eq_zero.1 h⟩

private theorem spf_nilp2 {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) {n : ℕ} (x : Fin n → Q)
    (c : Fin n → k) (f : Polynomial k)
    (h : ∏ i, (Polynomial.X - Polynomial.C (φ (c i) + x i)) = f.map φ) (i : Fin n)
    (hx : ∀ y, IsUnit (x i * y + 1)) : IsNilpotent (x i) := by
  classical
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · exact ⟨1, Subsingleton.elim _ _⟩
  have hmon : (∏ j, (Polynomial.X - Polynomial.C (φ (c j) + x j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at h
    exact hmon.ne_zero h
  have hroot : f.eval₂ φ (φ (c i) + x i) = 0 := by
    rw [← Polynomial.eval_map, ← h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine spf_nilp φ (x i) hx (f.comp (Polynomial.X + Polynomial.C (c i))) ?_ ?_
  · intro h0
    apply hf
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_eq_zero] at h0
  · rw [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, add_comm]
    exact hroot

theorem UpperTheory.V.Pa.BC.sp_fin :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), Module.Finite B (Sp P ut) ∧ IsNoetherianRing (Sp P ut) := by
  intro B _ _ _ _ q n P ut
  classical
  let k := ResidueField B
  let J := spIdeal P ut
  let Jb : Ideal (MvPowerSeries (Fin q × Fin n) k) := Ideal.map (MvPowerSeries.map (residue B)) J
  let π := Ideal.Quotient.mk Jb
  let φ : k →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) := π.comp MvPowerSeries.C
  let ψ : MvPowerSeries (Fin q × Fin n) B →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) :=
    π.comp (MvPowerSeries.map (residue B))
  have hunit : ∀ (p : Fin q × Fin n) (y : MvPowerSeries (Fin q × Fin n) k ⧸ Jb),
      IsUnit (π (MvPowerSeries.X p) * y + 1) := by
    intro p y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one π, ← map_add (f := _)]
    apply IsUnit.map
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hnil : ∀ p : Fin q × Fin n, IsNilpotent (π (MvPowerSeries.X p)) := by
    rintro ⟨j, i⟩
    refine spf_nilp2 φ (fun i => π (MvPowerSeries.X (j, i))) (fun i => residue B (ut j i))
      ((P j).map (residue B)) ?_ i (hunit _)
    have hD : (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) -
        (P j).map MvPowerSeries.C).map ψ = 0 := by
      ext k'
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      show π _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, k', rfl⟩)
    rw [Polynomial.map_sub, sub_eq_zero, Polynomial.map_prod, Polynomial.map_map] at hD
    have hC : ψ.comp MvPowerSeries.C = φ.comp (residue B) := by
      ext b
      simp [ψ, φ, MvPowerSeries.map_C]
    rw [hC, ← Polynomial.map_map] at hD
    rw [← hD]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [ψ, φ, MvPowerSeries.map_C, MvPowerSeries.map_X]
  have hle : Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k))) ≤ nilradical _ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact mem_nilradical.2 (hnil p)
  have hfg : (Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)))).FG := by
    rw [Ideal.map_span]
    exact Submodule.fg_span ((Set.finite_range _).image _)
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  have hpow : Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N ≤ Jb := by
    have h0 : Ideal.map π (Ideal.span (Set.range
        (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N) = ⊥ := by
      rw [Ideal.map_pow, hN, Ideal.zero_eq_bot]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0
    exact h0
  have hfin : Module.Finite B (MvPowerSeries (Fin q × Fin n) B ⧸ J) :=
    GlobalTheory.FormalIsogeny.finite_quotient_of_residue J (GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le hpow)
  have hfin' : Module.Finite B (Sp P ut) := hfin
  refine ⟨hfin', ?_⟩
  have hB : IsNoetherian B (Sp P ut) := inferInstance
  exact isNoetherian_of_tower B hB
end

