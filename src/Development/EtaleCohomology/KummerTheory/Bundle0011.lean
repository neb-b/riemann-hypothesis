module

public import Development.EtaleCohomology.KummerTheory.Bundle0004
public import Development.EtaleCohomology.KummerTheory.SHenCut
public import Development.EtaleCohomology.KummerTheory.Bundle0002

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.SHInsepLocPf
section
noncomputable section
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section
variable {κ K : Type} [Field κ] [Field K] [Algebra κ K]

theorem shl_nontriv (B : Type) [CommRing B] [Nontrivial B] [Algebra κ B] : Nontrivial (B ⊗[κ] K) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right κ B K (Algebra.linearMap κ B)
    (algebraMap κ B).injective

variable [IsPurelyInseparable κ K] {A : Type} [CommRing A] [Algebra κ A]

theorem shl_pow (q : ℕ) [ExpChar κ q] [ExpChar (A ⊗[κ] K) q] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := (isPurelyInseparable_iff_pow_mem κ q).1 inferInstance k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      Algebra.TensorProduct.algebraMap_apply]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add (f := _), map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

end

theorem SHInsepLoc_of : SHInsepLoc := by
  intro κ K A _ _ _ _ _ _ hA
  obtain ⟨hH, _⟩ := hA
  have : IsLocalRing A := hH.toIsLocalRing
  obtain ⟨q, hq⟩ := ExpChar.exists κ
  have : Nontrivial (A ⊗[κ] K) := shl_nontriv A
  have : ExpChar (A ⊗[κ] K) q := expChar_of_injective_algebraMap (algebraMap κ _).injective q
  have hqpos : ∀ n : ℕ, q ^ n ≠ 0 := fun n => pow_ne_zero _ (expChar_pos κ q).ne'

  have hm : ∀ a ∈ IsLocalRing.maximalIdeal A, ¬ IsUnit (algebraMap A (A ⊗[κ] K) a) := by
    intro a ha hu
    have : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[κ] K) := shl_nontriv _
    let φ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ κ (IsLocalRing.maximalIdeal A)) (AlgHom.id κ K)
    have h0 : φ (algebraMap A (A ⊗[κ] K) a) = 0 := by
      simp [φ, Algebra.TensorProduct.algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    have := hu.map φ
    rw [h0] at this
    exact not_isUnit_zero this
  have hkey : ∀ y : A ⊗[κ] K, ¬ IsUnit y →
      ∃ n : ℕ, ∃ a ∈ IsLocalRing.maximalIdeal A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
    intro y hy
    obtain ⟨n, a, ha⟩ := shl_pow q y
    refine ⟨n, a, ?_, ha⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hy ((isUnit_pow_iff (hqpos n)).1 (ha ▸ hu.map _))
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy hxy
  obtain ⟨n, a, ha, hxa⟩ := hkey x hx
  obtain ⟨m, b, hb, hyb⟩ := hkey y hy
  apply hm (a ^ q ^ m + b ^ q ^ n)
  · exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ ha _ (Nat.pos_of_ne_zero (hqpos m)))
      (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero (hqpos n)))
  · have : (x + y) ^ q ^ (n + m) = algebraMap A (A ⊗[κ] K) (a ^ q ^ m + b ^ q ^ n) := by
      rw [add_pow_expChar_pow, map_add (f := _), map_pow, map_pow, ← hxa, ← hyb, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm m n]
    rw [← this]
    exact hxy.pow _

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SHInsepResPf
section
noncomputable section
open scoped TensorProduct
open Polynomial

namespace LateralTheory.KummerTheory

section
variable (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A]

theorem shInsepRes_pow [Nontrivial (A ⊗[κ] K)] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ (ringExpChar κ) ^ n = algebraMap A (A ⊗[κ] K) a := by
  set q := ringExpChar κ
  have : ExpChar (A ⊗[κ] K) q :=
    expChar_of_injective_algebraMap (algebraMap κ (A ⊗[κ] K)).injective q
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem κ q k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc]
    show (a ^ q ^ n) ⊗ₜ[κ] (algebraMap κ K c) = (c • a ^ q ^ n) ⊗ₜ[κ] (1 : K)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add (f := _), map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

omit [IsPurelyInseparable κ K] in
theorem shInsepRes_inj : Function.Injective (algebraMap A (A ⊗[κ] K)) :=
  Algebra.TensorProduct.includeLeft_injective (S := A) (algebraMap κ K).injective

theorem shInsepRes_localHom [Nontrivial (A ⊗[κ] K)] : IsLocalHom (algebraMap A (A ⊗[κ] K)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, b, hb⟩ := shInsepRes_pow κ K A (↑u⁻¹ : A ⊗[κ] K)
  have hQ : (ringExpChar κ) ^ n ≠ 0 := pow_ne_zero _ (expChar_pos κ (ringExpChar κ)).ne'
  have h1 : algebraMap A (A ⊗[κ] K) (a ^ (ringExpChar κ) ^ n * b) = algebraMap A (A ⊗[κ] K) 1 := by
    rw [map_mul, map_pow, ← hb, ← hu, ← mul_pow, Units.mul_inv, one_pow, map_one]
  have h2 := shInsepRes_inj κ K A h1
  exact (isUnit_pow_iff hQ).mp (isUnit_of_mul_isUnit_left (h2 ▸ isUnit_one))

end

theorem SHInsepRes_of : SHInsepRes := by
  intro κ K A _ _ _ _ _ _ hA _
  obtain ⟨hh, hsc⟩ := hA
  have : IsLocalRing A := hh.toIsLocalRing
  have : IsLocalHom (algebraMap A (A ⊗[κ] K)) := shInsepRes_localHom κ K A
  let _ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) :=
    (IsLocalRing.ResidueField.map (algebraMap A (A ⊗[κ] K))).toAlgebra
  have : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨n, a, ha⟩ := shInsepRes_pow κ K A y
    have hQ : 0 < (ringExpChar κ) ^ n := pow_pos (expChar_pos κ (ringExpChar κ)) _
    refine ⟨X ^ (ringExpChar κ) ^ n - C (IsLocalRing.residue A a), X_pow_sub_C_ne_zero hQ _, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, ← map_pow, ha, sub_eq_zero]
    rfl
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField A)

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SHenCutPf
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.SHenCut

theorem satUnit : SatUnit := by
  intro J _ _ D c hc e hF hs x hx
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep D hc x
  let ej : D.obj j →+* e.pt := (e.ι.app j).hom
  have hy : (hc.desc e).hom ((c.ι.app j).hom y) = ej y := congrArg (fun t => t.hom y) (hc.fac e j)
  have hu : IsUnit (ej y) := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel (a := ej y) (fun h => hx (hy.trans h))
    exact IsUnit.of_mul_eq_one b hb
  obtain ⟨k, f, γ, h1, -⟩ := hs j (CommRingCat.of (Localization.Away y)) (CommRingCat.ofHom (algebraMap _ _))
    (CommRingCat.ofHom (IsLocalization.Away.lift y hu))
    (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway y))
    (CommRingCat.hom_ext (IsLocalization.Away.lift_comp y hu))
  have h2 : γ.hom (algebraMap _ (Localization.Away y) y) = (D.map f).hom y := congrArg (fun t => t.hom y) h1
  have h3 : (c.ι.app k).hom ((D.map f).hom y) = (c.ι.app j).hom y := congrArg (fun t => t.hom y) (c.w f)
  have h4 : IsUnit ((D.map f).hom y) := h2 ▸ (IsLocalization.Away.algebraMap_isUnit y).map γ.hom
  have h5 := h4.map (c.ι.app k).hom
  rw [h3] at h5
  exact h5

theorem exists_lift {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (f : Polynomial c.pt) : ∃ j, f ∈ lifts (show D.obj j →+* c.pt from (c.ι.app j).hom) := by
  classical
  choose j y hy using fun n => Concrete.isColimit_exists_rep D hc (f.coeff n)
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (f.support.image j)
  refine ⟨S, (lifts_iff_coeff_lifts _).2 fun n => ?_⟩
  by_cases hn : n ∈ f.support
  · obtain ⟨g⟩ := hS (Finset.mem_image_of_mem j hn)
    exact ⟨(D.map g).hom (y n), (congrArg (fun t => t.hom (y n)) (c.w g)).trans (hy n)⟩
  · exact ⟨0, (map_zero _).trans (notMem_support_iff.1 hn).symm⟩

theorem satRoot : SatRoot := by
  intro J _ _ D c hc e hF hs f hf ω h0 h1
  obtain ⟨j, hj⟩ := exists_lift D c hc f
  obtain ⟨g, rfl, -, hg⟩ := lifts_and_natDegree_eq_and_monic hj hf
  let ej : D.obj j →+* e.pt := (e.ι.app j).hom
  let cj : D.obj j →+* c.pt := (c.ι.app j).hom
  have hy : (hc.desc e).hom.comp cj = ej := congrArg (fun t => t.hom) (hc.fac e j)
  change (g.map cj).eval₂ _ ω = 0 at h0
  change (g.map cj).derivative.eval₂ _ ω ≠ 0 at h1
  rw [eval₂_map, hy] at h0
  rw [derivative_map, eval₂_map, hy] at h1
  let P : StandardEtalePair (D.obj j) := ⟨g, hg, g.derivative, 1, 0, 1, by simp⟩
  let _ : Algebra (D.obj j) e.pt := ej.toAlgebra
  have hP : P.HasMap ω := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h1
    exact ⟨h0, IsUnit.of_mul_eq_one b hb⟩
  obtain ⟨k, t, γ, h2, h3⟩ := hs j (CommRingCat.of P.Ring) (CommRingCat.ofHom (algebraMap _ _))
    (CommRingCat.ofHom (P.lift ω hP).toRingHom) (RingHom.etale_algebraMap.2 inferInstance)
    (CommRingCat.hom_ext (P.lift ω hP).comp_algebraMap)
  let ck : D.obj k →+* c.pt := (c.ι.app k).hom
  let γ' : P.Ring →+* D.obj k := γ.hom
  have h4 : (ck.comp γ').comp (algebraMap (D.obj j) P.Ring) = cj := by
    have : (CommRingCat.ofHom (algebraMap (D.obj j) P.Ring) ≫ γ) ≫ c.ι.app k = c.ι.app j := by rw [h2]; exact c.w t
    exact congrArg (fun t => t.hom) this
  refine ⟨(ck.comp γ') P.X, ?_, ?_⟩
  · change (g.map cj).eval _ = 0
    have h5 : g.eval₂ (algebraMap (D.obj j) P.Ring) P.X = 0 := P.hasMap_X.1
    rw [Polynomial.eval_map, ← h4, ← hom_eval₂, h5, map_zero]
  · have h6 : (hc.desc e).hom (ck (γ' P.X)) = (e.ι.app k).hom (γ' P.X) := congrArg (fun t => t.hom (γ' P.X)) (hc.fac e k)
    have h7 : (e.ι.app k).hom (γ' P.X) = P.lift ω hP P.X := congrArg (fun t => t.hom P.X) h3
    exact h6.trans (h7.trans (P.lift_X ω hP))

theorem shOfLift : SHOfLift := by
  intro C Ω _ _ _ ε hu hr
  have : Nontrivial C := ε.domain_nontrivial
  have : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : ε a = 0
    · exact Or.inr (hu _ (by simp [h]))
    · exact Or.inl (hu _ h)
  have hm : ∀ x, x ∈ IsLocalRing.maximalIdeal C ↔ ε x = 0 := fun x => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by_contra fun h' => h (hu x h'), fun h h' => (h'.map ε).ne_zero h⟩
  have : IsLocalHom ε := ⟨fun a ha => hu a ha.ne_zero⟩
  refine ⟨{ is_henselian := fun f hf a₀ h0 h1 => ?_ }, IsSepClosed.of_exists_root _ fun p hp hi hsep => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := hr f hf (ε a₀) (by rw [eval₂_at_apply]; exact (hm _).1 h0)
      (by rw [eval₂_at_apply]; exact (h1.map ε).ne_zero)
    exact ⟨a, ha, (hm _).2 (by rw [map_sub, ha', sub_self])⟩
  · let ι := IsLocalRing.ResidueField.lift ε
    have hι : ι.comp (IsLocalRing.residue C) = ε := IsLocalRing.ResidueField.lift_comp_residue ε
    obtain ⟨ω, hω⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective ι ι.injective p hi.degree_pos.ne'
    have hd := hsep.eval₂_derivative_ne_zero ι hω
    obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic (f := IsLocalRing.residue C)
      ((lifts_iff_coeff_lifts p).2 fun n => IsLocalRing.residue_surjective _) hp
    rw [eval₂_map, hι] at hω
    rw [derivative_map, eval₂_map, hι] at hd
    obtain ⟨a, ha, -⟩ := hr f hf ω hω hd
    exact ⟨IsLocalRing.residue C a, by rw [Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]⟩

theorem shen : LateralTheory.KummerTheory.StrictHenselization := goal_of satUnit satRoot shOfLift

end LateralTheory.KummerTheory.SHenCut

end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SemiUniqPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SemiUniqPf

theorem cpush_homotopy {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (ho : Homotopy f g) (n : ℤ)
    (x : CohomologyClass K I n) : cpush K f n x = cpush K g n x := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy ho) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) (by omega) (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  ext p q hpq
  simp [zcomp, Cochain.comp_sub]

theorem secMap_comp {R : Type} [CommRing R] {F G M : Shv R} (f : F ⟶ G) (g : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (f ≫ g) a = Sec.map g (Sec.map f a) := rfl

theorem factor (hZ : LateralTheory.KummerTheory.BockCut.ZHom) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) {S : Type} [CommRing S]
    {I : Cx S} {T J : Cx ℤ} (σ : SemiMap I T) (hσ : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (σ.app U s))
    (κ : SemiMap I J) : ∃ u : T ⟶ J, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      κ.app U s a = Sec.map (u.f s) (σ.app U s a) := by
  let e : ∀ (U : Scheme.{0}) (s : ℤ), Sec (I.X s) U ≃+ Sec (T.X s) U :=
    fun U s => AddEquiv.ofBijective (σ.app U s) (hσ U s)
  have he : ∀ U s a, e U s a = σ.app U s a := fun _ _ _ => rfl
  have hu : ∀ s, ∃ φ : T.X s ⟶ J.X s, ∀ (U : Scheme.{0}) (b : Sec (T.X s) U),
      Sec.map φ b = κ.app U s ((e U s).symm b) := by
    intro s
    refine hZ _ _ (fun U => (κ.app U s).comp (e U s).symm.toAddMonoidHom) ?_
    intro V U g b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    rw [κ.nat]
    congr 1
    apply (e V s).injective
    rw [AddEquiv.apply_symm_apply, he, he, σ.nat]
  choose φ hφ using hu
  refine ⟨{ f := φ, comm' := ?_ }, ?_⟩
  · intro s t _
    refine (hME ℤ (φ s ≫ J.d s t)).2.2.2 (T.d s t ≫ φ t) ?_
    intro U b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    rw [secMap_comp, secMap_comp, hφ, AddEquiv.symm_apply_apply, κ.comm, he, σ.comm, hφ, ← he,
      AddEquiv.symm_apply_apply]
  · intro U s a
    show κ.app U s a = Sec.map (φ s) (σ.app U s a)
    rw [hφ, ← he, AddEquiv.symm_apply_apply]

theorem SemiUniq_of (hRR : LateralTheory.KummerTheory.BockCut.RestrRes) (hZ : LateralTheory.KummerTheory.BockCut.ZHom)
    (hOC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hEH : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso)
    (hRB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.SemiUniq := by
  intro S _ F G ρ ρ' hρ E n x
  obtain ⟨T, σ, ε, hε, hσ, hσε⟩ := hRR ℤ S (Int.castRingHom S) F
  obtain ⟨u, hu⟩ := factor hZ hME σ hσ ρ
  obtain ⟨u', hu'⟩ := factor hZ hME σ hσ ρ'
  obtain ⟨hK, -, hGE, -⟩ := hRB ℤ G
  have heq : ε ≫ u = ε ≫ u' := by
    apply HomologicalComplex.from_single_hom_ext
    refine (hME ℤ _).2.2.2 _ ?_
    intro U b
    let ι := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
    have hb : b = Sec.map (sglι _) (Sec.map ι.hom b) := by
      rw [← secMap_comp]; exact (congrArg (fun f => Sec.map f b) ι.hom_inv_id).symm
    have h1 := hσε U (Sec.map ι.hom b)
    dsimp only at h1
    rw [hb]
    change Sec.map (u.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b))) =
      Sec.map (u'.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b)))
    rw [h1, ← hu, ← hu']
    exact hρ U _
  obtain ⟨ho⟩ := (hEH ℤ _ T (res ℤ G) ε).2 u u' heq
  rw [(hOC S ℤ σ ρ u hu).1 E n x, (hOC S ℤ σ ρ' u' hu').1 E n x]
  exact cpush_homotopy _ ho n _

end LateralTheory.KummerTheory.SemiUniqPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.TwSESPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwSESPf
open LateralTheory.KummerTheory.BockCut

theorem smap_add {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f + g) x = Sec.map f x + Sec.map g x := by
  show ((f+g).hom.app (op U)).hom x = (f.hom.app (op U)).hom x + (g.hom.app (op U)).hom x
  simp

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := by
  show ((0 : F ⟶ G).hom.app (op U)).hom x = 0
  simp

theorem smap_nsmul {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) (n : ℕ) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (n • f) x = n • Sec.map f x := by
  induction n with
  | zero => simp [smap_zero]
  | succ n ih => rw [succ_nsmul, smap_add, ih, succ_nsmul]

theorem smap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem smap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem tz_kill (q : ℕ) (i : ℤ) {U : Scheme.{0}} (y : Sec (TZ q i) U) : q • y = 0 := by
  change q • (show ((tw q i).obj.obj (op U) : ModuleCat (ULift (ZMod q))) from y) = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  have : ((q : ℕ) : ULift (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem TwSES_of (hEpi : RedEpi) (hKer : RedKer) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hEx : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : TwSES := by
  intro l _ b a i π₁ π₂ h₁ h₂
  have : NeZero (l ^ (b + a)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Epi π₁ := hEpi l (b + a) a (by omega) i π₁ h₁
  have : Epi π₂ := hEpi l (b + a) b (by omega) i π₂ h₂
  have hm1 : l ^ (b + a) = l ^ b * l ^ a := pow_add _ _ _
  have hm2 : l ^ (b + a) = l ^ a * l ^ b := by rw [pow_add, mul_comm]
  have hk : kernel.ι π₁ ≫ (l ^ b • 𝟙 _) = 0 := by
    refine ((hME ℤ (kernel.ι π₁ ≫ (l ^ b • 𝟙 _))).2.2.2 0 fun U x => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    exact ((hKer _ _ _ hm1 i π₁ h₁ U _).1).1 (by rw [← smap_comp, kernel.condition, smap_zero])
  let ι := Abelian.epiDesc π₁ (l ^ b • 𝟙 _) hk
  have hι : π₁ ≫ ι = l ^ b • 𝟙 _ := Abelian.comp_epiDesc _ _ _
  have hιs : ∀ {U : Scheme.{0}} (y : Sec (TZ (l ^ (b + a)) i) U), Sec.map ι (Sec.map π₁ y) = l ^ b • y := by
    intro U y; rw [← smap_comp, hι, smap_nsmul, smap_id]
  have w : ι ≫ π₂ = 0 := by
    rw [← cancel_epi π₁, ← Category.assoc, hι, comp_zero]
    refine ((hME ℤ _).2.2.2 0 fun U y => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    refine ((hKer _ _ _ hm2 i π₂ h₂ U _).1).2 ?_
    rw [smul_smul, ← hm2]; exact tz_kill _ _ _
  refine ⟨ι, hι, w, ?_⟩
  have : Mono ι := by
    refine (hME ℤ ι).2.1.2 fun U x hx => ?_
    refine hL.2.1 _ _ _ ((hME ℤ π₁).2.2.1.1 ‹_› U x) fun V g ⟨y, hy⟩ => ?_
    rw [← hy]
    refine ((hKer _ _ _ hm1 i π₁ h₁ V y).1).2 ?_
    rw [← hιs, hy, smap_res, hx, sres_zero]
  refine ShortComplex.ShortExact.mk' ?_ ‹Mono ι› ‹Epi π₂›
  refine (hEx ℤ _).2 fun U y hy => ?_
  refine hL.2.1 _ _ _ ((hKer _ _ _ hm2 i π₂ h₂ U y).2 hy) fun V g ⟨x, hx⟩ => ⟨Sec.map π₁ x, ?_⟩
  show Sec.map ι (Sec.map π₁ x) = _
  rw [hιs, hx]

end LateralTheory.KummerTheory.TwSESPf
end

-- bundled from Development.EtaleCohomology.KummerTheory.TwSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PrimTors : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], SH B → IsUnit (q : B) →
  Nonempty (Prim q B) ∧ ∀ (i : ℤ) (ζ : Prim q B), Function.Bijective fun t : ZMod q =>
    (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B)

def SecSH : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (R : Type) [CommRing R]
  (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), Function.Bijective (ofRings.sec (R := R) M (Spec (CommRingCat.of A)))

theorem TwSec_of (h1 : PrimTors) (h2 : SecSH) : TwSec := by
  intro q _ A _ hA hq
  have hB := SHGamma_holds A hA
  have hqB : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨hne, hbij⟩ := h1 q _ hB hqB
  refine ⟨hne, fun i ζ => ?_⟩
  have key : (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      ofRings.sec (R := ZMod q) (twF q i) (Spec (CommRingCat.of A)) ∘ (fun t : ZMod q =>
        (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
          (Prim q _ →₀ ULift.{1} (ZMod q)) ⧸ twRel q i _)) := by
    funext t
    simp only [twGen, ofRings.sec]
    exact (map_smul _ _ _).symm
  rw [key]
  exact (h2 A hA (ZMod q) (twF q i)).comp (hbij i ζ)

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.ZHomPf
section
noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ZHomPf

def linOf {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} ℤ) M] [Module (ULift.{1} ℤ) N]
    (f : M →+ N) : M →ₗ[ULift.{1} ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    have h : ((r.down : ℤ) : ULift.{1} ℤ) = r := by ext; simp
    simp only [RingHom.id_apply]
    rw [← h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem ZHom_of : LateralTheory.KummerTheory.BockCut.ZHom := by
  intro F G f hf
  refine ⟨⟨{ app := fun U => ModuleCat.ofHom (linOf (f U.unop)), naturality := ?_ }⟩, ?_⟩
  · intro X Y g
    ext a
    exact (hf Y.unop X.unop g.unop a).symm
  · intro U a
    rfl

end LateralTheory.KummerTheory.ZHomPf
end
end

