module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_localizedModule_eq_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : Function.Surjective π) (Q : Ideal T) [Q.IsPrime] (W : Ideal S) [W.IsPrime]
    (hW : W = Q.comap π) (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
    (e : M ≃+ N) (he : ∀ (s : S) (x : M), e (s • x) = π s • e x) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by
  let φ : Localization.AtPrime W →+* Localization.AtPrime Q := Localization.localRingHom W Q π hW
  have hmem : ∀ s : S, s ∈ W.primeCompl ↔ π s ∈ Q.primeCompl := fun s => by
    subst hW; rfl
  have hφ : ∀ s : S, φ (algebraMap S _ s) = algebraMap T _ (π s) :=
    Localization.localRingHom_to_map W Q π hW
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b
    obtain ⟨s, rfl⟩ := hπ t
    obtain ⟨v, hv⟩ := hπ u
    refine ⟨IsLocalization.mk' _ s (⟨v, (hmem v).2 (hv ▸ u.2)⟩ : W.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hv
  let _ : Algebra (Localization.AtPrime W) (Localization.AtPrime Q) := φ.toAlgebra
  let _ : Module (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) := Module.compHom _ φ
  have _ : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl N) :=
    ⟨fun a b n => mul_smul (φ a) b n⟩
  let _ : Module S (LocalizedModule Q.primeCompl N) := Module.compHom _ (φ.comp (algebraMap S _))
  have _ : IsScalarTower S (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) :=
    ⟨fun s a n => by
      show φ (s • a) • n = φ (algebraMap S _ s) • (φ a • n)
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsmul : ∀ (s : S) (y : LocalizedModule Q.primeCompl N), s • y = π s • y := fun s y => by
    show φ (algebraMap S _ s) • y = _
    rw [hφ, algebraMap_smul]
  let g : M →ₗ[S] LocalizedModule Q.primeCompl N :=
    { toFun := fun x => LocalizedModule.mkLinearMap Q.primeCompl N (e x)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun s x => by
        rw [RingHom.id_apply, hsmul, he, LinearMap.map_smul] }
  have hg : IsLocalizedModule W.primeCompl g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · have hu : IsUnit (φ (algebraMap S _ (s : S))) :=
        (IsLocalization.map_units (Localization.AtPrime W) s).map φ
      rw [Module.End.isUnit_iff]
      refine ⟨fun y z h => ?_, fun y => ⟨((hu.unit⁻¹ : (Localization.AtPrime Q)ˣ) :
        Localization.AtPrime Q) • y, ?_⟩⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at h
        exact hu.smul_left_cancel.mp h
      · rw [Module.algebraMap_end_apply]
        show φ (algebraMap S _ (s : S)) • _ = y
        rw [← mul_smul, hu.mul_val_inv, one_smul]
    · induction y using LocalizedModule.induction_on with
      | h n t =>
      obtain ⟨s, hs⟩ := hπ t
      refine ⟨(e.symm n, ⟨s, (hmem s).2 (hs ▸ t.2)⟩), ?_⟩
      show s • LocalizedModule.mk n t = LocalizedModule.mk (e (e.symm n)) 1
      rw [hsmul, hs, AddEquiv.apply_symm_apply, LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel t n
    · have h' : LocalizedModule.mk (e x₁) (1 : Q.primeCompl) = LocalizedModule.mk (e x₂) 1 := h
      obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h'
      obtain ⟨s, hs⟩ := hπ c
      refine ⟨⟨s, (hmem s).2 (hs ▸ c.2)⟩, e.injective ?_⟩
      show e (s • x₁) = e (s • x₂)
      rw [he, he, hs]
      simpa [Submonoid.smul_def] using hc
  let eA := (IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)
  rw [eA.length_eq]
  exact Module.length_eq_of_surjective hsurj

theorem SpecialMultAt.proof : SpecialMultAt.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W _ hW _
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hspec : ∀ I : Ideal (MRing ι O), specialIdeal I = I.map π := fun _ => rfl
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hcm : ∀ I : Ideal (MRing ι O), (specialIdeal I).comap π = I ⊔ Ideal.span {C ϖ} := by
    intro I
    rw [hspec, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hker]
  have hWc : W = (specialIdeal W).comap π := by
    rw [hcm]
    exact (sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hW))).symm
  let f : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk _).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
  have hkerf : RingHom.ker f = P ⊔ Ideal.span {C ϖ} := by
    rw [← hcm]
    ext x
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let e := ((Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))
  have hemk : ∀ z, e (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have he : ∀ (s : MRing ι O) (x : MRing ι O ⧸ (P ⊔ Ideal.span {C ϖ})),
      e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, hemk]
    simp [f]
    rw [← map_mul]
    rfl
  exact length_localizedModule_eq_of_surjective π hπ (specialIdeal W) W hWc _ _ e.toAddEquiv he

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialPieceRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Reduction

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem map_residue_weightedHomogeneousComponent (m : K → ℕ) (f : MRing ι O) :
    MvPolynomial.map (IsLocalRing.residue O) (weightedHomogeneousComponent (blockWeight ι) m f) =
      weightedHomogeneousComponent (blockWeight ι) m (MvPolynomial.map (IsLocalRing.residue O) f) := by
  classical
  ext d
  simp only [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem map_residue_mem_weightedHomogeneousSubmodule {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m) :
    MvPolynomial.map (IsLocalRing.residue O) f ∈
      weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m := by
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← weightedHomogeneousComponent_eq_self hf, map_residue_weightedHomogeneousComponent]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem exists_form_map_residue_eq {m : K → ℕ} {g : MRing ι (IsLocalRing.ResidueField O)}
    (hg : g ∈ weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m) :
    ∃ f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m,
      MvPolynomial.map (IsLocalRing.residue O) f = g := by
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
  refine ⟨weightedHomogeneousComponent (blockWeight ι) m f, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [map_residue_weightedHomogeneousComponent]
    exact weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hg)

theorem exists_eq_add_mul_of_map_residue_mem {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    (hP : IsMultiHomogIdeal P) {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m)
    (hfP : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal P) :
    ∃ p ∈ P, ∃ g ∈ weightedHomogeneousSubmodule O (blockWeight ι) m, f = p + C ϖ * g := by
  have hfh := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hf
  obtain ⟨p, hp, hpf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hfP
  have hpm : weightedHomogeneousComponent (blockWeight ι) m p ∈ P := hP p hp m
  have hker : f - weightedHomogeneousComponent (blockWeight ι) m p ∈
      RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* _) := by
    rw [RingHom.mem_ker, map_sub, map_residue_weightedHomogeneousComponent, hpf,
      weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1
        (map_residue_mem_weightedHomogeneousSubmodule hf)), sub_self]
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨_, hpm, weightedHomogeneousComponent (blockWeight ι) m g, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · have h2 : C ϖ * weightedHomogeneousComponent (blockWeight ι) m g =
        f - weightedHomogeneousComponent (blockWeight ι) m p := by
      rw [C_mul', ← map_smul, ← C_mul', mul_comm, hg, map_sub, weightedHomogeneousComponent_eq_self hfh,
        weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
    rw [h2]
    ring

end Reduction

theorem SpecialPieceRank.proof (h1 : GradedPieceFree.Statement.{u}) : SpecialPieceRank.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP htor m
  obtain ⟨hfree, hfin⟩ := h1 O ϖ hϖ K ι P htor m
  let ρ : MRing ι O →ₐ[O] MRing ι (IsLocalRing.ResidueField O) :=
    mapAlgHom (Algebra.ofId O (IsLocalRing.ResidueField O))
  have hρ : ∀ f, ρ f = MvPolynomial.map (IsLocalRing.residue O) f := fun f => rfl
  have hle : P ≤ (specialIdeal P).comap ρ := fun x hx => by
    rw [Ideal.mem_comap, hρ]
    exact Ideal.mem_map_of_mem _ hx
  let T := Ideal.quotientMapₐ (specialIdeal P) ρ hle
  have hT : ∀ f, T (Ideal.Quotient.mk P f) =
      Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) := fun f => rfl
  have hTM : ∀ y ∈ gradedPieceR P m, T y ∈ gradedPiece (specialIdeal P) m := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨_, map_residue_mem_weightedHomogeneousSubmodule hf, (hT f).symm⟩
  let b := Module.Free.chooseBasis O (gradedPieceR P m)
  let v : Module.Free.ChooseBasisIndex O (gradedPieceR P m) → gradedPiece (specialIdeal P) m :=
    fun i => ⟨T (b i), hTM _ (b i).2⟩
  have hv : ∀ i, ((v i : gradedPiece (specialIdeal P) m) : _) = T (b i) := fun i => rfl
  have hsmul : ∀ (c : O) (x : MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P),
      IsLocalRing.residue O c • x = c • x := fun c x => by
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have hli : LinearIndependent (IsLocalRing.ResidueField O) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose c hc using fun j => IsLocalRing.residue_surjective (g j)
    let y : gradedPieceR P m := ∑ j, c j • b j
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 y.2
    have hfy' : Ideal.Quotient.mk P f = (y : MRing ι O ⧸ P) := hfy
    have h0 : Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) = 0 := by
      rw [← hT, hfy']
      have hg' := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hv] at hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      rw [← hg']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j, hsmul]
    obtain ⟨p, hp, g0, hg0, hfp⟩ :=
      exists_eq_add_mul_of_map_residue_mem hϖ hP hf (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let z : gradedPieceR P m := ⟨Ideal.Quotient.mk P g0, Submodule.mem_map.2 ⟨g0, hg0, rfl⟩⟩
    have hyz : y = ϖ • z := by
      apply Subtype.ext
      rw [← hfy', hfp, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_add, map_mul,
        Submodule.coe_smul]
      show _ = ϖ • Ideal.Quotient.mk P g0
      rw [← map_mul, C_mul']
      exact map_smul (Ideal.Quotient.mkₐ O P) ϖ g0
    have hbli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbli
    have key : ∑ j, (c j - ϖ * b.repr z j) • b j = 0 := by
      have e1 : ∑ j, (c j - ϖ * b.repr z j) • b j =
          ∑ j, c j • b j - ϖ • ∑ j, b.repr z j • b j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (sub_smul (c j) (ϖ * b.repr z j) (b j)).trans
          (congrArg (c j • b j - ·) (mul_smul ϖ (b.repr z j) (b j)))
      rw [e1, b.sum_repr]
      exact sub_eq_zero.2 hyz
    have hi := hbli _ key i
    rw [← hc i, sub_eq_zero.1 hi, map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 (mem_nonunits_iff.2 hϖ.not_isUnit)), zero_mul]
  have hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨f, hf, rfl⟩ := exists_form_map_residue_eq hg
    let y : gradedPieceR P m := ⟨Ideal.Quotient.mk P f, Submodule.mem_map.2 ⟨f, hf, rfl⟩⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => IsLocalRing.residue O (b.repr y j), ?_⟩
    apply Subtype.ext
    have hy := congrArg Subtype.val (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hy ⊢
    change _ = T (y : MRing ι O ⧸ P)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hv, hsmul]
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTopDimMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem TopDimMinimal.proof (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def FibreVarieties.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      (IsMultiProjPrime (genFib P) ∧
        ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) ∧
      ∀ W : Ideal (MRing ι O), divCycle P (C ϖ) W ≠ 0 →
        IsMultiProjPrime (specialIdeal W) ∧
          ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
            ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

