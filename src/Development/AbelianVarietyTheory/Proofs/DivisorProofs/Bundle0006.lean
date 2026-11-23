module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLinearCombinationOfRankAtStalk
section
namespace GlobalTheory


open Module in
theorem bijective_linearCombination_of_rankAtStalk :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ),
      (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M,
      Module.support R (M ⧸ Submodule.span R (Set.range s)) = ∅ →
      Function.Bijective (Fintype.linearCombination R s) := by
  intro R M _ _ _ _ _ r hr s hs
  have hspan : Submodule.span R (Set.range s) = ⊤ := by
    have : Subsingleton (M ⧸ Submodule.span R (Set.range s)) := Module.support_eq_empty_iff.1 hs
    exact Submodule.Quotient.subsingleton_iff.1 this
  refine ⟨?_, ?_⟩
  · rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    refine LinearIndependent.of_isLocalized_maximal (fun P _ => Localization.AtPrime P)
      (fun P _ => LocalizedModule P.primeCompl M) (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      s fun P hP => ?_
    have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    have hrk : Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = r :=
      hr ⟨P, hP.isPrime⟩
    have hsp : Submodule.span (Localization.AtPrime P)
        (Set.range (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) = ⊤ := by
      rw [Set.range_comp]
      exact span_eq_top_of_isLocalizedModule (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M) hspan
    have hsurj : Function.Surjective (Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]
    let b := Module.finBasisOfFinrankEq (Localization.AtPrime P) (LocalizedModule P.primeCompl M) hrk
    have hinj := OrzechProperty.injective_of_surjective_endomorphism
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) (b.equivFun.surjective.comp hsurj)
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    exact Function.Injective.of_comp (f := ⇑b.equivFun) hinj
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfInjectiveModMaximal
section
open scoped TensorProduct

namespace GlobalTheory.ProjBij

theorem eq_bot_of_forall_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by
  rw [← Submodule.annihilator_eq_top_iff]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)
  have h1 : r ∈ m := hle (Submodule.mem_annihilator.2 hr0)
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  have := m.sub_mem h1 hr
  simpa using this

theorem one_tmul_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (x : M) :
    ((1 : R ⧸ m) ⊗ₜ[R] x : (R ⧸ m) ⊗[R] M) = 0 ↔ x ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (y : (R ⧸ m) ⊗[R] M) : ∃ x : M, (1 : R ⧸ m) ⊗ₜ[R] x = y :=
  TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y

theorem bijective_of_injective_mod_maximal
    (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hinj : ∀ m : Ideal R, m.IsMaximal → ∀ x, f x ∈ m • (⊤ : Submodule R N) →
      x ∈ m • (⊤ : Submodule R M)) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have key : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
      apply eq_bot_of_forall_le_smul _ Module.Finite.fg_top
      intro m hm y _
      letI := Ideal.Quotient.field m
      have hi : Function.Injective (f.baseChange (R ⧸ m)) := by
        set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨x, rfl⟩ := exists_one_tmul m z
        rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hz
        exact (one_tmul_eq_zero_iff m x).2 (hinj m hm x hz)
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrk m hm)).1 hi
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, hz⟩ := hs (1 ⊗ₜ n)
      obtain ⟨x, rfl⟩ := exists_one_tmul m z
      rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub,
        one_tmul_eq_zero_iff] at hz
      have h2 := Submodule.mem_map_of_mem (f := (LinearMap.range f).mkQ) hz
      rw [Submodule.map_smul''] at h2
      have h3 := Submodule.smul_mono (le_refl m) le_top h2
      have h4 : (LinearMap.range f).mkQ (f x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f x)
      rw [map_sub, h4, zero_sub] at h3
      exact (Submodule.neg_mem_iff _).1 h3
    intro n
    have : (Submodule.Quotient.mk n : N ⧸ LinearMap.range f) ∈ (⊥ : Submodule R _) := by
      rw [← key]; trivial
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact this
  refine ⟨?_, hsurj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ n, f (s n) = n := fun n => LinearMap.congr_fun hs n
  let p : M →ₗ[R] M := LinearMap.id - s ∘ₗ f
  have hp : Submodule.map p ⊤ = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      simp [p, hs']
    · intro x hx
      exact ⟨x, trivial, by simp [p, LinearMap.mem_ker.1 hx]⟩
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_of_forall_le_smul
  · rw [← hp]; exact Module.Finite.fg_top.map p
  · intro m hm x hx
    have hx0 : f x = 0 := hx
    have h1 := hinj m hm x (by rw [hx0]; exact Submodule.zero_mem _)
    have h2 := Submodule.mem_map_of_mem (f := p) h1
    rw [Submodule.map_smul'', hp] at h2
    simpa [p, hx0] using h2

end GlobalTheory.ProjBij
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamily
section
open TensorProduct

namespace GlobalTheory

theorem subsingleton_of_lTensor_flat_family (R : Type) [CommRing R] (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (hflat : ∀ i, Module.Flat R (B i))
    (hmax : ∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤)
    (M : Type) [AddCommGroup M] [Module R M] (h : ∀ i, Subsingleton (B i ⊗[R] M)) :
    Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M x with hg
  set I : Ideal R := LinearMap.ker g with hIdef
  have hI : I ≠ ⊤ := by
    intro hT
    have h1 : (1 : R) ∈ I := hT ▸ Submodule.mem_top
    rw [hIdef, LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx h1
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  obtain ⟨i, hi⟩ := hmax m hm
  let e : (R ⧸ I) →ₗ[R] M := (LinearMap.ker g).liftQ g le_rfl
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hinj : Function.Injective (e.lTensor (B i)) :=
    Module.Flat.lTensor_preserves_injective_linearMap e he
  haveI := h i
  haveI : Subsingleton (B i ⊗[R] (R ⧸ I)) := hinj.subsingleton
  haveI : Subsingleton ((R ⧸ I) ⊗[R] B i) := (TensorProduct.comm R (R ⧸ I) (B i)).toEquiv.injective.subsingleton
  haveI : Subsingleton (B i ⧸ (I • (⊤ : Submodule R (B i)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (B i) I).symm.toEquiv.injective.subsingleton
  have htop : I • (⊤ : Submodule R (B i)) = ⊤ :=
    Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
  exact hi (top_le_iff.mp (htop ▸ Ideal.map_mono hIm))

theorem bijective_of_lTensor_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  intro R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij
  constructor
  · set K := LinearMap.ker f
    have hK : ∀ i, Subsingleton (B i ⊗[R] K) := by
      intro i
      have hinjK : Function.Injective (K.subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
      have hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : f ∘ₗ K.subtype = 0 := by
          ext x
          exact LinearMap.mem_ker.mp x.2
        rw [this, LinearMap.lTensor_zero]
      refine ⟨fun a b => hinjK ((hbij i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax K hK
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  · set q := (LinearMap.range f).mkQ
    have hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f)) := by
      intro i
      have hsurj : Function.Surjective (q.lTensor (B i)) :=
        LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)
      have hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : q ∘ₗ f = 0 := by
          ext x
          simp [q]
        rw [this, LinearMap.lTensor_zero]
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := (hbij i).2 z
      rw [← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ
    have htop : LinearMap.range f = ⊤ :=
      Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
    exact LinearMap.range_eq_top.mp htop

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesIsCompact
section
namespace GlobalTheory.BoundedUnitsCompact

theorem boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))

theorem isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]

end GlobalTheory.BoundedUnitsCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDvdSumOfInvariantOfCardStabilizerDvd
section
namespace GlobalTheory

theorem card_dvd_sum_of_invariant_of_card_stabilizer_dvd (G X : Type) [AddGroup G] [Finite G]
    [Fintype X] [AddAction G X] (h : X → ℤ) (hinv : ∀ (g : G) (x : X), h (g +ᵥ x) = h x)
    (hdvd : ∀ x, (Nat.card (AddAction.stabilizer G x) : ℤ) ∣ h x) :
    (Nat.card G : ℤ) ∣ ∑ x, h x := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun x : X => (Quotient.mk (AddAction.orbitRel G X) x)) (f := h)]
  refine Finset.dvd_sum fun q _ => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hconst : ∀ y ∈ Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x),
      h y = h x := by
    intro y hy
    have hy' := Quotient.exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, rfl⟩ : y ∈ AddAction.orbit G x := AddAction.orbitRel_apply.mp hy'
    exact hinv g x
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y
        = Quotient.mk (AddAction.orbitRel G X) x)).card = Nat.card (AddAction.orbit G x) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Quotient.eq]
    exact AddAction.orbitRel_apply
  have hG : Nat.card G = Nat.card (AddAction.orbit G x) * Nat.card (AddAction.stabilizer G x) := by
    rw [Nat.card_congr (AddAction.orbitEquivQuotientStabilizer G x)]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [hcard, hG, Nat.cast_mul]
  exact mul_dvd_mul_left _ (hdvd x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFiberDoubleCosetMapEqCardInfConj
section
open scoped Pointwise

namespace GlobalTheory

theorem doubleCoset_fibre_card {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G) :
    Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) =
      Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
        (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by
  classical
  set U : Subgroup G := T ⊓ K'.map (MulAut.conj x).toMonoidHom with hU
  have memU : ∀ u : G, u ∈ U ↔ u ∈ T ∧ x⁻¹ * u * x ∈ K' := by
    intro u
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨hT, k, hk, rfl⟩
      exact ⟨hT, by simpa [mul_assoc] using hk⟩
    · rintro ⟨hT, hk⟩
      exact ⟨hT, _, hk, by group⟩
  let F := fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)
  have hland : ∀ t : T, DoubleCoset.mk (Γ ⊓ T) K' ((t : G) * x) ∈ F ⁻¹' {DoubleCoset.mk T K' x} := by
    intro t
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (Γ ⊓ T) K' ((t : G) * x)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, F]
    rw [eq_comm, DoubleCoset.eq]
    refine ⟨h * t, T.mul_mem (Subgroup.mem_inf.mp hh).2 t.2, k, hk, ?_⟩
    rw [he]; group
  let φ₀ : T → F ⁻¹' {DoubleCoset.mk T K' x} := fun t => ⟨_, hland t⟩
  have hwd : ∀ a b : T, (DoubleCoset.setoid ((Γ.subgroupOf T : Subgroup T) : Set T)
      ((U.subgroupOf T : Subgroup T) : Set T)) a b → φ₀ a = φ₀ b := by
    intro a b hab
    obtain ⟨g, hg, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp hab
    apply Subtype.ext
    simp only [φ₀]
    rw [DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hg hu
    refine ⟨g, Subgroup.mem_inf.mpr ⟨hg, g.2⟩, x⁻¹ * u * x, ((memU u).mp hu).2, ?_⟩
    simp only [Subgroup.coe_mul]
    group
  let φ : DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
      ((U.subgroupOf T : Subgroup T) : Set T) → F ⁻¹' {DoubleCoset.mk T K' x} :=
    Quotient.lift (s := DoubleCoset.setoid _ _) φ₀ hwd
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      induction p using Quotient.inductionOn with | h a => ?_
      induction q using Quotient.inductionOn with | h b => ?_
      have h1 : DoubleCoset.mk (Γ ⊓ T) K' ((a : G) * x) = DoubleCoset.mk (Γ ⊓ T) K' ((b : G) * x) :=
        congrArg Subtype.val hpq
      obtain ⟨h, hh, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp h1
      have hhT : h ∈ T := (Subgroup.mem_inf.mp hh).2
      have huT : (a : G)⁻¹ * h⁻¹ * b ∈ T :=
        T.mul_mem (T.mul_mem (T.inv_mem a.2) (T.inv_mem hhT)) b.2
      apply Quotient.sound
      refine DoubleCoset.rel_iff.mpr ⟨⟨h, hhT⟩, ?_, ⟨_, huT⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact (Subgroup.mem_inf.mp hh).1
      · rw [Subgroup.mem_subgroupOf, memU]
        refine ⟨huT, ?_⟩
        have : x⁻¹ * ((a : G)⁻¹ * h⁻¹ * b) * x = k := by
          rw [show (b : G) = h * a * x * k * x⁻¹ by
            rw [show h * (a : G) * x * k * x⁻¹ = h * ((a : G) * x) * k * x⁻¹ by group, ← he]; group]
          group
        rw [this]; exact hk
      · apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
    · rintro ⟨q, hq⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, F] at hq
      obtain ⟨s, hs, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp hq
      refine ⟨Quotient.mk _ ⟨s⁻¹, T.inv_mem hs⟩, ?_⟩
      apply Subtype.ext
      show DoubleCoset.mk (Γ ⊓ T) K' (s⁻¹ * x) = q
      conv_rhs => rw [← DoubleCoset.out_eq' q]
      rw [DoubleCoset.eq]
      refine ⟨1, Subgroup.one_mem _, k⁻¹, K'.inv_mem hk, ?_⟩
      rw [he]; group
  exact (Nat.card_eq_of_bijective φ hφ).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFiberEqOfSumEq
section
open Polynomial

namespace GlobalTheory.CharDeg

theorem card_fiber_eq_of_sum_eq {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∑ j, f j x = ∑ j, g j x) (ψ : M →* ℂ) :
    Nat.card {j // f j = ψ} = Nat.card {j // g j = ψ} := by
  classical
  have hli := linearIndependent_monoidHom M ℂ
  set s : Finset (M →* ℂ) := Finset.univ.image f ∪ Finset.univ.image g ∪ {ψ} with hs
  have key : ∀ u : Fin n → (M →* ℂ), (∀ j, u j ∈ s) →
      ∑ φ ∈ s, ((Finset.univ.filter fun j => u j = φ).card : ℂ) • (φ : M → ℂ) = ∑ j, (u j : M → ℂ) := by
    intro u hu
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s) (g := u) (fun j _ => hu j)
      (fun j => (u j : M → ℂ))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hc : ∑ j ∈ Finset.univ.filter (fun j => u j = φ), (u j : M → ℂ)
        = ∑ j ∈ Finset.univ.filter (fun j => u j = φ), (φ : M → ℂ) :=
      Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
    rw [hc, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hzero : ∑ φ ∈ s, (((Finset.univ.filter fun j => f j = φ).card : ℂ)
      - ((Finset.univ.filter fun j => g j = φ).card : ℂ)) • (φ : M → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key f (fun j => by simp [hs]), key g (fun j => by simp [hs]), sub_eq_zero]
    funext x
    simp [Finset.sum_apply, h x]
  have hψ := linearIndependent_iff'.mp hli s _ hzero ψ (by simp [hs])
  rw [sub_eq_zero, Nat.cast_inj] at hψ
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hψ

theorem sum_eq_of_prod_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : ∏ j, (X - C (a j)) = ∏ j, (X - C (b j))) : ∑ j, a j = ∑ j, b j := by
  have := congrArg Polynomial.nextCoeff h
  rw [Polynomial.prod_X_sub_C_nextCoeff, Polynomial.prod_X_sub_C_nextCoeff] at this
  exact neg_inj.mp this

end GlobalTheory.CharDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardInertiaEqRamificationIdxOfPerfectResidue
section
open IsDedekindDomain

namespace GlobalTheory.InertiaDVR

theorem perfectField_residueField_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)] (p : Ideal R) [p.IsPrime] (hp : p = IsLocalRing.maximalIdeal R) :
    PerfectField p.ResidueField := by
  subst hp
  have hb := Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R)
  let e : IsLocalRing.ResidueField R ≃+* (IsLocalRing.maximalIdeal R).ResidueField :=
    RingEquiv.ofBijective _ hb
  letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    e.toRingHom.toAlgebra
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    ⟨fun x => by obtain ⟨y, rfl⟩ := e.surjective x; exact isIntegral_algebraMap⟩
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R)

theorem card_inertia_eq_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L]
    [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)),
    Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective R _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat R (integralClosure R L) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have := P.isPrime
  have hp0 : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
  have hpm : P.asIdeal.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal ((Ideal.IsPrime.under R P.asIdeal).isMaximal hp0)
  have : PerfectField (P.asIdeal.under R).ResidueField :=
    perfectField_residueField_maximalIdeal R _ hpm
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.asIdeal.under R) P.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under R) P.asIdeal (L ≃ₐ[K] L)]

end GlobalTheory.InertiaDVR
end

