module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.TorsMem

private theorem div_N_mem_tauPair_lattice_iff_dvd (N : ℕ) [NeZero N] (τ : ℍ) (a b : ℤ) :
    ((a : ℂ) * τ + (b : ℂ)) / N ∈ (tauPair τ).lattice ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    rw [h1, h2, eq_div_iff hN] at h
    obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.mp (tauPair τ).indep
      (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by
        rw [h1, h2, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination h)
    norm_cast at k1 k2
    exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    rw [h1, h2, eq_div_iff hN]
    push_cast
    ring

theorem div_mem_iff (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  rw [div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  intro N _ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : ∀ x : Fin 2 → ZMod N,
      tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N := by
    intro x
    simp only [tors, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ
        + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht]; push_cast; ring
    rw [e, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp [sub_eq_zero]
  · intro x y
    have e : tors N τ (x + y) - (tors N τ x + tors N τ y) =
        (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ)
        + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht, ht]; push_cast; ring
    rw [e, div_mem_iff]
    simp
  · intro x
    rw [ht, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp
  · intro x
    rw [PeriodPair.mem_lattice]
    refine ⟨(x 0).val, (x 1).val, ?_⟩
    change (((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _
    rw [ht]
    field_simp
  · intro z hz
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
    change (m : ℂ) * τ + n * 1 = N * z at h
    refine ⟨![(m : ZMod N), (n : ZMod N)], ?_⟩
    have hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N := by
      rw [eq_div_iff hN]
      linear_combination -h
    have e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] =
        (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N := by
      rw [hz', ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    rw [e, div_mem_iff]
    simp

end GlobalTheory.WpFam.TorsMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
section
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc.Translate

theorem exists_X_sub_C_mem_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k]
    (Q : Ideal k[X]) [hQ : Q.IsPrime] :
    ∀ (n : ℕ) (g : k[X]), g ≠ 0 → g.natDegree = n → g ∈ Q → ∃ r : k, X - C r ∈ Q := by
  intro n
  induction n with
  | zero =>
    intro g hg hdeg hgQ
    exfalso
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hgQ hg
    have h0 : g.coeff 0 ≠ 0 := fun h => hg (by rw [h, map_zero])
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hgQ (isUnit_C.2 (IsUnit.mk0 _ h0)))
  | succ n ih =>
    intro g hg hdeg hgQ
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g (by
      rw [Polynomial.degree_eq_natDegree hg, hdeg]; exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := g) (a := r)).2 hr
    rw [← hdiv] at hgQ hg
    rcases hQ.mem_or_mem hgQ with h | h
    · exact ⟨r, h⟩
    · refine ih _ (right_ne_zero_of_mul hg) ?_ h
      have := natDegree_divByMonic g (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [this, hdeg]; omega

theorem exists_X_sub_C_mem (T : Type) [CommRing T] [IsLocalRing T] [IsAlgClosed (ResidueField T)]
    (P : Ideal T[X]) [hPp : P.IsPrime] (hP : P.comap (C : T →+* T[X]) = maximalIdeal T)
    (hne : P ≠ (maximalIdeal T).map (C : T →+* T[X])) : ∃ c : T, X - C c ∈ P := by
  set π : T[X] →+* (ResidueField T)[X] := mapRingHom (residue T) with hπ
  have hsurj : Function.Surjective π := map_surjective _ residue_surjective
  have hker : RingHom.ker π = (maximalIdeal T).map (C : T →+* T[X]) := by
    rw [hπ, ker_mapRingHom, ker_residue]
  have hle : RingHom.ker π ≤ P := by
    rw [hker, Ideal.map_le_iff_le_comap, hP]
  haveI hQ : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hle
  have hPQ : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hle
  have hQbot : P.map π ≠ ⊥ := by
    intro h
    apply hne
    rw [← hker, ← hPQ, h, RingHom.ker_eq_comap_bot]
  obtain ⟨g, hgQ, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQbot
  obtain ⟨r, hr⟩ := exists_X_sub_C_mem_of_isAlgClosed _ _ _ g hg rfl hgQ
  obtain ⟨c, rfl⟩ := residue_surjective r
  refine ⟨c, ?_⟩
  rw [← hPQ, Ideal.mem_comap]
  simpa [hπ] using hr

end GlobalTheory.LocAcyc.Translate

namespace GlobalTheory.LocAcyc.Translate

theorem keyClosedPts_of_keyOrigin : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  intro hKO
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith at hKO
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne q hq hqu
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP' q hq hqu

end GlobalTheory.LocAcyc.Translate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialGenericFibreOfStrictHenselClosedFib
section
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem torsorsTrivial_of_ringEquiv {B B' : Type} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (q : ℕ) (h : TorsorsTrivial B' q) : TorsorsTrivial B q := by
  intro D _ _ hfin hproj hff act hbij
  let : Algebra B' B := e.symm.toRingHom.toAlgebra
  let : Algebra B' D := ((algebraMap B D).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower B' B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : ∀ b : B, algebraMap B D b = algebraMap B' D (e b) := by
    intro b
    change algebraMap B D b = algebraMap B D (e.symm (e b))
    rw [RingEquiv.symm_apply_apply]
  have hsmul : ∀ (b : B) (d : D), b • d = (e b) • d := by
    intro b d
    rw [Algebra.smul_def, Algebra.smul_def, hmap]
  let eL : B ≃ₗ[B'] B' :=
    { e.toAddEquiv with
      map_smul' := fun b' b => by
        change e (e.symm b' * b) = b' * e b
        rw [map_mul, RingEquiv.apply_symm_apply] }
  have : Module.FaithfullyFlat B' B := Module.FaithfullyFlat.of_linearEquiv B' B' eL
  have : Module.Finite B' B := Module.Finite.equiv eL.symm
  have : Module.FaithfullyFlat B D := hff
  have : Module.Finite B D := hfin
  have hfin' : Module.Finite B' D := Module.Finite.trans B D
  have hff' : Module.FaithfullyFlat B' D := Module.FaithfullyFlat.trans B' B D
  have i1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have i2 : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let sl : D ≃ₛₗ[e.toRingHom] D :=
    { AddEquiv.refl D with
      map_smul' := fun b d => hsmul b d }
  have := hproj
  have hproj' : Module.Projective B' D := Module.Projective.of_equiv sl
  let act' : Multiplicative (ZMod q) →* (D ≃ₐ[B'] D) :=
    { toFun := fun g => (act g).restrictScalars B'
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have : TensorProduct.CompatibleSMul B' B D D := ⟨fun b m n => by
    rw [hsmul b m, hsmul b n, TensorProduct.smul_tmul]⟩
  let s : TensorProduct B' D D ≃ₗ[B'] TensorProduct B D D :=
    TensorProduct.equivOfCompatibleSMul B B' B' D D
  have hcomp : ∀ x : TensorProduct B' D D,
      Algebra.TensorProduct.productMap
        (AlgHom.pi (fun _ : Multiplicative (ZMod q) => AlgHom.id B' D))
        (AlgHom.pi (fun g => (act' g).toAlgHom)) x =
      Algebra.TensorProduct.productMap
        (AlgHom.pi (fun _ : Multiplicative (ZMod q) => AlgHom.id B D))
        (AlgHom.pi (fun g => (act g).toAlgHom)) (s x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  obtain ⟨σ⟩ := h D hfin' hproj' hff' act' (by
    convert hbij.comp s.bijective using 1
    exact funext hcomp)
  refine ⟨{ toRingHom := (e.symm : B' →+* B).comp σ.toRingHom, commutes' := fun b => ?_ }⟩
  change e.symm (σ (algebraMap B D b)) = b
  rw [hmap, σ.commutes]
  exact e.symm_apply_apply b

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

theorem nonempty_genFib_equiv {T T' O : Type} [CommRing T] [IsDomain T] [CommRing T'] [CommRing O]
    [Algebra T T'] [Algebra T O] [Algebra T' O] [IsScalarTower T T' O] (M : Submonoid T)
    (hM : M ≤ nonZeroDivisors T) [IsLocalization M T'] :
    Nonempty (GenFib T O ≃+* GenFib T' O) := by
  have : IsDomain T' := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hM
  set M1 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)
  set M2 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T')
  have h1 : M1 ≤ M2 := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨algebraMap T T' s, ?_, (IsScalarTower.algebraMap_apply T T' O s).symm⟩
    have hs' : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs' (hinj (by rw [h, map_zero]))
  have h2 : ∀ x : M2, ∃ m : O, m * x ∈ M1 := by
    rintro ⟨x, y, hy, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    refine ⟨algebraMap T O s, a, ?_, ?_⟩
    · have hy' : IsLocalization.mk' T' a s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
      refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
      rintro rfl
      exact hy' (IsLocalization.mk'_zero s)
    · change algebraMap T O a = algebraMap T O s * algebraMap T' O (IsLocalization.mk' T' a s)
      rw [IsScalarTower.algebraMap_apply T T' O s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
  have : IsLocalization M2 (GenFib T O) :=
    IsLocalization.isLocalization_of_is_exists_mul_mem (S := GenFib T O) (M := M1) (N := M2) h1 h2
  exact ⟨(IsLocalization.algEquiv M2 (GenFib T O) (GenFib T' O)).toRingEquiv⟩

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc


open CategoryTheory in
theorem keyAll_of_keyLocal : KeyLocal → KeyAll := by
  intro hL T O _ _ _ _ _ _ _ hAIC P _ φ hφ hSH q hq hqu
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  have : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2

  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  let : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  have : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  let : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  have : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])

  let : Algebra T[X] T'[X] := Polynomial.algebra T T'
  have : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  have hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    apply (IsLocalization.orderEmbedding p.primeCompl T').injective
    change (P'.comap C).under T = (maximalIdeal T').under T
    rw [IsLocalization.AtPrime.under_maximalIdeal T' p]
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']

  have : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      have : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have hqu' : IsUnit (q : T') := by
    simpa using hqu.map (algebraMap T T')
  have key := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial q hq hqu'
  obtain ⟨eG⟩ := nonempty_genFib_equiv (T := T) (T' := T') (O := O) p.primeCompl hle
  exact torsorsTrivial_of_ringEquiv eG q key

end GlobalTheory.LocAcyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
section
open IsLocalRing

noncomputable section

namespace GlobalTheory.LocAcyc

def IsZModTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) : Prop :=
  Module.Finite B D ∧ Module.Projective B D ∧ Module.FaithfullyFlat B D ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)))

theorem torsorsTrivial_iff (B : Type) [CommRing B] (q : ℕ) :
    TorsorsTrivial B q ↔ ∀ (D : Type) [CommRing D] [Algebra B D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)), IsZModTorsor B D q act →
        Nonempty (D →ₐ[B] B) := by
  constructor
  · intro h D _ _ act hD
    exact h D hD.1 hD.2.1 hD.2.2.1 act hD.2.2.2
  · intro h D _ _ h1 h2 h3 act h4
    exact h D act ⟨h1, h2, h3, h4⟩

def LocPiecesEtale (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
    ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)

end GlobalTheory.LocAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeFormComplexStructureBaseChStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), (S.map (Int.cast : ℤ → ℝ)).PosDef → ∀ x : ℝ ⊗[ℤ] GlobalTheory.UnitaryStd.Lat ρ g, x ≠ 0 → 0 < (GlobalTheory.UnitaryStd.form ρ g S).baseChange ℝ ((GlobalTheory.UnitaryStd.cx ρ g).baseChange ℝ x) x := by
  first | exact @GlobalTheory.UnitaryStd.form_cx_baseChange_pos | exact GlobalTheory.UnitaryStd.form_cx_baseChange_pos | (intros; apply GlobalTheory.UnitaryStd.form_cx_baseChange_pos <;> assumption)
end

