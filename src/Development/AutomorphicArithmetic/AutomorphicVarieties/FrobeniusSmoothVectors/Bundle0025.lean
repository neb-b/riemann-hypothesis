module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocCpl
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cpl_of_nil {R : Type} [CommRing R] (I : Ideal R) (N : ℕ) (h : I ^ N = ⊥) : IsAdicComplete I R := by
  have hle : ∀ n, N ≤ n → (I ^ n • ⊤ : Submodule R R) = ⊥ := by
    intro n hn
    rw [eq_bot_iff]
    calc (I ^ n • ⊤ : Submodule R R) ≤ I ^ N • ⊤ := Submodule.smul_mono (Ideal.pow_le_pow_right hn) le_rfl
      _ = ⊥ := by rw [h, Submodule.bot_smul]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ⟨f N, fun n => ?_⟩ }
  · have hxN := hx N
    rw [hle N le_rfl, SModEq.bot] at hxN
    exact hxN
  · rcases le_total n N with hn | hn
    · exact hf hn
    · have hfn := hf hn
      rw [hle N le_rfl, SModEq.bot] at hfn
      rw [hfn]

private theorem res_eq_of {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x : R} {a : O} (h : x - algebraMap O R a ∈ maximalIdeal R) : res O R x = algebraMap O _ a := by
  have := (res_eq_zero_iff O R _).2 h
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

private theorem co_pow {O D R : Type} [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (ι : D →ₐ[O] R) (y : Ideal D) (hy : ∀ a, a ∈ y ↔ ι a ∈ maximalIdeal R)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ h : IsCO O (D ⧸ y ^ N), (@maximalIdeal _ _ h.toIsLocalRing) ^ N = ⊥ ∧
      ∀ a, res O (D ⧸ y ^ N) (Ideal.Quotient.mk _ a) = res O R (ι a) := by
  classical
  let f : D →+* ResidueField O := (res O R).toRingHom.comp ι.toRingHom
  have hfa : ∀ a : O, f (algebraMap O D a) = IsLocalRing.residue O a := by
    intro a
    show res O R (ι (algebraMap O D a)) = _
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap O D a, hfa a⟩
  have hker : RingHom.ker f = y := by
    ext a
    rw [RingHom.mem_ker, hy]
    exact res_eq_zero_iff O R (ι a)
  haveI hymax : y.IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective f hf
  have hyN : y ^ N ≤ y := Ideal.pow_le_self hN
  let f' : D ⧸ y ^ N →+* ResidueField O := Ideal.Quotient.lift (y ^ N) f (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact hyN ha)
  have hf'mk : ∀ d, f' (Ideal.Quotient.mk _ d) = f d := fun d => rfl
  have hf' : Function.Surjective f' := by
    intro z
    obtain ⟨d, rfl⟩ := hf z
    exact ⟨_, hf'mk d⟩
  haveI hMmax : (RingHom.ker f').IsMaximal := RingHom.ker_isMaximal_of_surjective f' hf'
  have hMle : RingHom.ker f' ≤ y.map (Ideal.Quotient.mk (y ^ N)) := by
    intro z hz
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, hf'mk, ← RingHom.mem_ker, hker] at hz
    exact Ideal.mem_map_of_mem _ hz
  have hMN : RingHom.ker f' ^ N = ⊥ := by
    rw [eq_bot_iff]
    calc RingHom.ker f' ^ N ≤ (y.map (Ideal.Quotient.mk (y ^ N))) ^ N := Ideal.pow_right_mono hMle N
      _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  haveI : IsAdicComplete (RingHom.ker f') (D ⧸ y ^ N) := cpl_of_nil _ N hMN
  haveI hloc : IsLocalRing (D ⧸ y ^ N) := isLocalRing_of_isAdicComplete_maximal (RingHom.ker f')
  have hMeq : RingHom.ker f' = maximalIdeal (D ⧸ y ^ N) := IsLocalRing.eq_maximalIdeal hMmax
  have hmem : ∀ z, z ∈ maximalIdeal (D ⧸ y ^ N) ↔ f' z = 0 := by
    intro z; rw [← hMeq, RingHom.mem_ker]
  have hfq : ∀ a : O, f' (algebraMap O (D ⧸ y ^ N) a) = IsLocalRing.residue O a := fun a => hfa a
  let hco : IsCO O (D ⧸ y ^ N) :=
    { complete := hMeq ▸ inferInstance
      isLocalHom := ⟨fun a ha => by
        by_contra hna
        have h0 : IsLocalRing.residue O a = 0 :=
          (IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)
        have hu := ha.map f'
        rw [hfq, h0] at hu
        exact not_isUnit_zero hu⟩
      res_surj := fun z => by
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (f d)
        refine ⟨a, (hmem _).2 ?_⟩
        rw [map_sub, hfq, hf'mk, ha, sub_self] }
  letI := hco
  refine ⟨hco, ?_, fun d => ?_⟩
  · rw [← hMeq]; exact hMN
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (ι d)
    rw [res_eq_of ha]
    apply res_eq_of
    rw [hmem, map_sub, hfq, hf'mk]
    have h0 := (res_eq_zero_iff O R _).2 ha
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
    show res O R (ι d) - _ = 0
    rw [h0, sub_eq_zero]
    rfl

private theorem cpl_of_univ {O D R : Type} [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (ι : D →ₐ[O] R)
    (univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
      (∀ a, res O C (f a) = res O R (ι a)) → ∃! g : R →ₐ[O] C, ∀ a, g (ι a) = f a) :
    @UpperTheory.V.CA.IsCplAt _ _ ((maximalIdeal R).comap ι.toRingHom) R _ ι.toRingHom.toAlgebra _ := by
  letI : Algebra D R := ι.toRingHom.toAlgebra
  have hy : ∀ a, a ∈ (maximalIdeal R).comap ι.toRingHom ↔ ι a ∈ maximalIdeal R := fun a => Iff.rfl
  have hmg : ∀ {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (g : R →ₐ[O] C),
      Ideal.map g (maximalIdeal R) ≤ maximalIdeal C := by
    intro C _ _ _ g
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← res_eq_zero_iff O C]
    show res O C (g r) = 0
    rw [res_map]
    exact (res_eq_zero_iff O R r).2 hr
  refine ⟨inferInstance, IsCO.complete (O := O), fun n => ?_, fun n r => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨hco, hnil, hres⟩ := co_pow ι _ hy n hn.ne'
    letI := hco
    obtain ⟨g, hg, -⟩ := univ _ (Ideal.Quotient.mkₐ O _) (fun a => hres a)
    apply le_antisymm
    · intro a ha
      have hgm : ∀ r ∈ maximalIdeal R ^ n, g r = 0 := by
        intro r hr
        have h1 : Ideal.map g (maximalIdeal R ^ n) ≤ ⊥ := by
          rw [Ideal.map_pow, ← hnil]
          exact Ideal.pow_right_mono (hmg g) n
        exact Ideal.mem_bot.1 (h1 (Ideal.mem_map_of_mem g hr))
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk O, ← hg a]
      exact hgm _ ha
    · exact Ideal.le_comap_pow _ n
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by simp⟩
    haveI : Nontrivial (R ⧸ maximalIdeal R ^ n) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self hn.ne'))
    letI hcoR : IsCO O (R ⧸ maximalIdeal R ^ n) :=
      co_quot O R _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)
    obtain ⟨hco, hnil, hres⟩ := co_pow ι _ hy n hn.ne'
    letI := hco
    obtain ⟨g, hg, -⟩ := univ _ (Ideal.Quotient.mkₐ O _) (fun a => hres a)
    have hker : ∀ a ∈ ((maximalIdeal R).comap ι.toRingHom) ^ n,
        ((Ideal.Quotient.mkₐ O (maximalIdeal R ^ n)).comp ι) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.le_comap_pow _ n ha
    let hbar := Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ O (maximalIdeal R ^ n)).comp ι) hker
    have hbar_mk : ∀ d, hbar (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (ι d) := fun d => rfl
    obtain ⟨g0, -, huniq⟩ := univ (R ⧸ maximalIdeal R ^ n) ((Ideal.Quotient.mkₐ O _).comp ι)
      (fun a => res_map (Ideal.Quotient.mkₐ O _) (ι a))
    have e1 := huniq (Ideal.Quotient.mkₐ O _) (fun a => rfl)
    have e2 := huniq (hbar.comp g) (fun a => by
      rw [AlgHom.comp_apply, hg a, Ideal.Quotient.mkₐ_eq_mk, hbar_mk]
      rfl)
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (g r)
    refine ⟨d, ?_⟩
    rw [← Ideal.Quotient.eq]
    have h3 : Ideal.Quotient.mkₐ O (maximalIdeal R ^ n) r = (hbar.comp g) r := by rw [e1, e2]
    rw [AlgHom.comp_apply, ← hd, hbar_mk, Ideal.Quotient.mkₐ_eq_mk] at h3
    exact h3

theorem UpperTheory.V.Fr.loc_cpl :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R, (∀ a, ι' (1 ⊗ₜ a) = L.ι a) → @UpperTheory.V.CA.IsCplAt _ _ ((maximalIdeal L.R).comap ι'.toRingHom) L.R _ ι'.toRingHom.toAlgebra _ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L ι' hι'
  obtain ⟨-, -, -, -, -, hnoeth, -⟩ := gr_A hF hn S
  haveI : IsNoetherianRing (TensorProduct O S.A L.O') := IsNoetherianRing.of_finite S.A _
  haveI : IsNoetherianRing (TensorProduct O L.O' S.A) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv
  apply cpl_of_univ ι'
  intro C _ _ _ f hf
  letI : Algebra O C := Algebra.compHom C (algebraMap O L.O')
  haveI : IsScalarTower O L.O' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let f' : S.A →ₐ[O] C := (f.restrictScalars O).comp Algebra.TensorProduct.includeRight
  obtain ⟨g, hg, hu⟩ := L.univ C f' (fun a => by
    show res L.O' C (f (1 ⊗ₜ a)) = _
    rw [← hι' a]
    exact hf _)
  refine ⟨g, fun t => ?_, fun g' hg' => hu g' (fun a => by
    rw [← hι' a]
    exact hg' _)⟩
  have hcomp : g.comp ι' = f := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    show g (ι' (1 ⊗ₜ a)) = f (1 ⊗ₜ a)
    rw [hι', hg]
    rfl
  exact AlgHom.congr_fun hcomp t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MaximalIdealImageKills
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.maximal_ideal_image_kills :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ {Q : Type} [CommRing Q] [IsLocalRing Q] [IsNoetherianRing Q] (f : ResidueField O →+* Q) (φ : S.A →+* Q), (∀ a : O, φ (algebraMap O S.A a) = f (residue O a)) → (∀ y ∈ S.mB, φ (S.inc y) ∈ maximalIdeal Q) → (S.u.map φ).triM = ⊥ → (S.u.map φ).IsBar f → ∀ y ∈ S.mB, φ (S.inc y) = 0 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ _ f φ hf hm htri hbar y hy
  have hK : (⨅ N : ℕ, maximalIdeal Q ^ N) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top
  rw [← Ideal.mem_bot, ← hK, Ideal.mem_iInf]
  intro N
  obtain ⟨M, hM⟩ := (cont_u hF hn S).2.2.2 0 N
  obtain ⟨z, hz, hyz⟩ := y.2 (M + 1)
  let zB : S.B := ⟨z, le_adicClosure _ hz⟩
  have hd : y - zB ∈ S.mB := by
    show (y : S.R) - z ∈ maximalIdeal S.R
    exact Ideal.pow_le_self (Nat.succ_ne_zero M) hyz
  have hzB : zB ∈ S.mB := by
    have := sub_mem hy hd
    simpa using this
  have hz0 : φ (S.inc zB) = 0 := by
    obtain ⟨c, hc⟩ := adjoin_image_in_residue_range S f φ hf htri hbar (S.inc zB) hz
    have h1 := hm zB hzB
    rw [← hc] at h1 ⊢
    by_cases h0 : c = 0
    · rw [h0, map_zero]
    · exact absurd ((IsUnit.mk0 c h0).map f) h1
  have hgr : S.inc (y - zB) ∈ S.gr 0 := by
    have h1 : (1 : S.A) ∈ S.gr 0 := Submodule.subset_span ⟨[], by simp, by simp⟩
    have h2 := Submodule.smul_mem _ (y - zB) h1
    rw [Algebra.smul_def, mul_one] at h2
    exact h2
  have ha := hM _ hgr (Ideal.pow_le_pow_right (Nat.le_succ M) hyz)
  have hle : S.mB ^ N ≤ (maximalIdeal Q ^ N).comap (φ.comp (S.inc : S.B →+* S.A)) :=
    le_trans (Ideal.pow_right_mono (fun b hb => hm b hb) N) (Ideal.le_comap_pow _ N)
  have key : φ (S.inc (y - zB)) ∈ maximalIdeal Q ^ N := by
    refine Submodule.smul_induction_on (p := fun a => φ a ∈ maximalIdeal Q ^ N) ha ?_ ?_
    · intro b hb x _
      rw [Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hle hb)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact add_mem ha hb
  rwa [map_sub, map_sub, hz0, sub_zero] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MinHom
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem aux {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    (h1 : DirectSum.IsInternal 𝒜) (h2 : SetLike.GradedMonoid 𝒜) (η : Ideal A) (hη : η ∈ minimalPrimes A) :
    η = Ideal.span {x | x ∈ η ∧ ∃ j, x ∈ 𝒜 j} := by
  classical
  letI : DirectSum.Decomposition 𝒜 := h1.chooseDecomposition
  letI : GradedRing 𝒜 := { }
  have hp : η.IsPrime := hη.1.1
  have hc : (η.homogeneousCore 𝒜).toIdeal.IsPrime := Ideal.IsPrime.homogeneousCore hp
  have hle : (η.homogeneousCore 𝒜).toIdeal ≤ η := Ideal.toIdeal_homogeneousCore_le 𝒜 η
  have hge : η ≤ (η.homogeneousCore 𝒜).toIdeal := hη.2 ⟨hc, bot_le⟩ hle
  apply le_antisymm
  · refine hge.trans ?_
    show Ideal.homogeneousCore' 𝒜 η ≤ _
    unfold Ideal.homogeneousCore'
    apply Ideal.span_mono
    rintro _ ⟨⟨x, hx⟩, hx', rfl⟩
    exact ⟨hx', hx⟩
  · exact Ideal.span_le.2 fun x hx => hx.1

theorem UpperTheory.V.Fr.min_hom :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η ∈ minimalPrimes S.A, S.IsHom η := by
  intro l _ O _ _ _ _ F C₀ n hF hn S η hη
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.Fr.gr_A hF hn S
  exact aux S.gr h1 h2 η hη
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrTsurj
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Fr.pr_tsurj :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → ∀ x ∈ Z1C F.loc (B.bar O).ad (B.bar O).b, ∃ D ∈ Tan O R, ∃ X, ∀ s, B.tanCo O D s = x.1 s + ((B.bar O).ad s X - X) := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hOf hCont hGood x hx
  obtain ⟨hco1, hco2⟩ := co_res O
  haveI := hco1
  haveI := hco2
  have hresk : ∀ c : ResidueField O, res O (ResidueField O) c = c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← IsLocalRing.ResidueField.algebraMap_eq, AlgHom.commutes]
  let p := TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)
  have hresd : ∀ a : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) a = a.fst := by
    intro a
    rw [← res_map p a, hresk]
    rfl
  obtain ⟨-, -, hlc⟩ := pr_open (C₀ := C₀) hF O R B hCont
  obtain ⟨B', hB'c, hB'map, hB'snd⟩ := pr_tbox hF O (B.bar O) hlc x hx
  have hOfbar : (Box.map (p : DualNumber (ResidueField O) →+* ResidueField O) B').Of (ρ.bar O) := by
    rw [hB'map]
    refine ⟨?_, ?_, ?_⟩
    · show ((B.r F.c).mat).map (res O R) = 1
      rw [hOf.atc]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro s
      show ((B.r s).mat).map (res O R) = _
      rw [hOf.res]
      rfl
    · intro v i s
      have e : (((B.bar O).g v : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) * (ρ.bar O).r (F.loc0 v s) *
          ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) =
          (res O R).mapMatrix ((B.g v : Matrix (Fin n) (Fin n) R) * ρ.r (F.loc0 v s) *
            (((B.g v)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) := by
        rw [map_mul, map_mul]
        rfl
      rw [e]
      exact congrArg (res O R) (hOf.psi v i s)
  have hn := pr_norm hF O (DualNumber (ResidueField O)) (ResidueField O) p (ρ.bar O) B'
  have hker : maximalIdeal (DualNumber (ResidueField O)) * RingHom.ker p = ⊥ := by
    refine eq_bot_iff.2 (Ideal.mul_le.2 fun a ha b hb => ?_)
    have ha0 : a.fst = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).1 ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne))
    have hb0 : b.fst = 0 := by simpa [p] using RingHom.mem_ker.1 hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha0, hb0]
  have hbb : NRep.bar O (NRep.bar O ρ) = NRep.bar O ρ := by
    refine NRep.ext ?_ ?_
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      simp only [NRep.bar, NRep.map_r]
      exact hresk _
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      simp only [NRep.bar, NRep.map_ψ]
      exact hresk _
  obtain ⟨h, ρ', hh1, hρ'p, hρ'c, hrc, hr0⟩ := hn hker (by rw [hbb]; exact hGood) hOfbar hB'c
  have hfun : ((res O (DualNumber (ResidueField O))) : DualNumber (ResidueField O) →+* ResidueField O) = (p : DualNumber (ResidueField O) →+* ResidueField O) :=
    RingHom.ext fun a => hresd a
  have hbar' : NRep.bar O ρ' = NRep.bar O ρ := by
    show NRep.map _ ρ' = _
    rw [hfun, hρ'p]
  have hdof : ∃ D ∈ Tan O R, ∀ s, (conjBy h B'.r s).mat.map TrivSqZeroExt.snd = B.tanCo O D s * ((B.bar O).r s).mat := by
    obtain ⟨g, hg, -⟩ := hU.univ _ ρ' hρ'c hbar'
    have hfst : ∀ x, (g x).fst = res O R x := fun x => by
      rw [← hresd (g x), res_map]
    let Dd : R →ₗ[O] ResidueField O :=
      { toFun := fun x => (g x).snd
        map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
        map_smul' := fun a x => by simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
    have hDd : ∀ x, Dd x = (g x).snd := fun _ => rfl
    have hr : (Box.map (g : R →+* DualNumber (ResidueField O)) B).r = conjBy h B'.r := by
      refine pr_ext hF _ _ _ (Box.nu _) (fun s => by simp [conjBy, B'.nu s]) ?_ ?_
      · change (B.r F.c).mat.map g = (conjBy h B'.r F.c).mat
        rw [hOf.atc, hrc]
        exact Matrix.map_one _ (map_zero g) (map_one g)
      · intro s
        change (B.r s).mat.map g = (conjBy h B'.r s).mat
        rw [hOf.res]
        change (ρ.map (g : R →+* DualNumber (ResidueField O))).r s = (conjBy h B'.r s).mat
        rw [hg, hr0]
    refine ⟨Dd, ?_, fun s => ?_⟩
    · intro f hf
      rw [hDd, hDd, hDd, map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
    · rw [← hr]
      show ((B.r s).mat.map g).map TrivSqZeroExt.snd = ((B.r s).mat.map Dd * ((((Box.bar O B).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) * ((((Box.bar O B).r s).left : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
      rw [mul_assoc, Units.inv_mul, mul_one, Matrix.map_map]
      rfl
  obtain ⟨D, hD, hDs⟩ := hdof
  let μ : ResidueField O →+ DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inrHom (ResidueField O) (ResidueField O)).toAddMonoidHom
  have hμ : IsSq O μ := by
    constructor
    · intro a c
      rw [hresd]
      ext
      · simp [μ]
      · simp [μ, TrivSqZeroExt.snd_mul, MulOpposite.smul_eq_mul_unop, smul_eq_mul, mul_comm]
    · intro c
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [μ]
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O (DualNumber (ResidueField O)) n μ hμ
  let Y : Matrix (Fin n) (Fin n) (ResidueField O) := (h : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))).map TrivSqZeroExt.snd
  have hhe : h = e Y := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [he1]
    have h0 := congrFun (congrFun hh1 i) j
    simp only [Matrix.map_apply] at h0
    refine TrivSqZeroExt.ext ?_ ?_
    · by_cases hij : i = j
      · subst hij
        simpa [μ, p] using h0
      · simpa [μ, p, Matrix.one_apply_ne hij] using h0
    · by_cases hij : i = j
      · subst hij
        simp [μ, Y]
      · simp [μ, Y, Matrix.one_apply_ne hij]
  refine ⟨D, hD, -Y, fun s => ?_⟩
  have hgbar : GG.map ((res O (DualNumber (ResidueField O))) : DualNumber (ResidueField O) →+* ResidueField O) (B'.r s) = (B.bar O).r s := by
    rw [hfun, ← hB'map]
    rfl
  have hconj : conjBy h B'.r s = GG.ofGL (e (Y + ((B.bar O).r s).adFun (-Y))) * B'.r s := by
    have h5 := he5 (B'.r s) (-Y)
    rw [hgbar] at h5
    rw [he2, map_mul, mul_assoc, ← h5, ← mul_assoc, ← he3, ← hhe, map_inv]
    rfl
  have hm : ∀ (A : GL (Fin n) (DualNumber (ResidueField O))) (g : GG (m := n) (R := DualNumber (ResidueField O))),
      (GG.ofGL A * g).mat = (A : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))) * g.mat := by
    intro A g
    simp [GG.mat, GG.ofGL]
  have hmat : (conjBy h B'.r s).mat = (B'.r s).mat + ((Y + ((B.bar O).r s).adFun (-Y)) * ((B.bar O).r s).mat).map μ := by
    rw [hconj, hm, he1, add_mul, one_mul, (he4 _ _).2, ← hgbar, GG.map_mat]
    rfl
  have hsnd := hDs s
  rw [hmat] at hsnd
  have hadd : ∀ (P Q : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))),
      (P + Q).map TrivSqZeroExt.snd = P.map TrivSqZeroExt.snd + Q.map TrivSqZeroExt.snd := by
    intro P Q
    ext i j
    simp
  have hmapsnd : ∀ W : Matrix (Fin n) (Fin n) (ResidueField O), (W.map μ).map TrivSqZeroExt.snd = W := by
    intro W
    ext i j
    simp [μ]
  rw [hadd, hmapsnd, hB'snd s, ← add_mul] at hsnd
  have hM : ((B.bar O).r s).mat * (((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O) ) = (1 : Matrix (Fin n) (Fin n) (ResidueField O)) := Units.mul_inv _
  have h6 := congrArg (· * ((((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) hsnd
  simp only [Matrix.mul_assoc, hM, Matrix.mul_one] at h6
  rw [← h6]
  show _ = x.1 s + (((B.bar O).r s).adFun (-Y) - -Y)
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  have h2 : a ≠ a⁻¹ := by
    intro h
    apply ha
    rw [sq]
    nth_rewrite 2 [h]
    simp
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals first | exact h1 | exact Ne.symm h1 | exact h2 | exact Ne.symm h2
  · fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals first | exact h1 | exact Ne.symm h1 | exact h2 | exact Ne.symm h2

theorem UpperTheory.V.Fr.flag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : S.A →+* C) (v : F.V), UpperTheory.V.W.HasFlag ((S.u.map f).r.comp (F.loc0 v)).toHomUnits ((S.u.map f).ψ v) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ f v
  obtain ⟨g, hg⟩ := hF.f3 v
  obtain ⟨hB, hm⟩ := co_B hF hn S
  refine flag_loc _ _ g (fun i j hij => ?_) ?_ (fun s => (S.u.map f).ord v s)
  · have hu : IsUnit (S.ψB v i g - S.ψB v j g) := by
      by_contra hu
      have h1 : S.ψB v i g - S.ψB v j g ∈ S.mB := by
        rw [← hm]
        exact hu
      have h2 : (S.ρ.ψ v i g : S.R) - S.ρ.ψ v j g ∈ maximalIdeal S.R := h1
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      have h4 : ∀ i, res O S.R (S.ρ.ψ v i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
        fun i => S.lift.2.1.2 v i g
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne hn _ hg i j hij (Units.ext h3)
    have h5 := (hu.map S.inc).map f
    rw [map_sub, map_sub] at h5
    exact h5
  · have h := congrArg (Polynomial.map ((residue C).comp f)) (o1 hF hn S v g)
    rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact h
end

