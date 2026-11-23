module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
open Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential
universe u v

set_option autoImplicit false

private theorem natCast_isUnit (k : Type) [Field k] [CharZero k] {A : Type} [CommRing A] [Algebra k A]
    {n : ℕ} (hn : n ≠ 0) : IsUnit (n : A) := by
  have h : IsUnit (n : k) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)
  simpa using h.map (algebraMap k A)

private theorem unit_of_trace_one (k : Type) [Field k] [CharZero k] {A A' : Type} [CommRing A]
    [CommRing A'] [Algebra k A] [Algebra A A'] [Module.Finite A A'] [Module.Projective A A']
    (onto : Function.Surjective (PrimeSpectrum.comap (algebraMap A A'))) :
    IsUnit (algTrace A A' 1) := by
  by_contra hnot
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hnot
  obtain ⟨Q, hQ⟩ := onto ⟨M, hM.isPrime⟩
  have hcomap : Q.asIdeal.comap (algebraMap A A') = M := congrArg PrimeSpectrum.asIdeal hQ
  let Am := Localization.AtPrime M
  let L := LocalizedModule M.primeCompl A'
  have base := IsLocalizedModule.isBaseChange M.primeCompl Am
    (LocalizedModule.mkLinearMap M.primeCompl A')
  haveI : Module.Free Am L := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial L := by
    refine ⟨⟨LocalizedModule.mkLinearMap M.primeCompl _ 1, 0, fun h ↦ ?_⟩⟩
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff M.primeCompl
      (LocalizedModule.mkLinearMap M.primeCompl A')).1 h
    have ht0 : algebraMap A A' t = 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact ht
    have hin : (t : A) ∈ Q.asIdeal.comap (algebraMap A A') := by
      rw [Ideal.mem_comap, ht0]; exact Q.asIdeal.zero_mem
    exact t.2 (hcomap.le hin)
  have hrank : algebraMap A Am (algTrace A A' 1) = (Module.finrank Am L : Am) := by
    rw [algTrace_apply, ← projTrace_of_isBaseChange base (LinearMap.mul _ _ 1) LinearMap.id
      (fun x ↦ by simp), projTrace_eq_trace, LinearMap.trace_id]
  have hne : Module.finrank Am L ≠ 0 := fun h ↦
    not_subsingleton L ((Module.finrank_eq_zero_iff_of_free Am L).1 h)
  have hunit : IsUnit (algebraMap A Am (algTrace A A' 1)) := by
    rw [hrank, ← map_natCast (algebraMap A Am)]
    exact (natCast_isUnit k hne).map _
  exact (IsLocalization.AtPrime.isUnit_to_map_iff Am M _).1 hunit hmem

section
variable {k : Type} [Field k] [CharZero k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

private theorem unit_secTrace [Surjective f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsUnit (secTrace (f := f) s s' hU 1) := by
  letI := secAlg s s' f U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  have hsq : Surjective (Spec.map (f.app U)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_fromSpec_app_preimage f hU (hU.preimage f)) inferInstance
  exact unit_of_trace_one k (A := Sec s U) (A' := Sec s' (f ⁻¹ᵁ U)) hsq.surj

omit [CharZero k] in
private theorem pull_trace_app (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (w : Γ(Omega s j, U)) :
    (omegaPull hf j ≫ omegaTrace hf j).app U w = secTrace (f := f) s s' hU 1 • w := by
  obtain ⟨x, rfl⟩ := toOm_surjective (s := s) (j := j) hU w
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf j).app U ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x)) = _
  rw [omegaPull_toOmega hf j U x, ← one_smul (Sec s' (f ⁻¹ᵁ U)) (formPull hf U j x)]
  erw [omegaTrace_toOm_smul_formPull hf j hU]
  exact (toOm s j U).map_smul _ x

private theorem pull_trace_leftInv [Surjective f] (hf : f ≫ s = s') (j : ℕ) :
    ∃ ψ : Omega s j ⟶ Omega s j, (omegaPull hf j ≫ omegaTrace hf j) ≫ ψ = 𝟙 _ := by
  let t : ∀ U : X.affineOpens, (Sec s U.1)ˣ := fun U ↦
    (unit_secTrace (s := s) (s' := s') (f := f) U.2).unit
  have ht : ∀ U : X.affineOpens, (t U : Sec s U.1) = secTrace (f := f) s s' U.2 1 := fun _ ↦ rfl
  have hinv : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1),
      Sec.res s h ((t U)⁻¹ : (Sec s U.1)ˣ) = ((t V)⁻¹ : (Sec s V.1)ˣ) := fun U V h ↦ by
    have e : Sec.res s h (t U) = t V := by
      rw [ht, ht, secTrace_res U.2 V.2 h, map_one]
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← e, ← map_mul, Units.inv_mul, map_one]
  let mulInv : ∀ U : X.affineOpens, Γ(Omega s j, U.1) →ₗ[Γ(X, U.1)] Γ(Omega s j, U.1) := fun U ↦
    LinearMap.lsmul Γ(X, U.1) Γ(Omega s j, U.1) (show Sec s U.1 from ((t U)⁻¹ : (Sec s U.1)ˣ))
  have hmul : ∀ (U : X.affineOpens) (w : Γ(Omega s j, U.1)),
      mulInv U w = (((t U)⁻¹ : (Sec s U.1)ˣ) : Sec s U.1) • w := fun _ _ ↦ rfl
  have hres : ∀ (U V : X.Opens) (h : V ≤ U) (g : Sec s U) (n : Γ(Omega s j, U)),
      (Omega s j).presheaf.map (homOfLE h).op (g • n) =
        Sec.res s h g • (Omega s j).presheaf.map (homOfLE h).op n :=
    fun _ _ _ _ _ ↦ Scheme.Modules.map_smul _ _ _ _
  refine ⟨homOfAffine mulInv fun U V h w ↦ by rw [hmul, hmul, hres, hinv],
    hom_ext_affine fun U hU w ↦ ?_⟩
  refine (homOfAffine_app mulInv _ ⟨U, hU⟩ ((omegaPull hf j ≫ omegaTrace hf j).app U w)).trans ?_
  rw [hmul, pull_trace_app hf j hU, ← ht ⟨U, hU⟩, smul_smul, Units.inv_mul, one_smul]
  rfl
end

theorem UpperTheory.Gal.G3.pHodgeInj :
    HodgeInj := by
  intro k _ _ a b Z W p r c _ _ _ hc x y hxy
  letI := algΓ p
  obtain ⟨ψ, hψ⟩ := pull_trace_leftInv hc a
  have back : ∀ z : hodgeH p a b,
      cohOn.map k ψ ⊤ b (hodgeTrace hc a b (hodgePull hc a b z)) = z := fun z ↦ by
    refine (congrArg (cohOn.map k ψ ⊤ b) (hodgeTrace_hodgePull hc a b z)).trans ?_
    refine (cohOn.map_map k _ ψ z).trans ?_
    rw [hψ]
    exact LinearMap.congr_fun (cohOn.map_id k _ ⊤ b) z
  rw [← back x, ← back y, hxy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHopDeep :
    PlInv.{u} → HopDeep.{u} := by
  classical
  intro hPl B G _ X R _ _ T hT j f hf
  have hfin := hf.2.2
  have hpush : ∀ (n n' : X.ι), X.K n' ≤ X.K n → (∀ g, f g ≠ 0 → X.admitted n j g⁻¹) → ∀ x : T.H (X.q j),
      X.pl T n' n 1 (∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n j z.out⁻¹ x) =
        ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n' j z.out⁻¹ x := by
    intro n n' hn'n hadn x
    rw [map_finsum _ (hfin.subset ?_)]
    · refine finsum_congr fun z => ?_
      rw [map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hn'n) (hadn _ h0), mul_one]
    · intro z hz
      simp only [Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
  constructor
  · obtain ⟨m, hmj, -, hS⟩ := X.deep j (hfin.toFinset.image fun z => (j, (Quotient.out z)⁻¹))
    refine ⟨m, hmj, fun g hg => ⟨hf.2.1 g hg, fun u hu => ?_⟩⟩
    obtain ⟨⟨h, hh⟩, hheq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
    have hz : (g : G ⧸ X.K j) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hheq, (hf.1 h hh g).2]
      exact hg
    have hc := hS (j, (Quotient.out (g : G ⧸ X.K j))⁻¹) (Finset.mem_image_of_mem _ hz) u hu
    simp only [hheq] at hc
    have hmem := mul_mem (mul_mem hh hc) (inv_mem hh)
    convert hmem using 1
    group
  · intro A m hmj hadm hA m' hm'j hadm' x
    obtain ⟨n, -, -, hS⟩ := X.deep j {(m, 1), (m', 1)}
    have hnm : X.K n ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    have hnm' : X.K n ≤ X.K m' := fun u hu => by simpa using hS (m', 1) (by simp) u hu
    apply (hPl X T hT n m' hnm').1
    rw [hpush m' n hnm' hadm', X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm') (X.isAdmissibleIntegralBasisChange_one hm'j), ← hpush m n hnm hadm, ← hA,
      X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm) (X.isAdmissibleIntegralBasisChange_one hmj)]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem hop_summand {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {m j : X.ι} {f : G → R} (hf : X.IsFn j f) (had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹) (g : G)
    (x : T.H (X.q j)) :
    f (g : G ⧸ X.K j).out • X.pl T m j (g : G ⧸ X.K j).out⁻¹ x = f g • X.pl T m j g⁻¹ x := by
  obtain ⟨⟨k, hk⟩, hkeq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
  rw [hkeq, (hf.1 k hk g).2]
  by_cases h0 : f g = 0
  · simp [h0]
  · rw [mul_inv_rev, X.pl_left T (had g h0) (inv_mem hk)]

theorem UpperTheory.Gal.G3.pHopEx :
    PlInv.{u} → HopDeep.{u} → HopEx.{u} := by
  intro hPl hD B G _ X R _ _ T hT j f hf
  obtain ⟨⟨m0, hm0j, had0⟩, hiso⟩ := hD X T hT j f hf
  have huniq : ∀ A A' : Module.End R (T.H (X.q j)), X.IsHop T j f A → X.IsHop T j f A' → A = A' := by
    intro A A' hA hA'
    ext x
    apply (hPl X T hT m0 j hm0j).1
    rw [hA m0 hm0j had0 x, hA' m0 hm0j had0 x]
  obtain ⟨m, hmj, hnorm, hS⟩ := X.deep j {(m0, 1)}
  have hmm0 : X.K m ≤ X.K m0 := fun u hu => by simpa using hS (m0, 1) (by simp) u hu
  have had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm0).mul (had0 g hg)
  set S := hf.2.2.toFinset with hSdef
  have hsub : ∀ (w : G ⧸ X.K j → T.H (X.q m)),
      Function.support (fun z => f z.out • w z) ⊆ (S : Set (G ⧸ X.K j)) := by
    intro w z hz
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hz (by simp [h0])
  let Y : T.H (X.q j) →ₗ[R] T.H (X.q m) := ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹
  have hYS : ∀ x, Y x = ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    simp [Y, LinearMap.sum_apply]
  have hY : ∀ x, Y x = ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    rw [finsum_eq_sum_of_support_subset _ (hsub _), hYS]
  have hinv : ∀ x, ∀ k ∈ X.K j, X.pl T m m k (Y x) = Y x := by
    intro x k hk
    have hadk : X.admitted m m k := ⟨X.K_le j k hk, fun u hu => hnorm k hk u hu⟩
    have key : ∀ z : G ⧸ X.K j, X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x) =
        f (k⁻¹ • z).out • X.pl T m j (k⁻¹ • z).out⁻¹ x := by
      intro z
      have hz : k⁻¹ • z = ((k⁻¹ * z.out : G) : G ⧸ X.K j) := by
        conv_lhs => rw [← QuotientGroup.out_eq' z]
        rfl
      rw [hz, hop_summand X T hf had, (hf.1 k⁻¹ (inv_mem hk) z.out).1, map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T hadk (had _ h0), mul_inv_rev, inv_inv]
    have hsub2 : Function.support (fun z : G ⧸ X.K j => X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x))
        ⊆ (S : Set (G ⧸ X.K j)) := by
      intro z hz
      simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hYS, map_sum, ← finsum_eq_sum_of_support_subset _ hsub2, ← hYS, hY]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm k⁻¹ : Equiv.Perm (G ⧸ X.K j))
      (f := fun z : G ⧸ X.K j => f z.out • X.pl T m j z.out⁻¹ x)
  have hinj := (hPl X T hT m j hmj).1
  have hrange : ∀ x, Y x ∈ LinearMap.range (X.pl T m j 1) := by
    intro x
    obtain ⟨w, hw⟩ := (hPl X T hT m j hmj).2 hnorm (Y x) (hinv x)
    exact ⟨w, hw⟩
  let A : Module.End R (T.H (X.q j)) :=
    (LinearEquiv.ofInjective (X.pl T m j 1) hinj).symm.toLinearMap ∘ₗ Y.codRestrict _ hrange
  have hA : ∀ x, X.pl T m j 1 (A x) = Y x := by
    intro x
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (X.pl T m j 1) hinj).apply_symm_apply ⟨Y x, hrange x⟩)
    rw [LinearEquiv.ofInjective_apply] at h
    exact h
  have hex : ∃ A, X.IsHop T j f A := ⟨A, hiso A m hmj had (fun x => by rw [hA, hY])⟩
  have hh : X.IsHop T j f (X.hecke T j f) := by
    unfold Tower.hecke
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact ⟨hh, fun A' hA' => huniq _ _ hA' hh⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private lemma supp_fin {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] (T : Th.{u} B R)
    {j m : X.ι} {f : G → R} (hf : X.IsFn j f) (x : T.H (X.q j)) :
    (Function.support fun y : G ⧸ X.K j => f y.out • X.pl T m j y.out⁻¹ x).Finite := by
  refine hf.2.2.subset ?_
  intro y hy h0
  exact hy (by simp only [h0, zero_smul])

theorem UpperTheory.Gal.G3.pHopLin :
    FnRing → HopDeep.{u} → HopEx.{u} → HopLin.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' c hf hf'
  obtain ⟨⟨m1, hm1, ha1⟩, -⟩ := hD X T hT j f hf
  obtain ⟨⟨m2, hm2, ha2⟩, -⟩ := hD X T hT j f' hf'
  obtain ⟨m, hmm1, -, hS⟩ := X.deep m1 {(m2, 1)}
  have hmm2 : X.K m ≤ X.K m2 := by
    intro u hu
    simpa using hS (m2, 1) (by simp) u hu
  have hmj : X.K m ≤ X.K j := hmm1.trans hm1
  have hA1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm1).mul (ha1 g hg)
  have hA2 : ∀ g, f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm2).mul (ha2 g hg)
  have e1 := (hE X T hT j f hf).1 m hmj hA1
  have e2 := (hE X T hT j f' hf').1 m hmj hA2
  have hsum := ((hR X R j).2.2.1 f f' hf hf').1
  have hc := (hR X R j).2.2.2 c f hf
  constructor
  · symm
    apply (hE X T hT j (f + f') hsum).2
    apply (hD X T hT j (f + f') hsum).2 _ m hmj
    · intro g hg
      by_cases h1 : f g = 0
      · apply hA2 g
        intro h2
        apply hg
        simp [h1, h2]
      · exact hA1 g h1
    · intro x
      rw [LinearMap.add_apply, map_add (f := _), e1 x, e2 x,
        ← finsum_add_distrib (supp_fin (m := m) X T hf x) (supp_fin (m := m) X T hf' x)]
      apply finsum_congr
      intro y
      simp [add_smul]
  · symm
    apply (hE X T hT j (c • f) hc).2
    apply (hD X T hT j (c • f) hc).2 _ m hmj
    · intro g hg
      apply hA1 g
      intro h
      apply hg
      simp [h]
    · intro x
      rw [LinearMap.smul_apply, map_smul, e1 x, smul_finsum]
      apply finsum_congr
      intro y
      simp [smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem sum_translate {G R M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (g : G) :
    ∑ᶠ z : G ⧸ K, f' z.out • Φ (g * z.out) = ∑ᶠ w : G ⧸ K, f' (g⁻¹ * w.out) • Φ w.out := by
  refine Eq.trans (finsum_congr fun z => ?_)
    (finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ K))
      (f := fun w : G ⧸ K => f' (g⁻¹ * w.out) • Φ w.out))
  have e : (MulAction.toPerm g : Equiv.Perm (G ⧸ K)) z = ((g * z.out : G) : G ⧸ K) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g * z.out)
  simp only [e, hk]
  rw [show g⁻¹ * (g * z.out * (k : G)) = z.out * k by group, hf' _ k.2, hΦ _ k.2]

private theorem sum_conv {G R : Type} {M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (sf : {y : G ⧸ K | f y.out ≠ 0}.Finite)
    (sf' : {y : G ⧸ K | f' y.out ≠ 0}.Finite) :
    ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ᶠ w : G ⧸ K, conv K f f' w.out • Φ w.out := by
  classical
  let Tw : Finset (G ⧸ K) := sf.toFinset.biUnion fun y => sf'.toFinset.image fun z => y.out • z
  have hT : ∀ y ∈ sf.toFinset, ∀ w : G ⧸ K, f' (y.out⁻¹ * w.out) ≠ 0 → w ∈ Tw := by
    intro y hy w hw
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨((y.out⁻¹ * w.out : G) : G ⧸ K), ?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (y.out⁻¹ * w.out)
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [hk, hf' _ k.2]
      exact hw
    · show ((y.out * (y.out⁻¹ * w.out) : G) : G ⧸ K) = w
      rw [mul_inv_cancel_left, QuotientGroup.out_eq']
  have hin : ∀ y ∈ sf.toFinset, ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out =
      ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out := by
    intro y hy
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    refine hT y hy w fun h => hw ?_
    simp [h]
  have hc : ∀ w : G ⧸ K, conv K f f' w.out = ∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out) := by
    intro w
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hl : ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out := by
    refine (finsum_congr fun y => by rw [sum_translate K f' Φ hf' hΦ y.out]).trans ?_
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hs : Function.support (fun w : G ⧸ K => conv K f f' w.out • Φ w.out) ⊆ (Tw : Set (G ⧸ K)) := by
    intro w hw
    have h0 : conv K f f' w.out ≠ 0 := fun h => hw (by simp [h])
    rw [hc w] at h0
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact Finset.mem_coe.2 (hT y hy w (right_ne_zero_of_mul hne))
  rw [hl, finsum_eq_sum_of_support_subset _ hs]
  calc ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out
      = ∑ y ∈ sf.toFinset, f y.out • ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out :=
        Finset.sum_congr rfl fun y hy => by rw [hin y hy]
    _ = ∑ w ∈ Tw, (∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out)) • Φ w.out := by
        simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
        exact Finset.sum_comm
    _ = ∑ w ∈ Tw, conv K f f' w.out • Φ w.out :=
        Finset.sum_congr rfl fun w _ => by rw [hc w]

private theorem pl_left_all {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {i j : X.ι} {k : G} (hk : k ∈ X.K j) (h : G) (x : T.H (X.q j)) :
    X.pl T i j (k * h) x = X.pl T i j h x := by
  by_cases a : X.admitted i j h
  · exact X.pl_left T a hk x
  · have b : ¬ X.admitted i j (k * h) := fun b => a (by
      simpa using b.mul (X.tower_admissible_self ((X.K j).inv_mem hk)))
    simp [Tower.pl, a, b]

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pHopMul :
    FnRing → HopDeep.{u} → HopEx.{u} → HopMul.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' hf hf'
  have hF : X.IsFn j (conv (X.K j) f f') := ((hR X R j).2.2.1 f f' hf hf').2
  have hA := (hE X T hT j f hf).1
  have hA' := (hE X T hT j f' hf').1
  refine ((hE X T hT j _ hF).2 _ ?_).symm
  obtain ⟨m1, l1, a1⟩ := (hD X T hT j f hf).1
  obtain ⟨m2, l2, a2⟩ := (hD X T hT j f' hf').1
  obtain ⟨m3, l3, a3⟩ := (hD X T hT j _ hF).1
  classical
  let S : Finset (X.ι × G) :=
    {(m1, 1), (m2, 1), (m3, 1)} ∪ hf.2.2.toFinset.image fun y => (m2, y.out⁻¹)
  obtain ⟨m, lm, -, hm⟩ := X.deep j S
  have le1 : X.K m ≤ X.K m1 := fun u hu => by simpa using hm (m1, 1) (by simp [S]) u hu
  have le3 : X.K m ≤ X.K m3 := fun u hu => by simpa using hm (m3, 1) (by simp [S]) u hu
  have ad1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le1).mul (a1 g hg)
  have ad3 : ∀ g, conv (X.K j) f f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le3).mul (a3 g hg)
  refine (hD X T hT j _ hF).2 _ m lm ad3 fun x => ?_
  have step : ∀ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
      f y.out • ∑ᶠ z : G ⧸ X.K j, f' z.out • X.pl T m j (y.out * z.out)⁻¹ x := by
    intro y
    by_cases h : f y.out = 0
    · simp [h]
    have ad : X.admitted m m2 y.out⁻¹ := ⟨hf.2.1 _ h, fun u hu => hm (m2, y.out⁻¹)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, by simpa using h, rfl⟩)) u hu⟩
    have e : X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
        X.pl T m m2 y.out⁻¹ (X.pl T m2 j 1 (X.hecke T j f' x)) := by
      rw [X.pl_pl T ad (X.isAdmissibleIntegralBasisChange_one l2), one_mul]
    have fin : (Function.support fun z : G ⧸ X.K j => f' z.out • X.pl T m2 j z.out⁻¹ x).Finite :=
      hf'.2.2.subset fun z hz h0 => hz (by simp [h0])
    rw [e, hA' m2 l2 a2 x, map_finsum _ fin]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases h' : f' z.out = 0
    · simp [h']
    rw [map_smul, X.pl_pl T ad (a2 _ h'), mul_inv_rev]
  rw [Module.End.mul_apply, hA m lm ad1, finsum_congr step]
  exact sum_conv (X.K j) f f' (fun g => X.pl T m j g⁻¹ x) (fun k hk g => (hf'.1 k hk g).2)
    (fun k hk g => by
      simp only [mul_inv_rev]
      exact pl_left_all X T ((X.K j).inv_mem hk) _ x) hf.2.2 hf'.2.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesAbs
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pLiesAbs :
    FEtBasic → TrBase.{u} → TrPushM.{u} → LiesAbs.{u} := by
  intro hF hB hP B R _ T hT Z Y C D pZ pY pC pD π hπ sg tg htg s t ht κ h d m hsg hs hκt hsd hℓ tr trg htr htrg x
  have hpb : IsPullback (pullback.snd π s) (pullback.fst π s) s π := (IsPullback.of_hasPullback π s).flip
  have hfst : FEt (pullback.fst π s) d := hF.1 _ _ s π d hpb hsd
  haveI : IsFinite (pullback.fst π s) := hfst.1
  haveI : Etale (pullback.fst π s) := hfst.2.1
  obtain ⟨tr1, htr1⟩ := hT.tr pZ (pullback.fst π s ≫ pZ) (pullback.fst π s) rfl
  have hsndp : pullback.snd π s ≫ pD = pullback.fst π s ≫ pZ := by
    rw [← hs, ← Category.assoc, ← pullback.condition, Category.assoc, hπ]
  have base := hB T hT pY pD pZ (pullback.fst π s ≫ pZ) (pullback.snd π s) (pullback.fst π s) s π d
    hsndp hπ rfl hpb hsd tr tr1 htr htr1 ((T.pull t ht) x)
  have htrg' : T.IsTr pZ pC (pullback.lift sg κ h ≫ pullback.fst π s) trg := by
    rw [pullback.lift_fst]; exact htrg
  have hℓq : pullback.lift sg κ h ≫ (pullback.fst π s ≫ pZ) = pC := by
    rw [← Category.assoc, pullback.lift_fst, hsg]
  have push := hP T hT pZ (pullback.fst π s ≫ pZ) pC (pullback.lift sg κ h) (pullback.fst π s) d m hℓq rfl
    hfst hℓ tr1 trg htr1 htrg' ((T.pull (pullback.snd π s) hsndp) ((T.pull t ht) x))
  have hcongr : ∀ {W : Scheme} {r : W ⟶ B} (f f' : W ⟶ Y) (e : f = f') (hf : f ≫ pY = r) (hf' : f' ≫ pY = r),
      T.pull f hf x = T.pull f' hf' x := by
    intro W r f f' e hf hf'
    subst e
    rfl
  have h1 : (tg ≫ π) ≫ pY = pC := by rw [Category.assoc, hπ, htg]
  have h2 : (pullback.snd π s ≫ t) ≫ pY = pullback.fst π s ≫ pZ := by rw [Category.assoc, ht, hsndp]
  have h3 : (pullback.lift sg κ h ≫ pullback.snd π s ≫ t) ≫ pY = pC := by
    rw [Category.assoc, h2, hℓq]
  have hmor : tg ≫ π = pullback.lift sg κ h ≫ pullback.snd π s ≫ t := by
    rw [← Category.assoc, pullback.lift_snd, hκt]
  rw [← T.pull_comp tg π htg hπ h1, hcongr _ _ hmor h1 h3,
    T.pull_comp (pullback.lift sg κ h) (pullback.snd π s ≫ t) hℓq h2 h3,
    T.pull_comp (pullback.snd π s) t hsndp ht h2, push, base]
end

