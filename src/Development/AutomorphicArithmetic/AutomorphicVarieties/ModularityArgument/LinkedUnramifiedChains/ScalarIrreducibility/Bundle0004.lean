module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExistsBetweenFinset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ChevPrime
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem chev_prime (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (P : Ideal A) [P.IsPrime] (a : A) (ha : a ∉ P) :
    ∃ b : B, b ∉ P.comap (algebraMap B A) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
      P.comap (algebraMap B A) ≤ RingHom.ker y → y b ≠ 0 →
        ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 ∧ P ≤ RingHom.ker ξ := by
  set p := P.comap (algebraMap B A)
  haveI : Algebra.FiniteType B (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B P) (Ideal.Quotient.mkₐ_surjective B P)
  haveI : Algebra.FiniteType (B ⧸ p) (A ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType B (B ⧸ p) (A ⧸ P)
  obtain ⟨b', hb'0, hb'⟩ := UpperTheory.V.J.chev (B ⧸ p) (A ⧸ P) Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.mk P a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at hb'0
  · intro K _ _ y hy hyb
    let y' : B ⧸ p →+* K := Ideal.Quotient.lift p y (fun x hx => (RingHom.mem_ker).mp (hy hx))
    obtain ⟨ξ', hξ'1, hξ'2⟩ := hb' K y' (by simpa [y'] using hyb)
    refine ⟨ξ'.comp (Ideal.Quotient.mk P), ?_, hξ'2, ?_⟩
    · ext x
      have h := congrArg (fun f => f (Ideal.Quotient.mk p x)) hξ'1
      simp only [RingHom.comp_apply, y', Ideal.Quotient.lift_mk] at h ⊢
      exact h
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem gen_out {R : Type} [CommRing R] {s : Set R} {P : Ideal R} (h : ¬ Ideal.span s ≤ P) :
    ∃ x ∈ s, x ∉ P := by
  by_contra hc
  push_neg at hc
  exact h (Ideal.span_le.2 hc)

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.genPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (P : Ideal S.A) (Gd : (S.B →ₐ[c.O] Qbar l) → Prop), P ∈ minimalPrimes S.A → S.u.TI P →
          (∀ b ∉ S.π P, ∃ y : S.B →ₐ[c.O] Qbar l, S.π P ≤ RingHom.ker y ∧ Gd y ∧ y b ≠ 0) →
          ∃ ξ : S.A →ₐ[c.O] Qbar l, VPt S ξ ∧ S.u.TI (RingHom.ker ξ) ∧ P ≤ RingHom.ker ξ ∧ Gd (ξ.comp S.inc) := by
  intro l _ c _ F C₀ n hF hn S P Gd hP hTI hext
  obtain ⟨-, -, hgr0, -, hFT, -, hr⟩ := Fr.gr_A hF hn S
  haveI := hFT
  haveI hPp : P.IsPrime := hP.1.1
  have hTI' : (¬ S.u.triP ≤ P ∧ ¬ S.u.triM ≤ P) ∧ (n = 3 → ¬ S.u.ee ≤ P) := hTI
  obtain ⟨x1, ⟨g1, i1, j1, hlt1, rfl⟩, hx1⟩ :=
    gen_out (s := {x | ∃ g i, ∃ j < i, x = S.u.r g i j}) hTI'.1.1
  obtain ⟨x2, ⟨g2, i2, j2, hlt2, rfl⟩, hx2⟩ :=
    gen_out (s := {x | ∃ g i j, i < j ∧ x = S.u.r g i j}) hTI'.1.2
  obtain ⟨x3, ⟨k3, hx3k⟩, hx3P, hx3ee⟩ :
      ∃ x3 : S.A, (∃ k, x3 ∈ S.gr k) ∧ x3 ∉ P ∧ (n = 3 → x3 ∈ S.u.ee) := by
    by_cases h3 : n = 3
    · obtain ⟨x, ⟨g, i, j, hodd, rfl⟩, hx⟩ :=
        gen_out (s := {x | ∃ g i j, Odd (Fr.w n i - Fr.w n j) ∧ x = S.u.r g i j}) (hTI'.2 h3)
      exact ⟨_, ⟨_, hr g i j⟩, hx, fun _ => Ideal.subset_span ⟨g, i, j, hodd, rfl⟩⟩
    · refine ⟨1, ⟨0, ?_⟩, (Ideal.ne_top_iff_one P).mp hPp.ne_top, fun h => absurd h h3⟩
      rw [hgr0]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have ha : S.u.r g1 i1 j1 * S.u.r g2 i2 j2 * x3 ∉ P := by
    intro h
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    · exact hx3P h
  obtain ⟨b, hbP, hb⟩ := chev_prime S.B S.A P _ ha
  obtain ⟨y, hyP, hGd, hyb⟩ := hext b hbP
  obtain ⟨ξ0, hξ0, hξ0a, hPξ0⟩ := hb (Qbar l) (y : S.B →+* Qbar l) (fun x hx => hyP hx) hyb
  have hξ0' : ∀ x : S.B, ξ0 (S.inc x) = y x := fun x =>
    congrArg (fun f : S.B →+* Qbar l => f x) hξ0
  let ξ1 : S.A →ₐ[c.O] Qbar l :=
    { ξ0 with
      commutes' := fun r => by
        show ξ0 (algebraMap c.O S.A r) = algebraMap c.O (Qbar l) r
        rw [← S.inc.commutes r, hξ0', y.commutes r] }
  have hcomp : ξ1.comp S.inc = y := by
    ext x
    exact hξ0' x
  rw [map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hξ0a
  obtain ⟨⟨h1, h2⟩, h3⟩ := hξ0a
  have hoff : S.u.OffTri (RingHom.ker ξ1) :=
    ⟨fun h => h1 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩))),
      fun h => h2 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩)))⟩
  obtain ⟨ξ', hV, hc', hz⟩ := UpperTheory.V.J.scale l c F C₀ n hF hn S ξ1 hoff
  have hTIξ : S.u.TI (RingHom.ker ξ') :=
    ⟨⟨fun h => h1 ((hz _ _ (hr g1 i1 j1)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩)))),
      fun h => h2 ((hz _ _ (hr g2 i2 j2)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩))))⟩,
      fun hn3 h => h3 ((hz _ _ hx3k).mp (RingHom.mem_ker.mp (h (hx3ee hn3))))⟩
  refine ⟨ξ', hV, hTIξ, ?_, ?_⟩
  · intro x hx
    have hh := Fr.min_hom hF hn S P hP
    unfold Fr.Space.IsHom at hh
    rw [hh] at hx
    refine (Ideal.span_le.mpr ?_) hx
    rintro z ⟨hzP, k, hzk⟩
    exact RingHom.mem_ker.mpr ((hz k z hzk).mpr (RingHom.mem_ker.mp (hPξ0 hzP)))
  · rw [hc', hcomp]
    exact hGd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerExt
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Cofinal

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

private theorem artinian_quot (j : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ j) := by
  have : Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ j) := by
    refine Ring.krullDimLE_zero_iff.2 fun P hP => ?_
    have hc : (P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))).IsPrime := Ideal.comap_isPrime _ _
    have hle : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) := fun x hx => by
      refine hc.mem_of_pow_mem j ?_
      have : Ideal.Quotient.mk (maximalIdeal B ^ j) (x ^ j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx j)
      show Ideal.Quotient.mk _ (x ^ j) ∈ P
      rw [this]
      exact zero_mem _
    have he : P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = maximalIdeal B :=
      ((maximalIdeal.isMaximal B).eq_of_le hc.ne_top hle).symm
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hne
    have hc' : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) ≠ ⊤ := fun h =>
      hne (by rw [Ideal.eq_top_iff_one]; simpa using (Ideal.eq_top_iff_one _).1 h)
    have h1 : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) :=
      le_antisymm ((le_maximalIdeal hc').trans he.ge) (Ideal.comap_mono hJ.le)
    exact hJ.ne' (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem stab (I : ℕ → Ideal B) (hI : Antitone I) (j : ℕ) :
    ∃ e, ∀ N, e ≤ N → ∀ a ∈ I e, ∃ b ∈ I N, a - b ∈ maximalIdeal B ^ j := by
  haveI := artinian_quot (B := B) j
  let f : ℕ →o (Ideal (B ⧸ maximalIdeal B ^ j))ᵒᵈ :=
    ⟨fun N => OrderDual.toDual ((I N).map (Ideal.Quotient.mk _)), fun a b h => Ideal.map_mono (hI h)⟩
  obtain ⟨e, he⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨e, fun N hN a ha => ?_⟩
  have h1 : Ideal.Quotient.mk (maximalIdeal B ^ j) a ∈ (I N).map (Ideal.Quotient.mk _) := by
    have h2 : (I e).map (Ideal.Quotient.mk (maximalIdeal B ^ j)) = (I N).map (Ideal.Quotient.mk _) := he N hN
    rw [← h2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨b, hb, h3⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
  exact ⟨b, hb, Ideal.Quotient.eq.1 h3.symm⟩

private theorem cofinal [IsAdicComplete (maximalIdeal B) B] (I : ℕ → Ideal B) (hI : Antitone I)
    (h0 : ⨅ N, I N = ⊥) (k : ℕ) : ∃ N, I N ≤ maximalIdeal B ^ k := by
  by_contra hcon
  push_neg at hcon
  choose e he using fun j => stab I hI (k + j)

  let E : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup e + j
  have hE : Monotone E := monotone_nat_of_le_succ fun j =>
    Nat.add_le_add (Finset.sup_mono (Finset.range_mono (Nat.le_succ _))) (Nat.le_succ _)
  have hEe : ∀ j, e j ≤ E j := fun j =>
    le_trans (Finset.le_sup (f := e) (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)
  have hEj : ∀ j, j ≤ E j := fun j => Nat.le_add_left _ _
  let P : ℕ → B → Prop := fun j x => x ∈ I (E j) ∧ x ∉ maximalIdeal B ^ k
  have step : ∀ j x, P j x → ∃ y, P (j + 1) y ∧ x - y ∈ maximalIdeal B ^ (k + j) := by
    rintro j x ⟨h1, h2⟩
    obtain ⟨y, hy, hd⟩ := he j (E (j + 1)) ((hEe j).trans (hE (Nat.le_succ j))) x (hI (hEe j) h1)
    refine ⟨y, ⟨hy, fun h => h2 ?_⟩, hd⟩
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_add_right k j) hd) h
    rwa [sub_add_cancel] at this
  obtain ⟨x₀, h1, h2⟩ := SetLike.not_le_iff_exists.1 (hcon (E 0))
  let a : ∀ j, {x // P j x} := fun j => Nat.rec ⟨x₀, h1, h2⟩
    (fun j x => ⟨(step j x.1 x.2).choose, (step j x.1 x.2).choose_spec.1⟩) j
  have ha : ∀ j, (a j).1 - (a (j + 1)).1 ∈ maximalIdeal B ^ (k + j) := fun j =>
    (step j (a j).1 (a j).2).choose_spec.2
  have hchain : ∀ m n, m ≤ n → (a m).1 - (a n).1 ∈ maximalIdeal B ^ (k + m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.add_le_add_left hmn k) (ha n))
      rwa [sub_add_sub_cancel] at this
  have hsm : ∀ j : ℕ, (maximalIdeal B ^ j • ⊤ : Ideal B) = maximalIdeal B ^ j := fun j => by simp
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal B) (M := B) inferInstance
    (f := fun j => (a j).1) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      exact Ideal.pow_le_pow_right (Nat.le_add_left _ _) (hchain m n hmn))
  have hL' : ∀ j, (a j).1 - L ∈ maximalIdeal B ^ j := fun j => by
    have := SModEq.sub_mem.1 (hL j)
    simpa using this
  have hmem : ∀ N, L ∈ I N := by
    intro N
    by_cases hNt : I N = ⊤
    · simp [hNt]
    have hb : ⨅ i, maximalIdeal B ^ i • (⊤ : Submodule B (B ⧸ I N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top
    have : Ideal.Quotient.mk (I N) L ∈ (⊥ : Submodule B (B ⧸ I N)) := by
      rw [← hb]
      refine (Submodule.mem_iInf _).2 fun j => ?_
      have h3 : (a (max j N)).1 ∈ I N := hI ((le_max_right j N).trans (hEj _)) (a (max j N)).2.1
      have h4 := Ideal.pow_le_pow_right (le_max_left j N) (hL' (max j N))
      have h5 : Ideal.Quotient.mk (I N) L = ((a (max j N)).1 - L) • (-1 : B ⧸ I N) := by
        rw [Algebra.smul_def]
        have : Ideal.Quotient.mk (I N) (a (max j N)).1 = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h3
        simp [Ideal.Quotient.algebraMap_eq, this]
      rw [h5]
      exact Submodule.smul_mem_smul h4 trivial
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hz : L = 0 := by
    have : L ∈ ⨅ N, I N := (Submodule.mem_iInf _).2 hmem
    rwa [h0] at this
  have := hL' k
  rw [hz, sub_zero] at this
  have h6 := (a k).2.2
  exact h6 this

end Cofinal

section Der

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]

private theorem kill (A : Subalgebra O R) (ξ : A →ₐ[O] K) (D : A →ₗ[O] K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (s : Set R)
    (h : ∀ x ∈ s, ∃ hx : x ∈ A, D ⟨x, hx⟩ = 0) {x : R} (hx : x ∈ Algebra.adjoin O s) :
    ∃ h : x ∈ A, D ⟨x, h⟩ = 0 := by
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination (-1 : K) * this
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap a =>
    refine ⟨A.algebraMap_mem a, ?_⟩
    have : (⟨algebraMap O R a, A.algebraMap_mem a⟩ : A) = a • (1 : A) := by
      ext
      simp [Algebra.smul_def]
    rw [this, map_smul, h1, smul_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have : (⟨x + y, add_mem a b⟩ : A) = ⟨x, a⟩ + ⟨y, b⟩ := rfl
    rw [this, map_add (f := _), ha, hb, add_zero]
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨mul_mem a b, ?_⟩
    have : (⟨x * y, mul_mem a b⟩ : A) = ⟨x, a⟩ * ⟨y, b⟩ := rfl
    rw [this, hD, ha, hb, mul_zero, mul_zero, add_zero]

end Der

section Close

variable {O R K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [NormedField K] [Algebra O K]

private theorem close_zero (B : Subalgebra O R) [hB : IsCO O B]
    (hm : maximalIdeal B = (maximalIdeal R).comap (B.val : B →+* R)) (E : B →ₗ[O] K)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a ∈ maximalIdeal B ^ k, ‖E a‖ ≤ ε) (T : Set B) (hT : ∀ t ∈ T, E t = 0)
    (hd : ∀ x : B, ∀ N : ℕ, ∃ t ∈ T, ((x - t : B) : R) ∈ maximalIdeal R ^ N) : E = 0 := by
  let I : ℕ → Ideal B := fun N => (maximalIdeal R ^ N).comap (B.val : B →+* R)
  have hI : Antitone I := fun a b h => Ideal.comap_mono (Ideal.pow_le_pow_right h)
  have h0 : ⨅ N, I N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : (x : R) ∈ ⨅ N : ℕ, maximalIdeal R ^ N := (Submodule.mem_iInf _).2 fun N =>
      (Submodule.mem_iInf _).1 hx N
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Ideal.mem_bot] at h1
    exact Subtype.ext h1
  ext x
  by_contra hne
  have hpos : 0 < ‖E x‖ / 2 := half_pos (norm_pos_iff.2 hne)
  obtain ⟨k, hk⟩ := hc _ hpos
  obtain ⟨N, hN⟩ := cofinal I hI h0 k
  obtain ⟨t, ht, hd'⟩ := hd x N
  have h2 := hk (x - t) (hN hd')
  rw [map_sub, hT t ht, sub_zero] at h2
  linarith

end Close

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.derExt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, ∀ D ∈ PtDer ξ (Qbar l), (∀ g i j, D (S.u.r g i j) = 0) → (∀ v i g, D (S.u.ψ v i g : S.A) = 0) → D = 0 := by
  intro l _ c _ F C₀ n hF hn S ξ D hD hr hψ
  obtain ⟨hco, hm⟩ := Fr.co_B hF hn S
  haveI := hco
  have hD' : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f := hD

  have hs : ∀ x ∈ ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)} : Set S.R),
      ∃ hx : x ∈ S.A, D ⟨x, hx⟩ = 0 := by
    rintro x (⟨g, i, j, rfl⟩ | ⟨v, i, g, rfl⟩)
    · exact ⟨S.r_mem g i j, hr g i j⟩
    · exact ⟨S.B_le_A (S.ψ_mem v i g), hψ v i g⟩
  have hadj : Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤
      Algebra.adjoin c.O ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | hx)
    · refine Subalgebra.list_prod_mem _ fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact Algebra.subset_adjoin (Or.inl ⟨_, _, _, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr hx)

  have hB : D ∘ₗ S.inc.toLinearMap = 0 := by
    refine close_zero S.B (hm.trans rfl) _ (fun ε hε => ?_)
      {t | (t : S.R) ∈ Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})} (fun t ht => ?_)
      (fun x N => ?_)
    · have hDB : D ∘ₗ S.inc.toLinearMap ∈ PtDer (ξ.comp S.inc) (Qbar l) := fun f g => by
        simpa using hD (S.inc f) (S.inc g)
      obtain ⟨k, hk⟩ := derCont l c S.B (ξ.comp S.inc) _ hDB ε hε
      exact ⟨k, fun a ha => (hk a ha).1⟩
    · obtain ⟨_, h⟩ := kill S.A ξ D hD' _ hs (hadj ht)
      exact h
    · obtain ⟨y, hy, h⟩ := x.2 N
      exact ⟨⟨y, Fr.le_adicClosure _ hy⟩, hy, h⟩

  ext ⟨x, hx⟩
  obtain ⟨_, h⟩ := kill S.A ξ D hD' ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) (by
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact ⟨S.B_le_A hx, LinearMap.congr_fun hB ⟨x, hx⟩⟩
    · exact ⟨S.r_mem g i j, hr g i j⟩) hx
  exact h
end

