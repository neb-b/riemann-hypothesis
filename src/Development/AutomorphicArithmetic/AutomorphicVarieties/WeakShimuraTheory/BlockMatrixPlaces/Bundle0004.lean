module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Compat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

open CategoryTheory in
private theorem seq_ex (S : ℕ → Type) (hf : ∀ n, Finite (S n)) (hn : ∀ n, Nonempty (S n)) (t : ∀ n, S (n + 1) → S n) :
    ∃ u : ∀ n, S n, ∀ n, t n (u (n + 1)) = u n :=
  _root_.UpperTheory.Reformulated.B.Qj7.seq_ex S hf hn t

theorem UpperTheory.V.Ws.Bl.compat :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), (∀ n, Finite (T ⧸ lev A T n)) → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z) →
          ∃ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) ∧ (∀ n g, redn A T n (z (n + 1) g) = z n g) ∧ (∀ n, redn A T n (y (n + 1)) = y n) ∧ Prim (z 1) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hT hZ hP
  let S : ℕ → Type := fun n =>
    {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) // IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}
  let t : ∀ n, S (n + 1) → S n := fun n p =>
    ⟨(fun g => redn A T n (p.1.1 g), redn A T n p.1.2),
      (redMem A T Γ ρ c N H P n _ _ p.2.1).1,
      (redMem A T Γ ρ c N H P n _ _ p.2.1).2.1 (p.2.2 n.succ_pos)⟩
  have hf : ∀ n, Finite (S n) := fun n => by
    have := hT n
    have h : ((Zn ρ c N H P n) ×ˢ (Set.univ : Set (T ⧸ lev A T n))).Finite := (hZ n).prod Set.finite_univ
    have h' : {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) |
        IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}.Finite :=
      h.subset (by
        intro p hp
        exact ⟨⟨p.2, hp.1⟩, trivial⟩)
    exact h'.to_subtype
  have hn : ∀ n, Nonempty (S n) := fun n => by
    obtain ⟨z, ⟨y, hz⟩, hp⟩ := hP (n + 1) n.succ_pos
    exact ⟨t n ⟨(z, y), hz, fun _ => hp⟩⟩
  obtain ⟨u, hu⟩ := seq_ex S hf hn t
  exact ⟨fun n => (u n).1.1, fun n => (u n).1.2, fun n => (u n).2.1,
    fun n g => congrArg (fun p : S n => p.1.1 g) (hu n),
    fun n => congrArg (fun p : S n => p.1.2) (hu n), (u 1).2.2 Nat.one_pos⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GammaOneGammaZeroHomogeneousCocyclesFinite
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]

private theorem coc_one {ρ : Representation R Γ M} {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) : z 1 = 0 := by
  have h := hz 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ z g = 0}
  one_mem' := ⟨map_one ρ, coc_one hz⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hz, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hz a a⁻¹
    rw [mul_inv_cancel, coc_one hz, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) :
    (killSub ρ hz).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hz h h⁻¹
    rw [mul_inv_cancel, coc_one hz] at e
    rw [hz, hz, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

variable [TopologicalSpace Γ]

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m) {z : Γ → M}
    (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (hl : IsLocallyConstant z) : IsClosed (killSub ρ hz : Set Γ) := by
  have e : (killSub ρ hz : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | z g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun m => (hρ m).isClosed_fiber m) (hl.isClosed_fiber 0)

private theorem module_finite_z1_padicInt [TopologicalSpace M] [DiscreteTopology M] [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] :
    Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Bl.zcFin :
    GlobalFiniteness → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → ∀ P : Set M, (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) P).Finite := by
  intro hGF Ω _ _ _ l _ S c s B hP R M _ _ _ _ ρ r hr hρ K hK hI P
  obtain ⟨S', -, -, hS, -, -, -, hN⟩ := UpperTheory.V.Ws.Bl.placeSet S B hP.prime hP.mem hP.ovl
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hr' : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  obtain ⟨inst⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  have h0 : ∀ g h : G ℚ Ω, (0 : G ℚ Ω → M) (g * h) = (0 : G ℚ Ω → M) g + ρ g ((0 : G ℚ Ω → M) h) := by simp
  have hker : NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ killSub ρ h0 :=
    hN _ (killSub_normal ρ h0) (killSub_closed ρ hρ h0 (IsLocallyConstant.const 0)) fun A hA g hg => ⟨hK (hI A hA hg), rfl⟩
  let ρ' : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by rw [map_mul]; rfl }
  let ρS : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ' fun g hg => LinearMap.ext fun m => show ρ g m = m by rw [(hker hg).1]; rfl
  have hρS : ContAction ρS := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact (hρ m).continuous
  obtain ⟨-, f1, -⟩ := hGF ℚ Ω l (r + 1) M S' ρS r.succ_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun z : Z1 ρS => z.1 ∘ toGS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))).subset ?_
  rintro z ⟨y, hz⟩
  have hle : NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ killSub ρ hz.coc :=
    hN _ (killSub_normal ρ _) (killSub_closed ρ hρ _ hz.lc) fun A hA g hg =>
      ⟨hK (hI A hA hg), hz.kill g ⟨hI A hA hg, A, hA l hP.mem, hg⟩⟩
  let zS : GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) → M := Quotient.lift z fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hz.coc a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨zS, hz.lc.continuous.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hz.coc a b
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PrimEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.primEx :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, n ≤ Nat.card (Zn ρ c N H P n)) → ∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn
  by_contra hne
  push_neg at hne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z := by
    intro k
    induction k with
    | zero => exact hne
    | succ k ih =>
      intro z hz hpz
      obtain ⟨y, hy⟩ := hz
      have hr := redMem A T Γ ρ c N H P (n + k) z y hy
      exact ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))
  have hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k)) := by
    intro k
    haveI := (hfin (n + k)).to_subtype
    have key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k),
        ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g := by
      intro z
      obtain ⟨z', hz', h⟩ := divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)
      exact ⟨⟨z', hz'⟩, h⟩
    choose f hf using key
    refine Nat.card_le_card_of_injective f ?_
    intro z1 z2 h12
    apply Subtype.ext
    funext g
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)
    rw [← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]
  have hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hB k).trans ih
  have h1 := hcard (n + (Nat.card (Zn ρ c N H P n) + 1))
  have h2 := hC (Nat.card (Zn ρ c N H P n) + 1)
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.ResEntry
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem res_entry {R : Type} [CommRing R] [IsLocalRing R] {X X' : M4 R} (hX : Sep X) (h : X' * X = 1) (Y : M4 R)
    (i j : Fin 4) : residue R (X' j j) * residue R (X j j) = 1 ∧
      residue R ((X * Y * X' - Y) i j) = residue R ((X i i - X j j) * X' j j) * residue R (Y i j) := by
  have hoff : ∀ a b, a ≠ b → residue R (X a b) = 0 :=
    fun a b hab => (residue_eq_zero_iff _).2 (hX.off a b hab)
  have kr : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (B a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a b) * residue R (B b b) := by
    intro A B hB a b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single b]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hB c b hc, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have kl : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (A a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a a) * residue R (B a b) := by
    intro A B hA a b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single a]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hA a c (Ne.symm hc), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hdiag : ∀ j, residue R (X' j j) * residue R (X j j) = 1 := by
    intro j
    rw [← kr X' X hoff j j, h, Matrix.one_apply_eq, map_one]
  have hoff' : ∀ a b, a ≠ b → residue R (X' a b) = 0 := by
    intro a b hab
    have h0 : residue R (X' a b) * residue R (X b b) = 0 := by
      rw [← kr X' X hoff a b, h, Matrix.one_apply_ne hab, map_zero]
    linear_combination residue R (X' b b) * h0 - residue R (X' a b) * hdiag b
  refine ⟨hdiag j, ?_⟩
  rw [Matrix.sub_apply, map_sub, kr _ _ hoff' i j, kl _ _ hoff i j, map_mul, map_sub]
  linear_combination residue R (Y i j) * hdiag j

theorem UpperTheory.V.Ws.Bl.adBij :
    ∀ (R Γ : Type) [CommRing R] [IsLocalRing R] [Group Γ] (r : Γ →* M4 R) (h : BG r) (s : Γ), Sep (r s) → Function.Bijective fun Y => adU h s Y - Y := by
  intro R Γ _ _ _ r h s hs
  obtain ⟨hfin, -, hmem⟩ := uMFacts R
  haveI := hfin
  let φ : uM R →ₗ[R] uM R := adU h s - LinearMap.id
  have hinv : r s⁻¹ * r s = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hkey : ∀ Y : uM R, φ Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) →
      Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) := by
    intro Y hY
    rw [hmem] at hY ⊢
    intro i j
    by_cases hij : lamW i < lamW j
    · have h1 := hY i j
      have e := res_entry hs hinv (Y : M4 R) i j
      have hu : IsUnit (r s i i - r s j j) := hs.unit i j (ne_of_lt hij)
      have hc : (↑(φ Y) : M4 R) i j = (r s * ↑Y * r s⁻¹ - ↑Y) i j := rfl
      rw [hc, ← residue_eq_zero_iff, e.2, map_mul] at h1
      rw [← residue_eq_zero_iff]
      have hu' : residue R (r s i i - r s j j) ≠ 0 := (hu.map (residue R)).ne_zero
      have hv : residue R (r s⁻¹ j j) ≠ 0 := left_ne_zero_of_mul_eq_one e.1
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hu' hv)
    · have hY2 := (Submodule.mem_inf.1 Y.2).1
      rw [hY2 i j hij]
      exact zero_mem _
  have hS : (maximalIdeal R • ⊤ : Submodule R (uM R)) ≤
      (maximalIdeal R • ⊤ : Submodule R (uM R)).comap φ := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  let ψ := Submodule.mapQ _ _ φ hS
  have hψinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkey Y hq
  letI : Module (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  letI : IsScalarTower R (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  haveI : Module.Finite (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hsurjA : Function.Surjective (algebraMap R (ResidueField R)) := Ideal.Quotient.mk_surjective
  let ψk := LinearMap.extendScalarsOfSurjective hsurjA ψ
  have hψsurj : Function.Surjective ψ := (LinearMap.injective_iff_surjective (f := ψk)).1 hψinj
  have hrange : LinearMap.range φ = ⊤ := by
    rw [← IsLocalRing.map_mkQ_eq_top, ← LinearMap.range_comp, eq_top_iff]
    intro q _
    obtain ⟨q', rfl⟩ := hψsurj q
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q'
    exact ⟨Y, rfl⟩
  have hsurj : Function.Surjective φ := LinearMap.range_eq_top.1 hrange
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism φ hsurj, hsurj⟩
end

