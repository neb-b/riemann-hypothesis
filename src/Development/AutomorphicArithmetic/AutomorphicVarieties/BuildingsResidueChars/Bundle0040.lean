module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0004
public import Mathlib.GroupTheory.Perm.Fin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityOfArtinCongruence
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.card_padicAlgCl_eq_continuum (p : ℕ) [Fact p.Prime] :
    Cardinal.mk (PadicAlgCl p) = Cardinal.continuum := by
  have hle : Cardinal.mk ℚ_[p] ≤ Cardinal.continuum := by
    have h1 : Cardinal.mk ℚ_[p] ≤ Cardinal.mk (CauSeq ℚ (padicNorm p)) := Cardinal.mk_quotient_le
    have h2 : Cardinal.mk (CauSeq ℚ (padicNorm p)) ≤ Cardinal.mk (ℕ → ℚ) := Cardinal.mk_subtype_le _
    refine h1.trans (h2.trans ?_)
    rw [Cardinal.mk_arrow, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat]
    simp
  have hge : Cardinal.continuum ≤ Cardinal.mk ℚ_[p] := by
    obtain ⟨f, -, -, hf⟩ :=
      Perfect.exists_nat_bool_injection (PerfectSpace.univ_perfect (α := ℚ_[p])) Set.univ_nonempty
    have := Cardinal.mk_le_of_injective hf
    simpa using this
  apply le_antisymm
  · have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    refine this.trans ?_
    exact max_le hle Cardinal.aleph0_le_continuum
  · exact hge.trans (Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective)

private theorem UpperTheory.nonempty_qbar_ringEquiv_complex (p : ℕ) [Fact p.Prime] : Nonempty (Qbar p ≃+* ℂ) := by
  have hc := UpperTheory.card_padicAlgCl_eq_continuum p
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (PadicAlgCl p)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hQ : Cardinal.mk ℚ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hQ
    (by rw [hc]; exact Cardinal.aleph0_lt_continuum)
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hQ
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hc, Cardinal.mk_complex]
  obtain ⟨e⟩ := Cardinal.eq.mp hst
  exact ⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht⟩

private theorem UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots {F K : Type} [Field F] [Field K] [Algebra F K] (g : K ≃ₐ[F] K) :
    ∀ d : ℕ, d ≠ 0 → (∀ p b : ℕ, p.Prime → p ^ b ∣ d → ∀ ζ : K, ζ ^ (p ^ b) = 1 → g ζ = ζ) →
    ∀ ζ : K, ζ ^ d = 1 → g ζ = ζ := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ H ζ hζ
    exact H p n hp dvd_rfl ζ hζ
  | zero =>
    intro h
    exact absurd rfl h
  | one =>
    intro _ _ ζ hζ
    rw [pow_one] at hζ
    rw [hζ, map_one]
  | coprime a b ha hb hab iha ihb =>
    intro hd H ζ hζ
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hA : g (ζ ^ b) = ζ ^ b :=
      iha ha0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro _ rfl))) _
        (by rw [← pow_mul, mul_comm, hζ])
    have hB : g (ζ ^ a) = ζ ^ a :=
      ihb hb0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro_left _ rfl))) _
        (by rw [← pow_mul, hζ])
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero ha0 hb0)] at hζ
      exact zero_ne_one hζ
    have hbez : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
      have := Nat.gcd_eq_gcd_ab a b
      rw [Nat.Coprime.gcd_eq_one hab] at this
      exact_mod_cast this
    have e : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b := by
      rw [← zpow_natCast ζ a, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hbez,
        zpow_one]
    rw [e, map_mul, map_zpow₀, map_zpow₀, hA, hB]

theorem UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ M : ℕ, 1 ≤ M → ∀ σ : Weil h,
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    (σ : G F Ω) ∈ Ine (F := F) A ∧ ∀ ζ : Ω, ζ ^ M = 1 → (σ : G F Ω) ζ = ζ := by
  intro hGAR F Ω _ _ _ _ _ w A h a ha M hM σ hv hvM
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion F) (a σ) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.mpr hv
  have hdeg : deg σ = 0 := by
    have := ha.ord_eq σ
    rw [hord] at this
    omega
  refine ⟨deg_eq_zero_iff.mp hdeg, ?_⟩
  have hnat : ∀ n : ℕ, valuation (w.adicCompletion F) (n : w.adicCompletion F) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (Valuation.map_add _ _ _).trans (max_le ih (by rw [map_one]))
  apply UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots (σ : G F Ω) M (by omega)
  intro p b hp hpb ζ hζ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι⟩ := UpperTheory.nonempty_qbar_ringEquiv_complex p
  have hle : valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤
      valuation (w.adicCompletion F) ((p ^ b : ℕ) : w.adicCompletion F) := by
    obtain ⟨c, hc⟩ := hpb
    refine hvM.trans ?_
    rw [hc, Nat.cast_mul, map_mul]
    exact mul_le_of_le_one_right' (hnat c)
  have h82 := UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le F w p ι (p ^ b) (a σ) hle
  have h78 := UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit hGAR F Ω w A h a ha p ι σ hv
  rw [← h78] at h82
  exact UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one F Ω p b (σ : G F Ω) h82 ζ hζ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalOrbitRepresentatives
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

theorem UpperTheory.minimal_orbit_representatives :
    UpperTheory.V.Af.BA.MinOrb := by
  intro L _ _ _ N p
  classical
  obtain ⟨S, -, hS⟩ := hnf L N (I0 L N)
  refine ⟨⋃ B ∈ {B | B ∈ S ∧ B.det ≠ 0}, Set.pi Set.univ (fun _ => (nearVec B).powerset), ?_, ?_⟩
  · refine Set.Finite.biUnion ?_ ?_
    · exact S.finite_toSet.subset (fun B hB => hB.1)
    · intro B hB
      exact Set.Finite.pi (fun _ => (nearvec L N B hB.2).1.powerset)
  · intro h hR hsp
    obtain ⟨A, hA, hcol⟩ := exbasis L N _ hsp
    have hcm : ∀ j, ColsMin A (h j) := fun j a => hcol a j
    obtain ⟨g, hg⟩ := hS A hA (nrmle L N (h 0) A (hR 0) (hcm 0) hA).1
    have hdet : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA
    refine ⟨g, ?_⟩
    rw [Set.mem_iUnion₂]
    refine ⟨(g : Matrix (Fin N) (Fin N) (𝓞 L)) * A, ⟨hg, hdet⟩, ?_⟩
    intro j _
    rintro y ⟨x, hx, rfl⟩
    refine ⟨g • h j, smul_mem_Ry g (hR j), fun a => ?_, ?_⟩
    · have hc : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) = g • (fun i => A i a) := by
        funext i
        rfl
      rw [hc, q_smul, inv_smul_smul]
      exact hcm j a
    · rw [q_smul]
      change q (h j) (g⁻¹ • g • x) = 1
      rw [inv_smul_smul]
      exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalVectorStabilizerProperty
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

theorem UpperTheory.minimal_vector_stabilizer_property :
    UpperTheory.V.Af.BA.MinStab := by
  intro L _ _ _ N h hv hsp
  classical
  have hfin : (minVec h).Finite := by
    obtain ⟨S, hS, hev⟩ := locfin L N h (rypos L N hv) 1
    refine hS.subset fun y hy => ?_
    by_contra hn
    exact (hev.self_of_nhds y hn).ne' hy
  obtain ⟨A, hA, hcol⟩ := exbasis L N _ hsp
  haveI : Finite (minVec h) := hfin.to_subtype
  have hmem : ∀ (g : MulAction.stabilizer (Gm L N) (minVec h)) (a : Fin N),
      (g.1 • (fun i => A i a : Lat L N)) ∈ minVec h := fun g a => by
    have h1 : g.1 • minVec h = minVec h := g.2
    have h2 := Set.smul_mem_smul_set (a := g.1) (hcol a)
    rw [h1] at h2
    exact h2
  refine Finite.of_injective
    (fun (g : MulAction.stabilizer (Gm L N) (minVec h)) (a : Fin N) =>
      (⟨_, hmem g a⟩ : minVec h)) fun g k e => ?_
  have h1 : (g.1 : Matrix (Fin N) (Fin N) (𝓞 L)) * A =
      (k.1 : Matrix (Fin N) (Fin N) (𝓞 L)) * A := by
    refine Matrix.ext fun i a => ?_
    exact congrFun (congrArg Subtype.val (congrFun e a)) i
  have h2 := congrArg (· * A.adjugate) h1
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
  refine Subtype.ext (Units.ext ?_)
  refine Matrix.ext fun i j => ?_
  exact mul_left_cancel₀ hA (congrFun (congrFun h2 i) j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbReOfMinimalVectorStabilizer
section
open NumberField Pointwise UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA

private theorem minVec_smul' {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gm L N) (h : HS L N) :
    minVec (g • h) = g • minVec h := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp [minVec, q_smul]

private theorem vert_ext' {L : Type} [Field L] [NumberField L] {N : ℕ} (a b : ↥(HR L N))
    (ha : ConeExtensionAcyclic.IsVert (qr L N) a) (e : minVec a.1 = minVec b.1) : a = b := by
  have : a - b = 0 := ha.2 _ fun y hy => by
    have h1 : y.1 ∈ minVec a.1 := hy
    rw [e] at h1
    have h2 : qr L N y b = 1 := h1
    rw [map_sub, hy, h2, sub_self]
  exact sub_eq_zero.1 this

theorem UpperTheory.orbRe_of_minimal_vector_stabilizer :
    UpperTheory.V.Af.BA.FixOrb → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.ActRe → UpperTheory.V.Af.BA.SpanRe → UpperTheory.V.Af.BA.MinOrb → UpperTheory.V.Af.BA.MinStab → UpperTheory.V.Af.BA.OrbRe := by
  intro hFix hInv hAct hSpan hOrb hStab L _ _ _ N σ hσ p
  obtain ⟨hinv, hre⟩ := hInv L N σ hσ
  obtain ⟨inst, hval, -⟩ := hAct L N σ hσ
  have hRy : ∀ v : ConeExtensionAcyclic.Vert (qr L N), v.1.1 ∈ Ry L N := fun v y hy => v.2.1 ⟨y, hy⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := hOrb L N p
  obtain ⟨R₀, hR₀, hR₀'⟩ := hFix (Gm L N) (Fin (p + 1) → Set (Lat L N)) (sGm N σ)
    (fun z j => sLat σ '' z j)
    (fun g z => by
      funext j
      change sLat σ '' ((fun y => g • y) '' z j) = (fun y => sGm N σ g • y) '' (sLat σ '' z j)
      simp only [Set.image_image, sLat_smul])
    {z | ∃ t ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) (p + 1), z = fun j => minVec (t j).1.1}
    (by
      rintro _ ⟨t, -, rfl⟩
      funext j
      ext y
      have hq := (hre _ (t j).1.2).1
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hq x).trans hx
      · intro hy
        exact ⟨sLat σ y, (hq y).trans hy, funext fun a => hinv _⟩)
    (by
      rintro _ ⟨t, ht, rfl⟩
      have hs : Spans (minVec (t 0).1.1) := by
        have := hSpan L N σ hσ p t ht
        unfold Spans spanL at *
        refine top_le_iff.1 (this ▸ Submodule.span_mono (Set.image_mono fun y hy => hy 0))
      haveI := hStab L N _ (hRy (t 0)) hs
      have hle : MulAction.stabilizer (Gm L N) (fun j => minVec (t j).1.1) ≤
          MulAction.stabilizer (Gm L N) (minVec (t 0).1.1) := fun g hg => congrFun hg 0
      exact Finite.of_injective _ (Subgroup.inclusion_injective hle))
    ⟨R₁, hR₁, by
      rintro _ ⟨t, ht, rfl⟩
      exact hR₁' (fun j => (t j).1.1) (fun j => hRy _) (hSpan L N σ hσ p t ht)⟩
  refine ⟨{h | (∀ j, ∃ v : ConeExtensionAcyclic.Vert (qr L N), v.1.1 = h j) ∧ (fun j => minVec (h j)) ∈ R₀}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun h j => minVec (h j)) (hR₀.subset ?_) ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact hh.2
    · intro a ha b hb e
      funext j
      obtain ⟨v, hv⟩ := ha.1 j
      obtain ⟨w, hw⟩ := hb.1 j
      have ej : minVec (a j) = minVec (b j) := congrFun e j
      rw [← hv, ← hw] at ej ⊢
      rw [vert_ext' _ _ v.2 ej]
  · intro t ht
    obtain ⟨g, hg, hgR⟩ := hR₀' _ ⟨t, ht, rfl⟩
    refine ⟨g, hg, fun j => ⟨(⟨g, hg⟩ : ↥(Fix N σ)) • t j, hval _ _⟩, ?_⟩
    simp only [minVec_smul']
    exact hgR
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermSplitFinSucc
section
private theorem cycle_range_conjugate_succAbove {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      (j.succAbove k) = i.succAbove (τ k) := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_succAbove,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

private theorem cycle_range_conjugate_pivot {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      j = i := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_self,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

theorem UpperTheory.perm_split_fin_succ :
    UpperTheory.V.Af.BA.PermSplit := by
  intro n j
  classical
  let F : Fin (n + 1) × Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) := fun p =>
    (Fin.cycleRange p.1)⁻¹ * Equiv.Perm.decomposeFin.symm (0, p.2) * Fin.cycleRange j
  have hinj : Function.Injective F := by
    rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have hi : i = i' := by
      have h1 := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j) h
      simp only [F] at h1
      rw [cycle_range_conjugate_pivot, cycle_range_conjugate_pivot] at h1
      exact h1
    subst hi
    simp only [F] at h
    have h2 := Equiv.injective _ (mul_left_cancel (mul_right_cancel h))
    rw [Prod.mk.injEq] at h2
    rw [h2.2]
  have hsurj : Function.Surjective F := by
    intro σ
    have hρ : (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹) 0 = 0 := by
      simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_symm_zero, Fin.cycleRange_self]
    obtain ⟨⟨p, τ⟩, hp⟩ := Equiv.Perm.decomposeFin.symm.surjective
      (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹)
    have hp0 : p = 0 := by
      have h0 := congrArg (fun s : Equiv.Perm (Fin (n + 1)) => s 0) hp
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [h0, hρ]
    subst hp0
    refine ⟨(σ j, τ), ?_⟩
    simp only [F]
    rw [hp]
    group
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  intro i τ
  refine ⟨?_, fun k => cycle_range_conjugate_succAbove i j τ k⟩
  show ((Equiv.Perm.sign (F (i, τ)) : ℤ) : _) = _
  simp only [F, map_mul, map_inv, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, inv_pow, Int.units_inv_eq_self]
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermutationModuleHomologyRank
section
open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.permutation_module_homology_rank :
    UpperTheory.V.Af.BA.RankHomPerm := by
  intro Γ X _ _ h
  obtain ⟨R, hR, hRx⟩ := h
  haveI := hR.fintype
  refine ⟨Fintype.card R, fun A => ?_⟩
  let Φ : (PC Γ X ⟶ A) →ₗ[ℂ] (R → A) :=
    { toFun := fun φ r => φ.hom (Finsupp.single (r : X) 1)
      map_add' := fun φ ψ => by
        ext r
        rfl
      map_smul' := fun c φ => by
        ext r
        rfl }
  have key : ∀ (χ : PC Γ X ⟶ A) (g : Γ) (x : X),
      χ.hom (Finsupp.single x 1) = A.ρ g⁻¹ (χ.hom (Finsupp.single (g • x) 1)) := by
    intro χ g x
    rw [← Rep.hom_comm_apply]
    congr 1
    show _ = permC Γ X g⁻¹ (Finsupp.single (g • x) 1)
    rw [permC_single, inv_smul_smul]
  have hinj : Function.Injective Φ := by
    intro φ ψ hφψ
    apply PC_ext
    intro x
    obtain ⟨g, hg⟩ := hRx x
    have h1 := congrFun hφψ ⟨g • x, hg⟩
    rw [key φ g x, key ψ g x]
    exact congrArg _ h1
  calc Module.rank ℂ (PC Γ X ⟶ A) ≤ Module.rank ℂ (R → A) := Φ.rank_le_of_injective hinj
    _ = _ := by rw [rank_fun_eq_lift_mul, Cardinal.lift_id]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ProjPermOfLiftEquiv
section
open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.projPerm_of_liftEquiv :
    UpperTheory.V.Af.BA.LiftEquiv → UpperTheory.V.Af.BA.ProjPerm := by
  intro h Γ X _ _ hfin
  refine CategoryTheory.Projective.mk ?_
  intro E Y f e he
  have hs := (Rep.epi_iff_surjective e).1 he
  have heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) =
      (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1)) := by
    intro g x
    have hc := LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)
    simpa [UpperTheory.V.Af.BA.permC_single] using hc
  obtain ⟨ψ, hψ, hψe⟩ := h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq
  refine ⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ)
    ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩
  · intro g
    apply Finsupp.lhom_ext
    intro x c
    simp [UpperTheory.V.Af.BA.permC_single, hψ]
  · apply UpperTheory.V.Af.BA.PC_ext
    intro x
    simp [Rep.hom_comp, Rep.hom_ofHom, hψe]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticComplexMultiplication
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.quadratic_complex_multiplication :
    UpperTheory.V.Af.Cr.QuadCM := by
  intro F Ω _ _ _ _ _ _ d δ hδ hd
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (X ^ 2 - C d : F[X]).Monic := monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := natDegree_le_natDegree h1
    rwa [natDegree_X_pow_sub_C _] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let v : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h3 := hd ((InfinitePlace.embedding_of_isReal hv).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  haveI : IsAlgClosure K Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := F) K }
  refine ⟨K, inferInstance, inferInstance, IsCMField.ofCMExtension F K, inferInstance, inferInstance,
    inferInstance, inferInstance, hrk, y, hy, fun x => ?_⟩
  obtain ⟨f, hf, hx⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval x
  rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hx, IntermediateField.adjoin.powerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega)]
  simp only [map_add (f := _), map_mul, aeval_C, aeval_X]
  exact add_comm _ _
end

