module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CcOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ccEx :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ c : InfinitePlace F → G F Ω, ∀ w, w.IsReal → IsCCAt w (c w) := by
  intro F Ω _ _ _ _ _
  classical
  have key : ∀ w : InfinitePlace F, w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
    intro w hw
    have hφ : ∀ a, (starRingEnd ℂ) (w.embedding a) = w.embedding a := by
      intro a
      have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
      exact RingHom.congr_fun h a
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let e : Ω ≃ₐ[F] algebraicClosure F ℂ := IsAlgClosure.equiv F Ω (algebraicClosure F ℂ)
    let κ : ℂ →ₐ[F] ℂ :=
      { (starRingEnd ℂ) with commutes' := fun a => hφ a }
    let j : Ω →ₐ[F] ℂ := (algebraicClosure F ℂ).val.comp e.toAlgHom
    have hmem : ∀ x : Ω, (κ.comp j) x ∈ (algebraicClosure F ℂ).toSubalgebra := by
      intro x
      show (κ.comp j) x ∈ algebraicClosure F ℂ
      rw [map_mem_algebraicClosure_iff, mem_algebraicClosure_iff]
      exact Algebra.IsAlgebraic.isAlgebraic x
    let f : Ω →ₐ[F] algebraicClosure F ℂ := (κ.comp j).codRestrict _ hmem
    let c0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f
    let c : G F Ω := AlgEquiv.ofBijective c0 (Algebra.IsAlgebraic.algHom_bijective c0)
    refine ⟨c, j.toRingHom, fun x => ?_, ?_⟩
    · show ((e (e.symm (f x)) : algebraicClosure F ℂ) : ℂ) = (starRingEnd ℂ) (j x)
      rw [AlgEquiv.apply_symm_apply]
      rfl
    · have hj : j.toRingHom.comp (algebraMap F Ω) = w.embedding := by
        ext a
        exact j.commutes a
      rw [hj, InfinitePlace.mk_embedding]
  refine ⟨fun w => if hw : w.IsReal then (key w hw).choose else 1, fun w hw => ?_⟩
  simp only [dif_pos hw]
  exact (key w hw).choose_spec
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CharRep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.locNe :
    LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) → ∃ f ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), f ≠ 0 := by
  intro _ hE F Ω _ _ _ _ _ l _ A v hA hl _
  set ρ := Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) with hρ
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    show Continuous fun p : (Dec (F := F) A) × ZMod (l ^ 1) => (ρ p.1) p.2
    simpa [hρ] using continuous_snd
  have hE' := (hE F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hcont).2 hl
  have h0 : Nat.card ↥(ReciprocityTheory.Gal.H0 ρ) = l := by
    have htop : ReciprocityTheory.Gal.H0 ρ = ⊤ := by
      ext x
      simp [ReciprocityTheory.Gal.H0, hρ]
    rw [htop, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_zmod, pow_one]
  by_contra hne
  push_neg at hne
  haveI hz : Subsingleton ↥(ReciprocityTheory.Gal.Z1 ρ) :=
    ⟨fun a b => Subtype.ext ((hne a a.2).trans (hne b b.2).symm)⟩
  haveI hs : Subsingleton (ReciprocityTheory.Gal.H1 ρ) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  have h1 : Nat.card (ReciprocityTheory.Gal.H1 ρ) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨0⟩⟩
  rw [h1, h0] at hE'
  exact (Fact.out : l.Prime).one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hE'.symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CocConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cocConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ∀ c ∈ Z1 ρ, ∀ (v : HeightOneSpectrum (𝓞 F)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v →
      ((∃ m, ∀ g ∈ Dec (F := F) A, c g = ρ g m - m) → ∃ m, ∀ g ∈ Dec (F := F) A', c g = ρ g m - m) ∧
      ((∀ g ∈ Ine (F := F) A, ρ g = 1 ∧ c g = 0) → ∀ g ∈ Ine (F := F) A', c g = 0) := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ c hc v A A' hA hA'
  obtain ⟨-, hco⟩ := hc
  obtain ⟨s, hs⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  have h1 : c 1 = 0 := by simpa using hco 1 1
  have hinv : ρ s (c s⁻¹) = - c s := by
    have h := hco s s⁻¹
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hconj : ∀ g ∈ Dec (F := F) A', s⁻¹ * g * s ∈ Dec (F := F) A := by
    intro g hg
    rw [mem_Dec] at hg ⊢
    open scoped Pointwise in
    rw [mul_smul, mul_smul, hs, hg, ← hs, inv_smul_smul]
  refine ⟨?_, ?_⟩
  · rintro ⟨m, hm⟩
    refine ⟨ρ s m - c s, fun g hg => ?_⟩
    have hg' := hconj g hg
    have e2 : c (g * s) = c s + ρ s (c (s⁻¹ * g * s)) := by
      rw [← hco]
      congr 1
      group
    have e3 : c g = c (g * s) + ρ (g * s) (c s⁻¹) := by
      rw [← hco]
      congr 1
      group
    have e4 : ρ s (ρ (s⁻¹ * g * s) m) = ρ g (ρ s m) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e3, e2, map_mul ρ g s, Module.End.mul_apply, hinv, hm _ hg']
    simp only [map_sub, map_neg]
    rw [e4]
    abel
  · intro hI g hg
    rw [← hs] at hg
    obtain ⟨hρ, hc0⟩ := hI _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg)
    have e2 : c (g * s) = c s + ρ s (c (s⁻¹ * g * s)) := by
      rw [← hco]
      congr 1
      group
    have e3 : c g = c (g * s) + ρ (g * s) (c s⁻¹) := by
      rw [← hco]
      congr 1
      group
    have hρg : ρ g = 1 := by
      have hgs : g = s * (s⁻¹ * g * s) * s⁻¹ := by group
      rw [hgs, map_mul, map_mul, hρ, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rw [e3, e2, hc0, map_zero, add_zero, map_mul ρ g s, hρg, one_mul, hinv, add_neg_cancel]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CoefFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.coefFacts :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → CharP k l ∧ (Set.range a).Finite := by
  intro l _ c k _ a ha
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨_, hfin, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨?_, ?_⟩
  · have hk : (l : k) = 0 := by
      rw [← map_natCast a l]
      exact ha _ hl
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hk
  · let f : ResidueField c.O →+* k := Ideal.Quotient.lift (maximalIdeal c.O) a ha
    refine (Set.finite_range f).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨IsLocalRing.residue c.O x, Ideal.Quotient.lift_mk _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rt_val {O Γ k : Type} [CommRing O] [Group Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (w : ℤ × ℤ) (g : Γ) :
    a (Φ.rt w g) = (a (Φ.χ 0 g) * (a (Φ.χ 1 g))⁻¹) ^ w.1 * (a (Φ.χ 0 g) * (a (Φ.χ 2 g))⁻¹) ^ w.2 := by
  have h : ∀ u : Oˣ, a (u : O) = ((Units.map (a : O →* k) u : kˣ) : k) := fun _ => rfl
  have e : Φ.rt w g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ w.1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ w.2 := rfl
  rw [e, h, h (Φ.χ 0 g), h (Φ.χ 1 g), h (Φ.χ 2 g)]
  simp only [map_mul, map_zpow, map_inv, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]

private theorem rt_lc {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) : IsLocallyConstant fun g => a (Φ.rt w g) := by
  simp only [rt_val]
  exact (((h.lc 0).mul ((h.lc 1).comp (·⁻¹))).comp (· ^ w.1)).mul (((h.lc 0).mul ((h.lc 2).comp (·⁻¹))).comp (· ^ w.2))

private theorem rt_kill {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) (g : Γ) (hg : g ∈ Φ.N) : a (Φ.rt w g) = 1 := by
  simp [rt_val, h.kill g hg]

theorem UpperTheory.V.Ws.Gys.cupNorm :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → ∀ (w w' : ℤ × ℤ), a (Φ.rt w Φ.g0) ≠ 1 → a (Φ.rt (w + w') Φ.g0) ≠ 1 → ∀ (J : Type) (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j) ∧ y j Φ.g0 = 0) →
      ∀ (x : Γ → k) (m : Φ.ι → k), Φ.Coc a w x → Φ.LocTriv a w x m → (∀ j, ∃ z, Φ.Cup a w w' x (y j) z m) →
        ∃ (x' : Γ → k) (m' : Φ.ι → k), Φ.Coc a w x' ∧ x' Φ.g0 = 0 ∧ Φ.LocTriv a w x' m' ∧ (∀ g, a (Φ.rt w g) = 1 → x' g = x g) ∧
          ∀ j, ∃ z, Φ.Cup a w w' x' (y j) z m' ∧ z Φ.g0 = 0 := by
  intro O Γ k _ _ _ _ Φ a hok w w' h1 h2 J y hy x m hx hm hz
  have n1 : 1 - a (Φ.rt w Φ.g0) ≠ 0 := sub_ne_zero.2 h1.symm
  have n2 : 1 - a (Φ.rt (w + w') Φ.g0) ≠ 0 := sub_ne_zero.2 h2.symm
  have hmul : ∀ (u : ℤ × ℤ) (g h : Γ), a (Φ.rt u (g * h)) = a (Φ.rt u g) * a (Φ.rt u h) := fun u g h => by
    rw [map_mul, Units.val_mul, map_mul]
  have hadd : ∀ g : Γ, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  obtain ⟨m1, hm1⟩ : ∃ m1 : k, x Φ.g0 = m1 - a (Φ.rt w Φ.g0) * m1 :=
    ⟨x Φ.g0 / (1 - a (Φ.rt w Φ.g0)), by field_simp⟩
  have c := fun t : k => (IsLocallyConstant.const t : IsLocallyConstant fun _ : Γ => t)
  refine ⟨fun g => x g - (m1 - a (Φ.rt w g) * m1), fun v => m v - m1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j => ?_⟩
  · exact hx.lc.sub ((c m1).sub ((rt_lc Φ a hok w).mul (c m1)))
  · intro g h
    rw [hx.coc, hmul]; ring
  · intro g hg
    rw [hx.kill g hg, rt_kill Φ a hok w g hg]; ring
  · exact sub_eq_zero.2 hm1
  · intro v s hs
    beta_reduce
    rw [hm v s hs]; ring
  · intro g hg
    beta_reduce
    rw [hg]; ring
  · obtain ⟨z, hz⟩ := hz j
    obtain ⟨hyj, hy0⟩ := hy j
    obtain ⟨o1, ho1⟩ : ∃ o1 : k, z Φ.g0 = o1 - a (Φ.rt (w + w') Φ.g0) * o1 :=
      ⟨z Φ.g0 / (1 - a (Φ.rt (w + w') Φ.g0)), by field_simp⟩
    refine ⟨fun g => z g - (o1 - a (Φ.rt (w + w') g) * o1 - y j g * a (Φ.rt w g) * m1), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hz.lc.sub (((c o1).sub ((rt_lc Φ a hok _).mul (c o1))).sub ((hyj.lc.mul (rt_lc Φ a hok w)).mul (c m1)))
    · intro g h
      rw [hz.coc, hyj.coc, hmul, hmul, hadd g, hadd h]; ring
    · intro g hg
      rw [hz.kill g hg, hyj.kill g hg, rt_kill Φ a hok _ g hg]; ring
    · intro v
      obtain ⟨o, ho⟩ := hz.loc v
      refine ⟨o - o1, fun s hs => ?_⟩
      rw [ho s hs]; ring
    · beta_reduce
      rw [ho1, hy0]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupSwap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupSwap :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (w w' : ℤ × ℤ) (x y z : Γ → R) (m n : Φ.ι → R), Φ.Coc a w x → Φ.LocTriv a w x m → Φ.Coc a w' y → Φ.LocTriv a w' y n →
      Φ.Cup a w w' x y z m → Φ.Cup a w' w y x (x * y - z) n := by
  intro O Γ R _ _ _ _ Φ a w w' x y z m n hx hm hy hn hz
  have e : ∀ g, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  refine ⟨?_, fun g h => ?_, fun g hg => ?_, fun v => ?_⟩
  · exact (hx.lc.comp₂ hy.lc (· * ·)).comp₂ hz.lc (· - ·)
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, hx.coc, hy.coc, hz.coc, e]
    ring
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [hx.kill g hg, hz.kill g hg, zero_mul, sub_zero]
  · obtain ⟨o, ho⟩ := hz.loc v
    refine ⟨m v * n v - o, fun s hs => ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, ho s hs, e, hm v s hs, hn v s hs]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataAl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.dataAl :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nM p.r →
      ∃ x : Γ → R, Φ.Coc a (-wAl) x ∧ x Φ.g0 = 0 ∧ Φ.LocTriv a (-wAl) x (fun v => p.n v 1 0) ∧ ∀ g, p.r g 1 0 = x g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hp hs
  have h12 : ∀ g, p.r g 1 2 = 0 := fun g => hs g 1 2 (by decide) (by decide)
  have h13 : ∀ g, p.r g 1 3 = 0 := fun g => hs g 1 3 (by decide) (by decide)
  have hd := hp.res.diag
  have hu : ∀ g, a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) * a (Φ.χ 0 g) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hrt : ∀ g, a (Φ.rt (-wAl) g) = a (Φ.χ 1 g) * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_mul, ← Units.val_mul]
    congr 2
    simp [Fr.rt, wAl]
  have hlc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => by
    refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (hp.cont i j 1) ?_
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]
  refine ⟨fun g => p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (hlc 1 0).mul ?_
    have e : (fun g => a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) = Ring.inverse ∘ fun g => p.r g 0 0 := by
      funext g
      simp only [Function.comp, hd]
      exact (Ring.inverse_unit (Units.map (a : O →* R) (Φ.χ 0 g))).symm
    rw [e]
    exact (hlc 0 0).comp _
  · intro g h
    have e : p.r (g * h) 1 0 = p.r g 1 0 * a (Φ.χ 0 h) + a (Φ.χ 1 g) * p.r h 1 0 := by
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, h12, h13, hd, hd]; ring
    rw [e, hrt, map_mul, mul_inv, Units.val_mul, map_mul]
    linear_combination (p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) * hu h
  · intro g hg
    simp [hp.pair.kill g hg]
  · have : p.r Φ.g0 1 0 = 0 := hp.pair.nrm (by decide)
    simp [this]
  · intro v s hsv
    obtain ⟨l1, l2, l3⟩ := hp.pair.low v
    have hinv : p.n v * adj (p.n v) = 1 := by
      rw [IsGSp, one_smul] at l1
      exact mul_eq_one_comm.mp l1
    have hU := hp.pair.flag v s hsv
    have hc := hp.res.char v s hsv 0
    unfold PD.ψ at hc
    have key : p.n v * (adj (p.n v) * p.r s * p.n v) = p.r s * p.n v := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    generalize adj (p.n v) * p.r s * p.n v = U at hU hc key
    have k := congrFun (congrFun key 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four, hU 1 0 (by decide), hU 2 0 (by decide),
      hU 3 0 (by decide), hc, h12, h13, hd, l2, l2] at k
    rw [hrt]
    beta_reduce
    linear_combination (-a (((Φ.χ 0 s)⁻¹ : Oˣ) : O)) * k + p.n v 1 0 * hu s
  · intro g
    beta_reduce
    rw [mul_assoc, hu, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataPs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_of_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {f : Γ → R} (h : UpperTheory.V.Alg.AdicCont ⊥ f) :
    IsLocallyConstant f := by
  refine IsLocallyConstant.desc _ _ (h 1) ?_
  intro x y hxy
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

theorem UpperTheory.V.Ws.Gys.dataPs :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nP p.r →
      ∃ y : Γ → R, Φ.Coc a (-wPs) y ∧ y Φ.g0 = 0 ∧ Φ.LocTriv a (-wPs) y (fun v => p.n v 2 0) ∧ ∀ g, p.r g 2 0 = y g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hR hS
  have hc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => lc_of_cont (hR.cont i j)
  have hd := hR.res.diag
  have hinv : ∀ g, Ring.inverse (p.r g 0 0) = a ↑((Φ.χ 0 g)⁻¹) := by
    intro g
    rw [hd g 0]
    have hu : a ↑(Φ.χ 0 g) = ↑(Units.map a.toMonoidHom (Φ.χ 0 g)) := rfl
    rw [hu, Ring.inverse_unit]
    rfl
  have hone : ∀ g, a ↑(Φ.χ 0 g) * a ↑((Φ.χ 0 g)⁻¹) = 1 := by
    intro g
    rw [← map_mul, Units.mul_inv, map_one]
  have he : ∀ g, Φ.rt (-wPs) g = Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    intro g
    simp [Fr.rt, wPs]
  refine ⟨fun g => p.r g 2 0 * Ring.inverse (p.r g 0 0), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hc 2 0).mul ((hc 0 0).comp Ring.inverse)
  · intro g h
    have z1 : p.r g 2 1 = 0 := hS g 2 1 (by decide) (by decide)
    have z3 : p.r g 2 3 = 0 := hS g 2 3 (by decide) (by decide)
    show p.r (g * h) 2 0 * Ring.inverse (p.r (g * h) 0 0) =
      p.r g 2 0 * Ring.inverse (p.r g 0 0) + a ↑(Φ.rt (-wPs) g) * (p.r h 2 0 * Ring.inverse (p.r h 0 0))
    rw [hinv (g * h), hinv g, hinv h, he g]
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z1, z3, zero_mul, add_zero, hd, mul_inv,
      Units.val_mul]
    linear_combination (p.r g 2 0 * a ↑((Φ.χ 0 g)⁻¹)) * hone h
  · intro g hg
    show p.r g 2 0 * Ring.inverse (p.r g 0 0) = 0
    rw [hR.pair.kill g hg, Matrix.one_apply_ne (by decide), zero_mul]
  · show p.r Φ.g0 2 0 * Ring.inverse (p.r Φ.g0 0 0) = 0
    rw [hR.pair.nrm (by decide : (2 : Fin 4) ≠ 0), zero_mul]
  · intro v s hs
    have hn := hR.pair.low v
    have hna0 : adj (p.n v) * p.n v = 1 := by
      have h1 := hn.1
      simpa [IsGSp] using h1
    have hna : p.n v * adj (p.n v) = 1 := mul_eq_one_comm.mp hna0
    have hX := hR.pair.flag v s hs
    have hch : (adj (p.n v) * p.r s * p.n v) 0 0 = a ↑(Φ.χ 0 s) := hR.res.char v s hs 0
    have key : p.r s * p.n v = p.n v * (adj (p.n v) * p.r s * p.n v) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hna, Matrix.one_mul]
    have k20 := congrFun (congrFun key 2) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at k20
    rw [hS s 2 1 (by decide) (by decide), hS s 2 3 (by decide) (by decide), hd s 2, hn.2.1 0,
      hX 1 0 (by decide), hX 2 0 (by decide), hX 3 0 (by decide), hch] at k20
    show p.r s 2 0 * Ring.inverse (p.r s 0 0) = p.n v 2 0 - a ↑(Φ.rt (-wPs) s) * p.n v 2 0
    rw [hinv, he s, Units.val_mul, map_mul]
    linear_combination (a ↑((Φ.χ 0 s)⁻¹)) * k20 + (p.n v 2 0) * hone s
  · intro g
    show p.r g 2 0 = p.r g 2 0 * Ring.inverse (p.r g 0 0) * a ↑(Φ.χ 0 g)
    rw [hinv]
    linear_combination (-(p.r g 2 0)) * hone g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Descend
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.descend :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContAction ρ → UnrOut ρ S →
      ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, ρS.comp (toGS Ω _) = ρ ∧ ContAction ρS := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ S hρ hU
  have hclosed : IsClosed (ρ.ker : Set (G F Ω)) := by
    have hset : (ρ.ker : Set (G F Ω)) = ⋂ m : M, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    rw [hset]
    refine isClosed_iInter fun m => ?_
    have hc : Continuous fun g : G F Ω => ρ g m :=
      hρ.comp (continuous_id.prodMk continuous_const)
    exact isClosed_eq hc continuous_const
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hg
    obtain ⟨v, hv, A, hA, hgA⟩ := hg
    exact hU v hv A hA g (mem_Ine.mpr hgA)
  refine ⟨QuotientGroup.lift _ ρ hle, ?_, ?_⟩
  · exact MonoidHom.ext fun g => rfl
  · have h2 := (QuotientGroup.isOpenQuotientMap_mk (N := NS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).prodMap
      (IsOpenQuotientMap.id (X := M))).continuous_comp_iff
      (g := fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => (QuotientGroup.lift _ ρ hle) p.1 p.2)
    exact h2.mp hρ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RamCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ramCard :
    ∀ (R D M : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M), (∀ g, ρ g = 1) → m0 ≠ 0 → Finite (H1 ρ) →
      ∀ φ₁ ∈ Z1 (Representation.trivial R D R), ∀ φ₂ ∈ Z1 (Representation.trivial R D R), (∀ g ∈ I, φ₁ g = 0) → (∃ g, φ₁ g = 1) → (∃ g ∈ I, φ₂ g = 1) →
      2 * Nat.card M ≤ Nat.card (ramLine ρ I m0) := by
  rintro R D M _ _ _ _ _ _ _ _ _ _ ρ I m0 hρ hm0 _ φ₁ hφ₁ φ₂ hφ₂ hI1 ⟨g1, hg1⟩ ⟨g2, hg2I, hg2⟩
  obtain ⟨c1, a1⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₁
  obtain ⟨c2, a2⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₂
  let fn : R → M → D → M := fun t m g => φ₁ g • m + (t * φ₂ g) • m0
  have hz : ∀ t m, fn t m ∈ Z1 ρ := by
    intro t m
    rw [mem_Z1_iff_cocycle]
    refine ⟨(continuous_of_discreteTopology (f := fun p : R × R => p.1 • m + (t * p.2) • m0)).comp
      (c1.prodMk c2), ?_⟩
    intro g h
    simp [fn, hρ g, a1 g h, a2 g h, add_smul, mul_add] <;> abel
  let F : Bool × M → ramLine ρ I m0 := fun p =>
    ⟨Submodule.Quotient.mk ⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩,
      (mem_ramLine ρ I m0 _).2 ⟨⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩, fun g hg => by
        show fn _ _ g ∈ _
        simp only [fn, hI1 g hg, zero_smul, zero_add]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m0), rfl⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨b, m⟩ ⟨b', m'⟩ h
    have h1 := congrArg Subtype.val h
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h1
    obtain ⟨x, hx⟩ := h1
    have hpt : ∀ g, fn (if b then 1 else 0) m g = fn (if b' then 1 else 0) m' g := by
      intro g
      have h2 := hx g
      rw [hρ g, Module.End.one_apply, sub_self] at h2
      exact sub_eq_zero.1 h2
    have hb : b = b' := by
      have h3 := hpt g2
      simp only [fn, hI1 g2 hg2I, hg2, zero_smul, zero_add, mul_one] at h3
      cases b <;> cases b' <;> simp_all
    subst hb
    have h4 := hpt g1
    simp only [fn, hg1, one_smul] at h4
    rw [add_right_cancel h4]
  have hc := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hc
  exact hc
end

