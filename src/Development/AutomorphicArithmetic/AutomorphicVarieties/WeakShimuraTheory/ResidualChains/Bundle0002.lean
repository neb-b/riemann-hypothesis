module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.RtFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Chain.map_eq_one_iff {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (a : O →+* k)
    (ha : ∀ x ∈ maximalIdeal O, a x = 0) (x : O) : a x = 1 ↔ residue O x = 1 := by
  constructor
  · intro h
    rw [← sub_eq_zero, ← map_one (residue O), ← map_sub, residue_eq_zero_iff]
    by_contra hm
    have hu := (IsLocalRing.notMem_maximalIdeal.mp hm).map a
    rw [map_sub, h, map_one, sub_self] at hu
    exact not_isUnit_zero hu
  · intro h
    have hm : x - 1 ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_sub, h, map_one, sub_self]
    have := ha _ hm
    rwa [map_sub, map_one, sub_eq_zero] at this

private theorem UpperTheory.V.Ws.Chain.roots_wt : ∀ w ∈ roots, ∃ i j : Fin 4, i ≠ j ∧
    ((w = wt 0 j ∧ i = 0) ∨ (w = wt i 0 ∧ j = 0) ∨ (w = wt 1 2 ∧ i = 1 ∧ j = 2) ∨ (w = wt 2 1 ∧ i = 2 ∧ j = 1)) := by
  decide

private theorem UpperTheory.V.Ws.Chain.rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g), mul_inv_cancel_right]
  have e : ∀ k : Fin 4, Φ.χ k g = ![Φ.χ 0 g, Φ.χ 1 g, Φ.χ 2 g, Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹] k := by
    intro k
    fin_cases k <;> simp [hd]
  have key : ∀ k : Fin 4, Φ.χ k g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ *
      (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ lamW k * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ muW k := by
    intro k
    rw [e k]
    generalize Φ.χ 0 g = x at *
    generalize Φ.χ 1 g = y at *
    generalize Φ.χ 2 g = z at *
    fin_cases k <;> simp [lamW, muW] <;> group
  have hrt : Φ.rt (wt i j) g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW i - lamW j) *
      (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW i - muW j) := rfl
  rw [hrt, key i, key j]
  generalize Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ = d
  generalize Φ.χ 0 g * (Φ.χ 1 g)⁻¹ = u
  generalize Φ.χ 0 g * (Φ.χ 2 g)⁻¹ = v
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  rw [sub_smul, sub_smul]
  abel

theorem UpperTheory.V.Ws.Chain.rtFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) →
      (∀ w ∈ roots, a ((frQ D T.pr (resQ T.F T.g0)).rt w (resQ T.F T.g0)) ≠ 1) ∧
      ∀ w g, a ((T.fr ∅).rt w g) = 1 ↔ T.rb w g = 1 := by
  intro Ω _ _ _ l _ c D hD T hT k _ a ha
  have rel : ∀ (pr : Bool) (s : G ℚ Ω), chi D pr 0 s * chi D pr 3 s = chi D pr 1 s * chi D pr 2 s := by
    intro pr s
    cases pr <;> simp [chi, lab, Raw.ps, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi] <;> ac_rfl
  refine ⟨?_, fun w g => UpperTheory.V.Ws.Chain.map_eq_one_iff a ha _⟩
  intro w hw h1
  have hw' : ∃ i j : Fin 4, i ≠ j ∧ w = wt i j := by
    obtain ⟨i, j, hij, h⟩ := UpperTheory.V.Ws.Chain.roots_wt w hw
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact ⟨_, _, hij, rfl⟩
  obtain ⟨i, j, hij, rfl⟩ := hw'
  have key : (frQ D T.pr (resQ T.F T.g0)).rt (wt i j) (resQ T.F T.g0) * chi D T.pr j (resQ T.F T.g0) =
      chi D T.pr i (resQ T.F T.g0) :=
    UpperTheory.V.Ws.Chain.rt_wt (frQ D T.pr (resQ T.F T.g0)) (resQ T.F T.g0) (rel T.pr _) i j
  have hr : residue c.O ↑((frQ D T.pr (resQ T.F T.g0)).rt (wt i j) (resQ T.F T.g0)) = 1 :=
    (UpperTheory.V.Ws.Chain.map_eq_one_iff a ha _).1 h1
  apply hT.dist i j hij
  show residue c.O ↑(chi D T.pr i (resQ T.F T.g0)) = residue c.O ↑(chi D T.pr j (resQ T.F T.g0))
  rw [← key, Units.val_mul, map_mul, hr, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.SeedRes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [Matrix.map_mul, Matrix.map_mul, adj_map]

private theorem isGSp_map (j : R →+* R') {ν : R} {X : M4 R} (hX : IsGSp ν X) : IsGSp (j ν) (X.map j) := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp at hX ⊢
  rw [adj_map, ← Matrix.map_mul, h, hX]

private theorem isPair_map {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (a : O →+* R) (f : R →+* R')
    (P : PD Φ.ι Γ R) (h : Φ.IsPair a P) : Φ.IsPair (f.comp a) (P.map f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hr : ∀ g, (P.map f).r g = (P.r g).map f := fun _ => rfl
  have hn : ∀ v, (P.map f).n v = (P.n v).map f := fun _ => rfl
  refine ⟨fun g => isGSp_map f (h1 g), fun g hg => ?_, ?_, fun v => ⟨?_, fun i => ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => ?_⟩
  · rw [hr, h2 g hg, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [hr]; exact h3.map (map_zero f)
  · have := isGSp_map f (h4 v).1
    rwa [map_one] at this
  · rw [hn, Matrix.map_apply, (h4 v).2.1, map_one]
  · rw [hn, Matrix.map_apply, (h4 v).2.2 i j hij, map_zero]
  · rw [hr, hn, conj_map, Matrix.map_apply, h5 v s hs i j hij, map_zero]
  · have := h6 v s hs i
    unfold PD.ψ at this ⊢
    rw [hr, hn, conj_map, Matrix.map_apply, this, map_one]

end

theorem UpperTheory.V.Ws.Chain.seedRes :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O),
      T.SeedPair ι h Q → (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) ∧
        (Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) → Fr.InV (Φ := T.fr ∅) (Q.map (𝔞.red c₁))) ∧
        ∀ w, Ent (Q.map (residue c₁.O)).r w → Ent (Q.map (𝔞.red c₁)).r w := by
  intro Ω _ _ _ l _ c D T ι 𝔞 c₁ h Q hQ
  have hj : Function.Injective (𝔞.j c₁) := (𝔞.j c₁).injective
  have hjr : ∀ x, 𝔞.red c₁ x = 𝔞.j c₁ (residue c₁.O x) := fun x => rfl
  have hQm : Q.map (𝔞.red c₁) = (Q.map (residue c₁.O)).map (𝔞.j c₁) := rfl
  have ha : 𝔞.red c = (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) := by
    ext x
    change residue _ (𝔞.a c x) = residue _ (𝔞.a c₁ (Subalgebra.inclusion h x))
    rw [𝔞.compat]
  have hres : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨isPair_map _ _ _ _ hQ.pair, hQ.res, fun i j N => ?_⟩
    have h1 := hQ.cont i j 1
    have h2 : IsLocallyConstant fun g => residue c₁.O (Q.r g i j) := by
      have := h1.comp (Ideal.Quotient.factor (show maximalIdeal c₁.O ^ 1 ≤ maximalIdeal c₁.O by rw [pow_one]))
      exact this
    exact h2.comp _
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, hQm]
    exact (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 hres
  · rintro ⟨h1, h2⟩
    refine ⟨fun g i j hij hw => ?_, fun v => ⟨fun i j hij hw => ?_, fun h0 => (h2 v).2 ?_⟩⟩
    · exact (congrArg (𝔞.j c₁) (h1 g i j hij hw)).trans (map_zero _)
    · exact (congrArg (𝔞.j c₁) ((h2 v).1 i j hij hw)).trans (map_zero _)
    · exact hj (h0.trans (map_zero _).symm)
  · rintro w ⟨g, i, j, hw, hne⟩
    exact ⟨g, i, j, hw, fun h0 => hne (hj (h0.trans (map_zero _).symm))⟩
end

