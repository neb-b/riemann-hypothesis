module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published

namespace UpperTheory.V.Af.Bc

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]

def CharEig (ι : Qbar l ≃+* ℂ) (δ : G F Ω →* (Qbar l)ˣ) (w : HeightOneSpectrum (𝓞 F)) (z : ℂ) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := F) A, δ s = 1) ∧
    ∀ σ : G F Ω, IsFrob A (normV w) σ → ι ((δ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = z

theorem charEig_one (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) : CharEig ι (1 : G F Ω →* (Qbar l)ˣ) w 1 :=
  fun _ _ => ⟨fun _ _ => rfl, fun _ _ => by simp⟩


omit [NumberField F] in
variable (F Ω) in
abbrev res (E : Type) [Field E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] : G E Ω →* G F Ω :=
  AlgEquiv.restrictScalarsHom F


omit [NumberField F] in
def IsSign (E : Type) [Field E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] (δ : G F Ω →* (Qbar l)ˣ) : Prop :=
  (∀ s, δ s = 1 ↔ s ∈ (res F Ω E).range) ∧ ∀ s, δ s = 1 ∨ δ s = -1

abbrev cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  conjSrc (IsCMField.complexConj E).toRingEquiv w

end Defs

def FrobRes : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ), normV w = normV (w.under (𝓞 F)) ^ f →
    (∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (B : Multiset ℂ),
      FrobEig ι r (w.under (𝓞 F)) B → FrobEig ι (r.comp (res F Ω E)) w (B.map (· ^ f))) ∧
    ∀ (δ : G F Ω →* (Qbar l)ˣ) (z : ℂ), CharEig ι δ (w.under (𝓞 F)) z → CharEig ι (δ.comp (res F Ω E)) w (z ^ f)

def FrobTw : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (δ : G F Ω →* (Qbar l)ˣ) (w : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂ) (z : ℂ),
    FrobEig ι r w B → CharEig ι δ w z → FrobEig ι (tw r δ) w (B.map (· * z))

def FrobDual : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (θ : G F Ω →* (Qbar l)ˣ), DualTw r θ →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (B : Multiset ℂˣ) (z : ℂˣ),
      FrobEig ι r w (algSat n (normV w) B) → CharEig ι (θ * cycBar F Ω l ^ ((n : ℤ) - 1)) w z →
      B.map (·⁻¹) = B.map (· * z⁻¹)

def SignEx : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], Module.finrank F E = 2 →
    ∃ δ : G F Ω →* (Qbar l)ˣ, Continuous δ ∧ δ ≠ 1 ∧ IsSign E δ ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∀ s ∈ Ine (F := F) A, δ s = 1

def SignFrob : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (δ : G F Ω →* (Qbar l)ˣ), IsSign E δ →
    ∀ w : HeightOneSpectrum (𝓞 E),
      (∀ A : ValuationSubring Ω, IsPlaceOver A (w.under (𝓞 F)) → ∀ s ∈ Ine (F := F) A, δ s = 1) →
      CharEig ι δ (w.under (𝓞 F)) (if normV w = normV (w.under (𝓞 F)) then 1 else -1)

def SchurTw : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] (n : ℕ) (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
    IsIrr (r.comp φ) → δ.comp φ = 1 → RepIso r (tw r δ) → δ = 1

def IrrBasic : Prop :=
  (∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k),
    (∀ φ : Γ' →* Γ, IsIrr (r.comp φ) → IsIrr r) ∧ (IsIrr r → IsSSRep r) ∧ ∀ δ : Γ →* kˣ, IsSSRep r → IsSSRep (tw r δ)) ∧
  ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ)
    (r : Γ →* GL (Fin n) k) (δ : Γ →* kˣ), Continuous r → Continuous δ → Continuous (tw r δ)

def NoTwist : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), Module.finrank F E = 2 →
    ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n), Continuous r → AttR ι r π → IsIrr (r.comp (res F Ω E)) →
      ∀ η : HChar F, IsQuadCharOf E η → ¬ IsoTwist π η

def BcAtt : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (res F Ω E)) → AttC ι (r.comp (res F Ω E)) P)

def BcConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (cPl w) B

def ThetaSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ), (CG.mk P).HasSat (cPl w) B → (CG.mk (GlobalTheory.ThetaPull.thetaSub P)).HasSat w (B.map (·⁻¹))

def NormLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ),
    ∃ y : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))ˣ,
      ideleNorm E (localIdele E w x) = localIdele (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))) y ∧
      ∀ f : ℕ, normV w = normV (w.under (𝓞 (maximalRealSubfield E))) ^ f →
        Valued.v (y : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) =
          Valued.v (x : w.adicCompletion E) ^ f

def NormVal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)) (f : ℕ),
    normV w = normV (w.under (𝓞 (maximalRealSubfield E))) ^ f → χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) →
      (compNorm E χ).UnrAt w ∧ (compNorm E χ).val w = χ.val (w.under (𝓞 (maximalRealSubfield E))) ^ f

def NormGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E)) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
    IsLAdicCharOf ι χ μ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (compNorm E χ).UnrAt w ∧
      CharEig ι (μ.comp (res (maximalRealSubfield E) Ω E)) w ((compNorm E χ).val w : ℂˣ)

def CycHecke : Prop :=
  GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (wt : ℤ) (θ : G F Ω →* (Qbar l)ˣ), IsCycWt l wt θ →
    Continuous θ ∧ ∃ (χ : HChar F) (art : Ideles F →* Gab F Ω) (a : (F →+* ℂ) → ℤ),
      IsGlobalArtin art ∧ IsAlgPos χ a ∧ IsLAdicOf art ι χ a θ

def SignFix : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E], Module.finrank ℚ E = 2 →
    ∀ [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E)) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
    IsLAdicCharOf ι χ μ → ∀ n : ℕ, ∃ (χ' : HChar (maximalRealSubfield E)) (μ' : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
      IsLAdicCharOf ι χ' μ' ∧ compNorm E χ' = compNorm E χ ∧
      μ'.comp (res (maximalRealSubfield E) Ω E) = μ.comp (res (maximalRealSubfield E) Ω E) ∧
      ∀ v : InfinitePlace (maximalRealSubfield E), χ'.locInf v (-1) = (-1) ^ n

def PolOfSat : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (P : CuspSub E n) (ψ : HChar E),
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ∃ B B', (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (cPl w) B' ∧
      B'.map (·⁻¹) = B.map (· * (ψ.val w)⁻¹)) → GlobalTheory.ContraPair.DualIsConjBy P ψ

end UpperTheory.V.Af.Bc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
section
noncomputable section

namespace UpperTheory.V.Af

theorem finite_image_of_card_le {P Y : Type} (Sig : Set P) (Iso : P → P → Prop) (f : P → Y)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → f a = f b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N) :
    Finite ↥(f '' Sig) ∧ Nat.card ↥(f '' Sig) ≤ N := by
  classical
  have key : ∀ T : Finset Y, (↑T : Set Y) ⊆ f '' Sig → T.card ≤ N := by
    intro T hT
    have hpre : ∀ y : T, ∃ a, a ∈ Sig ∧ f a = y.1 := fun y => hT y.2
    choose g hgS hgf using hpre
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← hgf x, ← hgf y, hxy]
    have hS := hcard (Finset.univ.image g) ?_ ?_
    · rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] at hS
    · intro a ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ha
      exact hgS y
    · intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
      have hxy := hiso _ (hgS x) _ (hgS y) hab
      rw [hgf x, hgf y] at hxy
      rw [Subtype.ext hxy]
  have hfin : (f '' Sig).Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
    have := key t ht
    omega
  refine ⟨hfin.to_subtype, ?_⟩
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  exact key _ (by simp)

theorem exists_eigData {P W : Type} (Sig : Set P) (Iso : P → P → Prop) (sys : P → W → Multiset ℂ)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → sys a = sys b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N)
    (hconj : ∀ σ : ℂ ≃+* ℂ, ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ v, sys b v = (sys a v).map σ)
    (w : W) {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (hn : ∀ a ∈ Sig, (sys a w).card = n)
    (hpure : ∀ a ∈ Sig, ∀ b ∈ sys a w, ‖b‖ = (q : ℝ) ^ (-(wt : ℝ) / 2))
    (hint : ∀ a ∈ Sig, SlopesIn q m (sys a w)) :
    ∃ D : EigData n q m wt, Nat.card D.S ≤ N ∧ ∃ cl : ↥Sig → D.S, (∀ a b, cl a = cl b → sys a = sys b) ∧
      ∀ a, (D.β (cl a)).map (·⁻¹) = sys a w := by
  obtain ⟨hfin, hN⟩ := finite_image_of_card_le Sig Iso sys hiso N hcard
  refine ⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN,
    fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    simpa using hn a ha
  · intro σ
    have hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, h⟩ := hconj σ a ha
      exact ⟨b, hb, funext h⟩
    let F : ↥(sys '' Sig) → ↥(sys '' Sig) := fun s => ⟨_, hmem s⟩
    have hF : Function.Injective F := by
      intro s s' h
      refine Subtype.ext (funext fun v => ?_)
      exact Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)
    refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩
    simp [F, Multiset.map_map]
  · rintro ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_inv, hpure a ha c hc, ← Real.rpow_neg (Nat.cast_nonneg q)]
    congr 1
    ring
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    exact (hint a ha c hc).1 k hk
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [inv_inv]
    exact (hint a ha c hc).2 k hk
  · simp [Multiset.map_map]


open NumberField IsDedekindDomain in
theorem natCast_notMem_of_not_dvd {F : Type} [Field F] [NumberField F] {p M : ℕ} (hp : p.Prime)
    {w : HeightOneSpectrum (𝓞 F)} (hw : (p : 𝓞 F) ∈ w.asIdeal) (hM : ¬ p ∣ M) : (M : 𝓞 F) ∉ w.asIdeal := by
  intro hMw
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hM
  have h := Nat.gcd_eq_gcd_ab p M
  rw [Nat.Coprime.gcd_eq_one hcop] at h
  have h1 : (1 : 𝓞 F) = (p : 𝓞 F) * (Nat.gcdA p M : 𝓞 F) + (M : 𝓞 F) * (Nat.gcdB p M : 𝓞 F) := by
    have h' := congrArg (Int.cast : ℤ → 𝓞 F) h
    push_cast at h'
    exact h'
  have hone : (1 : 𝓞 F) ∈ w.asIdeal := by
    rw [h1]
    exact w.asIdeal.add_mem (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_right _ _ hMw)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)


open NumberField IsDedekindDomain in
theorem eventually_natCast_notMem {F : Type} [Field F] [NumberField F] {M : ℕ} (hM : M ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (M : 𝓞 F) ∉ w.asIdeal := by
  rw [Filter.eventually_cofinite]
  have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hI : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hM'
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_not] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

def IsLevelWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (M n : ℕ) (x : WD h) : Prop :=
  ∃ (χ : Fin n → G F Ω →* ℂˣ) (a : WDRep h (Fin n → ℂ)), (∀ i, KillsMu M (χ i)) ∧ WD.mk a = x ∧ a.N = 0 ∧
    ∀ s : ↥(Ine (F := F) A), a.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (χ i s : ℂ))


variable (F) in
def KLoc (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ) : Subgroup (GL (Fin n) (w.adicCompletion F)) :=
  (KLev F n M).comap (locGL F n w)

def LocIsotypic {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V)
    (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  Nontrivial V ∧ ⨆ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, LinearMap.range f.1 = ⊤

def FlagAt {l : ℕ} [Fact l.Prime] {n : ℕ} (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) : Prop :=
  ∃ χ : Fin n → G F Ω →* (Qbar l)ˣ, (∀ i, KillsMu M (χ i)) ∧ IsFlagOn r (Dec (F := F) A) κ ∧
    ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i * χ i s

end Defs

def WDAway : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (χ : Fin n → G F Ω →* (Qbar l)ˣ), (∀ i, KillsMu M (χ i)) → IsDiagOn r (Ine (F := F) A) χ →
      ∀ x : WD h, IsWDOf ι r x → IsLevelWD M n x

def WDAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ((∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ PotCrysAt r A) →
      IsLevelWD M n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype))

def JumpsAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw → ∀ (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → ∀ (τ : F →+* Qbar l) (J : Multiset ℤ),
      IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ J → J = Finset.univ.val.map fun i => -m i

def LocFixed : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n M : ℕ), 1 ≤ M →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      IsLevelWD M n (rc (algNorm σ)) → HasFixed σ.ρ (KLoc F w n M)

def GlobFixed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n M : ℕ), 1 ≤ M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V), GlobalTheory.PRep.IsSmooth ρ →
    (∀ w, ∃ σ, LocIsotypic ρ w σ ∧ HasFixed σ.ρ (KLoc F w n M)) → HasFixed ρ (KLev F n M)

def LocCompC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def LocCompR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def SatLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))),
    (HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n)) → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V), LocIsotypic ρ w σ →
      ∀ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SatFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc →
        IsWDOf ι r (rc (algNorm σ))) → FrobEig ι r w (algSat n (normV w) B)

def CrysSlopes : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime],
    ¬ (p : ℤ) ∣ discr F → ∀ (ι : Qbar p ≃+* ℂ) (n : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar p)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[p] O] [TopologicalSpace O]
      (Bw : LocBridge p F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsCrysAt (Loc.PP p) Bw (r.comp (Dec (F := F) A).subtype) →
      (∀ (τ : F →+* Qbar p) (LL' : FinExt p) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP p) Bw (r.comp (Dec (F := F) A).subtype) τ (Finset.univ.val.map fun i => -m i)) →
      ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      ∀ rc, IsRec h rc → wdAt (Loc.PP p) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = rc (algNorm σ) →
      ∀ b ∈ algSat n (normV w) B, (∀ a : ℤ, (∀ i, -a ≤ m i) → ‖ι.symm ((normV w : ℂ) ^ a * b⁻¹)‖ ≤ 1) ∧
        ∀ a : ℤ, (∀ i, m i ≤ a) → ‖ι.symm ((normV w : ℂ) ^ a * b)‖ ≤ 1

def WeylC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), ∃ c A : ℕ, ∀ m : Fin n → ℤ, StrictAnti m →
    ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∃ Ξ : GlobalTheory.GKCoh.AlgRep E n, (∀ τ, AlgInfChar Ξ τ ((infOf m).map Neg.neg)) ∧ Ξ.d ≤ c * (H + 1) ^ A

end UpperTheory.V.Af
end
end

