module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.FkFilt
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem fkFilt_holds : FkFilt := by
  intro D B P j X ka wL wF G la T
  refine ⟨?_, ?_, ?_⟩
  · intro k l hkl
    unfold Fk
    apply Submodule.span_mono
    apply Set.image_mono
    exact SetLike.coe_subset_coe.2 (Submodule.smul_mono_left (Ideal.pow_le_pow_right hkl))
  · unfold Fk
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ,
      (toWK_surjective X la G.w wF (a0 D j T)).range_eq, Submodule.span_univ]
  · unfold Fk
    rw [Submodule.span_eq_bot]
    rintro _ ⟨x, hx, rfl⟩
    exact (toWK_eq_zero_iff X la G.w wF _ x).2 hx

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseOf
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_mon_le (hM : MonoCount) (D : D7) (j T n : ℕ) :
    ∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * n ≤ Nat.choose (T - 1) (WeightFamilies.dimY D j) * n := by
  rw [← Finset.sum_mul]
  by_cases h : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ h]
  · have h0 : a0 D j T = 0 := by
      show T - WeightFamilies.dimY D j = 0
      omega
    simp [h0]

theorem lenBase_of (hF : FiltLenGr) (hM : MonoCount) (hK : FkFilt) (hG : GrBound) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hth hw hI
  obtain ⟨hA, h0, hT⟩ := hK G la T
  obtain ⟨φ, Pk, Qk, hker, hP, hQ, hL⟩ := hG G la Q S CRm T c hOk hth hw hI
  have key := hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) hA h0 hT
    (fun _ => Vg G la) φ hker (Q.AA T) (firstLength_le_prime_bound G la T ⊓ Q.AA T) Pk Qk inf_le_right hP hQ
  have e : (firstLength_le_prime_bound G la T ⊓ Q.AA T).comap (Q.AA T).subtype = (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype := by
    ext x
    simp [x.2]
  rw [e] at key
  refine key.trans ?_
  calc ∑ k ∈ Finset.range (a0 D j T), Module.length (Op X la G.N) (↥(Pk k) ⧸ (Qk k).comap (Pk k).subtype)
      ≤ ∑ k ∈ Finset.range (a0 D j T), ((((mon D j k).card * Q.Ila.toNat : ℕ)) : ℕ∞) :=
        Finset.sum_le_sum fun k hk => hL k (Finset.mem_range.1 hk)
    _ = ((∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * Q.Ila.toNat : ℕ) : ℕ∞) := by
        push_cast; rfl
    _ ≤ _ := by exact_mod_cast sum_mon_le hM D j T Q.Ila.toNat

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenPiU
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem lenPiU_holds : LenPiU := by
  intro R E V _ _ _ _ _ ι _ A B U hU
  classical
  set A' : Submodule R (ι → E) := Submodule.pi Set.univ fun _ => A with hA'
  set B' : Submodule R (ι → E) := Submodule.pi Set.univ fun _ => B with hB'
  let e : ↥A' ≃ₗ[R] ↥(A'.map U) := Submodule.equivMapOfInjective U hU A'
  have he : ∀ x : ↥A', ((e x : ↥(A'.map U)) : V) = U x := fun _ => rfl
  have hmap : (B'.comap A'.subtype).map (e : ↥A' →ₗ[R] ↥(A'.map U)) = (B'.map U).comap (A'.map U).subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply]
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply, he]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨z, hz, h⟩ => hU h ▸ hz⟩
  rw [← (Submodule.Quotient.equiv _ _ e hmap).length_eq]

  let f : ↥A' →ₗ[R] (ι → ↥A ⧸ B.comap A.subtype) :=
    LinearMap.pi fun i => (B.comap A.subtype).mkQ ∘ₗ
      LinearMap.codRestrict A ((LinearMap.proj i : (ι → E) →ₗ[R] E) ∘ₗ A'.subtype)
        (fun x => x.2 i (Set.mem_univ i))
  have hf : Function.Surjective f := by
    intro g
    choose a ha using fun i => Submodule.Quotient.mk_surjective _ (g i)
    refine ⟨⟨fun i => a i, fun i _ => (a i).2⟩, ?_⟩
    funext i
    exact ha i
  have hker : LinearMap.ker f = B'.comap A'.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h i _
      have h' : (B.comap A.subtype).mkQ
          (LinearMap.codRestrict A ((LinearMap.proj i : (ι → E) →ₗ[R] E) ∘ₗ A'.subtype)
            (fun x => x.2 i (Set.mem_univ i)) x) = 0 := congrFun h i
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
      exact h'
    · intro h
      funext i
      show (B.comap A.subtype).mkQ
          (LinearMap.codRestrict A ((LinearMap.proj i : (ι → E) →ₗ[R] E) ∘ₗ A'.subtype)
            (fun x => x.2 i (Set.mem_univ i)) x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h i (Set.mem_univ i)
  rw [← hker, (f.quotKerEquivOfSurjective hf).length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.N) : ↥(Frac0 X la G.w) :=
  fr0 X la G.w 1 ⟨emb X la G.N (X.inc wL (G.w k)), by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la G.N wL (G.w k)⟩

def uC (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    OsK X la G.w :=
  ∏ i, toOsK X la G.w (wfr G la jj) ^ α i

def ym (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (α : Fin (WeightFamilies.dimY D j) → ℕ) : ↥(Frac0 X la G.w) :=
  ∏ i, sfr X la G.w i.succ ^ α i

def bcol {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) : Idx D j N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2 = jj then Fin.cases (motive := fun _ => ℕ) 0 α p.1 else 0

def TaylorRep : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) (x : ↥(HK X la G.w wF)),
    x ∈ (Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) → ∃ cf : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF),
      x - ∑ α ∈ mon D j k, ym G la α • cf α ∈ (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)))

def TaylorHasse : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) (x : ↥(HK X la G.w wF)) (cf : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF)),
    x - ∑ α ∈ mon D j k, ym G la α • cf α ∈ (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) →
    ∀ (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ), α ∈ mon D j k →
      ∀ h : hasse X la G.w (bcol jj α) (x : Lw X la G.w) ∈ HK X la G.w wF,
        toA0K X la G.w wF ⟨_, h⟩ = uC G la jj α • toA0K X la G.w wF (cf α)

def HasseSmul : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) (o : Op X la G.N) (x : ↥(HK X la G.w wF)), x ∈ (Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) →
    ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) = k →
      ∀ (h : hasse X la G.w β ((o • x : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF)
        (h' : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF),
        toA0K X la G.w wF ⟨_, h⟩ = o • toA0K X la G.w wF ⟨_, h'⟩

def HasseVan : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (a : ℕ) (x : ↥(HK X la G.w wF)), x ∈ (Jid X la G.w ^ a • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) →
    ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) < a →
      ∀ h : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF, toA0K X la G.w wF ⟨_, h⟩ = 0

def Column : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ ζ : PtsG G la, (∀ jj, 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj))) ∧
      ∃ jj, ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) = 0

def UInj : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ (α : Fin (WeightFamilies.dimY D j) → ℕ) (b : SectionSheafQuotient X la G.w wF), (∀ jj, uC G la jj α • b = 0) → b = 0

def UBall : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ (α : Fin (WeightFamilies.dimY D j) → ℕ) (b : SectionSheafQuotient X la G.w wF), (∀ jj, uC G la jj α • b ∈ Q.A0) → b ∈ Q.A0

def AARep : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ x ∈ Q.AA T, ∃ x' : ↥(HK X la G.w wF), toWK X la G.w wF (a0 D j T) x' = x ∧
      ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
        ∀ h : hasse X la G.w β (x' : Lw X la G.w) ∈ HK X la G.w wF, toA0K X la G.w wF ⟨_, h⟩ ∈ Q.A0

def TaylorSpanGenerators : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T k : ℕ), k < a0 D j T → ∀ α ∈ mon D j k, ∀ i : Fin G.del,
    ∃ (x : ↥(HK X la G.w wF)) (cf : ↥(HK X la G.w wF)),
      toWK X la G.w wF (a0 D j T) x ∈ firstLength_le_prime_bound G la T ∧ x = ym G la α • cf ∧ toA0K X la G.w wF cf = tL G la i

def TaylorSpanLeBound : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    (∀ i, G.th' i ∈ B.Mlat j wF) → firstLength_le_prime_bound G la T ≤ Q.AA T

end PoleLengthBounds
end
end

