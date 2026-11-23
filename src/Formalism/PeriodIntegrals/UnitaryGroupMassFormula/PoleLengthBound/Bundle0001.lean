module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.GradedCoef

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AALeAAp
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem AA_le_AAp' (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ)
    (m : PtsG G la → ℕ) : Q.AA T ≤ Q.AAp T m := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun β hβ ζ => le_trans (WithTop.coe_le_coe.2 ?_) (hb β hβ ζ)⟩
  dsimp only
  omega

theorem bound (hF : FiltStep) (hM : MonCount) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (Q : LocalPointData G la) (T : ℕ) (m : PtsG G la → ℕ)
    (h1 : FiltOk G la T) (h2 : GradedCoef G la Q T m) (h3 : PiBallLen G la Q m) :
    Module.length (Op X la G.N) (↥(Q.AAp T m) ⧸ (Q.AA T).comap (Q.AAp T m).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by
  obtain ⟨ψ, hker, hP, hQ⟩ := h2
  refine (hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) h1.1 h1.2.1 h1.2.2
    (fun k => Vk G la k) ψ hker (Q.AAp T m) (Q.AA T) (fun k => Pk G la Q m k) (fun k => Qk G la Q k)
    (AA_le_AAp' G la Q T m) hP hQ).trans ?_
  refine (Finset.sum_le_sum (fun k _ => (h3 k).le)).trans ?_
  rw [← Nat.cast_sum, Nat.cast_le, ← Finset.sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  by_cases hT : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ hT]
  · rw [show a0 D j T = 0 from by simp only [a0]; omega]
    simp

theorem target (hF : FiltStep) (hM : MonCount) (hS : Steps) : PI.LengthPoleInLift := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  obtain ⟨h1, h2, h3⟩ := hS G la Q S CRm T e c hOk hw hL
  exact bound hF hM G la Q T _ h1 h2 h3

end PI.PoleLengthCount
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AssembleAlt
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def yPow (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} (w : Fin N → B.Cusp j wL)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) : ↥(Frac0 X la w) :=
  ∏ i, sfr X la w i.succ ^ α i

def colIdx (D : D7) (j : ℕ) {N : ℕ} (col : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) : Idx D j N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2 = col then Fin.cases (motive := fun _ => ℕ) 0 α p.1 else 0

def rD (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (β : Idx D j G.N →₀ ℕ) (x : ↥(HK X la G.w wF)) :
    SectionSheafQuotient X la G.w wF := by
  classical
  exact if h : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF then toA0K X la G.w wF ⟨_, h⟩ else 0

def uSpec (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (u : Fin G.N → OsK X la G.w) : Prop :=
  ∀ col, ∃ f : ↥(Frac0 X la G.w),
    (f : Lw X la G.w) = algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wL (G.w col))) * w0inv X la G.w ∧
    toOsK X la G.w f = u col

def HKPres (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (β : Idx D j G.N →₀ ℕ) (x : Lw X la G.w), x ∈ HK X la G.w wF → hasse X la G.w β x ∈ HK X la G.w wF

def Vanish (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (k : ℕ) (β : Idx D j G.N →₀ ℕ) (x : ↥(HK X la G.w wF)),
    x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) →
    (β.sum fun _ n => n) < k → rD G la β x = 0

def UnitCols (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∃ u : Fin G.N → OsK X la G.w, uSpec G la u ∧
    (∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) * u col = 1) ∧
    ∀ (ζ : PtsG G la) (col : Fin G.N), 0 ≤ ord (unifO X la G.N) ζ (u col)

def Taylor (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (k : ℕ) (x : ↥(HK X la G.w wF)),
    x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) →
    ∃ (cf : Mon (WeightFamilies.dimY D j) k → ↥(HK X la G.w wF)) (r : ↥(HK X la G.w wF)),
      r ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) ∧
      x = ∑ α, yPow X la G.w α.1 • cf α + r

def ColDeriv (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ u : Fin G.N → OsK X la G.w, uSpec G la u →
    ∀ (k : ℕ) (α α' : Mon (WeightFamilies.dimY D j) k) (col : Fin G.N) (cf : ↥(HK X la G.w wF)),
      rD G la (colIdx D j col α'.1) (yPow X la G.w α.1 • cf) =
        if α = α' then u col ^ k • toA0K X la G.w wF cf else 0

def LinOp (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (k : ℕ) (β : Idx D j G.N →₀ ℕ) (r : Op X la G.N) (x : ↥(HK X la G.w wF)),
    x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) →
    (β.sum fun _ n => n) ≤ k → rD G la β (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ r • x) = r • rD G la β x

def LiftMul (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ) : Prop :=
  ∀ (x : ↥(HK X la G.w wF)) (α : Fin (WeightFamilies.dimY D j) → ℕ),
    toWK X la G.w wF (a0 D j T) x ∈ Q.AA T → toWK X la G.w wF (a0 D j T) (yPow X la G.w α • x) ∈ Q.AA T

def Assemble : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) → Q.InLift T →
    HKPres G la → Vanish G la → UnitCols G la → Taylor G la → ColDeriv G la → LinOp G la → LiftMul G la Q T →
    GradedCoef G la Q T (Q.mm S T e)

end PI.PoleLengthCount
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.FiltOk
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem image_filtration_decreasing (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T : ℕ) : FiltOk G la T := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    unfold Fk
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)))
  · unfold Fk
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ,
      (toWK_surjective X la G.w wF _).range_eq, Submodule.span_univ]
  · unfold Fk
    rw [eq_bot_iff, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    exact (toWK_eq_zero_iff X la G.w wF _ x).2 hx

end PI.PoleLengthCount
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

def PiLen : Prop :=
  ∀ (R M ι : Type) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (P Q : Submodule R M), Q ≤ P →
    Module.length R (↥(Submodule.pi Set.univ fun _ : ι => P) ⧸
        (Submodule.pi Set.univ fun _ : ι => Q).comap (Submodule.pi Set.univ fun _ : ι => P).subtype) =
      (Fintype.card ι : ℕ∞) * Module.length R (↥P ⧸ Q.comap P.subtype)

def BallQuot : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    ∀ (V : Type) [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V] [Module O V]
      [IsScalarTower O A V] (e : V), IsGen A e → ∀ (c : Pts O A → ℤ) (m : Pts O A → ℕ),
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ᶠ ζ : Pts O A, m ζ * fdeg ζ : ℕ) : ℕ∞)

def PiBallFrom : Prop :=
  PiLen → BallQuot →
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → PiBallLen G la Q (Q.mm S T e)

end PI.PoleLengthCount
end
end

