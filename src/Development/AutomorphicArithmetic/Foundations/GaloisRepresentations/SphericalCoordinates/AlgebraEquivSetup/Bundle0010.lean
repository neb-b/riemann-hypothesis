module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def memFn {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X) : ℂ :=
  (Nat.card {k : K ⧸ KM.subgroupOf K // h * (k.out : X) * y ∈ K₀} : ℕ)

def MemSum : Prop := ∀ (X : Type) [Group X] (K KM K₀ : Subgroup X) (h : X), K₀ ≤ K → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) →
  memFn K KM K₀ h ∈ Hecke ℂ K₀ ∧ (∀ y, memFn K KM K₀ h y ≠ 0 → ∃ k ∈ K, h * k * y ∈ K₀) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K₀, ∀ g, Φ (g * k) = Φ g) → ∀ g,
    hAct K₀ (memFn K KM K₀ h) Φ g = ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹)

def SumDoset : Prop := ∀ (X : Type) [Group X] (K KM : Subgroup X) (h : X), KM ≤ K → KM.relIndex K ≠ 0 →
  (∀ u ∈ KM, h * u * h⁻¹ ∈ K) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) →
    (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ g,
    ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹) =
      ((KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) : ℂ) • hAct K (dosetInd ℂ K h⁻¹) Φ g

def TyLev.Acts {X M : Type} [Group X] [Group M] (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h : X) : Prop :=
  ψ ∈ Hecke ℂ T.K₀ ∧ T.L.pr h = 1 ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ → hAct T.K₀ ψ Φ = c • hAct T.K₀ (T.tf h) Φ

def TyLev.Triv {X M : Type} [Group X] [Group M] (T : TyLev X M) (K : Subgroup X) : Prop :=
  K ≤ T.K ∧ ∀ k ∈ K, ∀ h, T.ψ ⟨T.L.pr k, h⟩ = 1

def MemAct : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ K KM : Subgroup X, T.Triv K → L'.Fact K Kw → T.K₀ ≤ K → KM ≤ T.K₀ → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ (t : M') (z h : X), T.Cen z → h⁻¹ = L'.loc t * z →
  (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ T.K₀) →
  T.Acts (memFn K KM T.K₀ h) (KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) (L'.loc t * z)

def MemDeck : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (K : Subgroup X), T.Triv K → ∀ k ∈ K,
  (∀ u ∈ T.K₀, k * u * k⁻¹ ∈ T.K₀) → T.Acts (memFn T.K₀ T.K₀ T.K₀ k) 1 1

def RelOf : Prop := ∀ (X M J : Type) [Group X] [Group M] (T : TyLev X M) (ψ : J → X → ℂ) (c : J → ℂ) (h : J → X) (hu : X) (u' : X → ℂ),
  (∀ j, T.Acts (ψ j) (c j) (h j)) → T.L.pr hu = 1 → u' ∈ Hecke ℂ T.K₀ →
  (∀ i j, conv T.K₀ (T.tf (h i)) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf (h i))) →
  (∀ j, conv T.K₀ (T.tf hu) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf hu)) → conv T.K₀ u' (T.tf hu) = T.tf 1 →
  Spc.Rel (conv T.K₀) ψ (T.tf 1) (T.tf hu) u'

def SphComm : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (t t' : GL (Fin n) (w.adicCompletion E)),
  conv (KGL w (n := n)) (dosetInd ℂ (KGL w (n := n)) t) (dosetInd ℂ (KGL w (n := n)) t') = conv (KGL w (n := n)) (dosetInd ℂ (KGL w (n := n)) t') (dosetInd ℂ (KGL w (n := n)) t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

def Tr.lv (T : Tr S) (K : Subgroup (GUf E n)) : Subgroup S.G.GAf := K.comap T.sec

def AtApart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal),
  (∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x) ∧
  ∀ (w' : Plc E) (hw' : IsSplitAt w') (hp' : (p : 𝓞 E) ∉ w'.asIdeal), GlobalTheory.Cong.Apart w w' → (T.at hc w hw hp).Apart (T.at hc w' hw' hp')

def LevFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (S₀ : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E)))
  (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal), CertificateRingHomMap.cj w ∉ S₀ →
  (w ∈ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (Kw w)) ∧ (w ∉ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (KGL w (n := n)))

def IntConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E), 0 < n →
  (sim g ∈ ZU → comp w g ∈ KGL w (n := n) → comp (CertificateRingHomMap.cj w) g ∈ KGL (CertificateRingHomMap.cj w) (n := n)) ∧
  ((∀ u, comp u g ∈ KGL u (n := n)) → sim g ∈ ZU) ∧ {u : Plc E | comp u g ∉ KGL u (n := n)}.Finite

def KNOpen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsOpen (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n))

def KNIdx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsCommensurated (S.L.KN N) ∧ ∀ K : Subgroup (GUf E n), IsCompact (K : Set (GUf E n)) →
    IsOpen (K : Set (GUf E n)) → (S.L.KN N).relIndex (T.lv K) ≠ 0

def PPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n), ∃ k : GUf E n, g = T.sec (T.j g) * k ∧ (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) ∧
    (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k = comp w g) ∧ ∀ h, T.sec h * k = k * T.sec h

def HasEigOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (V : Type) [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (GL (Fin n) E × ℚˣ) V) (Φ : GUf E n → V),
  (∀ (γ : Gam0 E n) g, Φ (rat γ * g) = ξ γ (Φ g)) →
  (∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w (n := n)) →
    ∀ g, Φ (g * k) = Φ g) →
  (∃ g₀, Φ g₀ ≠ 0 ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g₀ ∈ KGL w (n := n)) →
  ∀ K₀ : Subgroup S.G.GAf, IsCommensurated K₀ → (∀ k ∈ K₀, ∀ h, Φ (T.sec (h * k)) = Φ (T.sec h)) →
  ∀ (J : Type) (ψ : J → S.G.GAf → ℂ) (θ : J → ℂ) (e : S.G.GAf → ℂ), (∀ j, ψ j ∈ Hecke ℂ K₀) → e ∈ Hecke ℂ K₀ →
    hAct K₀ e (fun h => Φ (T.sec h)) = (fun h => Φ (T.sec h)) →
    (∀ j, hAct K₀ (ψ j) (fun h => Φ (T.sec h)) = θ j • fun h => Φ (T.sec h)) →
  Spc.HasEig S.G (V := V) ξ K₀ ψ θ e

end UpperTheory.Gal.W2.Seed
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem exists_over (v : Plc ℚ) : ∃ w : Plc E, below ℚ w = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hQo.over.symm⟩

private theorem fam_inj : Function.Injective (finiteAdeleMap ℚ E) := by
  intro x y h
  refine FiniteAdeleRing.ext (K := ℚ) fun v => ?_
  obtain ⟨w, rfl⟩ := exists_over (E := E) v
  have h1 := congrArg (fun z : FiniteAdeleRing (𝓞 E) E => z w) h
  exact (GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w).injective h1

variable {n : ℕ}

private theorem mat_eq_of_comp {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : mat g = mat g' := by
  refine Units.ext (Matrix.ext fun i k => GlobalTheory.EulerTw.pLoc_ext E fun w => ?_)
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x.val i k) (h w)

private theorem sim_eq_of_mat (hn : 1 ≤ n) {g g' : GUf E n} (h : mat g = mat g') : sim g = sim g' := by
  have h1 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g.2
  have h2 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g'.2
  have h3 : (g : GL (Fin n) (Af E) × AfQˣ).1 = (g' : GL (Fin n) (Af E) × AfQˣ).1 := h
  rw [h3, h2] at h1
  have h4 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
  exact Units.ext (fam_inj h4.symm)

private theorem eq_of_comp (hn : 1 ≤ n) {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (mat_eq_of_comp h) (sim_eq_of_mat hn (mat_eq_of_comp h)))

private theorem map_eq_iff {p : ℕ} [Fact p.Prime] (T : AdT p E) (x y : GL (Fin n) (Af E)) :
    x.val.map T.Φ = y.val.map T.Φ ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y := by
  constructor
  · intro h w hw
    refine Units.ext (Matrix.ext fun i k => ?_)
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (congrFun (congrFun h i) k)
    have h2 := (T.Φ_ker _).1 h1 w hw
    rw [map_sub] at h2
    exact sub_eq_zero.1 h2
  · intro h
    refine Matrix.ext fun i k => ?_
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      refine (T.Φ_ker _).2 fun w hw => ?_
      rw [map_sub]
      exact sub_eq_zero.2 (congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i k) (h w hw))
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1

private theorem conj_comp_iff (a : GL (Fin n) (Af E)) (w : Plc E) (g g' : GUf E n) :
    GeneralLinearGroup.map (pLoc E w) (a * mat g * a⁻¹) = GeneralLinearGroup.map (pLoc E w) (a * mat g' * a⁻¹) ↔
      comp w g = comp w g' := by
  have e : ∀ h : GUf E n, GeneralLinearGroup.map (pLoc E w) (a * mat h * a⁻¹) =
      GeneralLinearGroup.map (pLoc E w) a * comp w h * (GeneralLinearGroup.map (pLoc E w) a)⁻¹ := fun h => by
    rw [map_mul, map_mul, map_inv]; rfl
  rw [e, e, mul_left_inj, mul_right_inj]

private theorem algMap_inj {p : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) (hμ : IsMu μ)
    {c c' : AfP p} (h : c ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) = c' ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) : c = c' := by
  have h1 := congrFun (congrFun (congrArg μ h) ⟨0, hn⟩) ⟨0, hn⟩
  rw [hμ, hμ, Matrix.one_apply_eq] at h1
  exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := AfP p) (B := E)
    (algebraMap ℚ E).injective h1

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pJEq :
    JEq := by
  intro E _ _ _ A n p _ S T μ hμ a j hj
  refine ⟨fun g g' h => eq_of_comp S.facts.pos h, fun g g' => ?_⟩
  have key : S.mx (j g) = S.mx (j g') ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g' := by
    rw [← μ.injective.eq_iff, hj, hj, map_eq_iff]
    exact forall₂_congr fun w _ => conj_comp_iff a w g g'
  rw [← key]
  refine ⟨fun h => congrArg S.mx h, fun h => ?_⟩
  have h1 : (((j g : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1) = ((j g' : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 := Units.ext h
  refine Subtype.ext (Prod.ext h1 (Units.ext ?_))
  have e1 := mem_uGroup.1 (j g).2
  have e2 := mem_uGroup.1 (j g').2
  rw [h1, e2] at e1
  exact algMap_inj S.facts.pos μ hμ e1.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MuAlgebraMap
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private theorem mu_algebraMap {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ) (r : R) :
    μ (algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r) =
      (r ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) := by
  ext i k
  have h : algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r = r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) := rfl
  rw [h, hμ r 1 i k]
  by_cases hik : i = k
  · subst hik; simp
  · simp [Matrix.one_apply, hik]

private theorem conj_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ} (D : Matrix (Fin n) (Fin n) K)
    (a g : GL (Fin n) K) (c : K) (ha : (a.val.map σ)ᵀ * D * a.val = 1)
    (hg : (g.val.map σ)ᵀ * g.val = c • (1 : Matrix (Fin n) (Fin n) K)) :
    ((a * g * a⁻¹).val.map σ)ᵀ * D * (a * g * a⁻¹).val = c • D := by
  set b : Matrix (Fin n) (Fin n) K := ((a⁻¹).val.map σ)ᵀ with hb
  have h1 : (a.val.map σ)ᵀ * b = 1 := by
    rw [hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have h1' : b * (a.val.map σ)ᵀ = 1 := by
    rw [hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hD : D = b * (a⁻¹).val := by
    calc D = (b * (a.val.map σ)ᵀ) * D * (a.val * (a⁻¹).val) := by rw [h1', Units.mul_inv]; simp
      _ = b * ((a.val.map σ)ᵀ * D * a.val) * (a⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = b * (a⁻¹).val := by rw [ha, Matrix.mul_one]
  have e : ((a * g * a⁻¹).val.map σ)ᵀ = b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ := by
    simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, hb, Matrix.mul_assoc]
  rw [e]
  calc b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ * D * (a * g * a⁻¹).val
      = b * (g.val.map σ)ᵀ * ((a.val.map σ)ᵀ * D * a.val) * g.val * (a⁻¹).val := by
        simp only [Units.val_mul, Matrix.mul_assoc]
    _ = b * ((g.val.map σ)ᵀ * g.val) * (a⁻¹).val := by
        rw [ha, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = c • D := by
        rw [hg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hD]

private theorem key {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E]
    (hst : MuStar) (A : Arith E) {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (u : (R ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) (s : R)
    (h : ((μ u).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ u =
      (s ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))) :
    (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * (starT (hermStar (A.H n) (A.det_ne n)) R u).unop =
      algebraMap R _ s := by
  set x' := (starT (hermStar (A.H n) (A.det_ne n)) R (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop with hx'
  have h1 := hst R E A n μ hμ u
  have hne : ∀ i, ((A.dg n i : 𝓞 E) : E) ≠ 0 := fun i => by
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this]
  have hDi : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) *
      Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have : ∀ i, ((A.dg n i : E))⁻¹ * (A.dg n i : E) = 1 := fun i => inv_mul_cancel₀ (hne i)
    simp only [this]
    exact Matrix.diagonal_one
  have h2 : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * (μ x' * μ u) =
      Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * ((s ⊗ₜ[ℚ] (1 : E)) • 1) := by
    rw [← Matrix.mul_assoc, h1, h, Matrix.mul_smul, Matrix.mul_one]
  have h3 : μ x' * μ u = (s ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) := by
    have := congrArg (fun M => Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) * M) h2
    simpa only [← Matrix.mul_assoc, hDi, Matrix.one_mul] using this
  have h4 : x' * (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) = algebraMap R _ s :=
    μ.injective (by rw [map_mul, h3, mu_algebraMap μ hμ])
  calc (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * x'
      = u * (x' * u) * (↑u⁻¹ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = algebraMap R _ s := by
        rw [h4, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem pJEx :
    MuStar → JEx := by
  intro hst E _ _ _ A n p _ S T μ hμ a ha
  let m : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) :=
    { toFun := fun g => μ.symm ((a * mat g * a⁻¹).val.map T.Φ)
      map_one' := by
        simp only [map_one, mul_one, mul_inv_cancel, Units.val_one]
        rw [Matrix.map_one _ (map_zero _) (map_one _), map_one]
      map_mul' := fun g h => by
        rw [← map_mul, ← Matrix.map_mul]
        congr 2
        simp only [map_mul, Units.val_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left] }
  have hm : ∀ g, μ (m g) = (a * mat g * a⁻¹).val.map T.Φ := fun g => μ.apply_symm_apply _
  let f₁ : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ := m.toHomUnits
  let f₂ : GUf E n →* (AfP p)ˣ := (Units.map (T.ρ : AfQ →* AfP p)).comp sim
  have mem : ∀ g, (f₁.prod f₂) g ∈ UPts (hermStar (A.H n) (A.det_ne n)) (AfP p) := by
    intro g
    show ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) *
        (starT (hermStar (A.H n) (A.det_ne n)) (AfP p)
          ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop =
      algebraMap (AfP p) _ (T.ρ (sim g : AfQˣ))
    apply key hst A μ hμ
    have hf : μ ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) =
      (a * mat g * a⁻¹).val.map T.Φ := hm g
    rw [hf]
    have h0 := conj_form (conjFin (conjE E)) (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))) a (mat g)
      (finiteAdeleMap ℚ E (sim g : AfQˣ)) ha.1 g.2
    have h1 := congrArg (fun M => M.map T.Φ) h0
    have e1 : ((((a * mat g * a⁻¹).val.map (conjFin (conjE E)))ᵀ).map T.Φ) =
        (((a * mat g * a⁻¹).val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
      ext i k
      exact T.Φ_conj _
    have e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
        Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      exact T.Φ_E _
    have e3 : (finiteAdeleMap ℚ E (sim g : AfQˣ) •
        Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
        (T.ρ (sim g : AfQˣ) ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
      rw [← e2]
      ext i k
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, T.Φ_Q]
    simp only [Matrix.map_mul] at h1
    rw [e1, e2, e3] at h1
    exact h1
  refine ⟨MonoidHom.codRestrict (f₁.prod f₂) (UPts S.G.star (AfP p)) mem, ?_, ?_⟩
  · intro g
    exact hm g
  · intro g
    rfl

end UpperTheory.Gal.W2.Seed
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MuHomSingle
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

variable (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ)

private def muHom : R ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) (R ⊗[ℚ] E) :=
  Algebra.TensorProduct.lift
    (((Algebra.ofId (R ⊗[ℚ] E) (Matrix (Fin n) (Fin n) (R ⊗[ℚ] E))).restrictScalars ℚ).comp
      Algebra.TensorProduct.includeLeft)
    (AlgHom.mapMatrix Algebra.TensorProduct.includeRight)
    (fun r x => Algebra.commutes _ _)

private theorem muHom_tmul (r : R) (x : Matrix (Fin n) (Fin n) E) (i k : Fin n) :
    muHom R E n (r ⊗ₜ x) i k = r ⊗ₜ x i k := by
  have h : muHom R E n (r ⊗ₜ x) =
      algebraMap (R ⊗[ℚ] E) (Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (r ⊗ₜ 1) *
        x.map (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] R ⊗[ℚ] E) :=
    Algebra.TensorProduct.lift_tmul _ _ _ r x
  rw [h, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_apply, Matrix.map_apply]
  simp

private def muInv (M : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : R ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ∑ i, ∑ k, LinearMap.lTensor R (Matrix.singleLinearMap ℚ i k) (M i k)

private theorem muInv_add (M N : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) :
    muInv R E n (M + N) = muInv R E n M + muInv R E n N := by
  simp [muInv, Matrix.add_apply, map_add (f := _), Finset.sum_add_distrib]

private theorem muInv_muHom (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    muInv R E n (muHom R E n y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [muInv]
  | add a b ha hb =>
    rw [map_add (f := _), muInv_add, ha, hb]
  | tmul r x =>
    simp only [muInv, muHom_tmul, LinearMap.lTensor_tmul, Matrix.singleLinearMap_apply]
    simp only [← TensorProduct.tmul_sum]
    rw [← Matrix.matrix_eq_sum_single x]

private theorem muHom_single (i k : Fin n) (b : R ⊗[ℚ] E) :
    muHom R E n (LinearMap.lTensor R (Matrix.singleLinearMap ℚ i k) b) = Matrix.single i k b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.single_add]
  | tmul r x =>
    ext a c
    rw [LinearMap.lTensor_tmul, muHom_tmul, Matrix.singleLinearMap_apply]
    by_cases h : i = a ∧ k = c
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto), Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
      simp

private theorem muHom_muInv (M : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) :
    muHom R E n (muInv R E n M) = M := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [muInv, map_sum, muHom_single]
  exact (Matrix.matrix_eq_sum_single M).symm

private def muEquiv : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E) where
  toFun := muHom R E n
  invFun := muInv R E n
  left_inv := muInv_muHom R E n
  right_inv := muHom_muInv R E n
  map_mul' := map_mul _
  map_add' := map_add _

end UpperTheory.Gal.W2.Seed

end

theorem UpperTheory.Gal.W2.Seed.pMuEx :
    MuEx := by
  intro R E _ _ _ _ n
  exact ⟨muEquiv R E n, fun r x i k => muHom_tmul R E n r x i k⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemP
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below finiteAdeleMap_apply)

theorem UpperTheory.Gal.W2.Seed.pIdemP :
    IdemP := by
  classical
  intro p _ E _ _
  let e : AfQ := ⟨fun v => if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      by_cases h : (p : 𝓞 ℚ) ∈ v.asIdeal
      · simpa [h] using one_mem (v.adicCompletionIntegers ℚ)
      · simpa [h] using zero_mem (v.adicCompletionIntegers ℚ)⟩
  have he : ∀ v : Plc ℚ, e v = if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun v => rfl
  refine ⟨e, fun v => ⟨fun h => by rw [he, if_pos h], fun h => by rw [he, if_neg h]⟩, fun w => ?_⟩
  have hiff : (p : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
    show (p : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hl : pLoc E w (finiteAdeleMap ℚ E e) =
      GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hl, he, if_pos (hiff.2 h), map_one]
  · rw [hl, he, if_neg (fun h' => h (hiff.1 h')), map_zero]
end

