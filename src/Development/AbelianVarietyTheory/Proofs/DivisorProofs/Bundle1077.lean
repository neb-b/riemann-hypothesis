module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import GroundTheory.AutomorphicForms.GLnLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLine
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreLine

theorem cancel_left {O : Type} [CommRing O] {a b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => hA ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem cancel_left₂ {O : Type} [CommRing O] {a a' b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    {A' : Matrix (Fin a') (Fin b) O} (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) (h' : A' * X = A' * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  refine sub_eq_zero.mp (hA _ ?_ ?_)
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, sub_self]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', sub_self]

theorem solve {O : Type} [CommRing O] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) O) (B : Matrix (Fin a) (Fin c) O)
    (h : ∀ v, ∃ w, A *ᵥ w = B *ᵥ v) : ∃ S : Matrix (Fin b) (Fin c) O, B = A * S := by
  choose w hw using h
  refine ⟨Matrix.of fun i j => w (Pi.single j 1) i, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← hw]
  congr 1
  rw [Matrix.mulVec_single_one]
  rfl

theorem mkRep {Γ O : Type} [Group Γ] [CommRing O] {a a' m : ℕ} (A : Matrix (Fin a) (Fin m) O)
    (A' : Matrix (Fin a') (Fin m) O) (ρ : Γ →* GL (Fin a) O) (ρ' : Γ →* GL (Fin a') O)
    (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    (hst : ∀ g v, ∃ w, A *ᵥ w = (ρ g : Matrix (Fin a) (Fin a) O) *ᵥ (A *ᵥ v) ∧
      A' *ᵥ w = (ρ' g : Matrix (Fin a') (Fin a') O) *ᵥ (A' *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin m) O, Tw r' ρ A ∧ Tw r' ρ' A' := by
  choose w hw using hst
  let M : Γ → Matrix (Fin m) (Fin m) O := fun g => Matrix.of fun i j => w g (Pi.single j 1) i
  have hM : ∀ g j, M g *ᵥ Pi.single j 1 = w g (Pi.single j 1) := fun g j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have k1 : ∀ g, A * M g = (ρ g : Matrix (Fin a) (Fin a) O) * A := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).1]
  have k2 : ∀ g, A' * M g = (ρ' g : Matrix (Fin a') (Fin a') O) * A' := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).2]
  let f : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := M
      map_one' := cancel_left₂ hA (by rw [k1, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
        (by rw [k2, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left₂ hA
        (by rw [k1, ← Matrix.mul_assoc, k1, Matrix.mul_assoc, k1, ← Matrix.mul_assoc, map_mul, Units.val_mul])
        (by rw [k2, ← Matrix.mul_assoc, k2, Matrix.mul_assoc, k2, ← Matrix.mul_assoc, map_mul, Units.val_mul]) }
  refine ⟨f.toHomUnits, fun g => ?_, fun g => ?_⟩
  · rw [MonoidHom.coe_toHomUnits]
    exact k1 g
  · rw [MonoidHom.coe_toHomUnits]
    exact k2 g

theorem rank_map {O F : Type} [CommRing O] [Field F] (f : O →+* F) {a b : ℕ} (A : Matrix (Fin a) (Fin b) O)
    (B : Matrix (Fin b) (Fin a) O) (h : A * B = 1) : (A.map f).rank = a ∧ (B.map f).rank = a :=
  rank_of_mul_eq_one _ _ (by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)])

theorem fibre_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  intro Γ O _ _ _ _ n r χ Ac As ρc ρs x hAc hAs htc hts h1 h2 h3 h4
  let B : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (x i) (fun j => Ac i j) j
  let Cm : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ j => Fin.lastCases (1 : O) (fun _ => 0) j
  let E : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i j => if i = j.castSucc then 1 else 0
  let P : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (0 : O) (fun j => if i = j then 1 else 0) j
  let e : Matrix (Fin (n + 1)) (Fin 1) O := Matrix.of fun _ _ => 1
  have hB : ∀ v, B *ᵥ v = Ac *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • x := fun v => by
    funext i
    simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hC : ∀ v, Cm *ᵥ v = fun _ => v (Fin.last n) := fun v => by
    funext i
    simp [Cm, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hBs : ∀ (u : Fin n → O) (c : O), B *ᵥ (Fin.snoc u c : Fin (n + 1) → O) = Ac *ᵥ u + c • x := fun u c => by
    rw [hB]
    simp
  have hBE : B * E = Ac := by
    ext i k
    simp [B, E, Matrix.mul_apply]
  have hCE : Cm * E = 0 := by
    ext i k
    simp [Cm, E, Matrix.mul_apply]
  have hPE : P * E = 1 := by
    ext i k
    simp [P, E, Matrix.mul_apply, Matrix.one_apply]
  have hCe : Cm * e = 1 := by
    ext i k
    rw [Subsingleton.elim i k]
    simp [Cm, e, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hinj : ∀ v, B *ᵥ v = 0 → Cm *ᵥ v = 0 → v = 0 := fun v hb hc => by
    have hl : v (Fin.last n) = 0 := by
      rw [hC] at hc
      exact congrFun hc 0
    rw [hB, hl, zero_smul, add_zero] at hb
    have h0 : (fun j : Fin n => v j.castSucc) = 0 := hAc (by rw [hb, Matrix.mulVec_zero])
    funext j
    refine Fin.lastCases hl (fun j => congrFun h0 j) j
  have hr : ∀ g, (GlobalTheory.TripleGal.rk1 χ g : Matrix (Fin 1) (Fin 1) O) = Matrix.scalar (Fin 1) (χ g : O) := fun _ => rfl
  obtain ⟨r2, hr2B, hr2C⟩ := mkRep B Cm r (GlobalTheory.TripleGal.rk1 χ) hinj (fun g v => by
    obtain ⟨u, hu⟩ := h4 g
    have hu' : (r g : Matrix (Fin n) (Fin n) O) *ᵥ x = Ac *ᵥ u + (χ g : O) • x := by
      rw [hu]
      exact (sub_add_cancel _ _).symm
    refine ⟨Fin.snoc ((ρc g : Matrix (Fin n) (Fin n) O) *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • u)
      ((χ g : O) * v (Fin.last n)), ?_, ?_⟩
    · rw [hBs, hB, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htc g,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hu', smul_add, smul_smul, mul_comm, add_assoc]
    · rw [hC, hC, hr]
      funext i
      simp [Matrix.mulVec_diagonal])
  obtain ⟨B', hB'⟩ := solve As B (fun v => by
    obtain ⟨w0, hw0⟩ := h2
    obtain ⟨w1, hw1⟩ := h3 (fun j => v j.castSucc)
    exact ⟨w1 + v (Fin.last n) • w0, by rw [hB, Matrix.mulVec_add, Matrix.mulVec_smul, hw0, hw1]⟩)
  obtain ⟨S, hS⟩ := solve B' (1 : Matrix (Fin n) (Fin n) O) (fun v => by
    obtain ⟨u, c, huc⟩ := h1 v
    refine ⟨Fin.snoc u c, hAs ?_⟩
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hB', hBs, huc]
    rfl)
  refine ⟨r2, B, B', Cm, E, hr2B, fun g => cancel_left hAs ?_, hr2C, fun g => cancel_left₂ hinj ?_ ?_, hBE, hCE, hB',
    (rank_map _ P E hPE).2, (rank_map _ Cm e hCe).1, (rank_map _ B' S hS.symm).1, hinj⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hB', hr2B g, hts g, Matrix.mul_assoc, ← hB']
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBE, hr2B g, Matrix.mul_assoc, hBE, htc g]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCE, hr2C g, Matrix.mul_assoc, hCE, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.FibreLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReduction
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatSep

theorem nilp_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilp_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilp_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem exists_lt_pow (x B : WithZero (Multiplicative ℤ)) (hx : 1 < x) : ∃ m : ℕ, B < x ^ m := by
  obtain ⟨k, hk⟩ := MulArchimedean.arch B hx
  refine ⟨k + 1, hk.trans_lt ?_⟩
  have h0 : x ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))
  rw [pow_succ]
  simpa using mul_lt_mul_of_pos_left hx (zero_lt_iff.2 h0)

theorem integral_of_commute_sep : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ w n P₀ hP A s hA hAc hsA hBd i j
  obtain ⟨B, hB⟩ := hBd
  have memO : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E ↔ Valued.v x ≤ 1 :=
    fun x => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  by_contra hij
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨⟨i₀, j₀⟩, hmax⟩ := Finite.exists_max (fun p : Fin n × Fin n => Valued.v (s p.1 p.2))
  have hc1 : 1 < Valued.v (s i₀ j₀) := by
    have : 1 < Valued.v (s i j) := not_le.1 (fun h => hij ((memO _).2 h))
    exact this.trans_le (hmax (i, j))
  have hvc : Valued.v (s i₀ j₀) ≠ 0 := ne_of_gt (zero_lt_one.trans hc1)
  have hc0 : s i₀ j₀ ≠ 0 := fun h => hvc (by rw [h, map_zero])
  set c := s i₀ j₀ with hcdef
  set u := c⁻¹ • s with hudef
  have hu : ∀ k l, u k l ∈ w.adicCompletionIntegers E := by
    intro k l
    rw [memO]
    simp only [u, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvc), mul_one]
    exact hmax (k, l)
  let A₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨A k l, hA k l⟩
  let u₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨u k l, hu k l⟩
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hA₀ : A₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = A := by
    ext; rfl
  have hu₀ : u₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = u := by
    ext; rfl
  have hcomm : Commute A₀ u₀ := by
    apply Matrix.map_injective hinj
    show (A₀ * u₀).map _ = (u₀ * A₀).map _
    rw [Matrix.map_mul, Matrix.map_mul, hA₀, hu₀]
    exact ((hsA.smul_left c⁻¹).symm).eq
  have hcp : A₀.charpoly = P₀ := by
    apply Polynomial.map_injective _ hinj
    rw [← Matrix.charpoly_map, hA₀, hAc]
  obtain ⟨m, hm⟩ := exists_lt_pow (Valued.v c) B hc1
  have hsmall : ∀ k l, Valued.v ((u ^ m) k l) < 1 := by
    intro k l
    rw [hudef, _root_.smul_pow, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_inv₀, inv_pow,
      inv_mul_lt_iff₀ (pow_pos (zero_lt_iff.2 hvc) _), mul_one]
    exact (hB m k l).trans_lt hm
  have hnil : IsNilpotent (u₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))) := by
    refine ⟨m, ?_⟩
    rw [← Matrix.map_pow]
    ext k l
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨y, hy⟩
    have e : (((u₀ ^ m) k l : w.adicCompletionIntegers E) : w.adicCompletion E) = (u ^ m) k l := by
      rw [← hu₀, ← Matrix.map_pow]; rfl
    have h1 := hsmall k l
    rw [← e, ← hy] at h1
    have h2 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
      have hy1 : ((y : w.adicCompletionIntegers E) : w.adicCompletion E) *
          (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
        first
          | exact congrArg Subtype.val y.mul_inv
          | exact_mod_cast congrArg Subtype.val y.mul_inv
          | simp
      rw [← map_mul, hy1, map_one]
    have h3 := (memO _).1 (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E)).2
    have h4 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) h1
    rw [h2] at h4
    exact lt_irrefl _ h4
  have hsep : (A₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))).charpoly.Separable := by
    rw [Matrix.charpoly_map, hcp]
    exact Polynomial.Separable.map hP
  have h0 := nilp_eq_zero_of_commute_sep hsep hnil
    (hcomm.map (IsLocalRing.residue (w.adicCompletionIntegers E)).mapMatrix)
  have hone : u₀ i₀ j₀ = 1 := by
    apply Subtype.ext
    show c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc0
  have := congrFun (congrFun h0 i₀) j₀
  simp only [Matrix.map_apply, Matrix.zero_apply, hone, map_one] at this
  exact one_ne_zero this

end GlobalTheory.IntMatSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open ValuativeRel GroundTheory.Automorphic.GLnLocal
open scoped Pointwise

noncomputable section
namespace GlobalTheory.StabInt

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem mem_O_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ w.adicCompletionIntegers E := by
  show _ ↔ Valued.v x ≤ 1
  simp only [Valuation.mem_integer_iff]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := (Valuation.Compatible.vle_iff_le (v := Valued.v) x 1)
  rw [map_one] at h1
  rw [← h1]
  exact Iff.symm (Valuation.vle_one_iff (valuation (w.adicCompletion E)))

theorem mem_integralGL_of_mem_KGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    g ∈ integralGL (w.adicCompletion E) n := by
  obtain ⟨u, rfl⟩ := hg
  rw [mem_integralGL_iff]
  refine ⟨fun i j => (mem_O_iff _).2 (u i j).2, fun i j => (mem_O_iff _).2 ?_⟩
  rw [← map_inv]
  exact ((u⁻¹ : GL (Fin n) (Ov E w)) i j).2

theorem mem_KGL_of_mem_integralGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ integralGL (w.adicCompletion E) n) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  rw [mem_integralGL_iff] at hg
  have h1 : ∀ i j, g.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.1 i j)
  have h2 : ∀ i j, g⁻¹.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.2 i j)
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_integralGL_of_conj (N t g : GL (Fin n) (w.adicCompletion E))
    (hN : N ∈ integralGL (w.adicCompletion E) n)
    (hsep : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1)
    (htN : t * N = N * t) (ht' : g⁻¹ * t * g ∈ integralGL (w.adicCompletion E) n)
    (hN' : g⁻¹ * N * g ∈ integralGL (w.adicCompletion E) n) : t ∈ integralGL (w.adicCompletion E) n := by
  set F := w.adicCompletion E
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist F :=
    inferInstanceAs (@IsUltrametricDist F (Valued.toNormedField F (WithZero (Multiplicative ℤ))).toDist)
  have hO : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ 𝒪[F] := fun x =>
    (Valued.toNormedField.norm_le_one_iff).trans (mem_O_iff x).symm
  have hs : N.val.charpoly.Separable := by
    obtain ⟨u, v, -, -, h⟩ := hsep
    exact ⟨u, v, h⟩
  have hsep' : ∃ u v : Polynomial F, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.val.charpoly + v * Polynomial.derivative N.val.charpoly = 1 := by
    obtain ⟨u, v, hu, hv, h⟩ := hsep
    exact ⟨u, v, fun i => (hO _).2 ((mem_O_iff _).2 (hu i)), fun i => (hO _).2 ((mem_O_iff _).2 (hv i)), h⟩
  have hNi : ∀ i j, ‖N.val i j‖ ≤ 1 := fun i j => (hO _).2 ((mem_integralGL_iff F n).1 hN |>.1 i j)
  have hN'i : ∀ i j, ‖((g.val)⁻¹ * N.val * g.val) i j‖ ≤ 1 := by
    intro i j
    have := ((mem_integralGL_iff F n).1 hN').1 i j
    rw [← Matrix.coe_units_inv]
    exact (hO _).2 this
  obtain ⟨c, hcu, hcN, hy, hdet⟩ := GlobalTheory.IntConj.exists_commuting_mul_integral F n N.val g.val hNi hsep' g.isUnit hN'i
  set cU := hcu.unit with hcU
  have hcUv : (cU : Matrix (Fin n) (Fin n) F) = c := rfl
  have hcadj : c ∈ Algebra.adjoin F {N.val} := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N.val c hs hcN
  have htNv : Commute t.val N.val := by
    show t.val * N.val = N.val * t.val
    have := congrArg Units.val htN
    simpa [Units.val_mul] using this
  have htc : Commute t.val c := Algebra.commute_of_mem_adjoin_singleton_of_commute hcadj htNv
  have htcU : t * cU = cU * t := Units.ext (by simpa [Units.val_mul, hcUv] using htc.eq)
  set yU := cU⁻¹ * g with hyU
  have hyv : (yU : Matrix (Fin n) (Fin n) F) = c⁻¹ * g.val := by
    rw [hyU, Units.val_mul, Matrix.coe_units_inv, hcUv]
  have hyO : yU ∈ integralGL F n := by
    rw [mem_integralGL_iff]
    have h1 : ∀ i j, (yU : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := fun i j => by
      rw [hyv]; exact (hO _).1 (hy i j)
    refine ⟨h1, fun i j => ?_⟩
    let y₀ : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, h1 i j⟩
    have hy₀ : (RingHom.mapMatrix (𝒪[F]).subtype) y₀ = (yU : Matrix (Fin n) (Fin n) F) := rfl
    have hadj : ∀ i j, (yU : Matrix (Fin n) (Fin n) F).adjugate i j ∈ 𝒪[F] := fun i j => by
      rw [← hy₀, ← RingHom.map_adjugate]
      exact (y₀.adjugate i j).2
    have hd : ‖Ring.inverse (yU : Matrix (Fin n) (Fin n) F).det‖ ≤ 1 := by
      rw [Ring.inverse_eq_inv', norm_inv, hyv, hdet, inv_one]
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ((hO _).1 hd) (hadj i j)
  have e : t = yU * (g⁻¹ * t * g) * yU⁻¹ := by
    have e1 : cU⁻¹ * t * cU = t := by
      rw [mul_assoc, htcU, ← mul_assoc, inv_mul_cancel, one_mul]
    calc t = cU⁻¹ * t * cU := e1.symm
      _ = (cU⁻¹ * g) * (g⁻¹ * t * g) * (cU⁻¹ * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyO ht') (Subgroup.inv_mem _ hyO)

def pairGrp {G : Type} [Group G] (t N : G) (h : Commute t N) : Subgroup G where
  carrier := {x | ∃ a b : ℤ, x = t ^ a * N ^ b}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    rw [_root_.zpow_add, _root_.zpow_add, mul_assoc, mul_assoc, ← mul_assoc (N ^ b), (h.zpow_zpow c b).eq.symm, mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [_root_.mul_inv_rev, _root_.zpow_neg, _root_.zpow_neg]
    exact (h.zpow_zpow a b).inv_inv.eq.symm

theorem mem_KGL_of_commute : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ n w N t hN hsep htN htc
  set F := w.adicCompletion E
  have hNO : N ∈ integralGL F n := mem_integralGL_of_mem_KGL hN
  let H0 := pairGrp t N htN
  have hC : IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F))) :=
    htc.mul (isCompact_integralGL F n)
  have hsub : (H0 : Set (GL (Fin n) F)) ⊆
      closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) := by
    rintro _ ⟨a, b, rfl⟩
    exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers t a)) (Subgroup.zpow_mem _ hNO b)
  have hH : IsCompact (H0.topologicalClosure : Set (GL (Fin n) F)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  have ht' := hg t (H0.le_topologicalClosure ⟨1, 0, by simp⟩)
  have hN' := hg N (H0.le_topologicalClosure ⟨0, 1, by simp⟩)
  exact mem_KGL_of_mem_integralGL (mem_integralGL_of_conj N t g hNO hsep htN ht' hN')

end GlobalTheory.StabInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma

def intVec (K : UQ) (n : ℕ) : Submodule K.O (Fin n → K.E) where
  carrier := {v | ∀ i, v i ∈ (algebraMap K.O K.E).range}
  add_mem' := fun ha hb i => Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun _ => Subring.zero_mem _
  smul_mem' := fun c v hv i => by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv i)

def modelLat {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))
    (P : Matrix (Fin n) (Fin n) K.E) : Submodule K.O B.A :=
  (intVec K n).comap ((Matrix.toLin' P).restrictScalars K.O ∘ₗ ψ.toLinearMap.restrictScalars K.O)

def unitLat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} {K : UQ}
    (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (q : UL n w) :
    Submodule K.O B.A :=
  modelLat B ψ ((((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm)

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConjStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairWeight_invariant_form_group_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β), GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) = GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  first | (exact @GlobalTheory.CxUnfold.cxF_smul_conj_gen) | (exact GlobalTheory.CxUnfold.cxF_smul_conj_gen) | (intros; apply GlobalTheory.CxUnfold.cxF_smul_conj_gen  <;> assumption)
end

