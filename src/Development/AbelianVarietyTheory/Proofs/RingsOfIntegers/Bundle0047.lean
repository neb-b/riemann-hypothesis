module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqOfSqEqOfOdd
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem eq_of_sq_eq_of_odd {U : Type} [CommGroup U] {r r' : U} {k : ℕ} (hk : Odd k) (h : r ^ 2 = r' ^ 2)
    (h₁ : r ^ k = 1) (h₂ : r' ^ k = 1) : r = r' := by
  obtain ⟨t, rfl⟩ := hk
  rw [pow_succ, pow_mul] at h₁ h₂
  rw [h] at h₁
  exact mul_left_cancel (h₁.trans h₂.symm)

theorem moves_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (e : Γ((ptO Xo x).left, ⊤)ˣ), a ^ k = 1 → b ^ k = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) a b e → ∃ r : S, toΓ S r ^ 2 = (e : Γ((ptO Xo x).left, ⊤)) ∧ r ^ k = 1 ∧ ∀ F F₁ F₂ F₃ : SecN Xo x k, Moves Xo b F F₁ → Moves Xo a F₁ F₂ → Moves Xo (a * b) F F₃ → (∀ j, F₂.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x) (toΓ S r) * F₃.f j) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b e ha hb he
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have ex : ∀ c : ptO Xo x ⟶ Xo.univ.t.G, c ^ k = 1 →
      ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x), SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k c U :=
    fun c hc => (symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) k hk
      (UnivPol.isUnit_natCast Xo _ hk.pos) (k : ℤ) rfl (ptO Xo x) c hc).1
  have hA := (moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨Ua, hUa⟩ := ex a ha
  obtain ⟨Ub, hUb⟩ := ex b hb
  obtain ⟨Uab, hUab⟩ := ex (a * b) (by rw [mul_pow, ha, hb, _root_.mul_one])
  obtain ⟨r₀, h₂, hp, -⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hUa hUb hUab he
  have bij : Function.Bijective (toΓ S) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv
  obtain ⟨r, hr⟩ := bij.2 (r₀ : Γ((ptO Xo x).left, ⊤))
  refine ⟨r, ?_, bij.1 ?_, ?_⟩
  · rw [hr, ← h₂]; exact (Units.val_pow_eq_pow_val r₀ 2).symm
  · rw [map_pow, map_one, hr]
    exact (Units.val_pow_eq_pow_val r₀ k).symm.trans (congrArg Units.val hp)
  · rintro F F₁ F₂ F₃ ⟨-, Vb, hVb, a₁⟩ ⟨-, Va, hVa, a₂⟩ ⟨-, Vab, hVab, a₃⟩ j
    obtain ⟨r₁, h₂', hp', h⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hVa hVb hVab he
    obtain rfl : r₁ = r₀ := eq_of_sq_eq_of_odd hk (h₂'.trans h₂.symm) hp' hp
    rw [hr]
    exact h F F₁ F₂ F₃ a₁ a₂ a₃ j

end GlobalTheory.PlaceInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqZeroOfComplex
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverRoot

theorem eq_zero_of_complex {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (r : p.R)
    (h : ∀ χ : p.R →ₐ[K] CAt σ, χ r = 0) : r = 0 := by
  refine ReciprocityTheory.ChartRestriction.G.TB.detAlg_holds K p.n p.I p.rad r fun L _ _ _ ψ => ?_
  letI : Algebra K ℂ := σ.toAlgebra
  let e : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h2 : e (ψ r) = 0 := h (e.comp ψ)
  exact (map_eq_zero_iff e e.injective).mp h2

theorem value_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ m₀ = 1 := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet h
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hnat := h.1.1
  refine ⟨Nat.card Cls, Nat.card_pos, fun k _ _ y₂ => ?_⟩
  obtain ⟨p, φ, y', hy⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ k y₂
  have key : d.cδ p y' ^ Nat.card Cls - 1 = 0 := by
    refine eq_zero_of_complex d.c₂.F.val.toRingHom p _ fun χ => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂ _ _ χ y'
    have e1 : evR d.Xo₂ d.c₂ d.cδ z = χ (d.cδ p y') :=
      ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p χ y' z hz
    have e2 := h.2 z
    rw [map_sub, map_pow, map_one, ← e1, e2, ← map_pow, if_neg (by simp), ← Units.val_pow_eq_pow_val, ← map_pow,
      pow_card_eq_one', map_one, Units.val_one, map_one, sub_self]
  have e3 : evR d.Xo₂ d.c₂ d.cδ y₂ = φ (d.cδ p y') :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p φ y' y₂ hy
  rw [e3, ← map_pow, sub_eq_zero.mp key, map_one]

end GlobalTheory.CoverRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsAdaptedSimilitudeDataAtPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.AdaptExists

theorem mem_std {E : Type} [Field E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = v i := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem single_mem {E : Type} [Field E] {n : ℕ} (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ stdLat E n := by
  rw [mem_std]
  intro i
  by_cases h : i = j
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem nat_smul_mem {E : Type} [Field E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (k : ℕ) {v : Fin n → E}
    (hv : v ∈ L) : (k : E) • v ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact L.toAddSubmonoid.nsmul_mem hv k

theorem exists_cols {E : Type} [Field E] {n : ℕ} (c : Fin n → Fin n → E) (hc : ∀ j, c j ∈ stdLat E n) :
    ∃ q : Matrix (Fin n) (Fin n) (𝓞 E), ∀ i j, algebraMap (𝓞 E) E (q i j) = c j i := by
  choose a ha using fun j => (mem_std (c j)).1 (hc j)
  exact ⟨Matrix.of fun i j => a j i, fun i j => ha j i⟩

theorem exists_adapt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n)
    (N M ℓ : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M) (hl : ℓ.Prime) :
    ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  obtain ⟨hodd, -, hN⟩ := hL
  have hN0 : 0 < N := hodd.pos
  have hm : 0 < 2 * ℓ := Nat.mul_pos two_pos hl.pos
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  obtain ⟨k₂, ga, hk₂, hun, hin, hon⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted E H n Λ N hU hN0 (hN.trans inf_le_left) (2 * ℓ) hm
  obtain ⟨k₁, g, hk₁, -, hcols, hsp⟩ := LocBasis.exists_matrix_primeTo E n Λ.Ln N hN0 inf_le_right hN (2 * ℓ) hm
  set G := g.map (algebraMap (𝓞 E) E) with hG
  have hNe : ∀ j : Fin n, (N : E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.Ln := by
    intro j
    have h := hN (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) (single_mem (E := E) j))
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  choose v hv hve using fun j => hsp _ (hNe j)
  obtain ⟨q, hq⟩ := exists_cols v hv
  obtain ⟨p, hp⟩ := exists_cols (fun j => (k₂ : E) • ga.mulVec (G.mulVec (Pi.single j 1)))
    (fun j => hin _ (hcols _ (single_mem j)).1)
  have hP : p.map (algebraMap (𝓞 E) E) = (k₂ : E) • (ga * G) := by
    ext i j
    rw [Matrix.map_apply, hp, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hGQ : G * q.map (algebraMap (𝓞 E) E) = ((k₁ * N : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h := congrFun (hve j) i
    simp only [Matrix.mul_apply, Matrix.map_apply, hq]
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h]
    simp [Matrix.one_apply, Pi.single_apply]
  have hprod : (p * q).map (algebraMap (𝓞 E) E) = ((k₁ * k₂ * N : ℕ) : E) • ga := by
    rw [Matrix.map_mul, hP, Matrix.smul_mul, Matrix.mul_assoc, hGQ, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    push_cast
    ring
  have hk : Nat.Coprime (k₁ * k₂) (2 * ℓ) := Nat.Coprime.mul_left hk₁ hk₂
  refine ⟨{
    k := k₁ * k₂, k₁ := k₁, ga := ga, p := p, q := q, g := g
    odd := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right hk)
    cop := Nat.Coprime.coprime_mul_left_right hk
    cop₁ := Nat.Coprime.coprime_mul_left_right hk₁
    unitary := hun
    into := ?_
    onto := ?_
    prod := hprod
    cols := hcols
    spans := hsp
    gq := ?_ }, ?_⟩
  · intro w hw
    rw [Nat.cast_mul, mul_smul]
    exact nat_smul_mem _ _ (hin w hw)
  · intro w hw
    obtain ⟨u, hu, e⟩ := hon w hw
    exact ⟨(k₁ : E) • u, nat_smul_mem _ _ hu, by rw [Nat.cast_mul, mul_smul, e, Matrix.mulVec_smul]⟩
  · apply Matrix.map_injective hinj
    show (g * q).map _ = Matrix.map _ _
    rw [Matrix.map_mul, hGQ]
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro j k
    apply hinj
    have he : ∀ a b, algebraMap (𝓞 E) E ((p * q) a b) = ((k₁ * k₂ * N : ℕ) : E) * ga a b :=
      fun a b => congrFun (congrFun hprod a) b
    have hb : ∀ a : 𝓞 E, algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq
    show algebraMap (𝓞 E) E (∑ i, H.bar ((p * q) i j) * (p * q) i k) =
      algebraMap (𝓞 E) E (if j = k then (((k₁ * k₂ * N) ^ 2 : ℕ) : 𝓞 E) else 0)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul (algebraMap (𝓞 E) E), hb, he, map_mul (IsCMField.complexConj E), map_natCast]
    have : ∀ i, ((k₁ * k₂ * N : ℕ) : E) * IsCMField.complexConj E (ga i j) * (((k₁ * k₂ * N : ℕ) : E) * ga i k) =
        ((k₁ * k₂ * N : ℕ) : E) ^ 2 * (IsCMField.complexConj E (ga i j) * ga i k) := fun i => by ring
    simp only [this]
    rw [← Finset.mul_sum, hun]
    split_ifs <;> simp

end GlobalTheory.PlaceInt.AdaptExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsThetaValData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.RatData

theorem epi_spMap_fields {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    rw [spMap, Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap i) := ⟨Function.surjective_to_subsingleton _⟩
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cancel_of_left_eq (Xo : Moduli Dw l) {K L : Type} [Field K] [Field L] {x : Sp K ⟶ Xo.X} {x' : Sp L ⟶ Xo.X}
    (i : K →+* L) (g : ptO Xo x' ⟶ ptO Xo x) (hg : g.left = spMap i) {a b : ptO Xo x ⟶ Xo.univ.t.G}
    (h : g ≫ a = g ≫ b) : a = b := by
  have := epi_spMap_fields i
  have h₁ := congrArg (fun f => f.left) h
  simp only [Over.comp_left, hg] at h₁
  ext1
  exact (cancel_epi (spMap i)).1 h₁

theorem descend (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ) (hx : AllRat Xo x M)
    {B : Type} [CommRing B] (φ : K →+* B) (hφ : φ.FaithfullyFlat) :
    ∃ (Ω : Type) (_ : Field Ω) (χ : B →+* Ω) (x' : Sp Ω ⟶ Xo.X) (g₁ : ptO Xo x' ⟶ ptO Xo (spMap φ ≫ x))
      (g₂ : ptO Xo x' ⟶ ptO Xo x), g₁.left = spMap χ ∧ g₂.left = spMap (χ.comp φ) ∧ g₂.left = g₁.left ≫ spMap φ ∧
      ∀ w : ptO Xo (spMap φ ≫ x) ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, g₂ ≫ a = g₁ ≫ w := by
  have : Nontrivial B := hφ.injective.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let χ : B →+* B ⧸ m := Ideal.Quotient.mk m
  have hc : spMap (χ.comp φ) = spMap χ ≫ spMap φ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let g₁ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo (spMap φ ≫ x) :=
    Over.homMk (spMap χ) (by
      change spMap χ ≫ spMap φ ≫ x = spMap (χ.comp φ) ≫ x
      rw [hc, Category.assoc])
  let g₂ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (χ.comp φ)) rfl
  refine ⟨B ⧸ m, inferInstance, χ, _, g₁, g₂, rfl, rfl, hc, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := hx (B ⧸ m) (χ.comp φ) (g₁ ≫ w) (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext ha.symm⟩

theorem exists_root (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (N : ℕ) (hN : 0 < N)
    (hx : AllRat Xo x (N ^ 2)) (t : ptO Xo x ⟶ Xo.univ.t.G) (ht : t ^ N = 1) : ∃ r, r ^ N = t := by
  obtain ⟨B, _, φ, w, hφ, hw⟩ := _root_.GlobalTheory.exists_faithfullyFlat_roots GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x N N hN hN Unit
    (fun _ => t) (fun _ => ht)
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, h₃, h₄⟩ := descend Xo x _ hx φ hφ
  let g : ptO Xo (spMap φ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap φ) rfl
  have hw' : w () ^ N = g ≫ t := Over.OverMorphism.ext (hw ())
  have hg : g₂ = g₁ ≫ g := Over.OverMorphism.ext h₃
  obtain ⟨a, ha⟩ := h₄ (w ()) (by rw [pow_two, pow_mul, hw', ← MonObj.comp_pow, ht, MonObj.comp_one])
  refine ⟨a, cancel_of_left_eq Xo _ g₂ h₂ ?_⟩
  rw [MonObj.comp_pow, ha, ← MonObj.comp_pow, hw', hg, Category.assoc]

theorem exists_linear_level (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (k : ℕ) (hk : 0 < k)
    (hx : AllRat Xo x k) : ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev (k • a) = 1) ∧
      ∀ a b, ev a = ev b → Dw.ModN k (a - b) := by
  obtain ⟨B, _, φ, ev, hφ, hadd, hsm, hkill, hinj⟩ := _root_.GlobalTheory.exists_faithfullyFlat_linear_level GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x k hk
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, -, h₄⟩ := descend Xo x _ hx φ hφ
  choose e he using fun a => h₄ (ev a) (by rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hkill])
  refine ⟨e, fun a b => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun o a => cancel_of_left_eq Xo _ g₂ h₂ ?_,
    fun a => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun a b hab => hinj Ω χ a b ?_⟩
  · rw [MonObj.comp_mul, he, he, he, hadd, MonObj.comp_mul]
  · rw [← Category.assoc, he, he, hsm, Category.assoc]
  · rw [he, hkill, MonObj.comp_one, MonObj.comp_one]
  · have h : g₁ ≫ ev a = g₁ ≫ ev b := by rw [← he, ← he, hab]
    have h' := congrArg (fun f => f.left) h
    simp only [Over.comp_left, h₁] at h'
    exact h'

theorem exists_thetaVal_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), (AllRat Xo y.x (l.M ^ 2) → ∀ x : Dw.La, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F) ∧ ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M → AllRat Xo y.x (N ^ 2) → ∃ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) := by
  intro E _ _ _ H Dw l Xo c K _ _ y
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := l.odd.pos
  have hlev : ∀ a : Dw.La, KilledBy Xo l.Mb (levPt Xo y.x a) ∧ levPt Xo y.x a ^ l.M = 1 := by
    intro a
    obtain ⟨h₁, -, h₃⟩ := moduli_univ_eta_killed hL E H Dw l Xo a
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [levPt, Category.assoc, h₁ b hb, MonObj.comp_one]
    · rw [levPt, ← MonObj.comp_pow, h₃, MonObj.comp_one]
  refine ⟨fun hx a => ?_, fun n Λ N hU hLev hx => ?_⟩
  · obtain ⟨v, hv⟩ := exists_root Xo y.x l.M hM hx _ (hlev a).2
    obtain ⟨t', ht', hk⟩ := (exists_root_killedBy_pow E H Dw l Xo _ _ v l.M hM (hlev a).1 hv).2 rfl
    refine (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1 _ _ t' ht' ?_ hk
    rw [pow_two, pow_mul, ht', (hlev a).2]
  · obtain ⟨hodd, hdvd, hle⟩ := hLev
    have hN : 0 < N := hodd.pos
    have hlevN : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
      intro a
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, (hlev a).2, one_pow]
    choose r hr using fun q : LevQ Dw l => exists_root Xo y.x N hN hx _ (hlevN (levRep q))
    choose t ht ht' using fun q =>
      (exists_root_killedBy_pow E H Dw l Xo _ _ _ N hN (hlev _).1 (hr q)).1
    have htN : ∀ q, t q ^ (N ^ 2) = 1 := fun q => by rw [pow_two, pow_mul, ht q, hlevN]
    obtain ⟨ev, hadd, hsm, hk, hinj⟩ := exists_linear_level Xo y.x (N ^ 2) (pow_pos hN 2) hx
    obtain ⟨zz, hz, hzi, -⟩ := _root_.GlobalTheory.ZCount.exists_class_representatives E H Dw n Λ N hU hN (hle.trans inf_le_left)
    have hZ : ∀ i, InZh Xo Λ N (fun b => ev (zz i b)) := by
      refine fun i => ⟨fun b => ?_, ?_⟩
      · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
      · intro mu hmu cm hcm i'
        obtain ⟨u, hu⟩ := hz i mu hmu cm hcm i'
        simp only [← hsm]
        rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd, hu]
        exact hk u
    choose F hF using fun (q : Fin n → LevQ Dw l) i b =>
      ((exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hodd _ y.s).2 (ev (zz i b)) (t (q b))
        ((hZ i).1 b) (htN _)).exists
    refine ⟨fun i b => ev (zz i b), fun q b => t (q b), F, hZ, ?_, fun q b => ⟨ht _, ht' _⟩, hF⟩
    intro k _ ψ g hg i i' hii
    exact hzi _ _ fun b => hinj _ _ (cancel_of_left_eq Xo ψ g hg (congrFun hii b))

end GlobalTheory.RatData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueCompatibleSectionExpansionIntegralFr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
namespace GlobalTheory

theorem tied_section_expansion_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ k : ℕ, 1 ≤ k → ∀ hh : SecN Xo xF k, (∃! σ, SecTieF I P F xF k σ hh) ∧ ∀ σ, SecTieF I P F xF k σ hh → ∃! s, P.U.toUnifPre.ExpandsG F k σ s := by
  intro E _ _ _ H Dw l Xo c T io y I P _ ϖ _ Q _ F _ _ _ _ _ v _ xF h hh k hk s
  have hx : xF = spMap (algebraMap T.Fr F) ≫ xOf y := by
    have := Over.w h
    rw [hh] at this
    exact this.symm
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  refine ⟨(GlobalTheory.T.powPullbackSec_modelUniversal_bijective E H Dw l Xo c T io y.1 I P F xF hx k).2.1 s, fun σ _ => ?_⟩
  exact (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 GlobalTheory.twistBaseChange T.V P.D P.A I.G.G P.U F k hk).1 σ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.SymMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem act_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    {θ θ' : ThetaGrp A L k T} (h : SymLift A L k n x θ) (h' : SymLift A L k n x θ')
    {s t t' : LB.Sec (LPow A L k T)} (a : IsActOf A L k θ s t) (a' : IsActOf A L k θ' s t') : t = t' := by
  have hc := SymLiftOdd.symLift_unique hG hA hL hn θ θ' h h'
  have e : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  have key : ∀ j, t.f j = t'.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (s := t) (s' := t')
      fun y J hJ => (twist_val a (𝟙 _) y hJ).trans (Eq.trans (congrArg₂ (· * ·)
        (congrArg Units.val (val_corr hJ hc (𝟙 _))) (by rw [e])) (twist_val a' (𝟙 _) y hJ).symm)
  obtain ⟨f₁, p₁⟩ := t
  obtain ⟨f₂, p₂⟩ := t'
  obtain rfl : f₁ = f₂ := funext key
  rfl

theorem exists_one (hL : L.IsLB) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (n : ℕ) (s : LB.Sec (LPow A L k T)) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n 1 θ ∧ IsActOf A L k θ s s := by
  obtain ⟨o, ho, vo⟩ := ThetaCoord.exists_symLift_one hL hν n
  refine ⟨o, ho, VVRank.isTwistPull_of_sv A hL o.isGen fun z J hJ => ?_⟩
  have e : translT A (1 : T ⟶ A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  change _ = (CommPairing.tval o (𝟙 _) z J).val * _
  rw [vo _ _ z J hJ, ho.pt_eq, e, Units.val_one, _root_.one_mul, Over.id_left]
  rfl

end GlobalTheory.SymMove

namespace GlobalTheory

theorem existsUnique_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (b : (ptO Xo x ⟶ Xo.univ.t.G)), b ^ k = 1 → ∀ F : SecN Xo x k, (∃! F' : SecN Xo x k, Moves Xo b F F') ∧ Moves Xo 1 F F := by
  intro E _ _ _ H Dw l Xo S _ x k hk b hb F
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have hA : IsAbelianScheme Xo.univ.t.G := (UnivPol.pol Xo).isAb
  have hL : Xo.univ.t.PP.L.IsLB := (UnivPol.pol Xo).isLB
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k b U :=
    exists_symLift_global hLaw Xo.X (UnivPol.pol Xo) k hk (UnivPol.isUnit_natCast Xo _ hk.pos) _ b hb
  obtain ⟨F', hF', -⟩ := existsUnique_isTwistPull _ _ _ hL _ (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _)
    k k U.φ U.isGen F
  obtain ⟨ν, hν, -⟩ := hU.sym
  refine ⟨⟨F', ⟨hb, U, hU, hF'⟩, fun F'' h => ?_⟩, one_pow k, SymMove.exists_one hL hν k F⟩
  obtain ⟨-, U', hU', a⟩ := h
  exact SymMove.act_unique hLaw.globalFns hA hL hk hU' hU a hF'

end GlobalTheory
end
end

