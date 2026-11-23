module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import GroundTheory.AutomorphicForms.FourierWhittaker
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRaisingWordMemSpanHigherWords
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.compactRaise_word_higher : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (w : V) (c d : Fin n), c < d → ε c = ε d → E c d w = 0 → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → E c d ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) ∈ Submodule.span ℂ {y : V | ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum < (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧ y = (l'.map fun p : Fin n × Fin n => E p.1 p.2).prod w} := by
  intro n ε V _ _ E hG w c d hcd hεcd hw s t l
  induction l with
  | nil =>
    intro _
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply, hw]
    exact Submodule.zero_mem _
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    intro hl
    have hab : ε a = s ∧ ε b = t := hl (a, b) List.mem_cons_self
    have hl' : ∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have IH := ih hl'
    have hcd' : (c : ℕ) < (d : ℕ) := hcd
    set y := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w with hy
    have hword : ((( (a, b) :: l).map fun p : Fin n × Fin n => E p.1 p.2).prod w) = E a b y := by
      simp [hy, Module.End.mul_apply]
    rw [hword]
    have key : E c d (E a b y) = E a b (E c d y) +
        ((if d = a then E c b else 0) - (if b = c then E a d else 0)) y := by
      have h := congrArg (fun f : Module.End ℂ V => f y) (hG c d a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      rw [LinearMap.sub_apply, ← h]; abel
    rw [key]
    refine Submodule.add_mem _ ?_ ?_
    · have hm : E a b (E c d y) ∈ (Submodule.span ℂ _).map (E a b) := Submodule.mem_map_of_mem IH
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨z, ⟨l', hlen, hty, hh, rfl⟩, rfl⟩
      refine ⟨(a, b) :: l', by simp [hlen], ?_, ?_, by simp [Module.End.mul_apply]⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        exacts [hab, hty p hp]
      · simp only [List.map_cons, List.sum_cons]; linarith
    · rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with h1
        · subst h1
          refine Submodule.subset_span ⟨(c, b) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            exacts [⟨hεcd.trans hab.1, hab.2⟩, hl' p hp]
          · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [LinearMap.zero_apply]; exact Submodule.zero_mem _
      · split_ifs with h2
        · subst h2
          refine Submodule.subset_span ⟨(a, d) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            exacts [⟨hab.1, hεcd.symm.trans hab.2⟩, hl' p hp]
          · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [LinearMap.zero_apply]; exact Submodule.zero_mem _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjEqNegOfSqEqNegNat
section
set_option autoImplicit false

namespace GlobalTheory.ConjugateNegativeSquare

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h0 : z.re = 0 := by
    by_contra hne
    have hi : z.im = 0 := by
      have h2 : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hne
    rw [hi] at hre
    have hpos : 0 < z.re * z.re := mul_self_pos.2 hne
    linarith
  apply Complex.ext
  · simp [h0]
  · simp

theorem conjugate_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (σ : E →+* ℂ) :
    (ComplexEmbedding.conjugate σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) =
      -(σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  obtain ⟨d, _, _, rt, hrt, _, _, _, _, _, _, _⟩ := H
  change ComplexEmbedding.conjugate σ (rt : E) = -σ (rt : E)
  rw [ComplexEmbedding.conjugate_coe_eq]
  apply conj_eq_neg_of_sq_eq_neg_nat _ d
  have h1 : (rt : E) ^ 2 = -(d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hrt
    simpa using this
  rw [← map_pow, h1, map_neg, map_natCast]

end GlobalTheory.ConjugateNegativeSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBlockUpperUnipotentRadical
section
open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem blockUni_conj_mem (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ)
    (e : ι ≃ Fin a ⊕ Fin b) :
    ∀ p ∈ GlobalTheory.OrbDesc.blockPar (K := K) e, ∀ n ∈ GlobalTheory.OrbDesc.blockUni e,
      p * n * p⁻¹ ∈ GlobalTheory.OrbDesc.blockUni e := by
  intro p hp n hn
  obtain ⟨x, rfl⟩ := hn
  have hre : ∀ M N : Matrix ι ι K,
      Matrix.reindex e e (M * N) = Matrix.reindex e e M * Matrix.reindex e e N := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have h21 : ∀ g ∈ blockPar (K := K) e, (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₁ = 0 := by
    intro g hg
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    apply hg
    simp [side]
  set P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := Matrix.reindex e e (p : Matrix ι ι K) with hP
  set Q : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K :=
    Matrix.reindex e e ((p⁻¹ : GL ι K) : Matrix ι ι K) with hQ
  have hP21 : P.toBlocks₂₁ = 0 := h21 p hp
  have hQ21 : Q.toBlocks₂₁ = 0 := h21 _ (Subgroup.inv_mem _ hp)
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← hre, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp
  refine ⟨Multiplicative.ofAdd (fun i j => (P.toBlocks₁₁ * Matrix.of x.toAdd * Q.toBlocks₂₂) i j), ?_⟩
  apply Units.ext
  apply (Matrix.reindex e e).injective
  show Matrix.reindex e e (uMat e _) = Matrix.reindex e e ((p : Matrix ι ι K) * uMat e x.toAdd * ((p⁻¹ : GL ι K) : Matrix ι ι K))
  rw [hre, hre, ← hP, ← hQ]
  have hU : ∀ Y : Fin a → Fin b → K, Matrix.reindex e e (uMat e Y) = Matrix.fromBlocks 1 (Matrix.of Y) 0 1 := by
    intro Y
    simp [uMat]
  rw [hU, hU]
  rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q] at hPQ ⊢
  rw [hP21, hQ21] at hPQ ⊢
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hPQ
  obtain ⟨h11, h12, -, h22⟩ := hPQ
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add] at h11 h12 h22 ⊢
  rw [h11, h22]
  congr 1
  have key : P.toBlocks₁₁ * Q.toBlocks₁₂ + (P.toBlocks₁₁ * Matrix.of x.toAdd + P.toBlocks₁₂) * Q.toBlocks₂₂
      = P.toBlocks₁₁ * Matrix.of x.toAdd * Q.toBlocks₂₂ := by
    rw [Matrix.add_mul, ← add_assoc, add_comm (P.toBlocks₁₁ * Q.toBlocks₁₂), add_assoc, h12, add_zero]
  rw [key]
  ext i j
  simp

end GlobalTheory.OrbDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.PairConj

section Generic

variable {S : Type*} [Ring S]

theorem unop_mul_inv (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

theorem unop_inv_mul (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ ((y⁻¹ : Sˣ) : S)).unop * (σ (y : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem triv_conj (σ : S →+* Sᵐᵒᵖ) (b : S) (x y : Sˣ) :
    ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop =
      (x : S) * b * (σ (x : S)).unop := by
  have h := unop_mul_inv σ y
  calc ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop
      = (x : S) * (((y⁻¹ : Sˣ) : S) * y) * b * ((σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop) *
          (σ (x : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h, mul_one, mul_one]

end Generic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

def shU (y : G.Cˣ) : G.Cˣ :=
  ⟨sh G y, sh G ((y⁻¹ : G.Cˣ) : G.C), unop_mul_inv G.star y, unop_inv_mul G.star y⟩

theorem shU_val (y : G.Cˣ) : ((shU G y : G.Cˣ) : G.C) = sh G y := rfl

def conjAlg (y : G.Cˣ) : G.C →ₐ[G.F] G.C where
  toFun a := y * a * ((y⁻¹ : G.Cˣ) : G.C)
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by
    show (y : G.C) * algebraMap G.F G.C r * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C r
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem conjAlg_injective (y : G.Cˣ) : Function.Injective (conjAlg G y) := by
  intro a b h
  have h' : (y : G.C) * a * ((y⁻¹ : G.Cˣ) : G.C) = y * b * ((y⁻¹ : G.Cˣ) : G.C) := h
  have := congrArg (fun z => ((y⁻¹ : G.Cˣ) : G.C) * z * (y : G.C)) h'
  simpa [mul_assoc] using this

variable {G} in
theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm


variable {G} in
theorem triv_conj_unit (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ)
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]
    rfl
  rw [e, triv_conj, hx]

variable {G}

theorem conj_val (β y : G.Cˣ) : ((y * β * shU G y : G.Cˣ) : G.C) = (y : G.C) * β * sh G y := by
  rw [Units.val_mul, Units.val_mul, shU_val]

def conjPair (P : Pair G) (y : G.Cˣ) : Pair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  trivR := by
    obtain ⟨z, hz⟩ := P.trivR
    have h := triv_conj_unit ℝ (P.β : G.C) y z 1 hz
    rw [← conj_val] at h
    exact ⟨_, h⟩

theorem conjPair_β (P : Pair G) (y : G.Cˣ) :
    (((conjPair P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

end GlobalTheory.LKMid.PairConj


open GlobalTheory.LKMid.PairConj in
theorem GlobalTheory.LKMid.Pair.exists_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (y : G.Cˣ),
    ∃ P' : Pair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  intro p _ G P y
  refine ⟨conjPair P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjPair_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjPair_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothForm
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology

namespace GlobalTheory.ConstTermZalg

open GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem good_add {φ ψ : Sm E a} (hφ : Good φ) (hψ : Good ψ) : Good (φ + ψ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1, hψ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      (Filter.inter_mem (hφ.2.mem_nhds (by simp)) (hψ.2.mem_nhds (by simp))) fun k hk => ?_)
    obtain ⟨h1, h2⟩ := hk
    have h1' : finRep E a k φ = φ := h1
    have h2' : finRep E a k ψ = ψ := h2
    show finRep E a k (φ + ψ) = φ + ψ
    rw [map_add (f := _), h1', h2']

theorem good_smul {φ : Sm E a} (hφ : Good φ) (s : ℂ) : Good (s • φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hφ.2.mem_nhds (by simp)) fun k hk => ?_)
    have h1' : finRep E a k φ = φ := hk
    show finRep E a k (s • φ) = s • φ
    rw [map_smul, h1']

theorem good_integrable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν] {φ : Sm E a} (h : Good φ) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) ν := by
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.2
  exact integrable_unip ν (Ψ := fun g (_ : Lie E a) => φ.1 g) (hc.comp continuous_fst).continuousOn
    (fun γ g => funext fun _ => h.1 γ g) g (y := oneL E a) isUnit_one

theorem constTerm_zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
      (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hH hF h1 φ hl ho z hz c hc
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  let CT : Sm E a → GA E a → ℂ := fun ψ g => ∫ x, ψ.1 (unip x * g) ∂(μ.restrict 𝓕)
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ ψ, Good ψ → Good (z ψ) ∧ ∀ c : Sm E a, c.1 = CT ψ → (z c).1 = CT (z ψ)}
      mul_mem' := by
        intro z w hz hw ψ h
        exact ⟨(hz _ (hw ψ h).1).1, fun c hc => (hz _ (hw ψ h).1).2 _ ((hw ψ h).2 c hc)⟩
      add_mem' := by
        intro z w hz hw ψ h
        refine ⟨good_add (hz ψ h).1 (hw ψ h).1, fun c hc => ?_⟩
        have e1 := (hz ψ h).2 c hc
        have e2 := (hw ψ h).2 c hc
        funext g
        simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, e1, e2, CT]
        rw [integral_add (good_integrable _ (hz ψ h).1 g) (good_integrable _ (hw ψ h).1 g)]
      algebraMap_mem' := by
        intro s ψ h
        simp only [Module.algebraMap_end_apply]
        refine ⟨good_smul h s, fun c hc => ?_⟩
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, hc, CT, smul_eq_mul]
        rw [integral_const_mul] }
  have hlie : ∀ X, lie E a X ∈ S := fun X ψ h => ⟨h.lie X, fun c hc => funext fun g => by
    rw [lie_apply, hc]
    exact (constTerm_mem_Sm E a r μ 𝓕 hH hF h1 ψ h.1 h.2).2 X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hlie _) (S.smul_mem (hlie _) _)) _
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, ho⟩).2 c hc

end GlobalTheory.ConstTermZalg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedean
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.JSW

theorem continuous_whit_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g h : GA E a,
      Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  intro E _ _ _ a φ hφ g h
  have hc : Continuous φ.1 := hφ.continuous
  have hW : Continuous (GlobalTheory.JSW.whit φ.1) := by
    have : GlobalTheory.JSW.whit φ.1 = GroundTheory.Automorphic.FourierWhittaker.partialCoeff φ.1 0 := by
      funext x
      exact GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hc x
    rw [this]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hc 0
  exact hW.comp ((continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL).mul continuous_const)

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | exact GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | (intros; apply GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminedByLowTypes
section
noncomputable section

namespace GlobalTheory.LowTypeRestriction

theorem determinedByLowTypes : DeterminedByLowTypes := _root_.GlobalTheory.LowTypeDetermined.eq_zero_of_lowT

theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end
end

