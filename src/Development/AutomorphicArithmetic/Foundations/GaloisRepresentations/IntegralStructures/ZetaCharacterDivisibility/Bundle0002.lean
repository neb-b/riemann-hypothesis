module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PInFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem pow_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (n : ℕ) :
    P ^ n * A = A * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, pow_succ]

private theorem aeval_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (Q : k[X]) :
    aeval P Q * A = A * aeval R Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, one_mul, Matrix.smul_mul, Matrix.mul_smul, pow_intertwine h n]

private theorem left_cancel {k : Type} [Field k] {a d : ℕ} {A : Matrix (Fin d) (Fin a) k} (hA : A.rank = a)
    {M N : Matrix (Fin a) (Fin a) k} (h : A * M = A * N) : M = N := by
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := hA
    rw [h2, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hinj := LinearMap.ker_eq_bot.mp hker
  ext i j
  have hv : M.mulVec (Pi.single j 1) = N.mulVec (Pi.single j 1) := by
    apply hinj
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]
  simpa using congrFun hv i

theorem UpperTheory.Gal.Int.Div.inFacts_of :
    InFacts := by
  intro Γ k _ _ a d r ρ ⟨A, hA, hc⟩
  refine ⟨hA ▸ A.rank_le_height, fun g hg => ?_, fun g Q hQ => ?_⟩
  · have h := hc g
    rw [hg] at h
    apply Units.ext
    apply left_cancel hA
    simpa using h.symm
  · apply left_cancel hA
    rw [← aeval_intertwine (hc g) Q, hQ]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PIsoMove
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.isoMove_of :
    IsoMove := by
  intro Γ k _ _ a d r r' ρ ⟨u, hu⟩
  set U : Matrix (Fin a) (Fin a) k := (u : Matrix (Fin a) (Fin a) k) with hUdef
  set V : Matrix (Fin a) (Fin a) k := ((u⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) with hVdef
  have hVU : V * U = 1 := by
    simp only [hUdef, hVdef]
    exact Units.inv_mul u
  have hUV : U * V = 1 := by
    simp only [hUdef, hVdef]
    exact Units.mul_inv u
  have hr' : ∀ x, (r' x : Matrix (Fin a) (Fin a) k) = U * (r x : Matrix (Fin a) (Fin a) k) * V := by
    intro x
    rw [hu x]
    rfl
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 ⟨u⁻¹, rfl⟩
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A * V, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_left_of_isUnit_det V A hVdet, hA]
    · rw [hr' g, ← Matrix.mul_assoc, h g]
      calc A * (r g : Matrix (Fin a) (Fin a) k) * V
          = A * (1 * (r g : Matrix (Fin a) (Fin a) k)) * V := by rw [Matrix.one_mul]
        _ = A * V * (U * (r g : Matrix (Fin a) (Fin a) k) * V) := by
            rw [← hVU]; simp only [Matrix.mul_assoc]
  · rintro ⟨m, B, hB, h⟩
    have hk : ∀ X Y : Matrix (Fin a) (Fin a) k,
        Matrix.kronecker (X * Y) (1 : Matrix (Fin m) (Fin m) k)
          = Matrix.kronecker X (1 : Matrix (Fin m) (Fin m) k) * Matrix.kronecker Y (1 : Matrix (Fin m) (Fin m) k) := by
      intro X Y
      have := Matrix.mul_kronecker_mul X Y (1 : Matrix (Fin m) (Fin m) k) (1 : Matrix (Fin m) (Fin m) k)
      simpa using this
    have h1 : Matrix.kronecker (1 : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) = 1 :=
      Matrix.one_kronecker_one
    set P := Matrix.kronecker U (1 : Matrix (Fin m) (Fin m) k) with hP
    set Q := Matrix.kronecker V (1 : Matrix (Fin m) (Fin m) k) with hQ
    have hQP : Q * P = 1 := by rw [hQ, hP, ← hk, hVU, h1]
    have hPQ : P * Q = 1 := by rw [hQ, hP, ← hk, hUV, h1]
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
    refine ⟨m, P * B, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_right_of_isUnit_det P B hPdet, hB]
    · have hc : Matrix.kronecker (U * (r g : Matrix (Fin a) (Fin a) k) * V) (1 : Matrix (Fin m) (Fin m) k)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q := by
        rw [hk, hk]
      rw [hr' g, hc]
      calc P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q * (P * B)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * ((Q * P) * B) := by
            simp only [Matrix.mul_assoc]
        _ = P * (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * B) := by
            rw [hQP, Matrix.one_mul, Matrix.mul_assoc]
        _ = P * B * (ρ g : Matrix (Fin d) (Fin d) k) := by
            rw [h g, Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PJumpSeed
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpSeed_of :
    CoverIn → SSBlock → SubLoc → LocConj → JumpCard → JumpCondition := by
  intro h1 h2 h3 h4 h5 E Ω _ _ _ _ _ _ l _ ι a dd U r ρ hss hcov w hcrys hocc P AI hT A hA O _ _ _ Bw hj
  have hc := hcrys P AI hT A hA O Bw hj
  have hdr := ((h4 l P AI hT E Ω A O Bw a (r.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)).1 hc).1
  refine ⟨hc, hdr, ?_⟩
  intro τ LL' τ' hτ lam J hw hJ
  obtain ⟨Jr, hJr, hcard⟩ := h5 l P AI hT E Ω A O Bw a _ hdr τ LL' τ' hτ
  obtain ⟨J', hJ', hsub⟩ := hocc P AI hT A hA O Bw hj τ LL' τ' hτ lam J hw hJ
  obtain ⟨m, n, e, hin⟩ := h1 _ _ a dd r ρ hcov
  have hR := h2 _ _ a m n e r hss
  have hcomp : (blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype =
      blockRep (a := fun _ : Fin m => a) e fun _ => r.comp (Dec (F := E) A).subtype := by
    ext g i j
    rfl
  have hjR : IsJumpsAt P Bw ((blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype) τ
      (∑ _ : Fin m, Jr) := by
    rw [hcomp]
    exact GlobalTheory.BlockSum.isJumpsAt_blockRep P Bw e hτ fun _ => hJr
  have hle : J' ≤ ∑ _ : Fin m, Jr :=
    (h3 E Ω l dd n ρ _ hR hin ι w P AI hT A hA O Bw hj).2 τ _ _ hjR hJ'
  have hJeq : J = (wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJ.trans (wtJumps_val lam).symm)
  have hnd : J.Nodup := hJeq ▸ (wtJumps lam).nodup
  have hJc : J.card = a := by rw [hJeq]; exact card_wtJumps lam
  have hss' : J ⊆ Jr := fun j hjJ => by
    obtain ⟨_, -, hj'⟩ := Multiset.mem_sum.1 (Multiset.mem_of_le hle (hsub j hjJ))
    exact hj'
  have hJJ : J = Jr :=
    Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 hss') (by rw [hcard, hJc])
  rw [hJJ]
  exact hJr
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLacBridge
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocSum
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

namespace UpperTheory.Gal.Int.Div.LocalSums

section Alg

variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k']

private theorem sumRep_ll {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.castAdd b i)) (finSumFinEquiv.symm (Fin.castAdd b j)) = _
  simp

private theorem sumRep_rr {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin b) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.natAdd a i) (Fin.natAdd a j) =
      (s g : Matrix (Fin b) (Fin b) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.natAdd a i)) (finSumFinEquiv.symm (Fin.natAdd a j)) = _
  simp

private theorem map_sum' {a b : ℕ} (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (sumRep r₁ r₂) = sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

private theorem descend {n : ℕ} (f : k →+* k') (hf : Function.Injective f) (r : Γ →* GL (Fin n) k')
    (A : Γ → Matrix (Fin n) (Fin n) k) (hA : ∀ g i j, f (A g i j) = (r g : Matrix (Fin n) (Fin n) k') i j) :
    ∃ r₁ : Γ →* GL (Fin n) k, mapRep f r₁ = r := by
  let M : Γ →* Matrix (Fin n) (Fin n) k :=
    { toFun := A
      map_one' := by
        ext i j
        apply hf
        rw [hA]
        simp [Matrix.one_apply, apply_ite f]
      map_mul' := fun g h => by
        ext i j
        apply hf
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hA, Matrix.mul_apply, map_sum]
        simp only [map_mul, hA, Units.val_mul, Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_⟩
  ext g i j
  simpa [mapRep, M] using hA g i j

end Alg

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {s : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_split {L : FinExt l} {ρ : ↥Gw →* GL (Fin (a + b)) ↥L.1}
    (h : IsModel Bw (sumRep r s) L ρ) :
    ∃ (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (s₁ : ↥Gw →* GL (Fin b) ↥L.1),
      IsModel Bw r L r₁ ∧ IsModel Bw s L s₁ ∧ IsModel Bw (sumRep r s) L (sumRep r₁ s₁) := by
  have hf : Function.Injective (algebraMap ↥L.1 (Om l)) := (algebraMap ↥L.1 (Om l)).injective
  have e : ∀ g i j, algebraMap ↥L.1 (Om l) ((ρ g : Matrix _ _ ↥L.1) i j) =
      (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) (Om l)) i j := fun g i j => by
    rw [← h.2]
    simp [mapRep]
  obtain ⟨r₁, hr⟩ := descend (algebraMap ↥L.1 (Om l)) hf r
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.castAdd b i) (Fin.castAdd b j))
    (fun g i j => by rw [e, sumRep_ll])
  obtain ⟨s₁, hs⟩ := descend (algebraMap ↥L.1 (Om l)) hf s
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.natAdd a i) (Fin.natAdd a j))
    (fun g i j => by rw [e, sumRep_rr])
  exact ⟨r₁, s₁, ⟨h.1, hr⟩, ⟨h.1, hs⟩, ⟨h.1, by rw [map_sum', hr, hs]⟩⟩

end UpperTheory.Gal.Int.Div.LocalSums

open UpperTheory.Gal.Int.Div.LocalSums in
theorem UpperTheory.Gal.Int.Div.locSum_of :
    LocSum := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a b r s
  refine ⟨fun hc => ?_, fun τ J J' hJ hJ' => ?_⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hc
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    obtain ⟨T⟩ := id tied
    have he : ∀ g v, GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b (Bw.repE L (sumRep r₁ s₁) g v) =
        (Bw.repE L r₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b v).1,
          Bw.repE L s₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b v).2) := by
      intro g v
      exact GlobalTheory.DirectSumLocal.splitEquiv_sumRep r₁ s₁ _ v
    obtain ⟨-, h2, -⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw L (Fin (a + b) → ↥L.1)
      (Bw.repE L (sumRep r₁ s₁)) (Fin a → ↥L.1) (Bw.repE L r₁) (Fin b → ↥L.1)
      (Bw.repE L s₁) (GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b) he
    have hc' : Bw.IsCrysE P L (sumRep r₁ s₁) := (m.isCrysAt_iff P).1 hc
    have h3 := h2.1 hc'
    exact ⟨(m₁.isCrysAt_iff P).2 h3.1, (m₂.isCrysAt_iff P).2 h3.2⟩
  · obtain ⟨L, ρ, hm, hd, τ', t, -⟩ := id hJ
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := _root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    have hds := S.1.1 ((m.isdRAt_iff P).1 ⟨L, ρ, hm, hd⟩)
    obtain ⟨K, hK⟩ := m₂.exists_isJumpsAt P hds.2 t
    rw [Multiset.le_iff_count]
    intro n
    have c := hJ.count_eq P m t n
    have c₁ := hJ'.count_eq P m₁ t n
    have c₂ := hK.count_eq P m₂ t n
    rw [S.2] at c
    omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PRootPin
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.rootPin_of :
    RootPin := by
  intro p s m hp hdeg hdvd hprod hgen
  have hspl : p.Splits := IsAlgClosed.splits p
  have hq : rootPol s ^ m ≠ 0 := by
    apply pow_ne_zero
    exact (monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hle : p.roots ≤ (rootPol s ^ m).roots := Polynomial.roots.le_of_dvd hq hdvd
  have hroots : (rootPol s ^ m).roots = m • s := by
    rw [Polynomial.roots_pow]
    unfold rootPol
    rw [roots_multiset_prod_X_sub_C]
  have hcard : p.roots.card = s.card := by
    rw [splits_iff_card_roots.mp hspl, hdeg]
  have hmem : ∀ x ∈ p.roots, x ∈ s := by
    intro x hx
    have := Multiset.mem_of_le hle hx
    rw [hroots, Multiset.mem_nsmul] at this
    exact this.2
  have heq : p.roots = s := hgen _ hcard hmem hprod
  rw [hspl.eq_prod_roots_of_monic hp, heq]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSSBlock
section
open Formalism.MainNotions.N
open GlobalTheory.BlockSum (blockRep vecComp vecComp_mulVec)

namespace UpperTheory.Gal.Int.Div

section Bridge

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def colRep (ρ : Γ →* GL (Fin n) k) : Representation k Γ (Fin n → k) where
  toFun g := Matrix.mulVecLin (ρ g).val
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.mulVecLin_mul]

private theorem colRep_apply (ρ : Γ →* GL (Fin n) k) (g : Γ) (v : Fin n → k) :
    colRep ρ g v = (ρ g).val.mulVec v := rfl

private theorem isSSRep_iff (ρ : Γ →* GL (Fin n) k) : IsSSRep ρ ↔ (colRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨W', hW', hc⟩ := h a.toSubmodule fun g v hv => a.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => hW' g v hv⟩,
      disjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.inf_eq_bot),
      codisjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.sup_eq_top)⟩
  · intro h W hW
    obtain ⟨b, hb⟩ := exists_isCompl (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (colRep ρ))
    exact ⟨b.toSubmodule, fun g v hv => b.apply_mem_toSubmodule g hv,
      disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.inf_eq_bot),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.sup_eq_top)⟩

end Bridge

theorem sSBlock_of : SSBlock := by
  intro Γ k _ _ a m n e r hr
  rw [isSSRep_iff, Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).1
    ((isSSRep_iff r).1 hr)
  set R := blockRep (a := fun _ : Fin m => a) e fun _ => r
  let L : (colRep R).asModule ≃ₗ[k] (Fin m → (colRep r).asModule) :=
    (colRep R).asModuleEquiv.trans ((vecComp e k).trans
      (LinearEquiv.piCongrRight fun _ => (colRep r).asModuleEquiv.symm))
  have hL : ∀ (g : Γ) (x : (colRep R).asModule),
      L (MonoidAlgebra.single g (1 : k) • x) = MonoidAlgebra.single g (1 : k) • L x := by
    intro g x
    funext j
    apply (colRep r).asModuleEquiv.injective
    simp only [L, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, Pi.smul_apply,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
      LinearEquiv.apply_symm_apply, colRep_apply]
    exact vecComp_mulVec e (fun _ => r) g _ j
  exact IsSemisimpleModule.of_injective
    (MonoidAlgebra.equivariantOfLinearOfComm L.toLinearMap hL) L.injective

end UpperTheory.Gal.Int.Div
end

