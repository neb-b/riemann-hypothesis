module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
public import Development.EtaleCohomology.WeilConjectures.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem aeval_smul_prod {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (S : Multiset K) :
    aeval (c • M) ((S.map fun b => X - C (b * c)).prod) =
      c ^ Multiset.card S • aeval M ((S.map fun b => X - C b).prod) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul (aeval (c • M)), map_mul (aeval M), ih]
    simp only [map_sub, aeval_X, aeval_C]
    have e : (algebraMap K (Matrix (Fin n) (Fin n) K)) (z * c) = c • (algebraMap K (Matrix (Fin n) (Fin n) K)) z := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    rw [e, ← smul_sub, smul_mul_smul_comm, pow_succ']

theorem UpperTheory.Gal.Int.Geo.twES :
    UpperTheory.Gal.Int.Geo.TwES := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hCl hw R hES A hA
  have hχ := hCl.1 hw A hA
  obtain ⟨hi, hf⟩ := hES A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 := (hχ.1 s hs)
    have h2 : (χ s : Qbar l) = 1 := by
      have h3 : ((GlobalTheory.TripleGal.rk1 χ s : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 = (χ s : Qbar l) := by
        simp [GlobalTheory.TripleGal.rk1]
      rw [h1] at h3
      simpa using h3.symm
    apply Units.ext
    rw [UpperTheory.V.Af.tw_val, hi s hs, h2]
    simp
  · have hk : ι ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c := by
      have h1 := (hχ.2 σ hσ)
      have h2 := (UpperTheory.Gal.TP.Sub.cpFacts_holds (G E Ω) (Qbar l) 0 0).2.1 χ σ⁻¹
      simp only [UpperTheory.Gal.TP.Sub.cp] at h2
      rw [h2] at h1
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C] at h1
      exact C_injective (sub_right_injective h1)
    have hs : ∀ T : Multiset ℂ, ((T.map fun b => X - C b).prod).map ι.symm.toRingHom =
        ((T.map ι.symm).map fun b => X - C b).prod := by
      intro T
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
      simp
    have hc : ι.symm c = ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← hk]; simp
    have hfin := hf σ hσ
    rw [hs] at hfin
    have hR : (R.map (· * c)).map ι.symm = (R.map ι.symm).map (· * ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l)) := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [map_mul, hc]
    rw [UpperTheory.V.Af.tw_val, hs, hR, Multiset.map_map]
    have := aeval_smul_prod (ρ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l)) ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) (R.map ι.symm)
    rw [hfin, smul_zero] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.Gal.Int.Geo

def cj {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (P : GL (Fin d) k) (ρ : Γ →* GL (Fin d) k) : Γ →* GL (Fin d) k :=
  (MulAut.conj P⁻¹).toMonoidHom.comp ρ

theorem cj_apply {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (P : GL (Fin d) k) (ρ : Γ →* GL (Fin d) k) (g : Γ) :
    cj P ρ g = P⁻¹ * ρ g * P := by simp [cj]

def low (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, i ≤ c j → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

def IsJH {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) (W : ℕ → Submodule k (Fin d → k)) : Prop :=
  (∀ i, IsInv ρ (W i)) ∧ ∀ i U, IsInv ρ U → W i ≤ U → U ≤ W (i + 1) → U = W i ∨ U = W (i + 1)

def FlagEx : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : Γ →* GL (Fin d) k),
  ∃ W : ℕ → Submodule k (Fin d → k), Monotone W ∧ W 0 = ⊥ ∧ W d = ⊤ ∧ IsJH ρ W

def FlagBasis : Prop := ∀ (k : Type) [Field k] (d m : ℕ) (W : ℕ → Submodule k (Fin d → k)), Monotone W → W 0 = ⊥ → W m = ⊤ →
  ∃ (P : GL (Fin d) k) (c : Fin d → ℕ), ∀ i v, v ∈ low k c i ↔ (P : Matrix (Fin d) (Fin d) k).mulVec v ∈ W i

def FlagMove : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : Γ →* GL (Fin d) k) (W : ℕ → Submodule k (Fin d → k))
  (P : GL (Fin d) k) (W' : ℕ → Submodule k (Fin d → k)), (∀ i v, v ∈ W' i ↔ (P : Matrix (Fin d) (Fin d) k).mulVec v ∈ W i) →
  IsJH ρ W → IsJH (cj P ρ) W'

def GrHom : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ : Γ →* GL (Fin d) k) (c : Fin d → ℕ),
  (∀ i, IsInv ρ₀ (low k c i)) → (∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) k).BlockTriangular c) ∧
    ∃ ρ : Γ →* GL (Fin d) k, ∀ g i j,
      (ρ g : Matrix (Fin d) (Fin d) k) i j = if c i = c j then (ρ₀ g : Matrix (Fin d) (Fin d) k) i j else 0

def SSOfSum : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : Γ →* GL (Fin d) k) (B : ℕ → Submodule k (Fin d → k)),
  (∀ i, IsInv ρ (B i)) → (∀ i U, IsInv ρ U → U ≤ B i → U = ⊥ ∨ U = B i) → ⨆ i, B i = ⊤ → IsSSRep ρ

def GrSS : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ ρ : Γ →* GL (Fin d) k) (c : Fin d → ℕ), IsJH ρ₀ (low k c) →
  (∀ g i j, (ρ g : Matrix (Fin d) (Fin d) k) i j = if c i = c j then (ρ₀ g : Matrix (Fin d) (Fin d) k) i j else 0) → IsSSRep ρ

def GrEx : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ : Γ →* GL (Fin d) k),
  ∃ (P : GL (Fin d) k) (ρ : Γ →* GL (Fin d) k), IsGr (cj P ρ₀) ρ ∧ IsSSRep ρ

theorem grEx_of (h1 : FlagEx) (h2 : FlagBasis) (h3 : FlagMove) (h4 : GrHom) (h5 : GrSS) : GrEx := by
  intro Γ k _ _ d ρ₀
  obtain ⟨W, hm, h0, ht, hJ⟩ := h1 Γ k d ρ₀
  obtain ⟨P, c, hP⟩ := h2 k d d W hm h0 ht
  have hJ' := h3 Γ k d ρ₀ W P (low k c) hP hJ
  obtain ⟨htri, ρ, hρ⟩ := h4 Γ k d _ c hJ'.1
  exact ⟨P, ρ, ⟨c, fun g => ⟨htri g, hρ g⟩⟩, h5 Γ k d _ ρ c hJ' hρ⟩

def ContGL : Prop := ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
  [IsTopologicalRing k] (d : ℕ) (ρ : Γ →* GL (Fin d) k),
  Continuous ρ ↔ ∀ i j, Continuous fun g => (ρ g : Matrix (Fin d) (Fin d) k) i j

def MatEx : Prop := ∀ (Γ L : Type) [Group Γ] [Field L] (M : Type 1) [AddCommGroup M] [Module L M] (a : Γ → M →ₗ[L] M),
  a 1 = LinearMap.id → (∀ g h, a (g * h) = a g ∘ₗ a h) → ∀ U : Submodule L M, (∀ g, ∀ x ∈ U, a g x ∈ U) →
  ∀ (d : ℕ) (b : Module.Basis (Fin d) L U), ∃ ρ : Γ →* GL (Fin d) L,
    (∀ g j, a g (b j).1 = ∑ i, (ρ g : Matrix (Fin d) (Fin d) L) i j • (b i).1) ∧
    ∀ i j, ∃ μ : M →ₗ[L] L, ∀ g, (ρ g : Matrix (Fin d) (Fin d) L) i j = μ (a g (b j).1)

def MatConj : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
  (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : H.Γ → L) (d : ℕ) (ρ : (Ω ≃ₐ[k] Ω) →* GL (Fin d) L) (P : GL (Fin d) L),
  IsMat l H Ω L θ ρ → IsMat l H Ω L θ (cj P ρ)

def HopGal : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
  (g : H.Γ) (d : ℕ), FEt (H.s g) d → ∀ σ : Ω ≃ₐ[k] Ω, hop l H Ω g ∘ₗ galTot l Ω H.q σ = galTot l Ω H.q σ ∘ₗ hop l H Ω g

def OpConj : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] (g : H.Γ)
  (T : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω))) (σ : Ω ≃ₐ[k] Ω),
  GlobalTheory.GalV.IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T →
  GlobalTheory.GalV.IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (galTot l Ω H.q σ ∘ₗ T ∘ₗ galTot l Ω H.q σ⁻¹)

def OpUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
  (g : H.Γ) (d : ℕ), FEt (H.s g) d → ∀ T, GlobalTheory.GalV.IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T → T = hop l H Ω g

def PieceStab : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ (H : HTower k), (∀ g, ∃ d, FEt (H.s g) d) →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : H.Γ → L) (σ : Ω ≃ₐ[k] Ω),
  ∀ x ∈ piece l H Ω L θ, galV l H Ω L σ x ∈ piece l H Ω L θ

def RelDim : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsIntegral X →
  ∃ d, SmoothOfRelativeDimension d p

def CompSum : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsProper p →
  ∃ (r : ℕ) (Y : Fin r → Scheme.{0}) (j : ∀ s, Y s ⟶ X), CrystallineSemistableComparison.IsSum j ∧ ∀ s, IsIntegral (Y s)

def DegFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsProjOver p →
  (∀ n, FiniteDimensional ℚ_[l] (HQ l (sch.obj X) n 0)) ∧ ∃ N : ℤ, ∀ n, (n < 0 ∨ N < n) → Subsingleton (HQ l (sch.obj X) n 0)

def HtotFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsProjOver p → FiniteDimensional ℚ_[l] (Htot l (sch.obj X))

def HtDesc : Prop := ∀ (q : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), QuasiCompact p → QuasiSeparated p → ∀ (n i : ℤ) (y : Ht q (sch.obj (geom Ω p)) n i),
  ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (z : Ht q (sch.obj (geom L p)) n i),
    pull _ (sch.map (LateralTheory.EWeil.StabPf.proj L p)) _ n z = y

def StabOpen : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), QuasiCompact p → QuasiSeparated p → ∀ (n i : ℤ) (x : Hl l (sch.obj (geom Ω p)) n i) (m : ℕ),
  IsOpen {σ : Ω ≃ₐ[k] Ω | (galHl l Ω p n i σ x).1 m = x.1 m}

def DegCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), QuasiCompact p → QuasiSeparated p → ∀ n i : ℤ,
  Module.Finite ℤ_[l] (Hl l (sch.obj (geom Ω p)) n i) → ∀ (v : HQ l (sch.obj (geom Ω p)) n i)
    (μ : Module.Dual ℚ_[l] (HQ l (sch.obj (geom Ω p)) n i)), Continuous fun σ => μ (galHQ l Ω p n i σ v)

def ExtCont : Prop := ∀ (Γ F L : Type) [TopologicalSpace Γ] [Field F] [TopologicalSpace F] [Field L] [TopologicalSpace L]
  [IsTopologicalRing L] [Algebra F L], Continuous (algebraMap F L) → ∀ (M : Type 1) [AddCommGroup M] [Module F M]
  [FiniteDimensional F M] (a : Γ → M →ₗ[F] M), (∀ (v : M) (μ : Module.Dual F M), Continuous fun g => μ (a g v)) →
  ∀ (v : L ⊗[F] M) (μ : (L ⊗[F] M) →ₗ[L] L), Continuous fun g => μ ((a g).baseChange L v)

def TotCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω], (l : k) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)), IsProper p → ∀ (v : Htot l (sch.obj (geom Ω p)))
    (μ : Module.Dual ℚ_[l] (Htot l (sch.obj (geom Ω p)))), Continuous fun σ => μ (galTot l Ω p σ v)

end UpperTheory.Gal.Int.Geo

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.jumpsOf :
    UpperTheory.Gal.Int.Geo.JumpsOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ w Q hQ hJ P AI hT A hA O _ _ _ Bw hBw τ LL' τ' hi lam J hl hJm
  obtain ⟨J', h1, h2⟩ := hJ P AI hT A hA O Bw hBw τ LL' τ' hi
  have e : J = (GlobalTheory.RoadWGeo.wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJm.trans (GlobalTheory.RoadWGeo.wtJumps_val lam).symm)
  refine ⟨J', h1, fun j hj => h2 j (hQ _ (GlobalTheory.CongL.LimAtLU.overPl_of_induced ι hA hBw hi) lam hl j ?_)⟩
  rw [e] at hj
  exact hj
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo

structure Steps : Prop where
  rep : RepEx
  es : ESStep
  crys : CrysStep
  jump : JumpStep
  phi : PhiStep
  cut : CutStep
  twES : TwES
  twCrys : TwCrys
  twJ : TwJ
  twPhi : TwPhi
  phiOf : PhiOf
  card : SatCard
  jumpsOf : JumpsOf
  rich : RichOf
  char : TP.Sub.CharEx
  ss : TP.Sub.SSLeft
  cont : TP.Sub.ContLeft

theorem map_inv_mul (R : Multiset ℂ) (c : ℂˣ) : (R.map (· * ((c : ℂ))⁻¹)).map (· * (c : ℂ)) = R := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id R]
  exact Multiset.map_congr rfl fun x _ => by simp

theorem Pack.rep (h : Steps) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a d : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (P : Pack ι d U)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (hlac : LacWtAt ι v U) (hP : P.HTFor v) :
    ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w → CrysAt ρ w ∧ JumpsOcc U ι ρ w) ∧
      ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → PhiKilled ι ρ w a B := by
  obtain ⟨dd, ρ, hc, hs, hp⟩ := h.rep E Ω l P.H P.θ P.nice
  obtain ⟨L, hL, -⟩ := h.char E Ω l ι
  obtain ⟨hχ, hcl⟩ := hL P.κ P.m P.alg
  have hES : ∀ w B, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → CongFor ι a P.H P.θ P.κ w B →
      ESAt ι (tw ρ (L P.κ P.m)) w (algSat a (normV w) B) := by
    rintro w B hw ⟨hu, ϑ, h1, h2⟩
    have := h.twES E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) hw _
      (h.es E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rwa [map_inv_mul] at this
  have hHT : ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w →
      CrysAt (tw ρ (L P.κ P.m)) w ∧ JumpsOcc U ι (tw ρ (L P.κ P.m)) w := by
    rintro w hw ⟨hu, h1, h2⟩
    have hg := (h.cut E _ P.H P.θ P.nice w).1 h1
    have h3 : ∀ τ : E →+* ℂ, ∃ σ : ℂ ≃+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam,
        HodgeAt (ι.trans σ) P.H P.θ (σ.toRingHom.comp τ) (j + P.m τ) := fun τ => by
      by_cases hτ : OverPl ι τ w
      · obtain ⟨σ, hσ⟩ := h2 τ hτ
        exact ⟨σ, fun _ => hσ⟩
      · exact ⟨RingEquiv.refl ℂ, fun h' => absurd h' hτ⟩
    choose σ hσ using h3
    have hJ : JOcc ι ρ w fun τ j => HodgeAt (ι.trans (σ τ)) P.H P.θ ((σ τ).toRingHom.comp τ) j := by
      intro Q AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
      exact h.jump E Ω l (ι.trans (σ (ι.toRingHom.comp τ))) P.H P.θ P.nice dd ρ hc hp w hw hg Q AI hT A hA O Bw hj τ LL' τ' hi
    refine ⟨?_, h.jumpsOf E Ω l ι a dd U _ w _ ?_ (h.twJ E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _ hJ)⟩
    · obtain ⟨C, hC, -⟩ := hg
      exact h.twCrys E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) (h.crys E Ω l P.H P.θ P.nice dd ρ hc hp w hw C hC)
    · intro τ hτ lam hl j hj
      simpa only [sub_neg_eq_add] using hσ τ hτ lam hl j hj
  refine ⟨dd, tw ρ (L P.κ P.m), ⟨(h.cont _ _ dd 0).2.2.1 ρ _ hc hχ, (h.ss _ _ dd 0).2.2 ρ _ hs, ?_,
    h.rich E Ω l ι a dd U _ v hv hlac (hHT v hv hP).2⟩, fun w hw hC B hB => hES w B hw (hC B hB), hHT, ?_⟩
  · obtain ⟨X, hX⟩ := P.cong
    exact ⟨X, fun w h1 h2 h3 B hB => hES w B h3 (hX w h1 h2 h3 B hB)⟩
  · intro w hw hC B hB
    obtain ⟨hu, ϑ, h1, h2⟩ := hC B hB
    have := h.twPhi E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _
      (h.phi E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rw [map_inv_mul] at this
    exact h.phiOf E Ω l ι dd _ w a B (h.card E a U w B hB) this

theorem geoOne_of (h : Steps) (hP : PackEx) : GeoOne := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph hlac
  obtain ⟨⟨P, hP0⟩, hA, hB⟩ := hP E l ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph
  refine ⟨?_, fun w hw hl hs => ?_, fun w hl hk ha0 hav hs => ?_⟩
  · obtain ⟨dd, ρ, hV, -⟩ := P.rep h Ω hv hlac hP0
    exact ⟨dd, ρ, hV⟩
  · obtain ⟨P, h1, h2⟩ := hA w hw hl hs
    obtain ⟨dd, ρ, hV, hE, -⟩ := P.rep h Ω hv hlac h1
    exact ⟨dd, ρ, hV, hE w hl h2⟩
  · obtain ⟨⟨P, h1, h2⟩, P', h1', h2'⟩ := hB w hl hk ha0 hav hs
    obtain ⟨dd, ρ, hV, -, hC, -⟩ := P.rep h Ω hv hlac h1
    obtain ⟨dd', ρ', hV', -, -, hF⟩ := P'.rep h Ω hv hlac h1'
    exact ⟨⟨dd, ρ, hV, hC w hl h2⟩, dd', ρ', hV', hF w hl h2'⟩

end UpperTheory.Gal.Int.Geo

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_lt_one_iff_mem {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (τ : E →+* Om l)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ∀ x ∈ v.asIdeal, ‖τ (x : E)‖ < 1) (x : 𝓞 E) :
    ‖τ (x : E)‖ < 1 ↔ x ∈ v.asIdeal := by
  refine ⟨fun hx => ?_, hv x⟩
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv hn
  have hy : ‖τ (y : E)‖ ≤ 1 :=
    GlobalTheory.CongW.PlaceEmb.norm_le_one_of_isIntegral_int ((NumberField.RingOfIntegers.isIntegral_coe y).map τ.toIntAlgHom)
  have h1 : τ (y : E) * τ (x : E) + τ (i : E) = 1 := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) e
    simpa using this
  have h2 : ‖τ (y : E) * τ (x : E)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hy) hx
  have h3 := IsUltrametricDist.norm_add_le_max (τ (y : E) * τ (x : E)) (τ (i : E))
  rw [h1, norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt h2 (hv i hi)))

private theorem exists_place {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) :
    ∃ A : ValuationSubring Ω, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 :=
  ⟨{ carrier := {x | ‖j x‖ ≤ 1}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *; exact mul_le_one₀ ha (norm_nonneg _) hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, map_add (f := _)] at *
       exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa using ha
     mem_or_inv_mem' := fun x => by
       simp only [Set.mem_setOf_eq, map_inv₀, norm_inv]
       rcases le_total ‖j x‖ 1 with h | h
       · exact Or.inl h
       · exact Or.inr (inv_le_one_of_one_le₀ h) }, fun _ => Iff.rfl⟩

theorem UpperTheory.Gal.Int.Geo.richOf :
    UpperTheory.Gal.Int.Geo.RichOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ v hv hlac hJ
  obtain ⟨τc, hover, lam, hw, hl⟩ := hlac
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  let τ₀ : E →+* Om l := ι.symm.toRingHom.comp τc
  have hτ₀ : ι.toRingHom.comp τ₀ = τc := by
    ext x
    simp [τ₀]
  have hsmall : ∀ x ∈ v.asIdeal, ‖τ₀ (x : E)‖ < 1 := hover
  letI : Algebra E (Om l) := τ₀.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[E] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let j : Ω →+* Om l := jA.toRingHom
  have hjτ : ∀ x : E, j (algebraMap E Ω x) = τ₀ x := fun x => jA.commutes x
  obtain ⟨A, hA⟩ := exists_place j
  obtain ⟨L, Bw, hBj, -, -⟩ := GlobalTheory.PhtCompare.exists_bridge (E := E) (A := A) j hA
  have hBw : Induces Bw := fun x => by rw [hBj]; exact hA x
  have hP : IsPlaceOver A v := fun x => by
    rw [hBw.valuation_lt_one_iff, hBj, hjτ]
    exact norm_lt_one_iff_mem τ₀ v hsmall x
  have hi : IsInduced Bw τ₀ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := fun x => by
    show τ₀ x = Bw.j (algebraMap E Ω x)
    rw [hBj, hjτ]
  obtain ⟨J', hJ', hsub⟩ := hJ P AI hT A hP _ Bw hBw τ₀ Bw.Kw (AlgHom.id ℚ_[l] ↥Bw.Kw.1) hi lam (wtJumps lam).val
    (by rw [hτ₀]; exact hw) (wtJumps_val lam)
  exact ⟨P, AI, hT, v, A, hv, hP, _, inferInstance, inferInstance, inferInstance, Bw, hBw, τ₀, J', hJ',
    wtJumps lam, card_wtJumps lam, fun j hj => hsub j hj, hl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.satCard :
    UpperTheory.Gal.Int.Geo.SatCard := by
  intro E _ _ _ a U w B h
  obtain ⟨σ, -, hB⟩ := h
  exact GlobalTheory.LFun.HasSatGL.card hB
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.twCrys :
    UpperTheory.Gal.Int.Geo.TwCrys := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hχ hρ P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, -, -, -⟩ := hχ.2 P AI hT A h O Bw hj
  have c2 := hρ P AI hT A h O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  rw [e1] at c1
  rw [e2]
  exact (UpperTheory.Gal.TP.Sub.twLoc_holds l P AI hT E Ω A O Bw dd (ρ.comp (Dec (F := E) A).subtype)
    (χ.comp (Dec (F := E) A).subtype)).2 c2 c1
end

