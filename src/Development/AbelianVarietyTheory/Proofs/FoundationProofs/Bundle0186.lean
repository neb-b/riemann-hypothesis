module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLev
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteGaloisMemFixingSubgroupMaxUnramified
section
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Bases

variable {Z O R M J ι : Type} [CommRing Z] [CommRing O] [CommRing R] [Algebra Z O] [Algebra Z R]
  [AddCommGroup M] [Module O M] [Fintype J] [Fintype ι] (o : Module.Basis J Z O) {r : ℕ}
  (e : Fin r ≃ ι × J)

end Bases

section Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {Z R RA : Type} [CommRing Z] [CommRing R] [CommRing RA] [Algebra Z O]
    [Algebra Z R] [Algebra O RA] {inclR : RA →ₐ[O] O ⊗[Z] R} {φR : O ⊗[Z] R →ₐ[O] O ⊗[Z] R}
    {gR : G → (O ⊗[Z] R →ₐ[O] O ⊗[Z] R)} {πA : RA}
    (E : EtTie W RA (O ⊗[Z] R) inclR φR gR πA) (A : Subring R)
    (hA : ∀ (lam : O →ₗ[Z] Z) a, cf lam (sc E a) ∈ A) {Y : LocLat G Qp LL O}
    {J ι : Type} [Fintype J] [Fintype ι] (o : Module.Basis J Z O)



end Module

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}


end Transport

section RankOne

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))


end RankOne

section Situation

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_levelFieldFiniteExtension (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℚ_[l] ↥(K0 (levelField K s)) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h1 : Ks (levelField K s) s = Ks K s := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le_sup_right ?_ _)
    exact le_inf le_sup_left inf_le_right
  have h2 := GlobalTheory.Cyc.finrank_Ks (levelField K s) s hs
  rw [h1, GlobalTheory.Cyc.finrank_Ks K s hs] at h2
  have h3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (pow_pos (by omega) _)) h2).symm

theorem val_le_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (s : ℕ) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ s * y := ⟨((l : ℚ_[l]) ^ s)⁻¹ * x, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l,
    norm_mul, norm_pow, Padic.norm_p, nsmul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
    mul_le_iff_le_one_right (zpow_pos hl1 _)]
  have h1 : (s : WithTop ℚ) ≤ s + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔
      0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    conv_lhs => lhs; rw [← add_zero (s : WithTop ℚ)]
    exact WithTop.add_le_add_iff_left (WithTop.natCast_ne_top s)
  rw [h1, P.v_O]
  change IsIntegral ℤ_[l] _ ↔ _
  rw [isIntegral_algebraMap_iff , IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩

theorem absoluteGalois_mem_fixingSubgroup_maxUnramified {K : FinExt l} (g : ↥(GK K)) : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
  fun x => g.2 ⟨x.1, x.2.1⟩

section Wach

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}

theorem mem_GKs (hs : W.s = s) (g : ↥(GK K)) : g ∈ W.GKs ↔ (g : GQ l) ∈ GK (levelField K s) := by
  rw [W.GKs_def, hs, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, val_le_iff]
  exact (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g (absoluteGalois_mem_fixingSubgroup_maxUnramified g)).1 s).symm

theorem prim_ζQ (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h : ∀ j, P.ζQ (j + 1) ^ l ^ j = P.ζQ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [h]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, h, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem resΓ_eq_one (g : ↥(GK K)) (hg : ∀ j : ℕ, (g : GQ l) (P.ζQ j) = P.ζQ j) : W.resΓ g = 1 := by
  have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ := GlobalTheory.Cyc.exists_zpow_neg_lt (l := l) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have h2 := GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim P.χQ_cyc g _ (prim_ζQ P m) (hg _)
    have h3 : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(m : ℤ)) :=
      zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le) (by push_cast; omega)
    exact absurd (h2.trans h3) (not_le.mpr hm)
  apply W.χΓ_inj
  apply Units.ext
  apply Subtype.val_injective
  have h2 := W.χΓ_res g
  rw [P.PD_χ, h1, map_one] at h2
  rw [map_one]
  exact h2

variable (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

end Wach

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteIrreducibilitySpan
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.Proof.AbsoluteIrreducibilitySpan


open Formalism.MainNotions.N in
theorem absIrr_of_span {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (M : Γ → Matrix (Fin a) (Fin a) k) (c : Γ → k)
    (hM : ∀ g, M g = c g • (ρ g : Matrix (Fin a) (Fin a) k))
    (h : Submodule.span k (Set.range M) = ⊤) : AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  have htop : Submodule.span K ((fun v : Fin a → k => (algebraMap k K) ∘ v) ''
      ((⊤ : Submodule k (Fin a → k)) : Set (Fin a → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub
  rw [htop]
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW => ?_⟩
  have key : ∀ X : Matrix (Fin a) (Fin a) k, ∀ v ∈ W', (X.map (algebraMap k K)).mulVec v ∈ W' := by
    intro X
    have hX : X ∈ Submodule.span k (Set.range M) := h ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      have h1 : (M g).map (algebraMap k K) = algebraMap k K (c g) •
          ((mapRep (algebraMap k K) ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
        ext p q
        simp [hM, mapRep]
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hW g v hv)
    | zero => intro v hv; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      exact W'.add_mem (hx v hv) (hy v hv)
    | smul r x _ hx =>
      intro v hv
      have h1 : (r • x).map (algebraMap k K) = algebraMap k K r • x.map (algebraMap k K) := by
        ext p q
        simp
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hx v hv)
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨b, hb'⟩ := Function.ne_iff.mp hv0
  rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h2 := W'.smul_mem (v b)⁻¹ (key (Matrix.single j b 1) v hv)
  have hb2 : v b ≠ 0 := hb'
  have h3 : (v b)⁻¹ • ((Matrix.single j b (1 : k)).map (algebraMap k K)).mulVec v = Pi.basisFun K (Fin a) j := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext x
    by_cases hx : x = j
    · subst hx; simp [hb2]
    · simp [hx]
  rw [h3] at h2
  exact h2

end GlobalTheory.Proof.AbsoluteIrreducibilitySpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped Pointwise

namespace GlobalTheory.AntiRamConj

section General
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

def moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) : ValuationSubring Ω :=
  B.comap (c.symm : Ω →+* Ω)

theorem mem_moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    y ∈ moveVal c B ↔ c.symm y ∈ B := Iff.rfl

theorem moveVal_lt_one (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    (moveVal c B).valuation y < 1 ↔ B.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_moveVal, mem_moveVal, map_inv₀,
    map_eq_zero_iff _ c.symm.injective]

def conjAut (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (σ : G E Ω) : G E Ω :=
  { (c.symm.trans (σ : Ω ≃+* Ω)).trans c with
    commutes' := fun x => by
      obtain ⟨y, hy⟩ := hc x
      show c (σ (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
      rw [hy, σ.commutes, ← hy, RingEquiv.apply_symm_apply] }

theorem conjAut_apply (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) (σ : G E Ω) (x : Ω) :
    conjAut c hc σ x = c (σ (c.symm x)) := rfl

theorem conjAut_mem_ine [NumberField E] (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) {B : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : conjAut c hc σ ∈ Ine (F := E) (moveVal c B) := by
  have hd : σ ∈ Dec (F := E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show conjAut c hc σ ∈ Dec (F := E) (moveVal c B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (conjAut c hc σ).surjective x
    have h1 : ((conjAut c hc σ)⁻¹ : G E Ω) (conjAut c hc σ z) = z := (conjAut c hc σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, conjAut_apply, RingEquiv.symm_apply_apply,
      apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, conjAut_apply, RingEquiv.symm_apply_apply]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

end General

theorem host_conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => D.host.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

theorem cc_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply
    (j.comp (algebraMap D.host.E D.nd.Om)) x).symm

theorem cc_symm_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  rw [RingEquiv.symm_apply_eq, cc_algebraMap_host, host_conj_conj]

theorem isPlaceOver_moveVal (D : D7) {P P' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : IsConjPl D.host P P') {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) :
    IsPlaceOver (moveVal D.ntw.cc B) P' := by
  intro y
  have hi : IsIntegral ℤ (D.host.conj (y : D.host.E)) :=
    (y.isIntegral_coe).map_of_comp_eq (RingHom.id ℤ) (D.host.conj : D.host.E →+* D.host.E) (by ext; simp)
  let x : 𝓞 D.host.E := ⟨_, hi⟩
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := rfl
  rw [moveVal_lt_one, cc_symm_algebraMap_host, ← hx, hB x]
  exact h x y (by rw [hx, host_conj_conj])

end GlobalTheory.AntiRamConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompatibleCoboundaries
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelmerLevel

section Comp

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {ι : Type} [Fintype ι]
  (b : Module.Basis ι O O')

structure Comp (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A'] where
  inc : A →+ A'
  p : ι → A' →+ A
  sum_p : ∀ x, ∑ a, b a • inc (p a x) = x
  p_inc : ∀ a c x, p a (c • inc x) = b.repr c a • x

def Comp.self : Comp b O O' where
  inc := (algebraMap O O').toAddMonoidHom
  p a := (b.coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm]
  p_inc a c x := by
    have : c • (algebraMap O O').toAddMonoidHom x = x • c := by simp [Algebra.smul_def, mul_comm]
    rw [this]; simp [mul_comm]

variable {b} {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A']

namespace Comp

variable (S : Comp b A A')


def Compat (N : Submodule O A) (N' : Submodule O' A') : Prop := ∀ x, x ∈ N' ↔ ∀ a, S.p a x ∈ N

variable {S}

variable (S)

section Coh

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
  [TopologicalSpace A'] [DiscreteTopology A'] [IsTopologicalAddGroup A'] [ContinuousConstSMul O' A']
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {ρ : Representation O Γ A} {ρ' : Representation O' Γ A'}
  (he : ∀ a g m, S.p a (ρ' g m) = ρ g (S.p a m))
include he

end Coh

end Comp

end Comp

section Frac

variable {O O' : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
  [FaithfulSMul O O'] [Module.Finite O O'] {ι : Type} [Fintype ι] (b : Module.Basis ι O O')

attribute [local instance] FractionRing.liftAlgebra

def fracBasis : Module.Basis ι (FractionRing O) (FractionRing O') :=
  b.localizationLocalization (FractionRing O) (nonZeroDivisors O) (FractionRing O')

def fracComp : Comp b (FractionRing O) (FractionRing O') where
  inc := (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom
  p a := ((fracBasis b).coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← (fracBasis b).sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm, fracBasis]
  p_inc a c x := by
    have : c • (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom x =
        x • algebraMap O' (FractionRing O') c := by simp [Algebra.smul_def, mul_comm]
    rw [this]
    change (fracBasis b).repr (x • _) a = _
    rw [map_smul, Finsupp.smul_apply, fracBasis, Module.Basis.localizationLocalization_repr_algebraMap,
      Algebra.smul_def (b.repr c a), smul_eq_mul, mul_comm]

theorem fracComp_inc (x : FractionRing O) :
    (fracComp b).inc x = algebraMap (FractionRing O) (FractionRing O') x := rfl

theorem frac_compat : (fracComp b).Compat (LinearMap.range (Algebra.linearMap O (FractionRing O)))
    (LinearMap.range (Algebra.linearMap O' (FractionRing O'))) := by
  intro x
  constructor
  · rintro ⟨c, rfl⟩ a
    refine ⟨b.repr c a, ?_⟩
    have := (fracComp b).p_inc a c 1
    simpa [fracComp_inc, ← Algebra.algebraMap_eq_smul_one] using this.symm
  · intro h
    choose m hm using h
    rw [← (fracComp b).sum_p x]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ⟨algebraMap O O' (m a), ?_⟩
    rw [← hm, fracComp_inc]
    simp [← IsScalarTower.algebraMap_apply]

open Formalism.MainNotions.BlochKatoReduction

end Frac

section Len

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] [FaithfulSMul O O'] [Module.Finite O O']
  {ι : Type} [Fintype ι] {b : Module.Basis ι O O'}

end Len

section Main

open Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.GaloisCohomology

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)


end Main

end GlobalTheory.SelmerLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualityDimOfLocalTheorem
section
namespace GlobalTheory.BlochKato₂

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem localTheorem_iff (D : D7) : LocalSituation.Conclusion5 D ↔ BlochKatoReduction.adm3 D ∧
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
      LocalSituation.bkARightExact ((D.loc l).PD K) ∧ LocalSituation.bkC ((D.loc l).PD K) :=
  ⟨fun h => ⟨fun l _ K => ⟨(h l K).1, (h l K).2.1, (h l K).2.2.2.1⟩,
      fun l _ K => ⟨(h l K).2.2.1, (h l K).2.2.2.2⟩⟩,
    fun h l _ K => ⟨(h.1 l K).1, (h.1 l K).2.1, (h.2 l K).1, (h.1 l K).2.2, (h.2 l K).2⟩⟩

theorem duality_dim_of_localTheorem : ∀ D : D7, LocalSituation.Conclusion5 D → BlochKatoReduction.Gen.adm3 D ∧ BlochKatoReduction.adm3 D :=
  fun D h => ⟨((localTheorem_iff D).1 h).1, ((localTheorem_iff D).1 h).1⟩

end GlobalTheory.BlochKato₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement
section
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_lev_of_gamma_le : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ' → letI := GlobalTheory.K4.algRat X Γ'; FiniteDimensional (RatFunc Ω) (GlobalTheory.K4.lev X Γ') := by
  first | exact @GlobalTheory.K4.finiteDimensional_lev | exact GlobalTheory.K4.finiteDimensional_lev | (intros; apply GlobalTheory.K4.finiteDimensional_lev <;> assumption)
end

