module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.IdentRank

theorem basis_of_baseChange {O R N ι : Type} [CommRing O] [CommRing R] [Algebra O R] [Nontrivial R]
    [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N] [Fintype ι]
    (j : (ι → R) ≃ₗ[R] R ⊗[O] N) : Nonempty (Module.Basis ι O N) := by
  classical
  have : Nontrivial O := (algebraMap O R).domain_nontrivial
  let b := Module.Free.chooseBasis O N
  have h1 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis R b)
  have h2 := j.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, h1] at h2
  exact ⟨b.reindex (Fintype.equivOfCardEq h2.symm)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL), Ident (thetaW a LL) ϖ P T → Nonempty (Module.Basis ι ↥(OL LL) ↥T.L.T) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  have := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨-, -, h3⟩ := GlobalTheory.WittTensorFixed.baseChange_flat (O := ↥(OL LL)) (frobW l) hs hk
    (GlobalTheory.WittTensorFixed.algebraMap_WCb_injective l)
  have : Nontrivial (OW l ↥(OL LL)) := h3.nontrivial
  exact basis_of_baseChange I.j

end GlobalTheory.BKGal.IdentRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinset
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefField

theorem entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ E Ω _ _ _ _ _ a ρ hρ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ
    ⟨⊥, inferInstance⟩
  haveI := L.2
  let B := Module.finBasis ℚ_[l] ↥L.1
  classical
  refine ⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩
  have key : ∀ x : ↥L.1, (x : Qbar l) ∈ K := by
    intro x
    have hx : x ∈ Submodule.span ℚ_[l] (Set.range B) := B.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => simpa using K.zero_mem
    | add y z _ _ hy hz => simpa using K.add_mem hy hz
    | smul c y _ hy => simpa using K.smul_mem hy (x := c)
  exact key ⟨_, hL g s t⟩

end GlobalTheory.CoefField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.GaloisFromAdm

theorem placesOver_finite (D : D7) (l : ℕ) (hl : l ≠ 0) : (placesOver D.host.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

end GlobalTheory.GaloisFromAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTaylorFormulaBreuilKisinLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TaylorBasis

theorem cauchy_dvd {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R)
    (hA : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p)
    (hB : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) :=
  _root_.GlobalTheory.cauchy_product_dvd_pow x α β A B hA hB r

theorem desc_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (v : Vec K a ι) : C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v :=
  _root_.GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow C k v

theorem nabla_pow_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) :=
  GlobalTheory.T.nabla_pow_apply_smul_leibniz C k f v

theorem descN_eq (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) :
    descN K p f = X ^ p * (⇑(derivative (R := K)))^[p] f :=
  GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' K p f

theorem muDiv_mul_choose {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {k p : ℕ} (h : p ≤ k) :
    ϖ.muDiv a O g k * (k.choose p : OCr l O) = ϖ.muDiv a O g p * ϖ.muDiv a O g (k - p) := by
  have hx := ϖ.theta_mu (ϖ.gal_pi a g)
  have key : dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) = dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p) := by
    apply sub_eq_zero.1
    refine acris_nat_cancel (Nat.factorial_ne_zero k) ?_
    have hf : (k.factorial : Per.Acris l) = (k.choose p : Per.Acris l) * p.factorial * (k - p).factorial := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial h]
    rw [show (k.factorial : Per.Acris l) * (dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) -
        dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p)) = (k.choose p : Per.Acris l) * ((k.factorial : Per.Acris l) *
        dpow (ϖ.mu g) hx k) - (k.choose p : Per.Acris l) * (((p.factorial : Per.Acris l) * dpow (ϖ.mu g) hx p) *
        (((k - p).factorial : Per.Acris l) * dpow (ϖ.mu g) hx (k - p))) by
      linear_combination (-(dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p))) * hf]
    rw [factorial_mul_dpow, factorial_mul_dpow, factorial_mul_dpow, ← pow_add, Nat.add_sub_cancel' h, sub_self]
  have hm : ∀ n, ϖ.muDiv a O g n =
      (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) (dpow (ϖ.mu g) hx n) := fun n => rfl
  rw [hm, hm, hm, ← map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O), ← map_mul,
    ← map_mul, key]

theorem galOCr_iC_taylor {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) (c : ZMod a → S O K e) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ galOCr O (g : GQ l) (ϖ.iC t K c) -
      ∑ p ∈ Finset.range n, ϖ.muDiv a O g p * ϖ.iC t K (fun τ => ⟨descN K p (c τ), descN_mem_S e p (c τ).2⟩) := by
  choose N hN using fun τ : ZMod a => ϖ.taylor_S a O K g (c τ) r
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun τ => hN τ n ((Finset.le_sup (Finset.mem_univ τ)).trans hn)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem coord_desc {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (m : Vec K a ι) (k : ℕ) (τ : ZMod a) (i : ι) :
    (P.mxInv τ *ᵥ C.desc k m τ) i = ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) *
      (descN K p ((P.mxInv τ *ᵥ m τ) j) * (X ^ (k - p) * (P.mxInv τ *ᵥ (C.nabla ^ (k - p)) (P.phi (bas j)) τ) i)) := by
  have hΦ : ∀ (f : ZMod a → K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (f • w) τ) i = f τ * (P.mxInv τ *ᵥ w τ) i := fun f w => by
    rw [Pi.smul_apply', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦs : ∀ (s : K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (s • w) τ) i = s * (P.mxInv τ *ᵥ w τ) i := fun s w => by
    rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦsum : ∀ {J : Type} (s : Finset J) (w : J → Vec K a ι),
      (P.mxInv τ *ᵥ (∑ x ∈ s, w x) τ) i = ∑ x ∈ s, (P.mxInv τ *ᵥ w x τ) i := fun s w => by
    rw [Finset.sum_apply, Matrix.mulVec_sum, Finset.sum_apply]
  conv_lhs => rw [desc_eq, P.eq_sum_phi_bas m]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦs, map_sum, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla_pow_smul, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
  rw [hΦs, hΦ, descN_eq]
  have hX : (X : K⟦X⟧) ^ k = X ^ p * X ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
  rw [hX]
  ring

theorem taylor_of_basis {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}
    [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (C : Conn P)
    (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι),
      (X : K⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S O K e)
    (hΓ : ∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (l : OCr l O) ^ r ∣ toOCr l O (Γ i j) -
        ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ j k i⟩)) :
    I.Taylor C := by
  intro g
  obtain ⟨Γ, hΓL, hconv⟩ := hΓ g
  refine ⟨Γ, hΓL, fun m r => ?_⟩
  let c : ι → ZMod a → ↥(S O K e) := coordL P (S O K e) m
  have hcj : ∀ j τ, (c j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m : Vec K a ι) τ) j := fun j τ => rfl
  have hcm : ∀ j, toCris t ϖ P m j = ϖ.iC t K (c j) := fun j => rfl
  have F3 : ∀ k i, toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩ i =
      ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : OCr l O) *
        (ϖ.iC t K (fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) *
          ϖ.iC t K (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
    intro k i
    have h1 : coordL P (S O K e) ⟨C.desc k m, C.desc_mem k m.2⟩ i =
        ∑ j, ∑ p ∈ Finset.range (k + 1), ((k.choose p : ℕ) : ZMod a → ↥(S O K e)) *
          ((fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) * (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
      funext τ
      apply Subtype.ext
      refine (coord_desc C m k τ i).trans ?_
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, AddSubmonoidClass.coe_finsetSum,
        MulMemClass.coe_mul, SubringClass.coe_natCast, hcj]
    rw [toCris_apply, h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_natCast]
  have key : ∀ p : ι × ι, ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      galOCr O (g : GQ l) (ϖ.iC t K (c p.2)) * toOCr l O (Γ p.1 p.2) -
        ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c p.2 τ), descN_mem_S e q (c p.2 τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 (k - q) p.1⟩)) :=
    fun p => cauchy_dvd _ _ (fun k => ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 k p.1⟩)) _ _
      (fun r => galOCr_iC_taylor t ϖ g (c p.2) r) (fun r => hconv p.1 p.2 r) r
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun p : ι × ι => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)
  refine ⟨fun i => ∑ j, z (i, j), funext fun i => ?_⟩
  have e1 : (Γ.map (toOCr l O) *ᵥ fun j => galOCr O (g : GQ l) (toCris t ϖ P m j)) i =
      ∑ j, galOCr O (g : GQ l) (ϖ.iC t K (c j)) * toOCr l O (Γ i j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hcm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : (∑ k ∈ Finset.range n, ϖ.muDiv a O g k • toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩) i =
      ∑ j, ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c j τ), descN_mem_S e q (c j τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ j (k - q) i⟩)) := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, F3, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rw [← mul_assoc, muDiv_mul_choose a O ϖ g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
    ring
  rw [Pi.sub_apply, e1, e2, ← Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => hz (i, j)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C :=
  fun _ _ _ _ _ _ ϖ LL _ _ _ _ _ _ _ _ I C hS hΓ => taylor_of_basis (thetaW _ LL) ϖ I C hS hΓ

end GlobalTheory.TaylorBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecomp
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.HCChar

theorem sum_subgroup {G : Type} [Group G] [Fintype G] (P : Subgroup G) (Φ : P → ℂ) :
    ∑ p : P, Φ p = ∑ x : G, if h : x ∈ P then Φ ⟨x, h⟩ else 0 := by
  have e := Finset.sum_subtype (F := (inferInstance : Fintype P)) (Finset.univ.filter (· ∈ P)) (p := (· ∈ P))
    (by simp) (fun x => if h : x ∈ P then Φ ⟨x, h⟩ else 0)
  rw [Finset.sum_filter] at e
  refine (Eq.trans ?_ e.symm).trans ?_
  · apply Finset.sum_congr rfl; intro a _; simp [dif_pos a.2]
  · apply Finset.sum_congr rfl; intro x _; split_ifs <;> rfl

theorem toG_val {g m : ℕ} [Fact g.Prime] {M : Mt g m} (h : IsUnit M) : ((toG M : Gn g m) : Mt g m) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem card_ker_eq_sum {P M : Type} [Group P] [Fintype P] [Group M] (π : P →* M) :
    (Nat.card π.ker : ℂ) = ∑ p : P, if π p = 1 then (1 : ℂ) else 0 := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MonoidHom.mem_ker]

def blocks {g : ℕ} [Fact g.Prime] (a b n : ℕ) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n))
    (hunit : ∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n)))
    (hmul : ∀ x y : Mt g n, InPar a x → InPar a y →
      tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) :
    P →* Gn g a × Gn g b :=
  MonoidHom.mk' (fun p => (toG (tl a ((p : Gn g n) : Mt g n)), toG (br a b ((p : Gn g n) : Mt g n)))) (by
    intro p q
    have hp := (hP p).1 p.2
    have hq := (hP q).1 q.2
    have hpq := (hP (p * q)).1 (p * q).2
    have hm := hmul _ _ hp hq
    have e1 : (((p * q : P) : Gn g n) : Mt g n) = ((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n) := rfl
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · show ((toG (tl a (((p * q : P) : Gn g n) : Mt g n)) : Gn g a) : Mt g a) =
        ((toG (tl a ((p : Gn g n) : Mt g n)) * toG (tl a ((q : Gn g n) : Mt g n)) : Gn g a) : Mt g a)
      have hu : IsUnit (tl a (((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n))) := by
        rw [hm.1]; exact (hunit _ hp).1.mul (hunit _ hq).1
      rw [Units.val_mul, e1, toG_val hu, toG_val (hunit _ hp).1, toG_val (hunit _ hq).1, hm.1]
    · show ((toG (br a b (((p * q : P) : Gn g n) : Mt g n)) : Gn g b) : Mt g b) =
        ((toG (br a b ((p : Gn g n) : Mt g n)) * toG (br a b ((q : Gn g n) : Mt g n)) : Gn g b) : Mt g b)
      have hu : IsUnit (br a b (((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n))) := by
        rw [hm.2]; exact (hunit _ hp).2.mul (hunit _ hq).2
      rw [Units.val_mul, e1, toG_val hu, toG_val (hunit _ hp).2, toG_val (hunit _ hq).2, hm.2])

theorem hc_isChar_and_res_decomp : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b →
    (∀ (α : Gn g a → ℂ) (β : Gn g b → ℂ), IsChar α → IsChar β → IsChar (hc a b α β n)) ∧
    ∀ χ : Gn g n → ℂ, IsChar χ → ∃ L : List ((Gn g a → ℂ) × (Gn g b → ℂ)),
      (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, res a b χ x y = (L.map fun p => p.1 x * p.2 y).sum := by
  intro g _ a b n hn
  obtain ⟨⟨P, hP⟩, -, hunit, hmul, hcard, hPcard⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  obtain ⟨π, hπv⟩ : ∃ π : P →* Gn g a × Gn g b,
      ∀ p : P, π p = (toG (tl a ((p : Gn g n) : Mt g n)), toG (br a b ((p : Gn g n) : Mt g n))) :=
    ⟨blocks a b n P hP hunit hmul, fun _ => rfl⟩
  have hπ : ∀ (x : Gn g n) (hx : x ∈ P) (h₁ : Gn g a) (h₂ : Gn g b),
      π ⟨x, hx⟩ = (h₁, h₂) ↔ (tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂) := by
    intro x hx h₁ h₂
    have hu := hunit x ((hP x).1 hx)
    rw [hπv]
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
  have hsum : ∀ (f : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b),
      ∑ p : P, (if π p = (h₁, h₂) then f p else 0) =
        ∑ x : Gn g n, if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂ then f x else 0 := by
    intro f h₁ h₂
    rw [sum_subgroup]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ P
    · rw [dif_pos hx]
      have hx' := (hP x).1 hx
      by_cases h : tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂
      · rw [if_pos ((hπ x hx h₁ h₂).2 h), if_pos ⟨hx', h⟩]
      · rw [if_neg (fun e => h ((hπ x hx h₁ h₂).1 e)), if_neg (fun e => h e.2)]
    · rw [dite_eq_right hx, if_neg (fun e => hx ((hP x).2 e.1))]
  have hNP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext x; simp [hP]
  refine ⟨?_, ?_⟩
  · intro α β hα hβ
    have hφ : IsChar (fun p : P => α (π p).1 * β (π p).2) :=
      GlobalTheory.GLm.isChar_comp_hom_and_mul.2 P _ _
        (GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ ((MonoidHom.fst _ _).comp π) α hα)
        (GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ ((MonoidHom.snd _ _).comp π) β hβ)
    obtain ⟨V, hV⟩ := GlobalTheory.GLm.IndChar.isChar_induced (Gn g n) P _ hφ
    refine ⟨V, fun x => (hV x).trans ?_⟩
    unfold hc hcT
    dsimp only
    rw [hNP]
    refine congrArg (fun t : ℂ => (((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹) * t) ?_
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y⁻¹ * x * y ∈ P
    · rw [dif_pos hy, if_pos ((hP _).1 hy), hπv]
    · rw [dite_eq_right hy, if_neg (fun e => hy ((hP _).2 e))]
  · intro χ hχ
    have hsurj : Function.Surjective π := by
      rintro ⟨h₁, h₂⟩
      have hpos : 0 < (Finset.univ.filter fun x : Gn g n =>
          InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card := by
        rw [hcard]; exact pow_pos (Fact.out : g.Prime).pos _
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_filter] at hx
      have hxP := (hP x).2 hx.2.1
      refine ⟨⟨x, hxP⟩, ?_⟩
      exact (hπ x hxP h₁ h₂).2 hx.2.2
    have hχP : IsChar (fun p : P => χ p) := GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ P.subtype χ hχ
    have hΨ := GlobalTheory.GLm.isChar_fibre_mean P (Gn g a × Gn g b) π _ hsurj hχP
    obtain ⟨L, hL, hLs⟩ := _root_.GlobalTheory.GLm.ProdChar.exists_list_prod (Gn g a) (Gn g b) _ hΨ
    refine ⟨L, hL, fun x y => ?_⟩
    rw [← hLs x y]
    have hker : (Nat.card π.ker : ℂ) = (g : ℂ) ^ (a * b) := by
      rw [card_ker_eq_sum, Prod.one_eq_mk]
      refine Eq.trans ?_ ((hsum (fun _ => 1) 1 1).trans ?_)
      · apply Finset.sum_congr rfl; intro p _; split_ifs <;> rfl
      rw [Finset.sum_boole, hcard 1 1]
      push_cast; rfl
    unfold res
    rw [hker]
    refine congrArg (fun t : ℂ => ((g : ℂ) ^ (a * b))⁻¹ * t) ?_
    convert (hsum χ x y).symm using 2
    split_ifs <;> rfl

end GlobalTheory.GLq.HCChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EigFinite

theorem eigSet_finite : HeckeStdPlain → ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.HypOutside X.J X.χ B → (∀ v k (s : SplitPlace D.host.E), GenAt D l Q v k → IsConjPl D.host v s.w → s.v ∉ B) → (EigSet X l Q).Finite := by
  intro hP D μ j X l Q B hB hBv
  classical
  have hex := GlobalTheory.SplitConjPlace.splitEx_all D
  let ι := {p : PlE D.host × ℕ // GenAt D l Q p.1 p.2}
  have hch : ∀ i : ι, ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host i.1.1 s.w ∧ IsUnif D.host.E s.v ϖ := fun i => hex i.1.1 i.2.1
  choose s ϖ hs hϖ using hch
  have hfact := fun i : ι => hP D.host.E D.R.nV X.wt X.J X.χ B X.J_open hB (s i) (ϖ i) i.1.2
    (hBv _ _ _ i.2 (hs i)) (hϖ i) i.2.2.2.2.2.1 i.2.2.2.2.2.2
  have hTS : ∀ y, X.real y ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun y => X.real_range ▸ LinearMap.mem_range_self X.real y
  have hmem : ∀ (i : ι) (y : D.what₂.Mt μ j), ∃ y', X.real y' = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => by
    have h := (hfact i).1 _ (hTS y)
    rw [← X.real_range] at h
    exact h
  choose g hg using hmem
  have h0 : ∀ i : ι, NG.tN X.J (s i) (ϖ i) i.1.2 0 = 0 := fun i => by
    have h := (hfact i).2.1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at h
    simpa using h
  let op : ι → Module.End ℂ (D.what₂.Mt μ j) := fun i =>
    { toFun := g i
      map_add' := fun y y' => X.real_inj (by
        rw [hg, map_add (f := _), map_add (f := _), hg, hg]
        have h := (hfact i).2.1 _ (hTS y) _ (hTS y') 1
        simpa using h)
      map_smul' := fun c y => X.real_inj (by
        rw [hg, map_smul, map_smul, hg]
        have h := (hfact i).2.1 _ (hTS y) 0 (Submodule.zero_mem _) c
        simpa [h0] using h) }
  have hop : ∀ i y, X.real (op i y) = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => hg i y
  have hcomm : ∀ i i' : ι, Commute (op i) (op i') := fun i i' => by
    ext y
    apply X.real_inj
    show X.real (op i (op i' y)) = X.real (op i' (op i y))
    rw [hop, hop, hop, hop]
    exact (hfact i).2.2.1 (s i') (ϖ i') i'.1.2 (hBv _ _ _ i'.2 (hs i')) (hϖ i') i'.2.2.2.2.2.1 i'.2.2.2.2.2.2 _ (hTS y)
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo op
    (fun i i' φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm i' i) φ)
  have hfin : {χ : ι → ℂ | ⨅ i, (op i).maxGenEigenspace (χ i) ≠ ⊥}.Finite :=
    Set.finite_coe_iff.mp (@Finite.of_fintype _ hind.fintypeNeBotOfFiniteDimensional)
  let Φ : (PlE D.host → ℕ → ℂ) → (ι → ℂ) := fun c i => c i.1.1 i.1.2
  apply Set.Finite.of_finite_image (f := Φ)
  · apply hfin.subset
    rintro _ ⟨c, ⟨-, y, hy0, hy⟩, rfl⟩
    show ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) ≠ ⊥
    intro hbot
    apply hy0
    have hyin : y ∈ ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) := by
      rw [Submodule.mem_iInf]
      intro i
      apply Module.End.eigenspace_le_maxGenEigenspace
      rw [Module.End.mem_eigenspace_iff]
      apply X.real_inj
      rw [hop, map_smul]
      exact hy i.1.1 i.1.2 (s i) (ϖ i) i.2 (hs i) (hϖ i)
    rw [hbot] at hyin
    exact (Submodule.mem_bot ℂ).1 hyin
  · rintro c ⟨hc, -⟩ c' ⟨hc', -⟩ hcc
    funext v k
    by_cases h : GenAt D l Q v k
    · exact congrFun hcc ⟨(v, k), h⟩
    · rw [hc v k h, hc' v k h]

end GlobalTheory.EigFinite
end
end

