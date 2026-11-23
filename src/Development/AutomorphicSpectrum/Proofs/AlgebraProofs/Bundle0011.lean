module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankAlgebraicBound
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspace
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwLift
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AffineHilbertIdealSheafOfQuotientIdealTop
section
namespace GlobalTheory.CompanionTheory.Ar.Num.DualLattice

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.Reflexive

theorem locFree_dual : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (β : E →ₗ[Ω] E₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∀ (r : ℕ) (L : AddSubgroup E) (L₁ : AddSubgroup E₁), LocFree R r L → (∀ w, w ∈ L₁ ↔ ∀ v ∈ L, β v w ∈ R) → LocFree R r L₁ ∧ ∀ v, v ∈ L ↔ ∀ w ∈ L₁, β v w ∈ R := by
  intro o Ω _ _ _ R E E₁ _ _ _ _ β hβ r L L₁ h h₁
  classical
  refine ⟨?_, fun v => ⟨fun hv w hw => (h₁ w).1 hw v hv, fun hv => ?_⟩⟩
  swap
  · refine locFree_reflexive R r L h v fun ψ hψ => ?_
    obtain ⟨w, rfl⟩ := hβ.2 ψ
    exact hv w ((h₁ w).2 hψ)
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine ⟨fun a ha w hw => (h₁ _).2 fun v hv => ?_, k, f, c, hf, hc, h1, fun l => ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact R.mul_mem ha ((h₁ w).1 hw v hv)
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  let e : E₁ ≃ₗ[Ω] Module.Dual Ω E := LinearEquiv.ofBijective β.flip hβ
  let C : Module.Basis (Fin r) Ω E₁ := B.dualBasis.map e.symm
  have hrepr : ∀ w q, C.repr w q = β (b q) w := fun w q => by
    simp [C, e, ← hB]
  have hsum : ∀ (a : Fin r → Ω) q, β (b q) (∑ q', a q' • C q') = a q := fun a q => by
    rw [← hrepr]
    exact congrFun (C.repr_sum_self a) q
  refine ⟨C, C.linearIndependent, C.span_eq, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => C.repr w q, fun q => ?_, (C.sum_repr w).symm⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, f l ^ m • b q ∈ L := by
      refine (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · by_cases hq : q' = q
        · subst hq; simp
        · simp [hq]
      · simp [Pi.single_apply]
    refine ⟨n + m, ?_⟩
    have h2 := (h₁ _).1 hn _ hm
    have h3 : β (f l ^ m • b q) (f l ^ n • w) = f l ^ (n + m) * C.repr w q := by
      rw [hrepr]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rwa [h3] at h2
  · rintro ⟨a, ha, rfl⟩
    let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
    have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
    obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l)
      (β.flip (∑ q, a q • C q)) fun v hv => by
        obtain ⟨a', ha', rfl⟩ := (hb v).1 ⟨0, by simpa using hv⟩
        have key : ∀ q, ∃ n : ℕ, f l ^ n • (a' q * a q) ∈ R' := fun q => by
          obtain ⟨n, hn⟩ := ha q
          obtain ⟨n', hn'⟩ := ha' q
          refine ⟨n' + n, ?_⟩
          have h4 : f l ^ (n' + n) • (a' q * a q) = f l ^ n' * a' q * (f l ^ n * a q) := by
            rw [smul_eq_mul]; ring
          rw [h4]
          exact R.mul_mem hn' hn
        obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f l) (hf l) _ key
        refine ⟨n, ?_⟩
        have h5 : β.flip (∑ q, a q • C q) (∑ q, a' q • b q) = ∑ q, a' q * a q := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum (β.flip (∑ q, a q • C q))]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, LinearMap.flip_apply, hsum, smul_eq_mul]
        rw [h5, Finset.mul_sum]
        exact R'.sum_mem fun q _ => hn q
    refine ⟨m, (h₁ _).2 fun v hv => ?_⟩
    rw [map_smul, smul_eq_mul]
    exact hm v hv

end GlobalTheory.CompanionTheory.Ar.Num.DualLattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGenerator
section
namespace GlobalTheory.CompanionTheory.Ar.Num.HhGraded

open GlobalTheory.CompanionTheory.Ar.Num

theorem mem_dotDual_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    (L : AddSubgroup (Fin n → Ω)) (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_annSub_iff {Ω : Type} [Field Ω] {n k : ℕ} (l : Fin n → Ω) :
    l ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → l j = 0 := by
  simp [annSub, Submodule.mem_pi]

theorem single_mem_annSub {Ω : Type} [Field Ω] {n k : ℕ} (j : Fin n) (hj : k ≤ (j : ℕ)) :
    (Pi.single j 1 : Fin n → Ω) ∈ annSub Ω n k := by
  rw [mem_annSub_iff]
  intro m hm
  have : m ≠ j := fun h => by subst h; omega
  simp [Pi.single_apply, this]

theorem map_eq_sum {Ω : Type} [Field Ω] {n : ℕ} (ρ : (Fin n → Ω) →ₗ[Ω] (Fin n → Ω)) (l : Fin n → Ω) :
    ρ l = ∑ j, l j • ρ (Pi.single j 1) := by
  have h : l = ∑ j, l j • (Pi.single j 1 : Fin n → Ω) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [h, map_sum]
  simp only [map_smul]

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ)
    (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) →
    ∀ (i : Fin n) (u : Ω), u ≠ 0 →
    (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔
      ∃ a ∈ R, c = a * u) →
    ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  intro o Ω _ _ _ R n L _ hS i u hu hc t
  constructor
  · rintro ⟨v, hv, hz, rfl⟩
    obtain ⟨l, hl, hlu⟩ := (hc u).2 ⟨1, R.one_mem, (one_mul u).symm⟩
    have hlL : l ∈ L := (AddSubgroup.mem_inf.1 hl).1
    have hlA : l ∈ annSub Ω n i := (AddSubgroup.mem_inf.1 hl).2
    have hlu' : l i = u := hlu
    have h2 : l ⬝ᵥ v = u * v i := by
      rw [dotProduct, Finset.sum_eq_single i, hlu']
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [(mem_annSub_iff l).1 hlA j h, zero_mul]
        · rw [hz j h, mul_zero]
      · simp
    refine ⟨u * v i, ?_, ?_⟩
    · rw [← h2]
      exact (mem_dotDual_iff R L v).1 hv l hlL
    · field_simp
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ρ, hρU, hρid, hρL⟩ := hS i
    have hfix : ∀ j : Fin n, i ≤ j → ρ (Pi.single j 1) = Pi.single j 1 := fun j hj =>
      hρid _ (single_mem_annSub j hj)
    refine ⟨fun j => (a * u⁻¹) * ρ (Pi.single j 1) i, ?_, ?_, ?_⟩
    · rw [mem_dotDual_iff]
      intro l hl
      have key : l ⬝ᵥ (fun j => (a * u⁻¹) * ρ (Pi.single j 1) i) = (a * u⁻¹) * ρ l i := by
        rw [map_eq_sum ρ l, dotProduct, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have hl' : ρ l i ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map
          (Pi.evalAddMonoidHom (fun _ => Ω) i) :=
        ⟨ρ l, AddSubgroup.mem_inf.2 ⟨hρL l hl, hρU l⟩, rfl⟩
      obtain ⟨b, hb, hbe⟩ := (hc _).1 hl'
      have h3 : a * u⁻¹ * (b * u) = a * b := by field_simp
      rw [key, hbe, h3]
      exact R.mul_mem ha hb
    · intro j hj
      have hne : i ≠ j := ne_of_lt hj
      simp only [hfix j hj.le, Pi.single_apply, hne, if_false, mul_zero]
    · simp only [hfix i le_rfl, Pi.single_eq_same, mul_one]

end GlobalTheory.CompanionTheory.Ar.Num.HhGraded
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegDual

open GlobalTheory.CompanionTheory.Ar.Crv Module

variable {K : Type} [Field K] (C : ACurve K)
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem isLatOf_dual (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K) (i : C.I) {n : ℕ}
    (b : Basis (Fin n) K V) (b' : Basis (Fin n) K V')
    (hb : ∀ y q, b'.repr y q = B (b q) y) (h : IsLatOf C i b (L i)) :
    IsLatOf C i b' (dualLat C L B i) := by
  intro y
  change (∀ x ∈ L i, C.v i (B x y) ≤ 1) ↔ _
  constructor
  · intro hy q
    rw [hb]
    refine hy _ ((h _).2 fun p => ?_)
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · intro hy x hx
    have hx' := (h x).1 hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine (C.v i).map_sum_le fun q _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, ← hb]
    exact mul_le_one' (hx' q) (hy q)

theorem dual_symm (B : V →ₗ[K] V' →ₗ[K] K) {n : ℕ}
    (b : Basis (Fin n) K V) (b' : Basis (Fin n) K V')
    (hb : ∀ y q, b'.repr y q = B (b q) y) (x : V) (q : Fin n) :
    b.repr x q = B.flip (b' q) x := by
  have : b.coord q = B.flip (b' q) := by
    refine b.ext fun p => ?_
    rw [LinearMap.flip_apply, ← hb, Basis.coord_apply, Basis.repr_self, Basis.repr_self,
      Finsupp.single_apply, Finsupp.single_apply]
    simp [eq_comm]
  rw [← this, Basis.coord_apply]

theorem exists_dual [FiniteDimensional K V] [FiniteDimensional K V'] (B : V →ₗ[K] V' →ₗ[K] K)
    (hB : Function.Bijective B) {n : ℕ} (b : Basis (Fin n) K V) :
    ∃ b' : Basis (Fin n) K V', ∀ y q, b'.repr y q = B (b q) y := by
  have hf : Function.Bijective B.flip := (LinearMap.flip_bijective_iff₁).2 hB
  refine ⟨b.dualBasis.map (LinearEquiv.ofBijective B.flip hf).symm, fun y q => ?_⟩
  simp

theorem det_dual (B : V →ₗ[K] V' →ₗ[K] K) {n : ℕ}
    (b₀ b : Basis (Fin n) K V) (b₀' b' : Basis (Fin n) K V')
    (h₀ : ∀ y q, b₀'.repr y q = B (b₀ q) y) (hb : ∀ y q, b'.repr y q = B (b q) y) :
    b₀'.det b' = (b₀.det b)⁻¹ := by
  have h1 : b₀'.toMatrix b' = (b.toMatrix b₀).transpose := by
    ext p q
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, h₀,
      dual_symm B b b' hb, LinearMap.flip_apply]
  have h2 : (b.toMatrix b₀).det * (b₀.toMatrix b).det = 1 := by
    rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [Basis.det_apply, Basis.det_apply, h1, Matrix.det_transpose]
  exact eq_inv_of_mul_eq_one_left h2

theorem isLatOf_reindex (i : C.I) {n m : ℕ} (b : Basis (Fin n) K V) (e : Fin n ≃ Fin m)
    (L : AddSubgroup V) (h : IsLatOf C i b L) : IsLatOf C i (b.reindex e) L := by
  intro x
  rw [h x]
  simp only [Basis.repr_reindex_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩

theorem deg_dual : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B →
    IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧
      dualLat C (dualLat C L B) B.flip = L := by
  intro K _ C V _ _ _ V' _ _ _ L B hL hB
  obtain ⟨hloc, b₀, hfin⟩ := id hL
  choose b hb using hloc
  choose d hd using fun c : Basis (Fin (finrank K V)) K V => exists_dual B hB c
  have hrk : finrank K V = finrank K V' := by
    rw [finrank_eq_card_basis (d b₀), Fintype.card_fin]
  have hd' : ∀ i, IsLatOf C i (d (b i)) (dualLat C L B i) := fun i =>
    isLatOf_dual C L B i (b i) _ (hd _) (hb i)
  have hbun : IsBun C (dualLat C L B) := by
    refine ⟨fun i => ⟨_, isLatOf_reindex C i _ (finCongr hrk) _ (hd' i)⟩,
      (d b₀).reindex (finCongr hrk), hfin.subset fun i hi h => hi ?_⟩
    exact isLatOf_reindex C i _ _ _ (isLatOf_dual C L B i b₀ _ (hd _) h)
  refine ⟨hbun, ?_, ?_⟩
  · rw [(_root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V' _ _ (d b₀) (fun i => d (b i)) hbun hd').2,
      (_root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V _ _ b₀ b hL hb).2, ← finsum_neg_distrib]
    refine finsum_congr fun i => ?_
    rw [det_dual B b₀ (b i) _ _ (hd _) (hd _), map_inv₀, WithZero.log_inv, mul_neg]
  · funext i
    ext x
    rw [hb i x]
    exact isLatOf_dual C _ B.flip i (d (b i)) (b i) (dual_symm B _ _ (hd _)) (hd' i) x

end GlobalTheory.CompanionTheory.Ar.Crv.DegDual
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrime
section
namespace GlobalTheory.CompanionTheory.CommAlg

theorem exists_flat_henselian_normal_over_prime :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime],
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R')
        (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧
          (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  exact @PositivityTheory.HtPt.Htat.hens_normal

end GlobalTheory.CompanionTheory.CommAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsPowPrincipal
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_principal : ∀ (F : Type) [Field F] [NumberField F]
    (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧
        v.valuation F α = WithZero.exp (-n) := by
  intro F _ _ r
  obtain ⟨M, α, hM, hα, h⟩ := GlobalTheory.RootIdeal.exists_count_spanSingleton_eq_mul F r
  exact ⟨M, α, hM, hα, fun v => ⟨_, h v, GlobalTheory.Idele.valuation_eq_exp_neg_count v hα⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
section
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFrob

variable {K : Type} [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]

theorem det_frobVec {d : ℕ} (b : Fin d → Fin d → K) :
    (Pi.basisFun K (Fin d)).det (fun q => frobVec p (b q)) =
      ((Pi.basisFun K (Fin d)).det b) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [Module.Basis.det_apply, Module.Basis.det_apply, ← frobenius_def, RingHom.map_det]
  congr 1

theorem exists_frob_basis {n d : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ q, b' q = frobVec p (b q) := by
  have hnd : n = d := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at h
    exact h.symm
  subst hnd
  have hb : IsUnit ((Pi.basisFun K (Fin n)).det b) :=
    (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).1 ⟨b.linearIndependent, b.span_eq⟩
  have hb' : IsUnit ((Pi.basisFun K (Fin n)).det (fun q => frobVec p (b q))) := by
    rw [det_frobVec p (⇑b)]; exact hb.pow p
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).2 hb'
  exact ⟨Module.Basis.mk hli hsp.ge, fun q => Module.Basis.mk_apply _ _ _⟩

theorem repr_frobVec {n d : ℕ} (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (y : Fin d → K) (q : Fin n) :
    b'.repr (frobVec p y) q = (b.repr y q) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  have key : frobVec p y = ∑ i, (b.repr y i) ^ p • b' i := by
    conv_lhs => rw [← b.sum_repr y]
    funext j
    simp only [frobVec, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_pow_char, mul_pow]
  rw [key, Module.Basis.repr_sum_self]

theorem isLatOf_frob {n d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (i : C.I)
    (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (hb : IsLatOf C i b (L i)) :
    IsLatOf C i b' (frobLat C p L i) := by
  intro x
  change x ∈ AddSubgroup.closure _ ↔ _
  constructor
  · intro hx
    have hle : AddSubgroup.closure {y | ∃ (a : K) (z : Fin d → K), C.v i a ≤ 1 ∧ z ∈ L i ∧
        y = a • frobVec p z} ≤ GlobalTheory.CompanionTheory.Ar.Crv.Inhab.latOf C i b' := by
      rw [AddSubgroup.closure_le]
      rintro y ⟨a, z, ha, hz, rfl⟩
      change ∀ q, C.v i (b'.repr (a • frobVec p z) q) ≤ 1
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, repr_frobVec p b b' h z q, map_mul, map_pow]
      exact mul_le_one' ha (pow_le_one' ((hb z).1 hz q) p)
    exact hle hx
  · intro hx
    rw [← b'.sum_repr x]
    refine AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure
      ⟨b'.repr x q, b q, hx q, (hb (b q)).2 fun r => ?_, by rw [h]⟩
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isBun_frobLat {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (hL : IsBun C L) :
    IsBun C (frobLat C p L) := by
  obtain ⟨h1, b₀, hfin⟩ := hL
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h1 i
    obtain ⟨b', hb'⟩ := exists_frob_basis p b
    exact ⟨b', isLatOf_frob C p L i b b' hb' hb⟩
  · obtain ⟨b', hb'⟩ := exists_frob_basis p b₀
    refine ⟨b', hfin.subset fun i hi => ?_⟩
    intro h
    exact absurd (isLatOf_frob C p L i b₀ b' hb' h) hi

theorem deg_frobLat : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L →
      IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  intro K _ C p _ _ d L hL
  have hL' := isBun_frobLat C p L hL
  refine ⟨hL', ?_⟩
  choose b hb using hL.1
  choose b' hb' using fun i => exists_frob_basis p (b i)
  have e : Fin d ≃ Fin (Module.finrank K (Fin d → K)) := finCongr (Module.finrank_fin_fun K).symm
  set b₀ := (Pi.basisFun K (Fin d)).reindex e with hb₀
  have hdet : ∀ i, b₀.det (b' i) = (b₀.det (b i)) ^ p := by
    intro i
    rw [hb₀, Module.Basis.det_reindex, Module.Basis.det_reindex]
    have hc : (⇑(b' i) ∘ ⇑e) = fun q => frobVec p ((⇑(b i) ∘ ⇑e) q) := by
      funext q; exact hb' i (e q)
    rw [hc, det_frobVec]
  obtain ⟨-, h1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C (Fin d → K) L _ b₀ b hL hb
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C (Fin d → K) (frobLat C p L) _ b₀ b' hL'
    (fun i => isLatOf_frob C p L i (b i) (b' i) (hb' i) (hb i))
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  rw [hdet, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.DegFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelRankBoundNormValuation
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lemF_algebra : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → (∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (ρ a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ :=
  @PositivityTheory.Xgn.kernel_rank_algebraic_bound

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspaceStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_adapted_to_subspace : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] (i : C.I) (n : ℕ) (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) (W : Submodule K V), IsLatOf C i b L → ∃ (bW : Module.Basis (Fin (Module.finrank K W)) K W) (bQ : Module.Basis (Fin (Module.finrank K (V ⧸ W))) K (V ⧸ W)) (b' : Module.Basis (Fin (Module.finrank K W + Module.finrank K (V ⧸ W))) K V), IsLatOf C i b' L ∧ IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) ∧ IsLatOf C i bQ (L.map W.mkQ.toAddMonoidHom) ∧ (∀ j, b' (Fin.castAdd _ j) = bW j) ∧ ∀ j, W.mkQ (b' (Fin.natAdd _ j)) = bQ j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnitsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_embeddings_conjugate_of_units : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (κ κ' : K →+* ℂ_[p]), (∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) → ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | exact GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIsometryEquivariance
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem proIsoAt_of_padic_isometry : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_lift

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProIsometryOfLocalIsometries
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem ProIso.nonempty_of_forall_prime : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_crt

end GlobalTheory.CompanionTheory.Ar
end

