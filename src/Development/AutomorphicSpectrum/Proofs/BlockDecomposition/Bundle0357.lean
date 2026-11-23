module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0346
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023
public import GroundTheory.AutomorphicForms.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishingStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_constant_term_vanishing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (r + s)), ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) → (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧ ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧ ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapStable.capStable | exact GlobalTheory.CompanionTheory.CTFin.CapStable.capStable | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapStable.capStable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliUnseenStatementStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_restrict_levi : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.capelli_restrict | exact GlobalTheory.CompanionTheory.CTFin.capelli_restrict | (intros; apply GlobalTheory.CompanionTheory.CTFin.capelli_restrict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalarStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_eq_of_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
  first | exact @GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | exact GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | (intros; apply GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegreeStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_twist_pow_degree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | exact GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | (intros; apply GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerCompactReduction
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem double_coset_eq_iff {G : Type*} [Group G] (D g g' a a' : G) :
    g * D * a⁻¹ = g' * D * a'⁻¹ ↔ (g⁻¹ * g')⁻¹ * D * (a⁻¹ * a') = D := by
  constructor
  · intro h
    calc (g⁻¹ * g')⁻¹ * D * (a⁻¹ * a') = g'⁻¹ * (g * D * a⁻¹) * a' := by group
      _ = g'⁻¹ * (g' * D * a'⁻¹) * a' := by rw [h]
      _ = D := by group
  · intro h
    calc g * D * a⁻¹ = g' * ((g⁻¹ * g')⁻¹ * D * (a⁻¹ * a')) * a'⁻¹ := by group
      _ = g' * D * a'⁻¹ := by rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def orbMap (d : GL (Fin n) E) (g : GA E n) : GA E n := g * ratGL E n d * (thetaA E n g)⁻¹

theorem orbMap_eq_iff (d : GL (Fin n) E) (g g' : GA E n) :
    orbMap d g = orbMap d g' ↔ g⁻¹ * g' ∈ adCent d := by
  have hm : g⁻¹ * g' ∈ adCent d ↔
      (g⁻¹ * g')⁻¹ * ratGL E n d * thetaA E n (g⁻¹ * g') = ratGL E n d := Iff.rfl
  rw [hm, map_mul, map_inv]
  exact double_coset_eq_iff _ _ _ _ _

theorem continuous_orbMap (d : GL (Fin n) E) : Continuous (orbMap (E := E) (n := n) d) := by
  unfold orbMap
  exact (continuous_id.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.inv

theorem orbMap_ratGL (d r : GL (Fin n) E) :
    orbMap d (ratGL E n r) = ratGL E n (r * d * (thetaE E n r)⁻¹) := by
  unfold orbMap
  rw [GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL, map_mul, map_mul, map_inv]

theorem finite_orbMap_inter (d : GL (Fin n) E) {C : Set (GA E n)} (hC : IsCompact C) :
    (orbMap d '' C ∩ orbMap d '' ((ratGL E n).range : Set (GA E n))).Finite := by
  refine ((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem (hC.image (continuous_orbMap d))).image (ratGL E n)).subset ?_
  rintro _ ⟨h1, _, ⟨r, rfl⟩, rfl⟩
  rw [orbMap_ratGL] at h1 ⊢
  exact ⟨_, h1, rfl⟩

theorem ratGL_mem_ratCent (d r : GL (Fin n) E) (h : ratGL E n r ∈ adCent d) :
    ratGL E n r ∈ ratCent d := by
  refine ⟨r, ?_, rfl⟩
  have h' : twConj (thetaA E n) (ratGL E n r) (ratGL E n d) = ratGL E n d := h
  rw [twConj, GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul] at h'
  exact GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL h'

theorem exists_isCompact_ratCent_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (C : Set (GA E n)), IsCompact C →
      ∃ C' : Set (GA E n), IsCompact C' ∧ ∀ t ∈ adCent d, t ∈ ((ratGL E n).range : Set (GA E n)) * C →
        t ∈ (ratCent d : Set (GA E n)) * C' := by
  intro E _ _ _ n d C hC
  obtain ⟨T, hTΓ, hT⟩ := GroundTheory.Automorphic.Anisotropic.exists_finset_of_orbit (orbMap d) (adCent d) (ratGL E n).range
    (orbMap_eq_iff d) C (finite_orbMap_inter d hC)
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  rintro t ht ⟨γ, hγ, c, hc, rfl⟩
  obtain ⟨δ, hδT, hγδ, -⟩ := hT _ ht γ hγ c hc rfl
  obtain ⟨r, rfl⟩ := hγ
  obtain ⟨s, rfl⟩ := hTΓ δ hδT
  rw [← map_mul] at hγδ
  refine Set.mem_mul.2 ⟨ratGL E n (r * s), ratGL_mem_ratCent d _ hγδ,
    (ratGL E n s)⁻¹ * c, Set.mem_biUnion hδT ⟨c, hc, rfl⟩, ?_⟩
  rw [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.TorusCh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizer
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.CommMem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_sq_eq_one : (thetaA E n) ^ 2 = 1 := by
  ext g : 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (thetaR (conjAd E) n (thetaR (conjAd E) n g)).val i j = g.val i j
  rw [thetaR_val]
  have h : (thetaR (conjAd E) n g)⁻¹ = thetaR (conjAd E) n g⁻¹ := (map_inv _ _).symm
  rw [h, thetaR_val, inv_inv]
  simp [GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol]

theorem twNorm_ratGL (d : GL (Fin n) E) :
    twNorm (thetaA E n) 2 (ratGL E n d) = ratGL E n (nrm d) := by
  rw [nrm, map_mul, ← GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL]
  simp [twNorm]

theorem rm_algebraMap (a : E) :
    rm (algebraMap E (Matrix (Fin n) (Fin n) E) a) =
      algebraMap (Ad E) (Matrix (Fin n) (Fin n) (Ad E)) (algebraMap E (Ad E) a) := by
  ext i j
  by_cases h : i = j <;> simp [rm, Matrix.algebraMap_matrix_apply, h]

theorem comm_rm_aeval (x : Matrix (Fin n) (Fin n) (Ad E)) (γ : Matrix (Fin n) (Fin n) E)
    (hx : x * rm γ = rm γ * x) (f : E[X]) : x * rm (aeval γ f) = rm (aeval γ f) * x := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, rm_algebraMap]
    exact (Algebra.commutes _ x).symm
  | add p q hp hq =>
    rw [map_add (f := _), rm_add, mul_add, add_mul, hp, hq]
  | monomial m a h =>
    have e : aeval γ (C a * X ^ (m + 1)) = aeval γ (C a * X ^ m) * γ := by
      simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
    rw [e, rm_mul, ← mul_assoc, h, mul_assoc, hx, mul_assoc]

theorem adCent_comm_rm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  intro E _ _ _ n d t ht e he
  obtain ⟨f, rfl⟩ := he
  refine comm_rm_aeval _ _ ?_ f
  have h := twCent_commute_twNorm (thetaA E n) thetaA_sq_eq_one (ratGL E n d) ht
  rw [twNorm_ratGL] at h
  exact congrArg Units.val h

end GlobalTheory.CompanionTheory.TorusCh.CommMem

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjection
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem exists_perm_of_reps {G : Type} [Group G] (J H : Subgroup G) {r : ℕ} (x : Fin r → G)
    (hx : ∀ i, x i ∈ J) (hu : ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) {j : G} (hj : j ∈ J) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, (x (σ i))⁻¹ * (j * x i) ∈ H := by
  have h : ∀ i, ∃ k, (x k)⁻¹ * (j * x i) ∈ H := fun i => (hu _ (J.mul_mem hj (hx i))).exists
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf a
    have hb := hf b
    rw [← hab] at hb
    have hm : (x a)⁻¹ * x b ∈ H := by
      have h2 := H.mul_mem (H.inv_mem ha) hb
      have e : ((x (f a))⁻¹ * (j * x a))⁻¹ * ((x (f a))⁻¹ * (j * x b)) = (x a)⁻¹ * x b := by group
      rwa [e] at h2
    have h1 : (x b)⁻¹ * x b ∈ H := by simp [H.one_mem]
    exact (hu (x b) (hx b)).unique hm h1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem exists_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  intro G _ _ _ J hJ V _ _ π hπ
  have hsub : ∀ v, v - GlobalTheory.LocGL.idem hπ hJ v ∈ twKer π J 1 := fun v => by
    rw [← GlobalTheory.LocGL.idem_eq_zero_iff hπ hJ, map_sub,
      GlobalTheory.LocGL.idem_of_mem hπ hJ (GlobalTheory.LocGL.idem_mem hπ hJ v), sub_self]
  refine ⟨GlobalTheory.LocGL.idem hπ hJ, GlobalTheory.LocGL.idem_mem hπ hJ, fun v hv => GlobalTheory.LocGL.idem_of_mem hπ hJ hv,
    ?_, ?_, ?_⟩
  · intro l hl
    have hk : twKer π J 1 ≤ LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨n, v, rfl⟩
      have h1 : l (π (n : G) v) = l v := LinearMap.congr_fun (hl n n.2) v
      simp [h1]
    refine LinearMap.ext fun v => ?_
    have h2 := hk (hsub v)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2.symm
  · intro x hx
    exact LinearMap.ext fun v => GlobalTheory.LocGL.idem_apply_mem hπ hJ hx v
  · intro u H _ hu r x hr hxJ hex
    have hrc : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
    have hfix : ((r : ℂ)⁻¹ • ∑ i, π (x i) u) ∈ fixed π J := GlobalTheory.Parabolic.mem_fixed.2 fun j hj => by
      obtain ⟨σ, hσ⟩ := exists_perm_of_reps J H x hxJ hex hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun i => ?_
      have e : j * x i = x (σ i) * ((x (σ i))⁻¹ * (j * x i)) := by group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hu _ (hσ i)]
    have h3 : GlobalTheory.LocGL.idem hπ hJ ((r : ℂ)⁻¹ • ∑ i, π (x i) u) = GlobalTheory.LocGL.idem hπ hJ u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => GlobalTheory.LocGL.idem_apply_mem hπ hJ (hxJ i) u,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hrc, one_smul]
    rw [← h3, GlobalTheory.LocGL.idem_of_mem hπ hJ hfix]

end GlobalTheory.CompanionTheory.CompactAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CosetReps

theorem exists_fin_coset_reps (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J H A : Subgroup G) (hJ : IsCompact (J : Set G)) (hH : IsOpen (H : Set G))
    (_hHJ : H ≤ J) (_hAJ : A ≤ J) (hcov : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) :
    ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧
      ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  classical
  obtain ⟨t, ht⟩ := hJ.elim_finite_subcover
    (fun a : A => (fun y : G => (a : G)⁻¹ * y) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_const.mul continuous_id))
    (fun y hy => by
      obtain ⟨a, ha, hay⟩ := hcov y hy
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, hay⟩)
  let T : Finset (G ⧸ H) := t.image (fun a : A => ((a : G) : G ⧸ H))
  have rep : ∀ q : T, ∃ a : A, ((a : G) : G ⧸ H) = q := by
    rintro ⟨q, hq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨a, rfl⟩
  choose f hf using rep
  have key : ∀ y ∈ J, ((y : G) : G ⧸ H) ∈ T := by
    intro y hy
    obtain ⟨a, hat, hay⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Finset.mem_image.2 ⟨a, hat, QuotientGroup.eq.2 hay⟩
  let e : T ≃ Fin T.card := T.equivFin
  have main : ∀ y ∈ J, ∃! i, ((f (e.symm i) : A) : G)⁻¹ * y ∈ H := by
    intro y hy
    refine ⟨e ⟨_, key y hy⟩, ?_, ?_⟩
    · refine QuotientGroup.eq.1 ?_
      rw [Equiv.symm_apply_apply, hf]
    · intro i hi
      have h1 : (((f (e.symm i) : A) : G) : G ⧸ H) = ((y : G) : G ⧸ H) := QuotientGroup.eq.2 hi
      rw [hf] at h1
      rw [← Equiv.symm_apply_eq]
      exact Subtype.ext h1
  obtain ⟨i₀, -⟩ := main 1 J.one_mem
  exact ⟨T.card, i₀.pos, fun i => ((f (e.symm i) : A) : G), fun i => (f (e.symm i)).2, main⟩

end GlobalTheory.CompanionTheory.CosetReps
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnseenStatementBStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unseen_statement_b : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₂ : Set (Module.End ℂ (Sm E s)), Cofin J₂ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₂ : Subgroup (GL (Fin s) (Af E))) (ρ₂ : Representation ℂ (Kinf E s) W), IsOpen (L₂ : Set (GL (Fin s) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₂ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₁ : GA E r, ∃ G ∈ genSpace L₂ ρ₂ J₂, ∀ m₂ : GA E s, G.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | exact GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMatMir
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

def rowQ (n : ℕ) (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  fun j => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) (Fin.castSucc j)

def unipM (n : ℕ) : Multiplicative (Fin (n + 1) → k) →* Mir k (n + 1) :=
  (unip k (n + 1)).codRestrict (Mir k (n + 1)) (fun v => MirU_le_Mir k (n + 1) ⟨v, rfl⟩)

theorem unipM_val (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) :
    ((unipM k n v : Mir k (n + 1)) : GL (Fin (n + 2)) k) = unip k (n + 1) v := rfl

theorem unipM_mem_MirUin (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) : unipM k n v ∈ MirUin k (n + 1) := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

theorem rowQ_one (n : ℕ) : rowQ k n 1 = Pi.single (Fin.last n) 1 := by
  funext j
  by_cases h : j = Fin.last n
  · subst h
    simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ]
  · simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ, Matrix.one_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_matMir (n : ℕ) :
    Continuous fun g : Mir k (n + 1) => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_rowQ (n : ℕ) : Continuous (rowQ k n) :=
  continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp (continuous_matMir n))

theorem continuous_unipM (n : ℕ) :
    Continuous fun v : Fin (n + 1) → k => unipM k n (Multiplicative.ofAdd v) := by
  have hcol : Continuous fun v : Fin (n + 1) → k => GlobalTheory.BZMir.colMat k (n + 1) v := by
    refine continuous_matrix fun i j => ?_
    unfold GlobalTheory.BZMir.colMat
    by_cases hj : j = Fin.last (n + 1)
    · simp only [if_pos hj]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simp only [Fin.lastCases_castSucc]
        exact continuous_apply i
      · simp only [Fin.lastCases_last]
        exact continuous_const
    · simp only [if_neg hj]
      exact continuous_const
  have hval : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) + GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.add hcol
  have hinv : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) - GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.sub hcol
  have hGL : Continuous fun v : Fin (n + 1) → k =>
      GlobalTheory.BZMir.unip k (n + 1) (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mirProj (n : ℕ) : Continuous (mirabolicProjection k n) := by
  have hval : Continuous fun g : Mir k n =>
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp continuous_subtype_val
  have hblock : Continuous fun g : Mir k n =>
      ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
  have hinv : Continuous fun g : Mir k n => g⁻¹ := by
    exact continuous_inv
  refine Units.continuous_iff.2 ⟨hblock, ?_⟩
  have : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    funext g
    rw [map_inv]
  show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
  rw [this]
  exact hblock.comp hinv

end GlobalTheory.CompanionTheory.BZMirFun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosieve_pairing_family_compat : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_gen | exact GlobalTheory.CompanionTheory.KunGlue.glue_gen | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_gen <;> assumption)
end

