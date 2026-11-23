module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0201
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Per.TiedField

theorem exists_inv_filD {l : ℕ} [Fact l.Prime] (x : Per.BdR l) (h0 : x ∈ Per.FilD l 0)
    (h1 : x ∉ Per.FilD l 1) : ∃ y ∈ Per.FilD l 0, x * y = 1 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := GlobalTheory.MemLoc.filD_laws l
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.FilLaws.exists_isEps l
  obtain ⟨z, hz⟩ := (_root_.GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l e he 0 x).1 h0
  rw [neg_zero, Int.toNat_zero, pow_zero, pow_zero, mul_one, one_mul] at hz
  subst hz
  have hz1 : Per.θD l z ≠ 0 := fun h => h1 ((hlast 1 z).2 ((hker z).1 h))
  obtain ⟨w, hw⟩ := (hunit z hz1).exists_right_inv
  refine ⟨algebraMap (Per.BdRp l) (Per.BdR l) w, ?_, by rw [← map_mul, hw, map_one]⟩
  have := Submodule.smul_mem _ w hone
  rwa [Algebra.smul_def, mul_one] at this

theorem tied_field : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    IsField P.R.BdR ∧ IsDomain P.R.B ∧ Function.Injective P.ιB ∧ Function.Injective P.φB ∧
      ∀ (K : FinExt l) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 → x ∉ (P.PD K).Fil 1 →
        ∃ y ∈ (P.PD K).Fil 0, x * y = 1 := by
  intro l _ P AI T
  have hF : IsField P.R.BdR := T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1
  obtain ⟨K₁⟩ : Nonempty (FinExt l) := ⟨⟨⊥, inferInstance⟩⟩
  have hι : Function.Injective P.ιB := fun a b h =>
    (P.PD K₁).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)
  have hφ : Function.Injective P.φB := fun a b h =>
    (P.PD K₁).φ_inj (by rw [P.PD_φ, P.PD_φ]; exact h)
  refine ⟨hF, ?_, hι, hφ, fun K x h0 h1 => ?_⟩
  · have := hF.isDomain
    exact hι.isDomain (P.ιB : P.R.B →+* P.R.BdR)
  · obtain ⟨y, hy, hxy⟩ := exists_inv_filD (T.eD x) ((T.fil K 0 x).1 h0) (fun h => h1 ((T.fil K 1 x).2 h))
    refine ⟨T.eD.symm y, (T.fil K 0 _).2 (by rwa [RingEquiv.apply_symm_apply]), T.eD.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, hxy, map_one]

end GlobalTheory.Per.TiedField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJordanHolderThroughLine
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models.ThroughLine

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (K : Ob k G) (f : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A f ∧ Function.Injective f ∧ Function.Exact f p := by
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) (fun g x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hp g x, LinearMap.mem_ker.mp hx, map_zero]))
  refine ⟨K, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (LinearMap.ker p).subtype_injective.comp e.symm.injective, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [← he]
    simp
  · exact ⟨e ⟨y, hy⟩, by simp⟩
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact j q := by
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) (fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨A.ρ g y, hj g y⟩))
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => he g (Submodule.Quotient.mk x),
    e.surjective.comp (LinearMap.range j).mkQ_surjective, fun y => ?_⟩
  simp [Submodule.Quotient.mk_eq_zero]

theorem simple_chr (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have h : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule k (Fin 1 → k)) (congrArg Subrepresentation.toSubmodule h')
  · rcases eq_bot_or_eq_top S.toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.toSubmodule_injective h')
    · exact Or.inr (Subrepresentation.toSubmodule_injective h')

theorem sameSS_three {s t u : ℕ} {M : Type} [AddCommGroup M] [Module k M] {π : Representation k G M}
    (C : (Fin s ⊕ Unit) ⊕ Fin t → Ob k G) (e : Fin u ≃ (Fin s ⊕ Unit) ⊕ Fin t)
    (h : SameSS π (((piRep fun a => (C (.inl (.inl a))).ρ).prod (C (.inl (.inr ()))).ρ).prod
      (piRep fun a => (C (.inr a)).ρ))) : SameSS π (piRep fun a => (C (e a)).ρ) := by
  have h1 : SameSS π (piRep fun a => (C a).ρ) := by
    refine h.congr_right
      ((((LinearEquiv.refl k _).prodCongr (LinearEquiv.piUnique k (fun a : Unit => Fin (C (.inl (.inr a))).m → k)).symm).trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s) Unit (fun a => Fin (C (.inl a)).m → k)).symm).prodCongr
          (LinearEquiv.refl k _) |>.trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s ⊕ Unit) (Fin t) (fun a => Fin (C a).m → k)).symm) ?_
    intro g x
    funext a
    rcases a with (a | a) | a <;> rfl
  refine h1.congr_right (LinearEquiv.piCongrLeft k (fun a => Fin (C a).m → k) e).symm ?_
  intro g x
  rfl

end GlobalTheory.Models.ThroughLine


open GlobalTheory.Models.ThroughLine in
theorem GlobalTheory.Models.ModTh.exists_jordanHolder_through_line : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  intro k G _ _ l n _ _ _ R F r Dt M B A₁ χ j p N hN hj hji hp hps
  obtain ⟨K, f, hf, hfi, hfe⟩ := exists_ker A₁ (chr χ) p hp
  obtain ⟨Q, q, hq, hqs, hqe⟩ := exists_coker A₁ B j hj
  have hA := _root_.GlobalTheory.Models.SubModel.model_pre F M A₁ B j N hj hji hN
  have hK := _root_.GlobalTheory.Models.SubModel.model_pre F M K A₁ f _ hf hfi hA
  have hL := GlobalTheory.Models.ModTh.model_push_of_surjective F M A₁ (chr χ) p _ hp hps hA
  have hQ := GlobalTheory.Models.ModTh.model_push_of_surjective F M B Q q _ hq hqs hN
  obtain ⟨s, C, L, c1, c2, c3, c4⟩ := _root_.GlobalTheory.Models.ModTh.exists_simple_pieces F M K _ hK
  obtain ⟨t, C', L', d1, d2, d3, d4⟩ := _root_.GlobalTheory.Models.ModTh.exists_simple_pieces F M Q _ hQ
  obtain ⟨oB, lB, -, cB⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M B N hN
  obtain ⟨oA, lA, -, cA⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M A₁ _ hA
  let S : (Fin s ⊕ Unit) ⊕ Fin t → Σ A : Ob k G, Lats k n A.m :=
    Sum.elim (Sum.elim (fun a => ⟨C a, L a⟩) fun _ => ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩)
      fun a => ⟨C' a, L' a⟩
  let e := (Fintype.equivFin ((Fin s ⊕ Unit) ⊕ Fin t)).symm
  have hfl : ∀ m : ℕ, IsFiniteLength k (Fin m → k) := fun m =>
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨_, fun a => (S (e a)).1, fun a => (S (e a)).2, e.symm (.inl (.inr ())), fun a => ?_, fun a => ?_,
    ?_, fun i x => ?_, ?_⟩
  · show M.Model (S (e a)).1 (S (e a)).2
    rcases e a with (b | b) | b
    exacts [c1 b, hL, d1 b]
  · show IsSimpleModule (MonoidAlgebra k G) (S (e a)).1.ρ.asModule
    rcases e a with (b | b) | b
    exacts [c2 b, simple_chr χ, d2 b]
  · refine sameSS_three (fun a => (S a).1) e ?_
    exact (SameSS.of_exact hj hq hji hqs hqe (hfl _)).trans
      (((SameSS.of_exact hf hp hfi hps hfe (hfl _)).trans (c3.prod (SameSS.refl _ (hfl _)))).prod d3)
  · rw [Equiv.sum_comp e (fun a => sen ((F.D (S a).1).γ i) ((S a).2 i) x), Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit),
      _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F A₁ B Q j q N oB hj hq hji hqs hqe i (lB i) (cB i) x,
      _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F K A₁ (chr χ) f p _ oA hf hp hfi hps hfe i (lA i) (cA i) x, c4, d4]
    rfl
  · show S (e (e.symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyEqLeadingCoeffBreuilKisinDescent
section
noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in
theorem natCast_l_ne_zero : (l : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K)]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem exists_Mon_eq_Lc_cls : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hU hUI hUc hη1 hηH hl hl2 hC hS y hy
  have hlK : (l : K) ≠ 0 := natCast_l_ne_zero
  set k : ℕ := l - 14 * H with hk
  have hlk : ((l : K) ^ k) ≠ 0 := pow_ne_zero _ hlK
  have hint := _root_.GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral O K l e a ι η H D hηH hl2
  have hcomp := _root_.GlobalTheory.IntegralityComp.integralityComputation O K l e a ι η H D hηH hl2
  have hY'Y : ∀ {y : Vec K a ι}, y ∈ D.Y' → y ∈ D.Y := fun h => D.desc.Y'_le_Y η h

  let LcK : Vec K a ι →ₗ[K] D.Pol := D.Lc ∘ₗ D.cls
  have hLc : ∀ v : D.Y', LcK.restrictScalars O (v : Vec K a ι) ∈ D.Z := fun v =>
    hint _ (D.desc.cls_mem_Z (hY'Y v.2))
  let Lc' : D.Y' →ₗ[O] D.Z := ((LcK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hLc

  let PK : Vec K a ι →ₗ[K] D.Pol := -((l : K) ^ k)⁻¹ • (D.cls ∘ₗ mulV K a ι (E K l e) ∘ₗ D.zeta)
  have hPK : ∀ y : Vec K a ι, PK y = -((l : K) ^ k)⁻¹ • D.cls (E K l e • D.zeta y) := fun y => by
    simp [PK]
  have hP : ∀ v : D.Y', PK.restrictScalars O (v : Vec K a ι) ∈ D.Z := by
    intro v
    have hv := v.2
    obtain ⟨p, hp, f, hf, hz⟩ := _root_.GlobalTheory.BK.zeta_Y'_fine_bound O K l e a ι η H D hη1 hηH (by omega) v hv
    have hEf : D.cls (E K l e • f) = 0 := by
      rw [PhiMod.cls_eq_zero_iff]
      have h1 := hcomp.2.1 f hf
      have h2 := D.smul_mem_Man (pow_mem (A_le_Rpi l e (E_mem l e (A O K))) (2 * H + 1)) h1
      rwa [smul_smul, ← Ezpow_natCast, ← Ezpow_add, show ((2 * H + 1 : ℕ) : ℤ) + -(2 * H : ℤ) = 1 by push_cast; ring,
        show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, Ezpow_natCast, pow_one] at h2
    have hval : PK (v : Vec K a ι) = D.cls (-(E K l e • p)) := by
      rw [hPK, hz, smul_add, smul_comm (E K l e) ((l : K) ^ k) p,
        smul_comm (E K l e) (((l : K) ^ (3 * H))⁻¹) f, map_add, map_smul D.cls ((l : K) ^ k), map_smul D.cls ((l : K) ^ (3 * H))⁻¹, hEf, smul_zero, add_zero,
        smul_smul, neg_mul, inv_mul_cancel₀ hlk, neg_smul, one_smul, map_neg]
    refine D.desc.mem_Z.2 ⟨⟨-(E K l e • p), ?_, hval.symm⟩, fun g => ?_⟩
    · refine neg_mem ?_
      rw [mem_divE, smul_comm]
      exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)
    · have h : D.cls (E K l e • D.zeta v) = D.Lc (D.cls v) - D.Mon v := by
        rw [D.Mon_eq, sub_sub_cancel]
      have hinv : D.cls (E K l e • D.zeta v) ∈ D.desc.actPol.invariants := by
        rw [h]
        refine sub_mem (fun g => ?_) (D.desc.Mon_mem_invariants (hY'Y hv).2)
        rw [BKDat.actPol_Lc, D.desc.cls_mem_invariants (hY'Y hv).2 g]
      have h2 : PK v ∈ D.desc.actPol.invariants := by
        rw [hPK]
        exact Submodule.smul_mem _ _ hinv
      exact h2 g
  let P : D.Y' →ₗ[O] D.Z := ((PK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hP
  have hLc'apply : ∀ v : D.Y', (Lc' v : D.Pol) = D.Lc (D.cls v) := fun v => rfl
  have hPapply : ∀ v : D.Y', (P v : D.Pol) = PK v := fun v => rfl
  have hsum : ∀ v : D.Y', (((Lc' + (l : O) ^ k • P) v : D.Z) : D.Pol) = D.Mon v := by
    intro v
    rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul_of_tower,
      hLc'apply, hPapply, hPK, ← algebraMap_smul K ((l : O) ^ k), map_pow, map_natCast, smul_smul, mul_neg,
      mul_inv_cancel₀ hlk, neg_one_smul, D.Mon_eq, sub_eq_add_neg]
  let W : Submodule O D.Z := ((D.Zl.map D.Lc).restrictScalars O).comap D.Z.subtype
  have hW : ∀ z : D.Z, z ∈ W ↔ ∃ w ∈ D.Zl, D.Lc w = z := fun z => Iff.rfl
  have hc : η + (N + 1) * η < k := by
    have : (N + 2) * η = η + (N + 1) * η := by ring
    omega
  have h1 : ∀ v, Lc' v ∈ W ∧ (Lc' + (l : O) ^ k • P) v ∈ W := by
    intro v
    refine ⟨(hW _).2 ⟨D.cls v, D.desc.mem_Zl_of_mem_Z (D.desc.cls_mem_Z (hY'Y v.2)), rfl⟩, (hW _).2 ?_⟩
    rw [hsum]
    obtain ⟨-, w, hw, h⟩ := _root_.GlobalTheory.BK.BKDat.Mon_mem_range_Lc O K l e a ι η H D v
      (D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hY'Y v.2⟩)
    exact ⟨w, hw, h⟩
  have h2 : ∀ z : D.Z, (l : O) • z ∈ W → z ∈ W := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW _).1 hz
    refine (hW _).2 ⟨((l : K))⁻¹ • w, D.Zl.smul_mem _ hw, ?_⟩
    rw [map_smul, h, Submodule.coe_smul_of_tower, ← algebraMap_smul K (l : O), map_natCast, smul_smul,
      inv_mul_cancel₀ hlK, one_smul]
  have h3 : ∀ z ∈ W, (l : O) ^ (η + (N + 1) * η) • z ∈ LinearMap.range Lc' := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW z).1 hz
    obtain ⟨y', hy', hy'eq⟩ := _root_.GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq O K l e a ι η H D U N hU hUI hUc hηH (by omega) hl2 0 w hw
      (by rw [pow_zero, one_smul, h]; exact z.2)
    refine ⟨⟨y', hy'⟩, Subtype.ext ?_⟩
    rw [hLc'apply, Submodule.coe_smul_of_tower, ← algebraMap_smul K ((l : O) ^ (η + (N + 1) * η)), map_pow, map_natCast, ← h, hy'eq,
      zero_add]
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.successive_approximation (l : O) Lc' P W (η + (N + 1) * η) k hc h1 h2 h3 ⟨y, hy⟩
  refine ⟨y₁, y₁.2, ?_⟩
  have := congrArg Subtype.val hy₁
  rw [hsum] at this
  exact this

end GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomPadicAlgCl
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.HV

namespace GlobalTheory

namespace PowerSeriesEvalAlgCl

theorem isIntegral_iff_norm_le_one {l : ℕ} [Fact l.Prime] (y : PadicAlgCl l) :
    IsIntegral ℤ_[l] y ↔ ‖y‖ ≤ 1 := by
  have hm : (minpoly ℚ_[l] y).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have key : ‖y‖ ≤ 1 ↔ ∀ n, ‖(minpoly ℚ_[l] y).coeff n‖ ≤ 1 := spectralValue_le_one_iff hm
  rw [key]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic
      ((lifts_iff_coeff_lifts (f := algebraMap ℤ_[l] ℚ_[l]) _).2 fun n => ⟨⟨_, h n⟩, rfl⟩) hm
    refine ⟨q, hq', ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq]
    exact minpoly.aeval ℚ_[l] y

theorem exists_coef_ge_finset {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ y ∈ s, IsIntegral ℤ_[l] y) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ y ∈ s, y ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c₁, h₁, h₂⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨c₂, h₃, h₄⟩ := (coefSup l).2.2.1 c₁ a (hs a (Finset.mem_insert_self _ _))
    refine ⟨c₂, h₁.trans h₃, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h₄
    · exact h₃ (h₂ y hy)

end PowerSeriesEvalAlgCl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeNormCyclotomicCharNeOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormChar

theorem split_trivial (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M,
      x ^ Ideal.absNorm v.asIdeal - x ∈ P) : Module.finrank K M = 1 := by
  by_contra h1
  have h2 : 1 < Module.finrank K M := by have := Module.finrank_pos (R := K) (M := M); omega
  obtain ⟨T, hT, hc⟩ := _root_.GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem K M
  refine _root_.GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq K M (S ∪ T) (hS.union hT) fun v hv => ?_
  simp only [Set.mem_union, not_or] at hv
  obtain ⟨hn, hN⟩ := hc v hv.2 (h v hv.1)
  rw [← hn] at h2
  have := v.isMaximal
  obtain ⟨P, P', hP, hP', hne⟩ := (Set.one_lt_ncard_iff (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M))).1 h2
  have := hP.2
  have := hP'.2
  exact ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ⟨P', hP'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P'⟩,
    fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hP.2, hP'.2, hN P hP, hN P' hP'⟩


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.NormChar.smulComm (K L : Type) [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := by
  refine ⟨fun σ a x => ?_⟩
  apply RingOfIntegers.ext
  have h1 : ((a • x : 𝓞 L) : L) = algebraMap K L a * x := by
    rw [Algebra.smul_def]; rfl
  have h3 : ((σ • (a • x) : 𝓞 L) : L) = σ ((a • x : 𝓞 L) : L) := rfl
  rw [h3, h1, Algebra.smul_def]
  push_cast
  rw [map_mul, AlgEquiv.commutes]
  rfl

attribute [local instance] smulComm

theorem eq_top_of_frob (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
      ∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ Q → σ ∈ H) : H = ⊤ := by
  set M := IntermediateField.fixedField H with hM
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have h1 : Module.finrank K M = 1 := by
    refine split_trivial K M S hS fun v hv P hP x => ?_
    have := hP.1
    have := hP.2
    obtain ⟨Q, hQ, hQ'⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 L)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) Q
    have hH := h v hv Q hQ hQv σ hσ
    have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
      rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h6 := hσ (algebraMap (𝓞 M) (𝓞 L) x)
    rw [h5] at h6
    have h7 : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ) (algebraMap (𝓞 M) (𝓞 L) x) = algebraMap (𝓞 M) (𝓞 L) x := by
      apply RingOfIntegers.ext
      exact (x : M).2 ⟨σ, hH⟩
    rw [h7] at h6
    rw [hQ'.over, Ideal.mem_comap, map_sub, map_pow, ← neg_mem_iff, neg_sub]
    exact h6
  have h2 : M = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  rw [← IntermediateField.fixingSubgroup_fixedField H, ← hM, h2, IntermediateField.fixingSubgroup_bot]

theorem exists_prime_norm_char_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  intro K _ _ m hm hirr χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero m := ⟨hm.ne_zero⟩
  let L := CyclotomicField m K
  have : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  let e := IsCyclotomicExtension.autEquivPow L hirr
  have hz := IsCyclotomicExtension.zeta_spec m K L
  have hm0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hH := eq_top_of_frob K L (χ.comp e.toMonoidHom).ker {v | v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}}
    (Ideal.finite_factors hm0) (fun v hv Q hQ hQv σ hσ => by
      have hζ := hz.toInteger_isPrimitiveRoot
      have hmQ : (m : 𝓞 L) ∉ Q := by
        intro hmQ
        apply hv
        rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton, hQv.over, Ideal.mem_comap, map_natCast]
        exact hmQ
      have h3 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hζ.pow_eq_one hmQ
      have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
        rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h5] at h3
      have h4 : σ (IsCyclotomicExtension.zeta m K L) =
          IsCyclotomicExtension.zeta m K L ^ Ideal.absNorm v.asIdeal := by
        have := congrArg (fun y : 𝓞 L => (y : L)) h3
        exact this
      have h6 := hz.autToPow_spec K σ
      rw [h4] at h6
      have h7 : ((hz.autToPow K σ : (ZMod m)ˣ) : ZMod m).val ≡ Ideal.absNorm v.asIdeal [MOD m] := by
        have := (hz.isOfFinOrder hm.ne_zero).pow_eq_pow_iff_modEq.1 h6
        rwa [← hz.eq_orderOf] at this
      refine hcon v (e σ) ?_
      rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h7, ZMod.natCast_zmod_val]
      rfl)
  apply hχ
  ext1 u
  have : e.symm u ∈ (χ.comp e.toMonoidHom).ker := hH ▸ Subgroup.mem_top _
  simpa using this

end GlobalTheory.NormChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory

theorem absoluteGalois_fixes_unramified_in_crystalline {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (g : ↥(GK K))
    (a : ↥(K0 K)) : P.actQ (g : GQ l) (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.B a := by
  have hfix : (g : GQ l) ((a : Om l)) = (a : Om l) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 (a : Om l) a.2.1
  exact P.actQ_Kur (g : GQ l) (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a)
    (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a) hfix

theorem ltChar_hom : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : P.R.B), IsUnit x → (∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x) → ∃ c : ↥(GK K) →* (↥(K0 K))ˣ, ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x := by
  intro l _ P K x hx h
  rcases subsingleton_or_nontrivial P.R.B with hB | hB
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  · have hinj : Function.Injective (algebraMap ↥(K0 K) P.R.B) := (algebraMap ↥(K0 K) P.R.B).injective
    have hcan : ∀ a b : ↥(K0 K), algebraMap ↥(K0 K) P.R.B a * x = algebraMap ↥(K0 K) P.R.B b * x → a = b :=
      fun a b e => hinj (hx.mul_left_injective e)
    let f : ↥(GK K) → ↥(K0 K) := fun g : ↥(GK K) => Classical.choose (h g)
    have hf : ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B (f g) * x :=
      fun g => Classical.choose_spec (h g)
    let F : ↥(GK K) →* ↥(K0 K) :=
      { toFun := f
        map_one' := by
          apply hcan
          rw [← hf, map_one, one_mul, OneMemClass.coe_one, map_one, AlgEquiv.one_apply]
        map_mul' := by
          intro g g'
          apply hcan
          rw [← hf]
          have e1 : P.actQ ((g * g' : ↥(GK K)) : GQ l) x = P.actQ (g : GQ l) (P.actQ (g' : GQ l) x) := by
            rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply]
          rw [e1, hf g', map_mul, absoluteGalois_fixes_unramified_in_crystalline, hf g, map_mul]
          ring }
    refine ⟨F.toHomUnits, fun g => ?_⟩
    rw [MonoidHom.coe_toHomUnits]
    exact hf g

end GlobalTheory
end

