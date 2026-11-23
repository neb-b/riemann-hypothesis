module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSimplePieces
section
noncomputable section
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open scoped LaurentSeries PowerSeries

theorem exists_simple_quotient {k G : Type} [Field k] [Group G] (B : Ob k G) (hB : B.m ≠ 0) :
    ∃ (A C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A B f ∧ IsHom B C p ∧ Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p ∧
      IsSimpleModule (MonoidAlgebra k G) C.ρ.asModule ∧ A.m < B.m := by
  haveI : Nonempty (Fin B.m) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩
  haveI : Nontrivial B.ρ.asModule := B.ρ.asModuleEquiv.toEquiv.nontrivial
  have hfl := finiteLength_asModule B.ρ
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  obtain ⟨S, hS, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) B.ρ.asModule)).resolve_left
    bot_ne_top
  let S' : Submodule k (Fin B.m → k) := (S.restrictScalars k).comap B.ρ.asModuleEquiv.symm.toLinearMap
  have hinv : ∀ g, S' ≤ S'.comap (B.ρ g) := by
    intro g x hx
    have hx' : B.ρ.asModuleEquiv.symm x ∈ S := hx
    change B.ρ.asModuleEquiv.symm (B.ρ g x) ∈ S
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact S.smul_mem _ hx'
  obtain ⟨A, eA, hA⟩ := exists_ob (B.ρ.subrepresentation S' hinv)
  obtain ⟨C, eC, hC⟩ := exists_ob (B.ρ.quotient S' hinv)
  have hp : IsHom B C (eC.toLinearMap ∘ₗ S'.mkQ) := fun g x => hC g (S'.mkQ x)
  have hps : Function.Surjective (eC.toLinearMap ∘ₗ S'.mkQ) := eC.surjective.comp S'.mkQ_surjective
  refine ⟨A, C, S'.subtype ∘ₗ eA.symm.toLinearMap, eC.toLinearMap ∘ₗ S'.mkQ, ?_, hp,
    S'.subtype_injective.comp eA.symm.injective, hps, ?_, ?_, ?_⟩
  · intro g x
    obtain ⟨y, rfl⟩ := eA.surjective x
    rw [← hA]
    simp
  · intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_range, Submodule.subtype_apply]
    exact ⟨fun h => ⟨eA ⟨x, h⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (eA.symm y).2⟩
  · let q := asModuleMap (π := B.ρ) (π' := C.ρ) _ hp
    have hq : Function.Surjective q := hps
    have hk : S = LinearMap.ker q := by
      ext x
      change _ ↔ eC (S'.mkQ (B.ρ.asModuleEquiv x)) = 0
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Iff.rfl
    haveI := isSimpleModule_iff_isCoatom.mpr hS
    exact IsSimpleModule.congr ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm
  · have h1 : S' ≠ ⊤ := by
      intro h
      refine hS.1 (eq_top_iff.mpr fun x _ => ?_)
      have : B.ρ.asModuleEquiv x ∈ S' := h ▸ Submodule.mem_top
      exact this
    have h2 := Submodule.finrank_lt h1
    rw [eA.finrank_eq] at h2
    simpa using h2

theorem sameSS_piRep_succ {k G : Type} [Field k] [Group G] {s : ℕ} (C : Fin (s + 1) → Ob k G) (A B : Ob k G)
    (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin (C 0).m → k))
    (ef : IsHom A B f) (ep : IsHom B (C 0) p) (hf : Function.Injective f) (hp : Function.Surjective p)
    (H : Function.Exact f p) (h : SameSS A.ρ (piRep fun a : Fin s => (C a.succ).ρ)) :
    SameSS B.ρ (piRep fun a => (C a).ρ) := by
  have h1 : SameSS B.ρ ((C 0).ρ.prod (piRep fun a : Fin s => (C a.succ).ρ)) :=
    SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inr k _ _) (p' := LinearMap.fst k _ _)
      (fun g x => by simp) (fun g x => by simp) LinearMap.inr_injective LinearMap.fst_surjective .inr_fst h
      (SameSS.refl _ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩))
  refine h1.congr_right (Fin.consLinearEquiv k fun a => Fin (C a).m → k) fun g x => ?_
  funext a
  refine Fin.cases ?_ (fun j => ?_) a <;> rfl

theorem ModTh.exists_simple_pieces : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  intro k G _ _ l n _ _ _ R F r Dt M B
  induction B using (measure fun A : Ob k G => A.m).wf.induction with
  | _ B ih =>
  intro N hN
  by_cases hB : B.m = 0
  · haveI : IsEmpty (Fin B.m) := ⟨fun a => by have := a.2; omega⟩
    refine ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun i x => ?_⟩
    · exact SameSS.of_equiv (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
        (LinearEquiv.ofSubsingleton _ _) fun _ _ => Subsingleton.elim _ _
    · rw [Finset.univ_eq_empty, Finset.sum_empty]
      unfold sen qmult gmult
      exact Module.finrank_zero_of_subsingleton
  · obtain ⟨A, C₀, f, p, ef, ep, hf, hp, H, hs, hlt⟩ := exists_simple_quotient B hB
    obtain ⟨s, C, L, hL, hC, hss, hsen⟩ := ih A hlt _ (_root_.GlobalTheory.Models.SubModel.model_pre F M A B f N ef hf hN)
    obtain ⟨hobj, hlat, -, hc⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M B N hN
    let C' : Fin (s + 1) → Ob k G := Fin.cons C₀ C
    refine ⟨s + 1, C', Fin.cons (α := fun a => Lats k n (C' a).m) (F.push B C₀ p N) L, fun a => ?_, fun a => ?_,
      sameSS_piRep_succ C' A B f p ef ep hf hp H hss, fun i x => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact ModTh.model_push_of_surjective F M B C₀ p N ep hp hN
      · exact hL j
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact hs
      · exact hC j
    · rw [Fin.sum_univ_succ, _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F A B C₀ f p N hobj ef ep hf hp H i (hlat i) (hc i) x, hsen, add_comm]
      rfl

end GlobalTheory.Models
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZero
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem ModTh.abc_Nχ_of_range {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (e : ℤ) (h1 : -1 ≤ e) (h2 : e < Dt.t) :
    ABC (F.D (chr (M.ω ^ (-e)))) Dt.w Dt.wst (M.Nχ e) := by
  refine ⟨fun i => (M.χ_lat e h1 h2 i).1, fun i => ?_, fun i => (M.χ_lat e h1 h2 i).2.1⟩
  have ht : (1 : ℤ) ≤ Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have a := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
  have b := Dt.range i (Dt.w i + Dt.t - 1) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))
  rw [(M.χ_lat e h1 h2 i).2.2.1]
  exact ⟨sh_le_sh_of_le (by omega) _, sh_le_sh_of_le (by unfold TopData.wst; omega) _⟩

theorem ModTh.hom_chr_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  intro k G _ _ l n _ _ _ R F r Dt M T1 T2 T3 e h1 h2 A₁ j p hj hinj hp
  by_contra hne
  have hsurj : Function.Surjective p := by
    obtain ⟨x, hx⟩ : ∃ x, p x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    have hx0 : p x 0 ≠ 0 := fun h => hx (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    intro y
    refine ⟨(y 0 / p x 0) • x, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0, map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hx0]
  have hT := _root_.GlobalTheory.Models.model_obj_and_abc F M M.T M.Nstd M.std_model
  have hsub := _root_.GlobalTheory.Models.SubModel.model_pre F M A₁ M.T j M.Nstd hj hinj M.std_model
  have hq := ModTh.model_push_of_surjective F M A₁ (chr (M.ω ^ (-e))) p _ hp hsurj hsub
  have hN := _root_.GlobalTheory.Models.model_obj_and_abc F M _ _ hq
  have hχ := M.abc_Nχ_of_range e h1 h2
  have hs : sen ((F.D (chr (M.ω ^ (-e)))).γ 0) (M.Nχ e 0) (e : k) ≠ 0 := by
    rw [(M.χ_lat e h1 h2 0).2.2.2]
    classical
    unfold resCount
    rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro h
    exact h e (Multiset.mem_singleton_self e) (by simp)
  obtain ⟨a, ha, hsa⟩ := _root_.GlobalTheory.Models.sen_near_of_abc (F.D (chr (M.ω ^ (-e)))) Dt _ _ hN.2 hχ 0 (e : k) hs
  have hle := _root_.GlobalTheory.Models.sen_push_pre_le F M.T A₁ (chr (M.ω ^ (-e))) j p Dt.w Dt.wst M.Nstd hT.1 hj hinj hp hsurj hT.2 0
    ((e : k) + a)
  have hstd : resCount (Dt.U 0) (Dt.w 0) ((e : k) + a) ≠ 0 := by
    rw [← M.std_sen]
    omega
  classical
  unfold resCount at hstd
  rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hstd
  push Not at hstd
  obtain ⟨u, hu, hu'⟩ := hstd
  rw [abs_le] at ha
  refine (_root_.GlobalTheory.WindowArith.windows (k := k) Dt T1 T2 T3 0).2.1 u hu (Dt.w 0 + e + a) (by omega) (by omega) ?_
  push_cast at hu' ⊢
  linear_combination hu'

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfPowSmulMem
section
noncomputable section

namespace GlobalTheory.WachSat

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_pow_smul_le {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (c : O) (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L S : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (hS : S.FG) :
    ∃ m : ℕ, ∀ x ∈ S, c ^ m • x ∈ L := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_7 h_8 h_9 h_10; revert LL O h_2 h_3 h_4 h_5 V h_7 h_8 h_9 h_10 c hc L S hL hS; exact @_root_.GlobalTheory.PowerScalarMembership.main)
  | exact @_root_.GlobalTheory.PowerScalarMembership.main
  | exact _root_.GlobalTheory.PowerScalarMembership.main
  | (apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScalarMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScalarMembership.main ..)

variable (W : LocWach PD LL O v n)

theorem ee_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (x : W.EE)
    (hx : (PD.p : W.EE) * x = 0) : x = 0 := by
  have hA : ∀ a : LetA O n, (PD.p : LetA O n) * a = 0 → a = 0 := by
    intro a ha
    funext i
    ext k
    have h1 : (PD.p : PowerSeries O) * a i = 0 := congrFun ha i
    have h2 := congrArg (PowerSeries.coeff k) h1
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, map_zero] at h2
    simpa using hp _ h2
  haveI := W.EE_complete
  refine IsHausdorff.haus (I := Ideal.span {((PD.p : ℕ) : W.EE)}) inferInstance x fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨a, m, ha⟩ := W.EE_dense x k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b, hb⟩ := W.EE_sat ((PD.p : LetA O n) * a) (k + 1) (by
    refine Ideal.mem_span_singleton'.2 ⟨-y, ?_⟩
    rw [map_mul, map_natCast]
    linear_combination (-(PD.p : W.EE)) * hy - (algebraMap (LetA O n) W.EE (letπ ^ m)) * hx)
  have hab : a = (PD.p : LetA O n) ^ k * b := by
    have := hA (a - (PD.p : LetA O n) ^ k * b) (by rw [mul_sub, hb]; ring)
    exact sub_eq_zero.1 this
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ m)) := by
    rw [map_pow]; exact W.EE_π.pow m
  refine Ideal.mem_span_singleton'.2 ⟨(y + algebraMap (LetA O n) W.EE b) * ↑u⁻¹, ?_⟩
  rw [hab, map_mul, map_pow (algebraMap (LetA O n) W.EE) (PD.p : LetA O n), map_natCast, ← hu] at hy
  have huu : (u : W.EE) * ↑u⁻¹ = 1 := u.mul_inv
  linear_combination (↑u⁻¹ : W.EE) * hy + x * huu

theorem mem_of_pow_smul_mem (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O)
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T) (m : ℕ) (x : W.DD T)
    (hx : ((PD.p : O) ^ m) • x ∈ W.N T) : x ∈ W.N T := by
  obtain ⟨b, hli, hsp⟩ := hb
  have hxs : x ∈ Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) := hsp ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hxs
  set a := b.repr ⟨_, hx⟩ with ha
  have h1 : ∑ j, algebraMap (LetA O n) W.EE (a j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simpa only [algebraMap_smul, map_smul, Submodule.subtype_apply] using this
  have h2 : ∑ j, ((PD.p : W.EE) ^ m * e j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    rw [← he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, ← algebraMap_smul W.EE ((PD.p : O) ^ m), map_pow, map_natCast]
  have h3 : ∀ j, algebraMap (LetA O n) W.EE (a j) = (PD.p : W.EE) ^ m * e j :=
    Fintype.linearIndependent_iffₛ.1 hli _ _ (h1.trans h2.symm)
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (ee_torsionFree W hp _ (by rw [← hy]; ring))
  have h4 : ∀ j, ∃ c : LetA O n, e j = algebraMap (LetA O n) W.EE c := by
    intro j
    obtain ⟨c, hc⟩ := W.EE_sat (a j) m (Ideal.mem_span_singleton'.2 ⟨e j, by rw [h3, mul_comm]⟩)
    refine ⟨c, sub_eq_zero.1 (hreg m _ ?_)⟩
    have := h3 j
    rw [hc, map_mul, map_pow, map_natCast] at this
    rw [mul_sub, this, sub_self]
  choose c hc using h4
  rw [← he]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hc, algebraMap_smul]
  exact (W.N T).smul_mem _ (b j).2

end Generic

end GlobalTheory.WachSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResidues
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_sen_mem : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M A N hN i x hx
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have hle := _root_.GlobalTheory.Models.sen_push_pre_le F B A₁ A j p Dt.w Dt.wst Nb (M.base_obj B Nb hB) hj hji hp hps
    (M.base_abc B Nb hB) i x
  obtain ⟨μ, -, hs⟩ := M.base_sen B Nb hB
  rw [hs i x] at hle
  have h0 : resCount (Dt.Ut i) (Dt.w i) x ≠ 0 := by
    intro h
    rw [h] at hle
    apply hx
    simpa using hle
  unfold resCount at h0
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero h0)
  classical
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotForallExistsTwoLiesOverAbsNormEq
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ S hS h
  choose P P' hne hP hP' hNP hNP' using h
  have key : ∀ {Q : HeightOneSpectrum (𝓞 M)} {v w : HeightOneSpectrum (𝓞 K)},
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w :=
    fun h₁ h₂ => HeightOneSpectrum.ext (h₁.over.trans h₂.over.symm)
  let f : {v // v ∉ S} × Bool → HeightOneSpectrum (𝓞 M) :=
    fun x => if x.2 then P x.1 x.1.2 else P' x.1 x.1.2
  have lies : ∀ x, (f x).asIdeal.LiesOver x.1.1.asIdeal := by
    rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hP' v hv, hP v hv]
  refine _root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes K M S hS f ?_ ?_
  · rintro ⟨⟨v, hv⟩, b⟩ ⟨⟨w, hw⟩, c⟩ hfe
    have hvw : v = w := key (lies (⟨v, hv⟩, b)) (by rw [hfe]; exact lies _)
    subst hvw
    cases b <;> cases c
    · rfl
    · exact absurd hfe.symm (hne v hv)
    · exact absurd hfe (hne v hv)
    · rfl
  · rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hNP' v hv, hNP v hv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem exists_continuous_div {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] {X : Type} [TopologicalSpace X]
    {π : O} (hπ : π ≠ 0) (u : X → O) (hu : Continuous u) (hd : ∀ x, π ∣ u x) :
    ∃ w : X → O, Continuous w ∧ ∀ x, u x = π * w x := by
  choose w hw using hd
  have hemb : Topology.IsClosedEmbedding (fun a : O => π * a) :=
    (continuous_const.mul continuous_id).isClosedEmbedding (mul_right_injective₀ hπ)
  refine ⟨w, hemb.isEmbedding.continuous_iff.2 ?_, hw⟩
  have : ((fun a : O => π * a) ∘ w) = u := funext fun x => (hw x).symm
  rw [this]; exact hu

theorem phi_quot_pow_injective :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G],
      PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) →
      ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ,
      Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p O _ _ _ _ _ G _ _ _ hO ε hε z hz k
  haveI : CompactSpace O := hO.compact
  haveI : T2Space O := hO.t2
  haveI hdisc := (quot_pow_maximalIdeal_discrete_finite hO k).1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hI : IsLocalRing.maximalIdeal O ^ k = Ideal.span {ϖ ^ k} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hπ : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
  generalize IsLocalRing.maximalIdeal O ^ k = I at hI hdisc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hm' : cocycles2Map (twist ε O) (twist ε (O ⧸ I))
      (LinearMap.toSpanSingleton O (O ⧸ I) (Ideal.Quotient.mk I a)) (cont_span _ _)
      (span_twist ε _ _) z₀ ∈ (B2 (twist ε (O ⧸ I))).comap (Z2 (twist ε (O ⧸ I))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 hm
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hm'
  have hcf' : ∀ g h : G, (ε g : O) • c h - c (g * h) + c g =
      z₀.1 (g, h) • Ideal.Quotient.mk I a := fun g h => congrFun hcf (g, h)
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  have hcs : Continuous (fun g => s (c g)) := continuous_of_discreteTopology.comp hc
  set u : G × G → O := fun q =>
    a * z₀.1 q - ((ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1)) with hu
  have huc : Continuous u :=
    (continuous_const.mul z₀.2.1).sub
      ((((hε.comp continuous_fst).mul (hcs.comp continuous_snd)).sub
        (hcs.comp (continuous_fst.mul continuous_snd))).add (hcs.comp continuous_fst))
  have hud : ∀ q, ϖ ^ k ∣ u q := by
    rintro ⟨g, h⟩
    rw [← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem]
    have e := hcf' g h
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at e
    simp only [hu, map_sub, map_add (f := _), map_mul, hs]
    rw [e]; ring
  obtain ⟨w, hwc, hw⟩ := exists_continuous_div hπ u huc hud
  have hwZ : w ∈ Z2 (twist ε O) := by
    refine ⟨hwc, fun g h l => ?_⟩
    apply mul_left_cancel₀ hπ
    have e : (ε g : O) * z₀.1 (h, l) - z₀.1 (g * h, l) + z₀.1 (g, h * l) - z₀.1 (g, h) = 0 :=
      z₀.2.2 g h l
    have e1 := hw (h, l)
    have e2 := hw (g * h, l)
    have e3 := hw (g, h * l)
    have e4 := hw (g, h)
    simp only [hu, map_mul, Units.val_mul, mul_assoc] at e1 e2 e3 e4
    show ϖ ^ k * ((ε g : O) * w (h, l) - w (g * h, l) + w (g, h * l) - w (g, h)) = ϖ ^ k * 0
    linear_combination a * e - (ε g : O) * e1 + e2 - e3 + e4
  obtain ⟨b, hb⟩ := hz.2 (Submodule.Quotient.mk ⟨w, hwZ⟩)
  have key : a • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) =
      (ϖ ^ k * b) • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) := by
    simp only at hb
    rw [mul_smul, hb, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => s (c g), hcs, funext fun q => ?_⟩
    have e := hw q
    show (ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1) = a * z₀.1 q - ϖ ^ k * w q
    rw [← e, hu]; ring
  have hab : a = ϖ ^ k * b := hz.1 key
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  exact ⟨b, hab⟩

end GlobalTheory.NatQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart
section
namespace GlobalTheory.WachSum

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem sumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumPart l P H := by
  intro K s LL h
  exact GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumFor_of_crys fun _ _ _ i i' hs hT hT' =>
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_isSumLat i i' hT hT' hs

end GlobalTheory.WachSum
end

