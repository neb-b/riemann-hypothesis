module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Examples
public import GroundTheory.LocalFields.Integers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
public import GroundTheory.LocalFields.Eisenstein
public import GroundTheory.LocalFields.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
section
noncomputable section
namespace GlobalTheory.TopSteps.CharBound
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

theorem exists_ext {k G : Type} [Field k] [Group G] (A : Ob k G) (z : G → Fin A.m → k)
    (h1 : z 1 = 0) (hz : ∀ g h, z (g * h) = z g + A.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin A.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt A E z ∧
      ∀ g x y, e (A.ρ g x + y • z g, y) = E.ρ g (e (x, y)) := by
  let π : Representation k G ((Fin A.m → k) × k) :=
    { toFun := fun g => ((A.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [h1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        obtain ⟨m, y⟩ := x
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g x y, e (A.ρ g x + y • z g, y) = E.ρ g (e (x, y)) := fun g x y => he g (x, y)
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simp at this
    exact this.symm
  · simpa using he' g x 0
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := e.injective hx
    simp at this
  · rw [← he']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_add (f := _)]
    simp

theorem exists_resEquiv {O k : Type} [CommRing O] [Field k] [Algebra O k] {c : O}
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ c ∣ x) :
    ∃ e : (O ⧸ Ideal.span {c}) ≃ₗ[O] k, ∀ y, e (Ideal.Quotient.mk _ y) = algebraMap O k y := by
  have h : Ideal.span {c} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [Ideal.mem_span_singleton, LinearMap.mem_ker, Algebra.linearMap_apply, hk]
  exact ⟨(Submodule.quotEquivOfEq _ _ h).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs),
    fun _ => rfl⟩

section
variable {O G k : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field k] [Algebra O k]

theorem exists_ext_Ea {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M) (χ : G →* Oˣ)
    {X : Type} [AddCommGroup X] [Module O X] {c : O} (hc : ∀ x : X, c • x = 0)
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ c ∣ x)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) (A : Ob k G) (q : (M ⊗[O] X) ≃ₗ[O] (Fin A.m → k))
    (hq : ∀ g x, q (twCoef W χ X g x) = A.ρ g (q x)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] (Fin E.m → k)),
      IsExt A E (fun g => q ((z : G → M ⊗[O] X) g)) ∧
      ∀ σ x, e (twistRep (Ea W χ hc z) χ⁻¹ σ x) = E.ρ σ (e x) := by
  obtain ⟨r, hr⟩ := exists_resEquiv hs hk
  obtain ⟨E, e, hE, he⟩ := exists_ext A (fun g => q ((z : G → M ⊗[O] X) g)) (by simp [cocycle_one])
    (fun g h => by rw [cocycle_mul z g h, map_add (f := _), hq])
  refine ⟨E, (q.prodCongr r).trans (e.restrictScalars O), hE, ?_⟩
  rintro σ ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have : twistRep (Ea W χ hc z) χ⁻¹ σ (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X σ m + y • (z : G → M ⊗[O] X) σ, Ideal.Quotient.mk _ y) := by
    rw [Ea, twistRep_apply, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [this]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.restrictScalars_apply, map_add (f := _),
    map_smul, hq, hr]
  rw [← he, algebraMap_smul]

theorem linearIndependent_of_indepMod {N : Type} [AddCommGroup N] [Module O N] (π : Representation O G N)
    {lam : O} (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    (A : Ob k G) (q : N ≃ₗ[O] (Fin A.m → k)) (hq : ∀ g x, q (π g x) = A.ρ g (q x)) {s : ℕ}
    (z : Fin s → ↥(Z1 π ⊤)) (h : IndepMod lam (fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤))) :
    LinearIndependent k (fun a => (cob A).mkQ (fun g => q ((z a : G → N) g))) := by
  rw [Fintype.linearIndependent_iff]
  intro y hy a
  choose x hx using fun a => hs (y a)
  rw [← hx, hk]
  refine h x ?_ a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum] at hy
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
  have e1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.mkQ _ (∑ a, x a • z a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; rfl
  rw [e1]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨q.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply q.injective
  have := congrFun hb g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply,
    ← hx, algebraMap_smul] at this
  change q (π g (q.symm b) - q.symm b) = _
  rw [map_sub, hq, q.apply_symm_apply, this]
  simp
end

theorem exists_charEquiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O k : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [Field k] [Algebra O k]
    (Γ : GalData G Qp LL O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (ω : G →* kˣ) (hω : ∀ σ, (ω σ : k) = algebraMap O k (Γ.ε σ))
    (c : ℕ) :
    ∃ q : (O ⊗[O] GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) ≃ₗ[O] (Fin (chr (ω ^ (-((c : ℤ) - 1)))).m → k),
      ∀ g x, q (twCoef (Γ.Wchi c) Γ.χ₁ _ g x) = (chr (ω ^ (-((c : ℤ) - 1)))).ρ g (q x) := by
  obtain ⟨r, -⟩ := exists_resEquiv hs hk
  refine ⟨((TensorProduct.lid O _).trans r).trans (LinearEquiv.funUnique (Fin 1) O k).symm, fun g x => ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.twCoef_Wchi, map_smul]
  have h : ω g = Units.map (algebraMap O k : O →* k) (Γ.ε g) := Units.ext (hω g)
  have h2 : (((ω ^ (-((c : ℤ) - 1))) g : kˣ) : k) = algebraMap O k ((Γ.ε g) ^ (-((c : ℤ) - 1)) : Oˣ) := by
    rw [MonoidHom.zpow_apply, h, ← map_zpow]; rfl
  have h3 : ∀ (θ : G →* kˣ) (v : Fin 1 → k), (chr θ).ρ g v = (θ g : k) • v := fun _ _ => rfl
  rw [h3, h2, algebraMap_smul]

section
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n r : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (D : TopData n r) (Γ : GalData G Qp LL O) {k : Type} [Field k] [Algebra O k]

theorem lam_smul_resK (x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) : Γ.lam ^ 1 • x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

theorem exists_cocycles_gen (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {l : ℕ} {R : RingPG k l} {F : DFun R n G} (M : ModTh F D)
    (hM : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    {V : Type} [AddCommGroup V] [Module O V] (W : Representation O G V) {X : Type} [AddCommGroup X] [Module O X]
    (hX : ∀ x : X, Γ.lam ^ 1 • x = 0) (A : Ob k G) (q : (V ⊗[O] X) ≃ₗ[O] (Fin A.m → k))
    (hq : ∀ g x, q (twCoef W Γ.χ₁ X g x) = A.ρ g (q x))
    {s : ℕ} (x : Fin s → H1 (twCoef W Γ.χ₁ X) ⊤)
    (hx : ∀ a, x a ∈ admAt PD emb Γ D.t D.Ut W X 1 hX) (hi : IndepMod Γ.lam x) :
    ∃ z : Fin s → G → Fin A.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles A) ∧
      LinearIndependent k (fun a => (cob A).mkQ (z a)) := by
  choose z hz hadm using hx
  obtain rfl : x = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨fun a g => q ((z a : G → V ⊗[O] X) g), fun a => ?_,
    linearIndependent_of_indepMod _ hs hk A q hq z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea W Γ.χ₁ hX hs (fun y => by rw [pow_one]; exact hk y) (z a) A q hq
  obtain ⟨L, hL⟩ := hM E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem bound_gen (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {l : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}
    {F : DFun R n G} (M : ModTh F D) (h1 : D.T1 l) (h2 : D.T2 l) (h3 : D.T3 l)
    (hω : ∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ))
    (hM : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (hfin : Finite (O ⧸ Ideal.span {Γ.lam})) (c : ℕ)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut (Γ.Wchi c) X = admAt PD emb Γ D.t D.Ut (Γ.Wchi c) X a ha)
    (s : ℕ) (x : Fin s → H1 (twCoef (Γ.Wchi c) Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hx : ∀ a, x a ∈ adm PD emb Γ D.t D.Ut (Γ.Wchi c) (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ))
    (hi : IndepMod Γ.lam x) : (2 ≤ c → c ≤ D.t → s ≤ 0) ∧ (c = 1 → s ≤ 1) := by
  rw [h0 _ 1 (lam_smul_resK Γ) le_rfl] at hx
  obtain ⟨q, hq⟩ := exists_charEquiv Γ hs hk M.ω hω c
  have key := exists_cocycles_gen PD emb D Γ hs hk M hM (Γ.Wchi c) (lam_smul_resK Γ) _ q hq x hx hi
  clear hq q hx hi x hM
  refine ⟨fun hc hct => ?_, fun hc => ?_⟩
  · obtain ⟨z, hz, hli⟩ := key
    by_contra hs0
    let a : Fin s := ⟨0, by omega⟩
    exact hli.ne_zero a ((Submodule.Quotient.mk_eq_zero _).mpr
      (_root_.GlobalTheory.CharSplit.admissibleCocycle_negCharPower_mem_coboundaries F M h1 h2 h3 ((c : ℤ) - 1) (by omega) (by omega) (z a) (hz a)))
  · have e : M.ω ^ (-((c : ℤ) - 1)) = 1 := by simp [hc]
    rw [e] at key
    obtain ⟨z, hz, hli⟩ := key
    by_contra hs0
    have h2s : 2 ≤ s := by omega
    exact _root_.GlobalTheory.TopSteps.TrivLine.main F M h1 h2 h3 (fun a => z (Fin.castLE h2s a)) (fun a => hz _)
      (hli.comp _ (Fin.castLE_injective h2s))

end

theorem exists_res {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ} [Fact l.Prime]
    (hl : ¬ IsUnit ((l : ℕ) : O)) (hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ 1})) {lam : O}
    (hlam : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k) (_ : CharP k l),
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer lam).mp hlam
  have hl' : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hl
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective,
    fun x => ?_⟩
  · refine Finite.of_surjective _ (Ideal.Quotient.factor_surjective (S := Ideal.span {((l : ℕ) : O) ^ 1}) ?_)
    rw [pow_one, ← hm, Ideal.span_singleton_le_iff_mem]
    exact hl'
  · rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl'
  · rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem resBound_chars : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Real →
    (∀ c : ℕ, 2 ≤ c → c ≤ S.D.t → S.Lem0 (S.Γ.Wchi c) → S.ResBound (S.Γ.Wchi c) 0) ∧
    (S.Lem0 (S.Γ.Wchi 1) → S.ResBound (S.Γ.Wchi 1) 1) := by
  intro l _ P S hR
  obtain ⟨hSt, -, h1, h2, h3⟩ := S.hyp
  obtain ⟨hd, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete S.LL
  obtain ⟨hfin, k, _, _, _, hs, hk⟩ := exists_res hl ((GlobalTheory.LocalIntegers.good_integers l S.LL).2 1)
    hSt.2.2.2.2.2
  obtain ⟨R, ι, -, F, M, hω, -, hM⟩ := hR k ⟨hs, hk⟩
  have key := bound_gen (P.PD S.K) S.emb S.D S.Γ hs hk M h1 h2 h3 hω hM hfin
  refine ⟨fun c hc hct h0 s x hx hi => ?_, fun h0 s x hx hi => ?_⟩
  · have key' := key c (fun X _ _ _ => (h0 X).2.1)
    exact (key' s x hx hi).1 hc hct
  · have key' := key 1 (fun X _ _ _ => (h0 X).2.1)
    exact (key' s x hx hi).2 rfl

end GlobalTheory.TopSteps.CharBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapPiContinuousCoord
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory

theorem linearMap_pi_continuous_coord : ∀ {l : ℕ} [Fact l.Prime] {O M ι : Type}
    [CommRing O] [Algebra ℤ_[l] O] [Fintype ι] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] O),
    (∀ m : M, Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m) →
    ∀ f : (ι → O) →ₗ[O] M,
      @Continuous (ι → O) M
        (Pi.topologicalSpace (t₂ := fun _ => TopologicalSpace.induced bO.equivFun inferInstance))
        inferInstance f := by
  intro l _ O M ι _ _ _ _ _ _ _ e bO hcont f
  classical
  letI : TopologicalSpace O := TopologicalSpace.induced bO.equivFun inferInstance
  have key : ∀ c : ι → O, f c = ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ f c]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (fun j => if i = j then (1:O) else 0) = Pi.single i 1 := by
      funext j; by_cases h : i = j <;> simp [Pi.single_apply, h, eq_comm]
    rw [hc]
    conv_lhs => rw [← bO.sum_equivFun (c i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Algebra.smul_def, mul_smul]
  have hf : (f : (ι → O) → M) = fun c => ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := funext key
  rw [hf]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun α _ => ?_
  exact (hcont _).comp ((continuous_apply α).comp (continuous_induced_dom.comp (continuous_apply i)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

noncomputable section

namespace GlobalTheory.PMon.Ram

theorem padic_mem_integer_iff (l : ℕ) [Fact l.Prime] (a : ℚ_[l]) : a ∈ 𝒪[ℚ_[l]] ↔ ‖a‖ ≤ 1 := by
  change valuation ℚ_[l] a ≤ 1 ↔ _
  rw [← map_one (valuation ℚ_[l]), ← (valuation ℚ_[l]).vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

theorem isIntegral_integer_iff_norm_le (l : ℕ) [Fact l.Prime] (y : Om l) :
    IsIntegral 𝒪[ℚ_[l]] y ↔ ‖y‖ ≤ 1 := by
  have hy : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hy)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact (padic_mem_integer_iff l _).1 ((minpoly 𝒪[ℚ_[l]] y).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] y ∈ Polynomial.lifts (algebraMap 𝒪[ℚ_[l]] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, (padic_mem_integer_iff l _).2 (h n)⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

end GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L]
    [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)]
    [IsScalarTower ℚ_[l] L (Om l)] (x : L) :
    (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  have key : ∀ z : L, z ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) z‖ ≤ 1 := by
    intro z
    let f : L →ₐ[𝒪[ℚ_[l]]] Om l := (IsScalarTower.toAlgHom ℚ_[l] L (Om l)).restrictScalars 𝒪[ℚ_[l]]
    have hf : Function.Injective f := (algebraMap L (Om l)).injective
    rw [← isIntegral_integer_iff_norm_le]
    change valuation L z ≤ 1 ↔ IsIntegral 𝒪[ℚ_[l]] (f z)
    rw [isIntegral_algHom_iff f hf, GroundTheory.LocalField.isIntegral_iff ℚ_[l] L z]
  refine ⟨key x, ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hy : algebraMap L (Om l) x ≠ 0 := (map_ne_zero _).2 hx
  have hv : valuation L x ≠ 0 := by simpa using hx
  have h1 := key x⁻¹
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 hy)] at h1
  change valuation L x⁻¹ ≤ 1 ↔ _ at h1
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hv)] at h1
  rw [← not_le, ← not_le, h1]

end GlobalTheory.PMon.Ram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImage
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.Letter

variable {l : ℕ} [Fact l.Prime]

theorem lin_ext (K : FinExt l) {M : Type} [AddCommGroup M] [Module ℚ_[l] M] (σ τ : ↥(K0 K) →ₗ[ℚ_[l]] M)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → σ c = τ c) (c : ↥(K0 K)) :
    σ c = τ c := by
  have h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c := by
    intro c hc
    obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
    have h2 : c = ∑ i, (z i : ℚ_[l]) • (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
      apply Subtype.ext
      rw [hsum]
      push_cast
      simp only [Algebra.smul_def]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, hx⟩ := (hω i).2
    rw [map_smul, map_smul, h _ m hm hl hx]
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
  have h3 := h1 (((l : ℚ_[l]) ^ n) • c) (by
    rw [Algebra.smul_def]
    push_cast
    rwa [norm_mul, norm_pow])
  rw [map_smul, map_smul] at h3
  have h0 : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← inv_smul_smul₀ h0 (σ c), h3, inv_smul_smul₀ h0]

theorem mul_ext (K : FinExt l) {L B : Type} [Field L] [Algebra ℚ_[l] L] [CommRing B] [Algebra ℚ_[l] B]
    (e : ↥(K0 K) →ₐ[ℚ_[l]] L) (f : ↥(K0 K) →ₐ[ℚ_[l]] B) (x : L ⊗[ℚ_[l]] B)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 →
      ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x) (c : ↥(K0 K)) : ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x :=
  lin_ext K ((LinearMap.mulRight ℚ_[l] x).comp ((TensorProduct.mk ℚ_[l] L B 1).comp f.toLinearMap))
    (((LinearMap.toSpanSingleton L _ x).restrictScalars ℚ_[l]).comp e.toLinearMap) h c

theorem const_mul_letE {O : Type} [CommRing O] {n : ℕ} (o : ZMod n → O) (i : ZMod n) :
    (fun j => PowerSeries.C (o j) : LetA O n) * letE i = algebraMap O (LetA O n) (o i) * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; rfl
  · simp [letE, hj]

theorem step {O R Q L B : Type} [CommRing O] [CommRing R] [Algebra O R] [Field Q] [Field L] [Algebra Q L]
    [CommRing B] [Algebra Q B] {n : ℕ} (io : LetA O n →ₐ[O] R) (β : R →+* L ⊗[Q] B) (o : ZMod n → O)
    (i : ZMod n) (a : L) (b : B) (h3 : β (io (fun j => PowerSeries.C (o j))) = (1 : L) ⊗ₜ[Q] b)
    (h5 : β (algebraMap O R (o i)) = a ⊗ₜ[Q] (1 : B)) :
    ((1 : L) ⊗ₜ[Q] b) * β (io (letE i)) = a • β (io (letE i)) := by
  rw [← h3, ← map_mul, ← map_mul, const_mul_letE, map_mul, AlgHom.commutes, map_mul, h5, Algebra.smul_def]
  rfl

theorem letter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  intro l _ P AI _ K s LL _ Γ R I hI β hβ i c
  refine mul_ext K (Γ.emb i) (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B) _ (fun c m hm hl hc => ?_) c
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have hc' : c ^ m = 1 := by exact_mod_cast hc
  obtain ⟨o, ho⟩ := GlobalTheory.UnramIdem.exists_vec Γ.emb hm hc'
  have h1 := hI c m hm hl hc xb hxb o ho
  have h2 : AI.ιA (WittVector.teichmuller l xb) = algebraMap ↥(K0 K) P.R.B c :=
    AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb
  have h3 := hβ 1 (WittVector.teichmuller l xb)
  have h5 := hβ (o i) 1
  rw [map_one, ho] at h5
  rw [h2] at h3
  exact step I.io β o i _ _ ((congrArg β h1).trans h3) h5

end GlobalTheory.HWL.Letter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisIncl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monV_eq_zero_iff_exists_crisIncl : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 ↔ ∃ w, crisIncl P ℚ_[l] V w = z :=
  fun _ _ P V _ _ z => monV_eq_zero_iff_mem_range_crisIncl P _ V z

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_of_ordIs_ext : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * e ∧ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card ↥(lowerRamificationGroup F L 0) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E h
  unfold OrdIs at h ⊢
  have hmap := addVal_algebraMap_integer F L (p : 𝒪[F])
  rw [map_natCast] at hmap
  rw [hmap] at h
  have hne : IsDiscreteValuationRing.addVal 𝒪[F] (p : 𝒪[F]) ≠ ⊤ := by
    intro ht
    rw [ht, ENat.mul_top (by exact_mod_cast (ramificationIndex_pos F L).ne')] at h
    exact ENat.coe_ne_top E h.symm
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨e, he.symm, ?_, (card_lowerRamificationGroup_zero (K := F) (L := L)).symm⟩
  rw [← he] at h
  exact_mod_cast h.symm

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurentStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_cyclotomic_endo_eq_frobenius_laurent : ∀ (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l] (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → ∀ a : O⟦X⟧, ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  first | exact @GlobalTheory.RedPhiProof.red_phi | exact GlobalTheory.RedPhiProof.red_phi | (intros; apply GlobalTheory.RedPhiProof.red_phi <;> assumption)
end

