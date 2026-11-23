module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwTrLevel

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  simp [fixed, GlobalTheory.PRep.eig]

theorem out_eq_of_inv {M : Type} (H : Subgroup G) (F : G → M) (hF : ∀ g, ∀ h ∈ H, F (g * h) = F g) (g : G) :
    F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hF g h h.2]

theorem finite_supp [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (f : G → ℂ) (hf : HasCompactSupport f) : {q : G ⧸ H | f q.out ≠ 0}.Finite := by
  haveI := QuotientGroup.discreteTopology hH
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' tsupport f) :=
    hf.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport f hq, QuotientGroup.out_eq' q⟩

theorem levOp_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (v : V)
    (hs : {q : G ⧸ H | f q.out ≠ 0}.Finite) :
    levOp ρ K H f A v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) v).toAddMonoidHom
    (f := fun q : G ⧸ H => f q.out • (ρ q.out ∘ₗ A)) (hs.subset ?_)
  · simpa using this
  · intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])

theorem A_mem_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V)
    (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (H : Subgroup G) (hH : ∀ k ∈ H, θ k ∈ H) (w : V)
    (hw : w ∈ fixed ρ H) : A w ∈ fixed ρ H := by
  rw [mem_fixed_iff] at hw ⊢
  intro k hk
  have h1 := LinearMap.congr_fun (hA (θ k)) w
  simp only [LinearMap.coe_comp, Function.comp_apply, hθ] at h1
  rw [← h1, hw _ (hH k hk)]

theorem levOp_mem_fixed [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (θ : G →* G)
    (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (K H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hH : ∀ k ∈ H, θ k ∈ H) (f : G → ℂ) (hf : IsHecke H f) (v : V)
    (hv : v ∈ fixed ρ H) : levOp ρ K H f A v ∈ fixed ρ H := by
  have hs := finite_supp H hHo f hf.1
  have hu := A_mem_fixed ρ θ hθ A hA H hH v hv
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K H f A v hs, mem_fixed_iff]
  intro k hk
  set F : G → V := fun g => f g • ρ g (A v) with hFdef
  have hF : ∀ g, ∀ h ∈ H, F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h hh g).2, map_mul, Module.End.mul_apply, hu h hh]
  have hsupp : (Function.support fun q : G ⧸ H => F q.out).Finite := by
    refine hs.subset ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq, hFdef] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ q : G ⧸ H, F q.out) = ∑ᶠ q : G ⧸ H, F q.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom hsupp
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ q : G ⧸ H, ρ k (F q.out) = F (k • q).out := by
    intro q
    have e1 : (k • q : G ⧸ H) = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e1, out_eq_of_inv H F hF]
    simp only [hFdef, map_smul, map_mul, Module.End.mul_apply, (hf.2 k hk q.out).1]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ H)) (f := fun q : G ⧸ H => F q.out)

def avgOp (ρ : Representation ℂ G V) (K' K'' : Subgroup G) : V →ₗ[ℂ] V :=
  ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G)

theorem finite_quot [TopologicalSpace G] [IsTopologicalGroup G] (K K' K'' : Subgroup G)
    (hK : IsCompact (K : Set G)) (h' : IsOpen (K' : Set G)) (h'' : IsOpen (K'' : Set G)) (hle : K' ≤ K) :
    Finite (K' ⧸ K''.subgroupOf K') := by
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen K' h') hle
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen ((K''.subgroupOf K' : Subgroup K') : Set K') := h''.preimage continuous_subtype_val
  haveI := QuotientGroup.discreteTopology ho
  exact finite_of_compact_of_discrete

theorem avgOp_apply (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V) :
    avgOp ρ K' K'' u = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u := by
  unfold avgOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) u).toAddMonoidHom
    (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G)) (Set.toFinite _)
  simpa using this

theorem levOp_le [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K K' K'' : Subgroup G)
    (hle : K'' ≤ K') (hK'K : K' ≤ K) [Finite (K' ⧸ K''.subgroupOf K')] (h'o : IsOpen (K' : Set G))
    (h''o : IsOpen (K'' : Set G)) (f : G → ℂ) (hf : IsHecke K' f) (u : V) (hu : u ∈ fixed ρ K'') :
    levOp ρ K K'' f LinearMap.id u = levOp ρ K K' f LinearMap.id (avgOp ρ K' K'' u) := by
  have hs' := finite_supp K' h'o f hf.1
  have hs'' := finite_supp K'' h''o f hf.1
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K K'' f _ u hs'', levOp_apply ρ K K' f _ _ hs', avgOp_apply]
  simp only [LinearMap.id_apply]
  set F : G → V := fun g => f g • ρ g u with hFdef
  have hF : ∀ g, ∀ h ∈ K'', F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hu h hh]
  set e := Subgroup.quotientEquivProdOfLE hle with hedef
  have he : ∀ (q : G ⧸ K') (j : K' ⧸ K''.subgroupOf K'),
      F (e.symm (q, j)).out = f q.out • ρ q.out (ρ (j.out : G) u) := by
    intro q j
    have h1 : e.symm (q, j) = (QuotientGroup.mk (q.out * (j.out : G)) : G ⧸ K'') := by
      rw [hedef, Subgroup.quotientEquivProdOfLE_symm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [h1, out_eq_of_inv K'' F hF]
    simp only [hFdef, (hf.2 _ (j.out).2 q.out).2, map_mul, Module.End.mul_apply]
  set S : G ⧸ K' → V := fun q => ∑ᶠ j : K' ⧸ K''.subgroupOf K', f q.out • ρ q.out (ρ (j.out : G) u) with hSdef
  have hL : ∑ᶠ r : G ⧸ K'', F r.out = ∑ᶠ q, S q := by
    rw [← finsum_comp_equiv e.symm]
    rw [finsum_curry]
    · simp only [he, hSdef]
    · refine (hs'.prod (Set.finite_univ (α := K' ⧸ K''.subgroupOf K'))).subset ?_
      rintro ⟨q, j⟩ hp
      simp only [Function.mem_support, ne_eq, he] at hp
      simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
      intro h0
      exact hp (by rw [h0, zero_smul])
  have hR : ∀ q : G ⧸ K', f q.out • ρ q.out (((K''.relIndex K' : ℕ) : ℂ)⁻¹ •
      ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u) = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • S q := by
    intro q
    have hm := AddMonoidHom.map_finsum (f q.out • ρ q.out).toAddMonoidHom
      (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G) u) (Set.toFinite _)
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
    rw [map_smul, smul_comm, hm]
  simp only [hR]
  rw [hL, ← smul_finsum, smul_smul, ← Subgroup.relIndex_mul_relIndex K'' K' K hle hK'K]
  congr 1
  push_cast
  rw [mul_inv, mul_comm]

theorem avgOp_mem (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K'') : avgOp ρ K' K'' u ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply, mem_fixed_iff]
  intro k hk
  set F : K' → V := fun x => ρ (x : G) u with hFdef
  have hF : ∀ x : K', ∀ h ∈ K''.subgroupOf K', F (x * h) = F x := by
    intro x h hh
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hu _ (Subgroup.mem_subgroupOf.mp hh)]
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out) = ∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)
    (Set.toFinite _)
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ j : K' ⧸ K''.subgroupOf K', ρ k (F j.out) = F ((⟨k, hk⟩ : K') • j).out := by
    intro j
    have e1 : ((⟨k, hk⟩ : K') • j : K' ⧸ K''.subgroupOf K') = QuotientGroup.mk ((⟨k, hk⟩ : K') * j.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [e1, out_eq_of_inv _ F hF]
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm (⟨k, hk⟩ : K') : Equiv.Perm (K' ⧸ K''.subgroupOf K'))
    (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)

theorem avgOp_fix (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K') : avgOp ρ K' K'' u = u := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply]
  have h1 : ∀ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u = u := fun j => hu _ (j.out).2
  simp only [h1]
  haveI := Fintype.ofFinite (K' ⧸ K''.subgroupOf K')
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h2 : (K''.relIndex K' : ℕ) = Fintype.card (K' ⧸ K''.subgroupOf K') := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have h3 : (Fintype.card (K' ⧸ K''.subgroupOf K') : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := K' ⧸ K''.subgroupOf K')).ne'
  rw [h2, inv_mul_cancel₀ h3, one_smul]

end GlobalTheory.TwTrLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentFrameFormsBaseChange
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.BaseChangeIndep

theorem indep_pi {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {L : Type} [Field L] (emb : O →+* L)
    (hemb : Function.Injective emb) {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module L V]
    (b : M →ₛₗ[emb] V) (hbinj : Function.Injective b)
    (hb : ∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent L fun a => b (x a))
    {T : Type} [Finite T] (n : ℕ) (y : Fin n → T → M) (hy : LinearIndependent O y) :
    LinearIndependent L fun a t => b (y a t) := by
  classical
  haveI : Fintype T := Fintype.ofFinite T

  haveI : Module.IsTorsionFree O M := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m h
    have h1 : emb r • b m = 0 := by rw [← LinearMap.map_smulₛₗ, h, map_zero]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (hemb (by rw [h2, map_zero]))
    · exact Or.inr (hbinj (by rw [h2, map_zero]))

  let P : Submodule O M := Submodule.span O (Set.range fun p : Fin n × T => y p.1 p.2)
  haveI : Module.Finite O P := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))
  haveI : Module.Free O P := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O P
  let k := Module.finrank O P
  have hmem : ∀ a t, y a t ∈ P := fun a t => Submodule.subset_span ⟨(a, t), rfl⟩
  have he : LinearIndependent O fun i => ((e i : P) : M) :=
    e.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hbe : LinearIndependent L fun i => b (e i : M) := by
    have := hb k (fun i => (e i : M)) he
    exact this

  let Y : Fin n → T × Fin k → O := fun a p => e.repr ⟨y a p.1, hmem a p.1⟩ p.2
  let Φ : (T × Fin k → O) →ₗ[O] (T → M) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • ((e i : P) : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΦ : ∀ a, Φ (Y a) = y a := by
    intro a; funext t
    have h2 : ((∑ i, e.repr ⟨y a t, hmem a t⟩ i • e i : P) : M) = y a t := by rw [e.sum_repr]
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    change ∑ i, Y a (t, i) • ((e i : P) : M) = y a t
    exact h2
  have hY : LinearIndependent O Y := by
    apply LinearIndependent.of_comp Φ
    have : (Φ ∘ Y) = y := funext hΦ
    rw [this]; exact hy
  letI : Algebra O L := emb.toAlgebra
  haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 hemb
  have hY' : LinearIndependent L fun a => algebraMap O L ∘ Y a :=
    linearIndependent_algebraMap_comp_iff.2 hY
  let Ψ : (T × Fin k → L) →ₗ[L] (T → V) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • b (e i : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Z hZ
    funext p
    have h1 : ∑ i, Z (p.1, i) • b (e i : M) = 0 := congrFun hZ p.1
    have := (Fintype.linearIndependent_iff.1 hbe) (fun i => Z (p.1, i)) h1 p.2
    simpa using this
  have key := hY'.map' Ψ hΨ
  have hfam : (Ψ ∘ fun a => algebraMap O L ∘ Y a) = fun a t => b (y a t) := by
    funext a t
    change ∑ i, (algebraMap O L (Y a (t, i))) • b (e i : M) = b (y a t)
    rw [← hΦ a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.map_smulₛₗ]
    rfl
  rw [hfam] at key
  exact key

end GlobalTheory.BaseChangeIndep

namespace GlobalTheory.BaseChangeIndep

theorem forms_indep : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok →
    (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) →
    ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x →
      LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  intro l _ ι _ _ N F mu jK b hbinj hOk hb n x hx
  obtain ⟨S, hS⟩ := hOk.classes
  let R : Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu) →ₗ[F.O] (S → NablaT F.O N mu) :=
    { toFun := fun f s => (f : F.G → NablaT F.O N mu) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf0
    apply Subtype.ext
    funext g
    obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
    have hf : ∀ (γ : F.Γ) (g : F.G) (κ : F.K), (f : F.G → NablaT F.O N mu) ((γ : F.G) * g * κ) =
        repOf F.O (A := alg F.O N mu) jK (NablaT F.O N mu) κ⁻¹ ((f : F.G → NablaT F.O N mu) g) := f.2
    have h0 : (f : F.G → NablaT F.O N mu) s = 0 := congrFun hf0 ⟨s, hs⟩
    have h1 := hf ⟨γ, hγ⟩ s ⟨κ, hκ⟩
    rw [h1, h0, map_zero]
    rfl
  have hx' : LinearIndependent F.O (R ∘ x) := hx.map' R hR
  have hOk1 := hOk.ring.1
  have key := indep_pi F.emb hOk1 b hbinj hb n (R ∘ x) hx'
  let R' : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (S → NablaT (PadicAlgCl l) N mu) :=
    { toFun := fun f s => f s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp R'
  exact key

end GlobalTheory.BaseChangeIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit

section OneVar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_mul_of_ne_zero {s : ℝ} (hs : s < 0) {a : k} (ha : a ≠ 0) (y : k) :
    ENNReal.ofReal (if h : a * y = 0 then 0 else nabs k (Units.mk0 (a * y) h)) ^ s =
      ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s *
        ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s := by
  have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
    simpa using Model.nabs_pos _
  by_cases hy : y = 0
  · subst hy
    have : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hpa]
    simp [ENNReal.zero_rpow_of_neg hs, ENNReal.mul_top this]
  · have hay : a * y ≠ 0 := mul_ne_zero ha hy
    have hpy : ENNReal.ofReal (nabs k (Units.mk0 y hy)) ≠ 0 := by
      simpa using Model.nabs_pos _
    have e : Units.mk0 (a * y) hay = Units.mk0 a ha * Units.mk0 y hy := Units.ext rfl
    rw [dite_eq_right hay, dite_eq_right hy, e, Model.nabs_mul, ENNReal.ofReal_mul (Model.nabs_pos _).le,
      ENNReal.mul_rpow_of_ne_zero hpa hpy]

theorem absPow_le_one_of_notMem [MeasurableSpace k] [BorelSpace k] {s : ℝ} (hs : s < 0) {y : k} (hy : y ∉ 𝒪[k]) :
    ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s ≤ 1 := by
  have h0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  rw [dite_eq_right h0]
  refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ hs
  have h1 : valuation k y⁻¹ ≤ 1 := ((valuation k).val_le_one_or_val_inv_le_one y).resolve_left hy
  have h2 : nabs k (Units.mk0 y h0)⁻¹ ≤ 1 := Model.nabs_le_one _ (by simpa using h1)
  have h3 : nabs k (Units.mk0 y h0) * nabs k (Units.mk0 y h0)⁻¹ = 1 := by
    rw [← Model.nabs_mul, mul_inv_cancel, Model.nabs_one]
  have h4 := Model.nabs_pos (Units.mk0 y h0)
  rw [ENNReal.one_le_ofReal]
  nlinarith

end OneVar

theorem lintegral_absPow_affine_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ)
    (hs : s < 0) (a b : k) :
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  have hO : IsOpen (𝒪[k] : Set k) := Model.isOpen_int
  by_cases ha : a = 0
  · have hpos : μ (𝒪[k] : Set k) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    rw [dite_eq_left ha, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hs, ENNReal.top_mul]
    · exact le_top
    · exact fun h => hpos (add_eq_zero.1 h).2
  rw [dite_eq_right ha]
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  set C : ℝ≥0∞ := ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s with hC
  have hCt : C ≠ ⊤ := by
    have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
      simpa using Model.nabs_pos _
    simp [hC, ENNReal.rpow_eq_top_iff, hpa]
  have hpt : ∀ x, (𝒪[k] : Set k).indicator (fun y => P (a * y + b)) x ≤
      C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) := by
    intro x
    by_cases hx : x ∈ (𝒪[k] : Set k)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have e : a * x + b = a * (x + b / a) := by field_simp
      have e' : P (a * x + b) = C * P (x + b / a) := by
        rw [e]; exact absPow_mul_of_ne_zero hs ha _
      rw [e']
      gcongr
      by_cases hx' : x + b / a ∈ (𝒪[k] : Set k)
      · rw [Set.indicator_of_mem hx']; exact le_self_add
      · rw [Set.indicator_of_notMem hx', zero_add]; exact absPow_le_one_of_notMem hs hx'
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  calc _ ≤ ∫⁻ x, C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ hCt,
          lintegral_add_right _ (measurable_one.indicator hO.measurableSet),
          lintegral_add_right_eq_self (fun x => (𝒪[k] : Set k).indicator P x),
          lintegral_indicator_one hO.measurableSet]

end GlobalTheory.KSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFinIrr
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.LocFinIrr

def conjMA (H : Type*) [Group H] : MulAction H H where
  smul g y := g * y * g⁻¹
  one_smul y := by show 1 * y * 1⁻¹ = y; group
  mul_smul a b y := by show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹; group

theorem conjMA_cont (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    @ContinuousSMul H H (conjMA H).toSMul _ _ :=
  @ContinuousSMul.mk H H (conjMA H).toSMul _ _ (by
    show Continuous fun q : H × H => q.1 * q.2 * q.1⁻¹
    fun_prop)

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.OrbFinAf.LocFinIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSameDoubleCosetOfHasElementaryDivisorsDefinitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  first | exact @GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | exact GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | (intros; apply GlobalTheory.LocalCartan.doubleCoset_of_hasDiv <;> assumption)
end

