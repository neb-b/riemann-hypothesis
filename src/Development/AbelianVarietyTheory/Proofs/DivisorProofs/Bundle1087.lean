module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrised
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.ClSumParam

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [map_inv, inv_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul, _root_.mul_inv_rev]; group⟩

theorem twCl_eq_iff (θ : G →* G) (x y : G) :
    (Quot.mk _ x : TwCl θ) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem rep_mk (θ : G →* G) (x : G) : ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g :=
  (twCl_eq_iff θ _ _).1 (Quot.out_eq (Quot.mk _ x : TwCl θ)).symm

theorem clSum_eq_finsum_param : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G)
    (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) →
    (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) →
    (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) →
    clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  intro G _ _ θ Kg S f C ι N hιS hsurj hinj hSinv horb hN
  let φ : C → TwCl θ := fun c => Quot.mk _ (ι c)
  have hφinj : Function.Injective φ := fun c c' h => hinj c c' ((twCl_eq_iff θ _ _).1 h)
  set F : TwCl θ → ℂ := fun c => if c.rep ∈ S then (fun _ => (1 : ℂ)) c.rep * twOrb θ Kg c.rep f else 0 with hF
  have hsupp : Function.support F ⊆ Set.range φ := by
    intro c hc
    by_contra hnot
    apply hc
    have : c.rep ∉ S := by
      intro hrep
      obtain ⟨c', g, hg⟩ := hsurj _ hrep
      apply hnot
      refine ⟨c', ?_⟩
      have h1 : (Quot.mk _ (ι c') : TwCl θ) = Quot.mk _ c.rep := (twCl_eq_iff θ _ _).2 ⟨g, hg⟩
      exact h1.trans (Quot.out_eq c)
    simp [F, this]
  have hcomp : ∀ c, F (φ c) = N c := by
    intro c
    obtain ⟨g, hg⟩ := rep_mk θ (ι c)
    have hmem : TwCl.rep (θ := θ) (φ c) ∈ S := by
      show TwCl.rep (θ := θ) (Quot.mk _ (ι c)) ∈ S
      rw [hg, hSinv]; exact hιS c
    simp only [F, if_pos hmem, one_mul]
    show twOrb θ Kg (TwCl.rep (θ := θ) (Quot.mk _ (ι c))) f = N c
    rw [hg, horb, hN]
  unfold clSum
  show ∑ᶠ c, F c = _
  rw [← finsum_congr hcomp, ← finsum_mem_range hφinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp,
    finsum_mem_support]

end GlobalTheory.BCT.ClSumParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOutFinite
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceLevel

theorem apply_out_mk {L W : Type} [Group L] (H : Subgroup L) (ψ : L → W) (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g)
    (g : L) : ψ (QuotientGroup.mk g : L ⧸ H).out = ψ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hψ g h h.2]

theorem finsum_out_left {L W : Type} [Group L] [AddCommMonoid W] (H : Subgroup L) (ψ : L → W)
    (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g) (l : L) :
    ∑ᶠ q : L ⧸ H, ψ (l * q.out) = ∑ᶠ q : L ⧸ H, ψ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) (f := fun q : L ⧸ H => ψ q.out)]
  congr 1
  funext q
  have : (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q = (QuotientGroup.mk (l * q.out) : L ⧸ H) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  show ψ (l * q.out) = ψ ((MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q).out
  rw [this, apply_out_mk H ψ hψ]

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (H : Subgroup G) (v : V) : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    show ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v
    simpa using hv h h.2

theorem support_out_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (F : G → ℂ) (hF : HasCompactSupport F) :
    (Function.support fun q : G ⧸ H => F q.out).Finite := by
  haveI := QuotientGroup.discreteTopology hH
  refine ((HasCompactSupport.isCompact hF).image QuotientGroup.continuous_mk).finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.TraceLevel

namespace GlobalTheory.TraceLevel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_id_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (F : G → ℂ)
    (hfin : (Function.support fun q : G ⧸ H => F q.out).Finite) (v : V) :
    levOp ρ K H F LinearMap.id v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, F q.out • ρ q.out v := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    LinearMap.sum_apply]
  simp

theorem levOp_mem_fixed (ρ : Representation ℂ G V) (K K₀ H : Subgroup G) (F : G → ℂ) (hF : IsHecke K₀ F)
    (hH : IsOpen (H : Set G)) (hle : H ≤ K₀) (v : V) (hv : v ∈ fixed ρ H) :
    levOp ρ K H F LinearMap.id v ∈ fixed ρ H := by
  have hfin := support_out_finite H hH F hF.1
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  rw [levOp_id_apply ρ K H F hfin, map_smul]
  congr 1
  have hfin' : (Function.support fun q : G ⧸ H => F q.out • ρ q.out v).Finite :=
    hfin.subset fun q hq => Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])
  rw [map_finsum (ρ k) hfin']
  have := finsum_out_left H (fun g => F g • ρ g v) (fun g h hh => by
    rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv h hh]) k
  rw [← this]
  congr 1
  funext q
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, (hF.2 k (hle hk) q.out).1]

theorem twTr_level (ρ : Representation ℂ G V) (K K₀ K'' : Subgroup G) (F : G → ℂ) (hK''o : IsOpen (K'' : Set G))
    (hK : IsCompact (K : Set G)) (hle : K'' ≤ K₀) (hle' : K₀ ≤ K) (hF : IsHecke K₀ F)
    (hfd : FiniteDimensional ℂ (fixed ρ K'')) :
    twTr ρ K K'' F LinearMap.id = twTr ρ K K₀ F LinearMap.id := by
  have hK₀o : IsOpen (K₀ : Set G) := Subgroup.isOpen_mono hle hK''o
  have hc : K''.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have ho : IsOpen ((K''.subgroupOf K : Subgroup K) : Set K) := hK''o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  have hmul : K''.relIndex K₀ * K₀.relIndex K = K''.relIndex K :=
    Subgroup.relIndex_mul_relIndex (H := K'') (K := K₀) (L := K) hle hle'
  have hd : K''.relIndex K₀ ≠ 0 := left_ne_zero_of_mul (hmul ▸ hc)
  have hcard : Nat.card (↥K₀ ⧸ K''.subgroupOf K₀) ≠ 0 := hd
  haveI : Finite (↥K₀ ⧸ K''.subgroupOf K₀) := Nat.finite_of_card_ne_zero hcard
  letI := Fintype.ofFinite (↥K₀ ⧸ K''.subgroupOf K₀)
  set d : ℕ := K''.relIndex K₀ with hd_def
  obtain ⟨P, hPapp⟩ : ∃ P : V →ₗ[ℂ] V, ∀ v, P v =
      (d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G) v :=
    ⟨(d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G), fun v => by
      simp [LinearMap.sum_apply]⟩
  have hPfix : ∀ v ∈ fixed ρ K'', P v ∈ fixed ρ K₀ := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPapp, map_smul, map_sum]
    congr 1
    have := finsum_out_left (K''.subgroupOf K₀) (fun x : K₀ => ρ (x : G) v) (fun g h hh => by
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hv _ (Subgroup.mem_subgroupOf.1 hh)]) ⟨k, hk⟩
    simp only [finsum_eq_sum_of_fintype, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this
    exact this
  have hPid : ∀ v ∈ fixed ρ K₀, P v = v := by
    intro v hv
    rw [mem_fixed_iff] at hv
    rw [hPapp, Finset.sum_congr rfl (fun k _ => hv _ (k.out).2), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have : (Fintype.card (↥K₀ ⧸ K''.subgroupOf K₀) : ℂ) = d := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [this, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hd), one_smul]
  have key : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v) := by
    intro v hv
    have hv' := (mem_fixed_iff ρ K'' v).1 hv
    have hfin'' := support_out_finite K'' hK''o F hF.1
    have hfin₀ := support_out_finite K₀ hK₀o F hF.1
    rw [levOp_id_apply ρ K K'' F hfin'', levOp_id_apply ρ K K₀ F hfin₀]
    have hR : ∀ a : G ⧸ K₀, F a.out • ρ a.out (P v) =
        (d : ℂ)⁻¹ • ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hPapp, map_smul, map_sum, smul_comm, finsum_eq_sum_of_fintype, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul, Module.End.mul_apply]
    simp_rw [hR]
    rw [← smul_finsum, smul_smul]
    have hL : ∑ᶠ q : G ⧸ K'', F q.out • ρ q.out v =
        ∑ᶠ a : G ⧸ K₀, ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      set e := Subgroup.quotientEquivProdOfLE hle
      rw [← finsum_comp_equiv e.symm]
      have hφ : ∀ g, ∀ h ∈ K'', (fun g => F g • ρ g v) (g * h) = (fun g => F g • ρ g v) g := fun g h hh => by
        simp only
        rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv' h hh]
      have he : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          e.symm p = (QuotientGroup.mk (p.1.out * ((p.2.out : K₀) : G)) : G ⧸ K'') := by
        rintro ⟨a, b⟩
        conv_lhs => rw [← QuotientGroup.out_eq' b]
        rfl
      have h2 : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          F (e.symm p).out • ρ (e.symm p).out v = F p.1.out • ρ (p.1.out * ((p.2.out : K₀) : G)) v := by
        intro p
        rw [he p]
        have := apply_out_mk K'' (fun g => F g • ρ g v) hφ (p.1.out * ((p.2.out : K₀) : G))
        rw [this, (hF.2 _ (p.2.out).2 p.1.out).2]
      simp_rw [h2]
      rw [finsum_curry]
      refine (hfin₀.prod Set.finite_univ).subset ?_
      rintro ⟨a, b⟩ hp
      refine ⟨?_, Set.mem_univ _⟩
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hp) (by simp [h0])
    rw [hL]
    congr 1
    rw [← hmul]
    push_cast
    rw [mul_inv, mul_comm]
  have hVle : fixed ρ K₀ ≤ fixed ρ K'' := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  haveI : FiniteDimensional ℂ (fixed ρ K₀) := Submodule.finiteDimensional_of_le hVle
  have h'' : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v ∈ fixed ρ K'' :=
    fun v hv => levOp_mem_fixed ρ K K₀ K'' F hF hK''o hle v hv
  have h0 : ∀ v ∈ fixed ρ K₀, levOp ρ K K₀ F LinearMap.id v ∈ fixed ρ K₀ :=
    fun v hv => levOp_mem_fixed ρ K K₀ K₀ F hF hK₀o le_rfl v hv
  unfold twTr
  rw [dite_eq_left h'', dite_eq_left h0]
  let Pr : fixed ρ K'' →ₗ[ℂ] fixed ρ K₀ :=
    (P.domRestrict (fixed ρ K'')).codRestrict (fixed ρ K₀) (fun v => hPfix v.1 v.2)
  let ι : fixed ρ K₀ →ₗ[ℂ] fixed ρ K'' := Submodule.inclusion hVle
  have h1 : (levOp ρ K K'' F LinearMap.id).restrict h'' =
      ι ∘ₗ (((levOp ρ K K₀ F LinearMap.id).restrict h0) ∘ₗ Pr) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v)
    exact key v v.2
  have h2 : Pr ∘ₗ ι = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show P v = v
    exact hPid v v.2
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]

end GlobalTheory.TraceLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCompactActionDerivative
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigSep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def evAt (π : CuspSub E a) (g : GA E a) : π.V →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp ((Sm E a).subtype.comp π.V.subtype)

def ell (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) :
    Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map (evAt π g) (LinearMap.proj i))

theorem ell_tmul (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) (φ : π.V) (v : Fin Ξ.d → ℂ) :
    ell π Ξ g i (φ ⊗ₜ v) = φ.1.1 g * v i := by
  simp [ell, evAt]

theorem piScalarRight_eval (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) (i : Fin Ξ.d) :
    ((TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d) m) i).1.1 g = ell π Ξ g i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul φ v =>
    rw [ell_tmul]
    simp [TensorProduct.piScalarRight_apply, mul_comm]

theorem ell_sep (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ))
    (h : ∀ g i, ell π Ξ g i m = 0) : m = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d))).1 ?_
  funext i
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [piScalarRight_eval, h]
  rfl

theorem ell_deriv (π : CuspSub E a) (Ξ : AlgRep E a) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t).1) (toL Z) 0) (g : GA E a) (i : Fin Ξ.d)
    (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => ell π Ξ g i (tensorK π Ξ (c t) m)) (ell π Ξ g i (tensorLie π Ξ (toL Z) m)) 0 := by
  have h0' : Unitary.toUnits (c 0) = 1 := by rw [h0, map_one]
  have hc' : HasDerivAt (fun t => toL (Unitary.toUnits (c t)).val) (toL Z) 0 := hc
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simp only [map_add (f := _)]; exact hx.add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc'
    have h2 : HasDerivAt (fun t => (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i) ((Ξ.dmat (toL Z) *ᵥ v) i) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc' i j).mul_const (v j)
    have e1 : ∀ t, ell π Ξ g i (tensorK π Ξ (c t) (φ ⊗ₜ v)) =
        φ.1.1 (g * infGL E a (Unitary.toUnits (c t))) * (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i := fun t => by
      rw [tensorK, TensorProduct.map_tmul, ell_tmul]
      rfl
    have e2 : ell π Ξ g i (tensorLie π Ξ (toL Z) (φ ⊗ₜ v)) =
        lieD (toL Z) φ.1.1 g * (Ξ.mat (Unitary.toUnits (c 0)) *ᵥ v) i +
          φ.1.1 (g * infGL E a (Unitary.toUnits (c 0))) * (Ξ.dmat (toL Z) *ᵥ v) i := by
      rw [h0', map_one, map_one, mul_one, Matrix.one_mulVec, tensorLie_tmul, map_add (f := _), ell_tmul, ell_tmul]
      rfl
    rw [funext e1, e2]
    exact h1.mul h2

end GlobalTheory.WigSep

namespace GlobalTheory.WigSep

theorem exists_separating_functionals : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), ∃ S : Set (Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), (∀ m, (∀ l ∈ S, l m = 0) → m = 0) ∧ ∀ (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → ∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (tensorK π Ξ (c t) m)) (l (tensorLie π Ξ (toL Z) m)) 0 := by
  intro E _ _ _ a π Ξ
  refine ⟨Set.range fun p : GA E a × Fin Ξ.d => ell π Ξ p.1 p.2, fun m h => ell_sep π Ξ m fun g i => h _ ⟨(g, i), rfl⟩, ?_⟩
  rintro c Z h0 hc _ ⟨⟨g, i⟩, rfl⟩ m
  exact ell_deriv π Ξ c Z h0 hc g i m

end GlobalTheory.WigSep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dite_eq_left (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeSumXMulCLe
section
namespace GlobalTheory.TotalDegreeBounds

open MvPolynomial

theorem totalDegree_aeval_le {σ τ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (f : σ → MvPolynomial τ A) (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap R (MvPolynomial τ A) (AddMonoidAlgebra.coeff P d)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.totalDegree_C]
  rw [h0, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hf i)

theorem totalDegree_sum_X_mul_C_le {ι τ A : Type*} [Fintype ι] [CommSemiring A]
    (g : ι → τ) (a : ι → A) :
    (∑ l : ι, (X (g l) * C (a l) : MvPolynomial τ A)).totalDegree ≤ 1 := by
  classical
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, add_zero]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  simp

theorem main : (let d1 : (n : ℕ) → Fin n × Fin n ⊕ Fin n × Fin n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) (x : Fin n × Fin n ⊕ Fin n × Fin n) ↦ match x with | Sum.inl x => ∑ l : Fin n, MvPolynomial.X (Sum.inr (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inl (l, Prod.snd x))) | Sum.inr x => ∑ l : Fin n, MvPolynomial.X (Sum.inl (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inr (l, Prod.snd x)))); let d2 : (n : ℕ) → GlobalTheory.PsCo.Pc1.Poly n →ₐ[ℂ] MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) ↦ MvPolynomial.aeval (d1 n)); ∀ {n : ℕ} (P : GlobalTheory.PsCo.Pc1.Poly n), MvPolynomial.totalDegree ((d2 n : GlobalTheory.PsCo.Pc1.Poly n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n)) P) ≤ MvPolynomial.totalDegree P) := by
  intro d1 d2 n P
  refine totalDegree_aeval_le (d1 n) ?_ P
  rintro (x | x)
  · exact totalDegree_sum_X_mul_C_le _ _
  · exact totalDegree_sum_X_mul_C_le _ _

end GlobalTheory.TotalDegreeBounds
end

