module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwining
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_injective : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  intro K L _ _ _ G _ V _ _ _ W _ _ _ ρ σ f hf
  have hcomm : ∀ g, ρ g ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ σ g := fun g =>
    (f.isIntertwining' g).symm
  have hle : ∀ g, LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (ρ g) := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨σ g w, (LinearMap.congr_fun (hcomm g) w).symm⟩
  refine ⟨fun g => algebraMap K L ((ρ.quotient _ hle).character g),
    (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep K L G _ (ρ.quotient _ hle)).1, fun g => ?_⟩
  rw [← map_add (f := _)]
  congr 1
  refine GlobalTheory.T.linear_map_short_exact_commute K W V _ f.toLinearMap (LinearMap.range f.toLinearMap).mkQ (σ g) (ρ g)
    (ρ.quotient _ hle g) hf (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm (hcomm g) ?_
  ext v
  rfl
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradicalStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical : ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (nilRad A) := by
  first | exact @GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | exact GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | (intros; apply GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
section
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), IsIrrChar L L χ → pair χ χ = 1 := by
  first | exact @GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | exact GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | (intros; apply GlobalTheory.BI.pair_self_of_isIrrChar_algClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSumStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧ ∀ k : ℕ, rootSum θ k (minpoly F α ^ (n / (minpoly F α).natDegree)) = ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  first | exact @GlobalTheory.CuspGL.torus_minpoly | exact GlobalTheory.CuspGL.torus_minpoly | (intros; apply GlobalTheory.CuspGL.torus_minpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndRestrictEqCardFixedByMul
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem out_conj_mem_iff_smul_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g * q.out ∈ H ↔ g • q = q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem ind_restrict_eq_card_fixedBy_mul : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  intro L _ _ G _ _ H χ hχ g
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h := by
    intro h x
    simpa using hχ h x
  have hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out)
      = (if g • q = q then (1 : L) else 0) * χ g := by
    intro q
    unfold ext0
    by_cases hq : g • q = q
    · have hm := (out_conj_mem_iff_smul_eq H g q).2 hq
      rw [dite_eq_left hm, if_pos hq, one_mul]
      exact hχ g q.out
    · have hm : q.out⁻¹ * g * q.out ∉ H := fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)
      rw [dite_eq_right hm, if_neg hq, zero_mul]
  rw [ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantEqTopOfIrreducible
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem invariant_eq_top_of_irreducible {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H
  · have H' : U = ⊥ := congrArg Subrepresentation.toSubmodule H
    exact absurd (by simpa [H'] using hv) hv0
  · exact congrArg Subrepresentation.toSubmodule H

theorem finrank_eq_one_or_imprimitive : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → ρ.IsIrreducible → Module.finrank k V = 1 ∨ ∃ (T : Subgroup G) (W : Submodule k V), T ≠ ⊤ ∧ (∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W) ∧ iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)) ∧ ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤ := by
  intro k _ G _ _ V _ _ _ ρ _ hG hirr
  haveI : Nontrivial V := by
    have h1 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    have h2 : (⊥ : Submodule k V) ≠ ⊤ := fun H => h1 (Subrepresentation.ext H)
    exact (Submodule.nontrivial_iff k).1 ⟨_, _, h2⟩
  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · left
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun g : G => ρ g) hc
    have htop := invariant_eq_top_of_irreducible ρ hirr (Submodule.span k {v}) (by
      intro g w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      obtain ⟨m, hm⟩ := hv g
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hm' : ρ g v = m • v := hm
      rw [hm']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      v (Submodule.mem_span_singleton_self v) hv0
    rw [← finrank_top, ← htop, finrank_span_singleton hv0]
  right
  have hB : ¬ ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) →
      ∀ b ∈ B, ∀ g : G, ρ b * ρ g = ρ g * ρ b := fun H => hc (commute_all G _ ρ hG H)
  push Not at hB
  obtain ⟨B, hBn, hBc, b₀, hb₀, g₀, hne⟩ := hB
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun b : B => ρ b)
    (fun a b => hBc a a.2 b b.2)
  choose μ hμ using hv
  let c : G →* MulAut B := MulAut.conjNormal
  have hcv : ∀ (g : G) (b : B), ((c g b : B) : G) = g * b * g⁻¹ := fun g b => rfl
  let E : (B → k) → Submodule k V := fun χ => ⨅ b : B, Module.End.eigenspace (ρ b) (χ b)
  have hE : ∀ χ w, w ∈ E χ ↔ ∀ b : B, ρ b w = χ b • w := by
    intro χ w
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hind : iSupIndep E :=
    (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => ρ b)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hBc j j.2 i i.2) φ).mono fun _ =>
        iInf_mono fun i => (Module.End.genEigenspace (ρ i) _).monotone le_top
  have hmap : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ E (fun b => μ (c g⁻¹ b)) := by
    intro g w hw
    rw [hE] at hw ⊢
    intro b
    rw [← map_smul, ← hw, hcv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul]
    congr 2
    group
  let T : Subgroup G :=
    { carrier := {g | ∀ b, μ (c g b) = μ b}
      one_mem' := fun b => by simp
      mul_mem' := fun {x y} hx hy b => by
        rw [map_mul, MulAut.mul_apply, hx, hy]
      inv_mem' := fun {x} hx b => by
        rw [← hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }
  have hT : ∀ g, g ∈ T ↔ ∀ b, μ (c g b) = μ b := fun g => Iff.rfl
  have hstab : ∀ t ∈ T, ∀ w ∈ E μ, ρ t w ∈ E μ := by
    intro t ht w hw
    have h1 := hmap t w hw
    have h2 : (fun b => μ (c t⁻¹ b)) = μ := funext ((hT _).1 (T.inv_mem ht))
    rwa [h2] at h1
  have hvE : v ∈ E μ := (hE _ _).2 hμ
  refine ⟨T, E μ, ?_, hstab, ?_, ?_⟩
  · intro hTop
    have htop := invariant_eq_top_of_irreducible ρ hirr (E μ)
      (fun g w hw => hstab g (hTop ▸ Subgroup.mem_top g) w hw) v hvE hv0
    have hs : ∀ w, ρ b₀ w = μ ⟨b₀, hb₀⟩ • w := fun w =>
      (hE μ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
    apply hne
    ext w
    simp only [Module.End.mul_apply, hs, map_smul]
  · have hinj : Function.Injective fun q : G ⧸ T => fun b => μ (c q.out⁻¹ b) := by
      intro q q' hq
      rw [← q.out_eq, ← q'.out_eq]
      refine QuotientGroup.eq.2 ((hT _).2 fun b => ?_)
      have h1 : μ (c q.out⁻¹ (c q'.out b)) = μ (c q'.out⁻¹ (c q'.out b)) := congrFun hq _
      rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    refine (hind.comp hinj).mono fun q => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hmap _ w hw
  · have hmem : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ ⨆ q : G ⧸ T, (E μ).map (ρ q.out) := by
      intro g w hw
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T g
      refine Submodule.mem_iSup_of_mem (g : G ⧸ T) ⟨ρ (t⁻¹ : G) w, hstab _ (T.inv_mem t.2) w hw, ?_⟩
      rw [ht, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    refine invariant_eq_top_of_irreducible ρ hirr _ ?_ v (by simpa using hmem 1 v hvE) hv0
    intro g w hw
    have hle : (⨆ q : G ⧸ T, (E μ).map (ρ q.out)) ≤
        (⨆ q : G ⧸ T, (E μ).map (ρ q.out)).comap (ρ g) := by
      refine iSup_le fun q => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact hmem _ u hu
    exact hle hw

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIco
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

noncomputable def oneValue (q a : ℕ) : ℂ :=
  if a = 0 then 0 else ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i)

theorem sum_oneValue_finrank (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, oneValue (Nat.card F) (Module.finrank F W) = (Module.finrank F V : ℂ) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := GlobalTheory.QBinomialSum.sum_gaussian_mul_prod (Nat.card F) (Module.finrank F V)
    (fun a => Nat.card {W : Submodule F V // Module.finrank F W = a}) hq
    (fun a ha => _root_.GlobalTheory.SubspaceNumber.card_subspaces_mul F V a ha)
  rw [← h, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Icc 0 (Module.finrank F V))
    (g := fun W : Submodule F V => Module.finrank F W)
    (fun W _ => Finset.mem_Icc.2 ⟨Nat.zero_le _, W.finrank_le⟩)]
  have h2 : ∀ a : ℕ, ∑ W ∈ Finset.univ.filter (fun W : Submodule F V => Module.finrank F W = a),
      oneValue (Nat.card F) (Module.finrank F W) =
      (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * oneValue (Nat.card F) a := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => oneValue (Nat.card F) a)
      (fun W hW => by rw [(Finset.mem_filter.1 hW).2]), Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = a}), Fintype.card_subtype]
  simp only [h2]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) ?_ ?_
  · intro a ha
    have : a = 0 := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]
  · intro a ha
    have : a ≠ 0 := by
      simp only [Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]

theorem psi_one_eq_oneValue (F : Type) [Field F] [Finite F] (s : F[X] → ℂ)
    (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = n →
      psi s V 1 = oneValue (Nat.card F) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn
    classical
    haveI : Finite V := Module.finite_of_finite F
    haveI : Fintype (Submodule F V) := Fintype.ofFinite _
    have hc : LinearMap.charpoly (1 : Module.End F V) = (X - C 1) ^ n := by
      rw [LinearMap.charpoly_one, hn, C_1]
    rw [psi_eq, hc, hs]
    have h1 : ∀ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, (1 : Module.End F V) x ∈ W},
        psi s W.1 ((1 : Module.End F V).restrict W.2.2) = oneValue (Nat.card F) (Module.finrank F W.1) := by
      intro W
      have : (1 : Module.End F V).restrict W.2.2 = (1 : Module.End F W.1) := by
        ext x
        rfl
      rw [this]
      exact ih _ (hn ▸ Submodule.finrank_lt W.2.1) _ rfl
    rw [finsum_congr h1, finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (Finset.univ.erase (⊤ : Submodule F V)) (by intro W; simp)
        (fun W : Submodule F V => oneValue (Nat.card F) (Module.finrank F W))]
    have h2 := sum_oneValue_finrank F V
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊤ : Submodule F V)), finrank_top, hn] at h2
    rw [← h2]
    ring

theorem psi_one (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  rw [psi_one_eq_oneValue F s hs _ V rfl, oneValue, if_neg h.ne']

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
section
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ φ : Module.End F V → ℂ, IsPrimitive φ → ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | exact GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | (intros; apply GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharTraceMulIdempotent
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.isChar_trace_mul_idempotent :
    ∀ (L : Type) [Field L] (T : Type) [Group T] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L T V) (e : Module.End L V), e * e = e → (∀ t, ρ t * e = e * ρ t) → _root_.GlobalTheory.BI.IsChar L L (fun t => LinearMap.trace L V (ρ t * e)) := by
  intro L _ T _ V _ _ _ ρ e he hc
  have hfix : ∀ v ∈ LinearMap.range e, e v = v := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, he]
  let W : Subrepresentation ρ :=
    ⟨LinearMap.range e, fun t v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact ⟨ρ t w, by rw [← Module.End.mul_apply e, ← hc t, Module.End.mul_apply]⟩⟩
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep L L T _ W.toRepresentation).1
  convert key using 2 with t
  rw [Algebra.algebraMap_self, RingHom.id_apply, Representation.character,
    ← LinearMap.trace_restrict_eq_of_forall_mem (LinearMap.range e) (ρ t * e)
      (fun x => ⟨ρ t x, by rw [hc t]; rfl⟩)]
  congr 1
  ext ⟨v, hv⟩
  change (ρ t * e) v = ρ t v
  rw [Module.End.mul_apply, hfix v hv]

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterFinsumConjSubgroupFunctionExtendByZer
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

private theorem trace_block_permutation (K : Type) [Field K] (X : Type) [Fintype X] [DecidableEq X]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (π : X → X)
    (A : X → W →ₗ[K] W) :
    LinearMap.trace K (X → W) (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q))
      = ∑ q, if π q = q then LinearMap.trace K W (A q) else 0 := by
  have hdec : (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q) : (X → W) →ₗ[K] (X → W))
      = ∑ q, LinearMap.single K (fun _ : X => W) q ∘ₗ (A q ∘ₗ LinearMap.proj (π q)) := by
    apply LinearMap.ext
    intro f
    funext p
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  split_ifs with h
  · have hid : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = LinearMap.id := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hid, LinearMap.comp_id]
  · have hz : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = 0 := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hz, LinearMap.comp_zero, map_zero]

section
variable {G : Type} [Group G] (H : Subgroup G)

theorem cosetCocycle_mem (g : G) (q : G ⧸ H) : q.out⁻¹ * g * (g⁻¹ • q).out ∈ H := by
  have h : ((g⁻¹ * q.out : G) : G ⧸ H) = (((g⁻¹ • q).out : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  have hm := QuotientGroup.eq.mp h
  simpa [mul_assoc] using hm

def cosetCocycle (g : G) (q : G ⧸ H) : H := ⟨_, cosetCocycle_mem H g q⟩

theorem cosetCocycle_one (q : G ⧸ H) : cosetCocycle H 1 q = 1 := by
  apply Subtype.ext
  simp [cosetCocycle]

theorem cosetCocycle_mul (a b : G) (q : G ⧸ H) :
    cosetCocycle H (a * b) q = cosetCocycle H a q * cosetCocycle H b (a⁻¹ • q) := by
  apply Subtype.ext
  simp only [cosetCocycle, Subgroup.coe_mul]
  rw [mul_inv_rev, mul_smul]
  group

theorem inv_smul_eq_iff_conj_mem (g : G) (q : G ⧸ H) :
    g⁻¹ • q = q ↔ q.out⁻¹ * g * q.out ∈ H := by
  have hs : g⁻¹ • q = ((g⁻¹ * q.out : G) : G ⧸ H) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  calc g⁻¹ • q = q ↔ ((g⁻¹ * q.out : G) : G ⧸ H) = ((q.out : G) : G ⧸ H) := by
        rw [hs, QuotientGroup.out_eq']
    _ ↔ q.out⁻¹ * g * q.out ∈ H := by
        rw [QuotientGroup.eq]
        simp [mul_assoc]

def cosetIndRep {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : Representation K H W) :
    Representation K G (G ⧸ H → W) where
  toFun g := LinearMap.pi fun q => σ (cosetCocycle H g q) ∘ₗ LinearMap.proj (g⁻¹ • q)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_mul, mul_smul]
end

theorem isChar_finsum_conj_ext0_of_isChar :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  intro K L _ _ _ G _ _ H ψ hψ
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨n, σ, hσ⟩ := hψ
  obtain ⟨m, ρ, hρ⟩ :=
    (isChar_and_isIrrChar_of_rep K L G (G ⧸ H → Fin n → K) (cosetIndRep H σ)).1
  refine ⟨m, ρ, fun g => ?_⟩
  have hg := hρ g
  simp only at hg
  rw [← hg]
  show (∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) = _
  have hc : (cosetIndRep H σ).character g
      = ∑ q, if g⁻¹ • q = q then LinearMap.trace K (Fin n → K) (σ (cosetCocycle H g q)) else 0 :=
    trace_block_permutation K (G ⧸ H) (Fin n → K) (fun q => g⁻¹ • q)
      (fun q => σ (cosetCocycle H g q))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, hc, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : g⁻¹ • q = q
  · have hm : q.out⁻¹ * g * q.out ∈ H := (inv_smul_eq_iff_conj_mem H g q).mp h
    have he : (⟨q.out⁻¹ * g * q.out, hm⟩ : H) = cosetCocycle H g q :=
      Subtype.ext (by simp [cosetCocycle, h])
    rw [if_pos h, ext0, dite_eq_left hm, hσ, he]
    rfl
  · have hm : q.out⁻¹ * g * q.out ∉ H := fun hm => h ((inv_smul_eq_iff_conj_mem H g q).mpr hm)
    rw [if_neg h, ext0, dite_eq_right hm, map_zero]

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumCharpolyRootsEqFinsumEigenspaceFinrankStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank : ∀ (k : Type) [Field k] [IsAlgClosed k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ), (N : k) ≠ 0 → g ^ N = 1 → ∀ h : k → ℂ, ((LinearMap.charpoly g).roots.map h).sum = ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  first | exact @GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace | exact GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace | (intros; apply GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace <;> assumption)
end

