module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import GroundTheory.AutomorphicForms.IwahoriFactorization
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ConjMemIwahori
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private noncomputable def onSub (ρ : Representation ℂ G V) (Z : Submodule ℂ V)
    (hZ : ∀ g, ∀ v ∈ Z, ρ g v ∈ Z) : Representation ℂ G Z where
  toFun g := (ρ g).restrict (hZ g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

private theorem cosets_finite [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G)
    (hc : IsCompact (I : Set G)) (ho : IsOpen (I : Set G)) (t : G) :
    {c : G ⧸ I | ∃ u ∈ I, c = QuotientGroup.mk (u * t)}.Finite := by
  haveI := QuotientGroup.discreteTopology ho
  have h : IsCompact ((fun u : G => (QuotientGroup.mk (u * t) : G ⧸ I)) '' (I : Set G)) :=
    hc.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))
  refine h.finite_of_discrete.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private theorem mem_twKer_of_sum (π : Representation ℂ G V) (I N : Subgroup G) (t : G) (v : V)
    (hv : ∀ u ∈ I, π u v = v) (T : Finset (G ⧸ I))
    (hT : ∀ c, c ∈ T ↔ ∃ u ∈ I, c = QuotientGroup.mk (u * t))
    (hfac : ∀ u ∈ I, ∃ x ∈ N, ∃ b ∈ I, u * t = x * t * b)
    (hnorm : ∀ x ∈ N, t⁻¹ * x * t ∈ N)
    (hsum : ∑ c ∈ T, π c.out v = 0) : v ∈ twKer π N 1 := by
  have key : ∀ c ∈ T, π c.out v - π t v ∈ twKer π N 1 := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := (hT c).1 hc
    obtain ⟨x, hx, b, hb, e⟩ := hfac u hu
    obtain ⟨i, hi⟩ := QuotientGroup.mk_out_eq_mul I (u * t)
    have h1 : π (QuotientGroup.mk (u * t) : G ⧸ I).out v = π x (π t v) := by
      rw [hi, e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Module.End.mul_apply, hv _ i.2, hv _ hb]
    rw [h1]
    exact GlobalTheory.IwahoriInj.sub_mem_twKer hx _
  have h2 : ∑ c ∈ T, (π c.out v - π t v) ∈ twKer π N 1 := Submodule.sum_mem _ key
  rw [Finset.sum_sub_distrib, hsum, zero_sub, neg_mem_iff, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ] at h2
  have hne : (T.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, (hT _).2 ⟨1, one_mem _, by rw [one_mul]⟩⟩)
  have h3 : π t v ∈ twKer π N 1 := (Submodule.smul_mem_iff _ hne).1 h2
  have h4 : twKer π N 1 ≤ (twKer π N 1).comap (π t⁻¹) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, w, rfl⟩
    have e : π t⁻¹ (π (h : G) w - w) =
        π (t⁻¹ * h * t) (π t⁻¹ w) - π t⁻¹ w := by
      rw [map_sub, ← Module.End.mul_apply (π (t⁻¹ * h * t)), ← map_mul,
        ← Module.End.mul_apply (π t⁻¹) (π (h : G)), ← map_mul]
      congr 3
      group
    simpa [e] using GlobalTheory.IwahoriInj.sub_mem_twKer (π := π) (hnorm h h.2) (π t⁻¹ w)
  have h5 := h4 h3
  rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul] at h5
  simpa using h5

end Abstract

section Local

open ValuativeRel Matrix

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

private theorem conj_apply (ν : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    (((Cartan.diagPow F n ν)⁻¹ * g * Cartan.diagPow F n ν : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (ν j - ν i) * (g : Matrix (Fin n) (Fin n) F) i j := by
  have h0 : ((GLnLocal.uniformizer F : 𝒪[F]) : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have e : (((Cartan.diagPow F n ν)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => ((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (-ν i) := rfl
  rw [Units.val_mul, Units.val_mul, e, Cartan.coe_diagPow, mul_diagonal, diagonal_mul,
    sub_eq_add_neg, add_comm, zpow_add₀ h0]
  ring

private theorem conj_mem_iwahori {ν : Fin n → ℤ} (hν : Antitone ν) {b : GL (Fin n) F}
    (hb : b ∈ GLnLocal.iwahori F n)
    (hl : ∀ i j, i < j → (b : Matrix (Fin n) (Fin n) F) i j = 0) :
    (Cartan.diagPow F n ν)⁻¹ * b * Cartan.diagPow F n ν ∈ GLnLocal.iwahori F n := by
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff F n).1 hb
  have hle : ∀ i j, j ≤ i → valuation F
      (((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (ν j - ν i) * (b : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ((b : Matrix (Fin n) (Fin n) F) i j) := fun i j hij => by
    have hz : 0 ≤ ν j - ν i := sub_nonneg.mpr (hν hij)
    rw [← Int.toNat_of_nonneg hz, zpow_natCast, map_mul, map_pow]
    exact mul_le_of_le_one_left' (pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le _)
  refine (GLnLocal.mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply]
    rcases lt_or_ge i j with h | h
    · rw [hl i j h, mul_zero, map_zero]
      exact zero_le'
    · exact (hle i j h).trans (h1 i j)
  · rw [conj_apply]
    exact (hle i j hij.le).trans_lt (h2 i j hij)
  · rw [conj_apply, sub_self, zpow_zero, one_mul]
    exact h3 i

private theorem conj_mem_unipB (ν : Fin n → ℤ) {x : GL (Fin n) F} (hx : x ∈ unipB F (Fin n)) :
    (Cartan.diagPow F n ν)⁻¹ * x * Cartan.diagPow F n ν ∈ unipB F (Fin n) := by
  obtain ⟨h1, h2⟩ := (mem_unipB F).1 hx
  refine (mem_unipB F).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply, h1 i j hij, mul_zero]
  · rw [conj_apply, h2 i, sub_self, zpow_zero, one_mul]

private theorem iwahori_le (g : GL (Fin n) F) (hg : g ∈ iwahori F (Fin n)) :
    g ∈ GLnLocal.iwahori F n := by
  obtain ⟨u, hu, rfl⟩ := hg
  refine ⟨u, ?_, ?_⟩
  · refine Subgroup.mem_comap.2 ((GroundTheory.Automorphic.mem_borel_iff _).2 fun i j hij => ?_)
    rw [GLnLocal.residueReduction_apply]
    exact (GlobalTheory.SmGL.mem_borel _).1 hu i j hij
  · refine Units.ext ?_
    ext i j
    rfl

private theorem factor {ν : Fin n → ℤ} (hν : Antitone ν) (u : GL (Fin n) F)
    (hu : u ∈ GLnLocal.iwahori F n) :
    ∃ x ∈ unipB F (Fin n), ∃ b ∈ GLnLocal.iwahori F n,
      u * Cartan.diagPow F n ν = x * Cartan.diagPow F n ν * b := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id u hu
  obtain ⟨hxP, hx1⟩ := Parabolic.mem_unipotentRadical.1 hx.2
  have hyL := Parabolic.mem_levi.1 hy.2
  obtain ⟨hz0, -⟩ := Parabolic.mem_oppositeUnipotentRadical.1 hz.2
  refine ⟨x, (mem_unipB F).2 ⟨fun i j hij => hxP hij, fun i => ?_⟩, _,
    mul_mem (conj_mem_iwahori hν hy.1 fun i j h => hyL i j h.ne)
      (conj_mem_iwahori hν hz.1 fun i j h => hz0 i j h), ?_⟩
  · simpa using hx1 i i rfl
  · group

private theorem local_inj {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (Z : Submodule ℂ V) (hZ : ∀ g, ∀ v ∈ Z, ρ g v ∈ Z)
    (hsm : ∀ v ∈ Z, IsOpen {g | ρ g v = v}) (ν : Fin n → ℤ) (hν : Antitone ν) (v : V) (hvZ : v ∈ Z)
    (hv : ∀ u ∈ GLnLocal.iwahori F n, ρ u v = v)
    (h0 : hopR ρ (GLnLocal.iwahori F n) (Cartan.diagPow F n ν) v = 0) : v = 0 := by
  have hS := cosets_finite (GLnLocal.iwahori F n) (GLnLocal.isCompact_iwahori F n)
    (GLnLocal.isOpen_iwahori F n) (Cartan.diagPow F n ν)
  have h1 : ∑ c ∈ hS.toFinset, ρ c.out v = 0 := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hS]
    exact h0
  let π := onSub ρ Z hZ
  have hπ : ∀ (g : GL (Fin n) F) (a : Z), ((π g a : Z) : V) = ρ g a := fun _ _ => rfl
  have hsmooth : GlobalTheory.PRep.IsSmooth π := fun a => by
    have : {g : GL (Fin n) F | π g a = a} = {g | ρ g a = a} := by
      ext g
      exact Subtype.ext_iff
    rw [this]
    exact hsm a a.2
  have hker : (⟨v, hvZ⟩ : Z) ∈ twKer π (unipB F (Fin n)) 1 := by
    refine mem_twKer_of_sum π (GLnLocal.iwahori F n) _ (Cartan.diagPow F n ν) _
      (fun u hu => Subtype.ext (hv u hu)) hS.toFinset (fun c => by simp)
      (factor hν) (fun x hx => conj_mem_unipB ν hx) (Subtype.ext ?_)
    rw [Submodule.coe_sum]
    exact h1
  have hfix : (⟨v, hvZ⟩ : Z) ∈ fixed π (iwahori F (Fin n)) :=
    GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => Subtype.ext (hv h (iwahori_le h hh))
  have h2 := (injective_iff_map_eq_zero _).1
    (GlobalTheory.IwahoriInj.iwahoriProj_injective F (Fin n) Z π hsmooth) ⟨_, hfix⟩
    (Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 hker))
  exact congrArg (fun a : fixed π (iwahori F (Fin n)) => ((a : Z) : V)) h2

end Local

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.iwInj :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (w : Pl K) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Gw n w) V) (Z : Submodule ℂ V), (∀ g, ∀ v ∈ Z, ρ g v ∈ Z) →
      (∀ v ∈ Z, IsOpen {g | ρ g v = v}) → ∀ ν : Fin n → ℤ, Antitone ν → ∀ v ∈ Z, (∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, ρ u v = v) →
        hopR ρ (GLnLocal.iwahori (w.adicCompletion K) n) (Cartan.diagPow (w.adicCompletion K) n ν) v = 0 → v = 0 := by
  intro K _ _ n w V _ _ ρ Z hZ hsm ν hν v hvZ hv h0
  exact UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection.local_inj ρ Z hZ hsm ν hν v hvZ hv h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HeckeSimple
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private lemma map_zero_eq_one_of_additive_to_group {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ V)
    (Z : Submodule ℂ V) (hZ : ∀ z ∈ Z, ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z) (w : V)
    (hw : w ∈ Submodule.span ℂ {x | ∃ u : Γ, ∃ z ∈ Z, x = σ u z - z}) (hfix : ∀ u, σ u w = w) : w = 0 := by
  have key : ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ (N' : Subgroup Γ) [Fintype (Γ ⧸ N')], N' ≤ N → N'.Normal →
      ∑ c : Γ ⧸ N', σ c.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, z, hz, rfl⟩ := hx
      obtain ⟨N, hN, hNz⟩ := hZ z hz
      refine ⟨N, hN, fun N' _ hle hn => ?_⟩
      simp only [map_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) _ _ fun c => ?_
      obtain ⟨n, hn'⟩ := QuotientGroup.mk_out_eq_mul N' (c.out * u)
      have h1 : (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) c = QuotientGroup.mk (c.out * u) := by
        simp
      rw [h1, hn', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hNz n (hle n.2)]
    | zero => exact ⟨⊤, inferInstance, fun N' _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      obtain ⟨N₂, h₂, k₂⟩ := hy
      refine ⟨N₁ ⊓ N₂, inferInstance, fun N' _ hle hn => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [k₁ N' (hle.trans inf_le_left) hn, k₂ N' (hle.trans inf_le_right) hn, add_zero]
    | smul a x _ hx =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      refine ⟨N₁, h₁, fun N' _ hle hn => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, k₁ N' hle hn, smul_zero]
  obtain ⟨N, hN, k⟩ := key
  letI : Fintype (Γ ⧸ N.normalCore) := Fintype.ofFinite _
  have h := k N.normalCore N.normalCore_le inferInstance
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast Fintype.card_ne_zero)

private lemma finite_translates_double_coset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : CO U) (g : G) :
    {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have := (hU.1.image hc).finite_of_discrete
  refine this.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.heckeSimple :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Z : Submodule ℂ V) (U : Subgroup G), CO U → SimpleIn ρ Z → (∀ v ∈ Z, IsOpen {g | ρ g v = v}) →
      ∀ Q ≤ Z, (∀ v ∈ Q, ∀ u ∈ U, ρ u v = v) → (∀ g, ∀ v ∈ Q, hopR ρ U g v ∈ Q) → Q = ⊥ ∨ ∀ v ∈ Z, (∀ u ∈ U, ρ u v = v) → v ∈ Q := by
  intro G _ _ _ V _ _ ρ Z U hU hS hsm Q hQZ hQfix hQhop
  by_cases hQ : Q = ⊥
  · exact Or.inl hQ
  right
  let σ : Representation ℂ U V := ρ.comp U.subtype
  have hσ : ∀ (u : U) (x : V), σ u x = ρ u x := fun _ _ => rfl
  set W : Submodule ℂ V := Submodule.span ℂ {x | ∃ u : U, ∃ z ∈ Z, x = σ u z - z} with hW
  have hZN : ∀ z ∈ Z, ∃ N : Subgroup U, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z := by
    intro z hz
    let N : Subgroup U :=
      { carrier := {n | σ n z = z}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.1
    have ho : IsOpen (N : Set U) := (hsm z hz).preimage continuous_subtype_val
    haveI := N.quotient_finite_of_isOpen ho
    exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun n hn => hn⟩
  have htr : ∀ g, ∀ q ∈ Q, ρ g q ∈ Q ⊔ W := by
    intro g q hq
    have hfin := finite_translates_double_coset U hU g
    have h1 := hQhop g q hq
    unfold hopR at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have h2 : ∑ c ∈ hfin.toFinset, (ρ c.out q - ρ g q) ∈ W := by
      refine W.sum_mem fun c hc => ?_
      obtain ⟨u, hu, rfl⟩ := hfin.mem_toFinset.mp hc
      obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul U (u * g)
      refine Submodule.subset_span ⟨⟨u, hu⟩, ρ g q, hS.1 g q (hQZ hq), ?_⟩
      rw [hn, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hQfix q hq n n.2, hσ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    have h3 := (Q ⊔ W).sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
    rw [sub_sub_cancel] at h3
    have hne : ((hfin.toFinset.card : ℕ) : ℂ) ≠ 0 := by
      have : hfin.toFinset.Nonempty := ⟨QuotientGroup.mk (1 * g), hfin.mem_toFinset.mpr ⟨1, U.one_mem, rfl⟩⟩
      exact_mod_cast this.card_ne_zero
    exact ((Q ⊔ W).smul_mem_iff hne).mp h3
  set T : Submodule ℂ V := Submodule.span ℂ {x | ∃ g : G, ∃ q ∈ Q, x = ρ g q} with hT
  have hTZ : T ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact hS.1 g q (hQZ hq)
  have hTst : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    have : T.map (ρ g) ≤ T := by
      rw [hT, Submodule.map_span_le]
      rintro x ⟨g', q, hq, rfl⟩
      exact Submodule.subset_span ⟨g * g', q, hq, by rw [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hQT : Q ≤ T := fun q hq => Submodule.subset_span ⟨1, q, hq, by simp⟩
  have hTeq : T = Z := (hS.2 T hTZ hTst).resolve_left fun h => hQ (le_bot_iff.mp (h ▸ hQT))
  have hTle : T ≤ Q ⊔ W := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact htr g q hq
  intro v hv hvfix
  obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.mp (hTle (hTeq ▸ hv))
  have hw0 : w = 0 := by
    refine map_zero_eq_one_of_additive_to_group σ Z hZN w hw fun u => ?_
    have := hvfix u u.2
    rw [map_add (f := _), hQfix q hq u u.2] at this
    exact add_left_cancel this
  simpa [hw0] using hq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndSeed
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indSeed :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Type} [Group H] [TopologicalSpace H] {Γ : Type} [Group Γ] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (j : H →* G) (y : Representation ℂ (H × Γ) Y) (v₀ : Y), Topology.IsEmbedding j →
      (∀ N ∈ nhds (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ N) → IsOpen {h : H | y (h, 1) v₀ = v₀} →
      ∃ (U : Subgroup G) (F : Y →ₗ[ℂ] (G → Y)), (∀ h, j h ∈ U → y (h, 1) v₀ = v₀) ∧ ∀ v, (∀ h, j h ∈ U → y (h, 1) v = v) →
        F v ∈ IndF j (y.comp (MonoidHom.inl H Γ)) ⊤ ∧ F v 1 = v ∧ ∀ c g, F (y (1, c) v) g = y (1, c) (F v g) := by
  intro G _ _ _ H _ _ Γ _ Y _ _ j y v₀ hj hsm hop
  obtain ⟨N, hN, hNe⟩ := hj.isInducing.isOpen_iff.1 hop
  have h1 : (1 : G) ∈ N := by
    have h0 : (1 : H) ∈ j ⁻¹' N := by
      rw [hNe]
      show y (1, 1) v₀ = v₀
      have : ((1, 1) : H × Γ) = 1 := rfl
      rw [this, map_one]
      rfl
    simpa using h0
  obtain ⟨U, hUo, hUN⟩ := hsm N (hN.mem_nhds h1)
  let D : G → Prop := fun g => ∃ h u, u ∈ U ∧ g = j h * u
  let F : Y →ₗ[ℂ] (G → Y) := LinearMap.pi fun g => if hg : D g then y (hg.choose, 1) else 0
  have Fin' : ∀ g (hg : D g) v, F v g = y (hg.choose, 1) v := by
    intro g hg v
    show (if hg : D g then y (hg.choose, 1) else 0) v = _
    rw [dite_eq_left hg]
  have Fout : ∀ g, ¬ D g → ∀ v, F v g = 0 := by
    intro g hg v
    show (if hg : D g then y (hg.choose, 1) else 0) v = _
    rw [dite_eq_right hg]
    rfl
  refine ⟨U, F, ?_, ?_⟩
  · intro h hh
    have h2 : h ∈ j ⁻¹' N := hUN hh
    rw [hNe] at h2
    exact h2
  · intro v hv
    have key : ∀ g h u, u ∈ U → g = j h * u → F v g = y (h, 1) v := by
      intro g h u hu hg
      have hD : D g := ⟨h, u, hu, hg⟩
      rw [Fin' g hD]
      obtain ⟨u', hu', e⟩ := hD.choose_spec
      generalize hD.choose = c at e
      have hc : j (h⁻¹ * c) ∈ U := by
        have e1 : j h * u = j c * u' := hg.symm.trans e
        have e2 : j (h⁻¹ * c) = u * u'⁻¹ := by
          rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, e1, mul_inv_cancel_right]
        rw [e2]
        exact U.mul_mem hu (U.inv_mem hu')
      have e3 := hv _ hc
      have e4 : ((c, 1) : H × Γ) = (h, 1) * (h⁻¹ * c, 1) := by simp
      rw [e4, map_mul, Module.End.mul_apply, e3]
    have notD : ∀ a g, ¬ D g → ¬ D (j a * g) := by
      rintro a g hg ⟨b, u, hu, e⟩
      exact hg ⟨a⁻¹ * b, u, hu, by rw [map_mul, map_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩
    have notD' : ∀ g u, u ∈ U → ¬ D g → ¬ D (g * u) := by
      rintro g u hu hg ⟨b, u', hu', e⟩
      exact hg ⟨b, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    have hfix : ∀ u ∈ U, rightReg ℂ G Y u (F v) = F v := by
      intro u hu
      funext x
      show F v (x * u) = F v x
      by_cases hx : D x
      · obtain ⟨a, u', hu', rfl⟩ := hx
        rw [key _ a (u' * u) (U.mul_mem hu' hu) (mul_assoc _ _ _), key _ a u' hu' rfl]
      · rw [Fout _ hx, Fout _ (notD' x u hu hx)]
    refine ⟨Submodule.mem_inf.2 ⟨⟨fun _ => Submodule.mem_top, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro h g
      show F v (j h * g) = y (h, 1) (F v g)
      by_cases hg : D g
      · obtain ⟨a, u, hu, rfl⟩ := hg
        rw [key _ (h * a) u hu (by rw [map_mul, mul_assoc]), key _ a u hu rfl]
        have e : ((h * a, 1) : H × Γ) = (h, 1) * (a, 1) := by simp
        rw [e, map_mul, Module.End.mul_apply]
      · rw [Fout _ hg, Fout _ (notD h g hg), map_zero]
    · show IsOpen {x : G | rightReg ℂ G Y x (F v) = F v}
      refine isOpen_iff_mem_nhds.2 fun s hs => ?_
      have hc : Continuous fun x : G => s⁻¹ * x := continuous_const.mul continuous_id
      have hm : {x : G | s⁻¹ * x ∈ U} ∈ nhds s :=
        (hUo.preimage hc).mem_nhds (by simpa using U.one_mem)
      refine Filter.mem_of_superset hm fun x hx => ?_
      have hxs : x = s * (s⁻¹ * x) := by group
      show rightReg ℂ G Y x (F v) = F v
      rw [hxs, map_mul, Module.End.mul_apply, hfix _ hx]
      exact hs
    · rw [key 1 1 1 U.one_mem (by simp)]
      have : ((1, 1) : H × Γ) = 1 := rfl
      rw [this, map_one]
      rfl
    · intro c g
      by_cases hg : D g
      · rw [Fin' g hg, Fin' g hg, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        simp
      · rw [Fout _ hg, Fout _ hg, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OccUnit
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.occUnit :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (w : Pl K) (σ : SmIrr (Gw n w)), Occurs μ τ w σ → IsUnitarisable σ.ρ := by
  intro K _ _ n μ _ τ w σ ⟨f, hf0, _, hf⟩
  have hin : ∀ g (x y : LL μ), inner ℂ (rhoL μ w g x) (rhoL μ w g y) = inner ℂ x y := by
    intro g x y
    unfold rhoL
    exact UnitaryRep.inner_map_map _ _ _ _
  have hinj : ∀ v, f v = 0 → v = 0 := by
    have hirr : σ.ρ.IsIrreducible := by cases σ; assumption
    let Q : Subrepresentation σ.ρ := ⟨LinearMap.ker f, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]⟩
    rcases eq_bot_or_eq_top Q with h | h
    · intro v hv
      have : v ∈ Q := hv
      rw [h] at this
      exact this
    · exfalso
      apply hf0
      ext1 v
      have : v ∈ Q := by rw [h]; trivial
      exact this
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (f y) (f x)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro a b c; simp only [map_add (f := _), inner_add_right]
  · intro a b c; simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]
  · intro a b c; simp only [map_add (f := _), inner_add_left]
  · intro a b c; simp only [map_smul, inner_smul_left, smul_eq_mul]
  · intro v u; simp only [LinearMap.mk₂'ₛₗ_apply, inner_conj_symm]
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact (re_inner_self_pos (𝕜 := ℂ)).2 (fun h => hv (hinj v h))
  · intro g v u; simp only [LinearMap.mk₂'ₛₗ_apply, hf, hin]
end

