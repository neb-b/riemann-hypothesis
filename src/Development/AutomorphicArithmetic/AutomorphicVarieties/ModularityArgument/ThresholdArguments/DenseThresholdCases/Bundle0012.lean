module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0014
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTop

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp
private theorem exists_place_above_prime_alt (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)
private theorem charpoly_eq_prod_flag_characters {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]
private theorem continuous_linear_closed {G κ : Type} [TopologicalSpace G] [Field κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T1Space κ] {n : ℕ}
    (a : G → Matrix (Fin n) (Fin n) κ) (ha : Continuous a) : Pr.LinClosed a := by
  intro f
  have h : (fun g => f (a g)) = fun g => ∑ i, ∑ j, a g i j * f (Matrix.single i j 1) := by
    funext g
    conv_lhs => rw [Matrix.matrix_eq_sum_single (a g)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    simp
  have hc : Continuous fun g => f (a g) := by
    rw [h]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (ha.matrix_elem i j).mul continuous_const
  exact isClosed_singleton.preimage hc
private theorem absolute_irreducible_rank_four (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (two : (2 : ResidueField O) ≠ 0) (χ : Fin 4 → F.G₀ →* (ResidueField O)ˣ)
    (K : Type) [Field K] [IsAlgClosed K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K] (twoK : (2 : K) ≠ 0)
    (ρ : F.G₀ →* GL (Fin 4) K) (hρ : Continuous ρ) (hb : U3.MatIrr ⊤ (W.mat ρ))
    (A : Type) [CommRing A] (j : A →+* K) (φ : A →+* ResidueField O) (hj : Function.Injective j) (hred : Pr.RedTo ρ j φ χ)
    (u : F.G₀) (hg : u ∈ F.G') (a : Fin 4 → Kˣ) (hu : (W.mat ρ u).charpoly = ∏ i, (X - C (a i : K))) (hfr : Pr.FreeRatios a)
    (hc : ∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * χ i = χ j) → η = 1)
    (hd : ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ i / χ j) ^ n ≠ 1) : Th.TypeI F ρ ∧ Th.N3 F ρ := by
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  have hm : Continuous (W.mat ρ) := Units.continuous_val.comp hρ
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => by
    obtain ⟨m, hm0, hm1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
    rw [div_pow, div_eq_one] at hm1
    exact hfr s t hst m hm0 hm1
  have hsep := Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _
  have hI : Th.TypeI F ρ := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction K F.G₀ 4 (W.mat ρ) hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction K F.G₀ twoK (W.mat ρ) hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := Ws.isClosed_setOf_matrix_stabilizes_submodule F.G₀ K 4 _ (continuous_linear_closed _ hm) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (Th.Det.perm4 K (ResidueField O) A F.G₀ 4 ρ j φ χ η hj hred hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) two
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨hI, ?_⟩
  have hsp : Submodule.span K (Set.range ((W.mat ρ).comp F.G'.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
  have hsp' : Submodule.span K (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
  have hnc := Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup K (ResidueField O) A F.G₀ (W.mat ρ) j φ χ hj hred hsp' hd F.G' _ hg hsep
  refine Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat ρ s).charpoly.Separable) fun V hV σ => ?_
  exact AlgebraTools.regCosetFour K F.G' twoK ((W.mat ρ).comp F.G'.subtype)
    (fun f => isClosed_singleton.preimage (f.continuous_eval.comp
      (continuous_pi fun p => (hm.comp continuous_subtype_val).matrix_elem p.1 p.2)))
    hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
theorem UpperTheory.V.Th.nice0four_alt :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {r : W.Resid V.frame c.O 4} {B : W.UniversalOrdinaryDeterminantRing r} (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin 4) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ → U3.MatIrr ⊤ (W.mat ρ) → Th.Free V.frame (fun v => x.psi v) → (∀ η : V.frame.G₀ →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (V.frame.eps c.O (ResidueField c.O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) → (∃ i j, ∀ m : ℕ, 0 < m → m ≤ 4 → (r.chib i / r.chib j) ^ m ≠ 1) → _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ := by
  intro l hl L Ω _ _ _ _ _ _ s V c r B ι x ρ hA hb hF hc hd
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (Base.dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  have two : (2 : ResidueField c.O) ≠ 0 := fun h =>
    s.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 (by exact_mod_cast h)))
  obtain ⟨w⟩ : Nonempty V.frame.Vl := (exists_place_above_prime_alt (W.Lp L) l).elim fun v hv => ⟨⟨v, hv⟩⟩
  obtain ⟨g, hg, hfr⟩ := hF w
  obtain ⟨-, A, _, j, φ, hj, hred, -⟩ := Th.Det.redB x ρ hA.rep
  obtain ⟨h1, h2⟩ := absolute_irreducible_rank_four l s.odd V.frame c.O two r.chib (Qbar l) two_ne_zero ρ hA.cont hb A j φ hj hred _ hg _
    (charpoly_eq_prod_flag_characters _ _ (hA.flag w) g) hfr hc hd
  exact ⟨hA, hF, h1, h2⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia
namespace UpperTheory.V.Aut
structure BPrime_s (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) a
def ThmS6_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat
def ThmS6Core_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) fun s => (r (toGS Ω _ s)).mat
end UpperTheory.V.Aut
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeForUp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace UpperTheory.V.Hi.LvR
section Gen
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))
end Gen
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))
variable (Q0 : QData V0) (Q : QData V) (hS : V0.S' ⊆ V.S')
theorem type_for_r_up_of_type_for (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ht : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt (rUp h) ι τ₀ := by
  intro t' ht'
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  have hk : ∀ i, (p0 h).ker ≤ (t' i).ker := fun i g hg => by
    refine teich_ext _ _ ?_ (ht' i g).2 (one_pow _)
    rw [(ht' i g).1, rUp_chib, MonoidHom.mem_ker.1 hg, map_one]
    simp
  let t : Fin n → V0.frame.G₀ →* c.Oˣ := fun i => (p0 h).liftOfSurjective (surjective_levelChangeBaseGroupHom h) ⟨t' i, hk i⟩
  have e : ∀ i g, t i (p0 h g) = t' i g := fun i g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have := ht t fun i g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    rw [e, ← rUp_chib]
    exact ht' i x
  have e2 : ∀ (u : s.St) i, (t' i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype) =
      (t i).comp (V0.pr.comp (Ine (F := L) (s.A u)).subtype) := fun u i => MonoidHom.ext fun x =>
    (e i (V.pr x)).symm.trans (congrArg (t i) (levelChangeBaseGroupHom_apply_projection h hp x))
  simp only [e2]
  exact this
end UpperTheory.V.Hi.LvR
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJTop
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem jacProd_of_alt (hjF : G.Step_jacFin_alt) (hsub : G.SubquotientProp) (hten : G.Step_tensor_alt) (hsupp : G.Step_suppProd_alt) :
    G.Step_jacProd_alt := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩
end Grp
def CStepsAlt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.Step_jacFin_alt ∧ G.SubquotientProp ∧ G.Step_tensor_alt ∧ G.Step_suppProd_alt
open UpperTheory.NonzeroTypeTheory in
theorem twisted_spherical_product_of_irreducible_of_eigenvector (hC : _root_.UpperTheory.TNZ.CStepsAlt) (hlL : LeviSubgroupRestriction) (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain_alt hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of_alt hjF hsub hten hsupp) L V ρ hs hi hx
open UpperTheory.NonzeroTypeTheory in
theorem need_CProps_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem
open UpperTheory.NonzeroTypeTheory in
theorem need_Grp_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩
end UpperTheory.TNZ
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpCount
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spCount
section Abstract
variable {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}
variable (G : Grp k n)
end Local
end UpperTheory.TNZ.Grp.P_spCount
namespace UpperTheory.TNZ.Grp
open P_spCount
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open scoped Classical in
set_option maxHeartbeats 800000 in
theorem step_spCount_alt {n : ℕ} (G : Grp k n) : G.Step_spCount_alt := by
  intro hL c hc hres
  have hE : G.etaSp (jacU G.e (prinSeries c)) =
      eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (jac G.e (parInd (points (Fin n)) (ρc c))) :=
    eS_jacU_eq G.e (parInd (points (Fin n)) (ρc c)) G.eta
  obtain ⟨N, b, hb⟩ := (hL.loc.geo k).1 (Fin n) (Fin G.s) (Fin n) (fun _ => Unit)
    (fun a => Fin (G.d a)) (points (Fin n)) G.e
  obtain ⟨S, hmono, h0, hN, hS⟩ := hb ℂ (ρc c) (isSmooth_ρc c hc)
  obtain ⟨fr⟩ : Nonempty (∀ t : Fin N, ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ (fun _ : Fin n => Unit) i) :=
    ⟨fun t => (b t).nonempty_rows.some⟩
  obtain ⟨gc⟩ : Nonempty (∀ t : Fin N, ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :=
    ⟨fun t => (b t).nonempty_cols.some⟩
  have hr : ∀ t : Fin N, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (subQuot (S t.succ) (S t.castSucc))) ≤ Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a)))
        G.eta (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := by
    intro t
    have e : Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := hS t (fr t) (gc t)
    exact rank_eS_le_of_equiv _ _ e.some
  have hr1 : ∀ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) ≤
        ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := by
    intro t
    split_ifs with hP
    · refine (rank_eS_le (gc t) (cellRep G c (b t) (fr t) (gc t)) G.eta).trans
        ((rank_quotient_le _).trans (le_of_eq ?_))
      rw [Module.rank_self, Nat.cast_one]
    · refine (rank_eS_eq_zero _ _ _ ?_).trans_le zero_le
      intro F hF
      by_contra hne
      apply hP
      intro i a h
      by_contra hab
      apply G.dist a (G.bl i) hab
      refine MonoidHom.ext fun w => ?_
      have h1 := cell_char G c (b t) (fr t) (gc t) F hF hne i a h w
      have h2 : c i (unitIncl k w) = G.μ (G.bl i) (unitIncl k w) := DFunLike.congr_fun (hres i) w
      exact h1.symm.trans h2
  have hsum : ∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) ≤ 1 := by
    rw [← Finset.card_filter]
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact b.injective (good_unique G ht ht')
  have hrank : Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 := by
    calc _ ≤ ∑ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
          (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) :=
          rank_le_of_filtration _ _ S hmono h0 hN _ hr
      _ ≤ ∑ t : Fin N, ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := Finset.sum_le_sum fun t _ => hr1 t
      _ = ((∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) : ℕ) : Cardinal) := (Nat.cast_sum _ _).symm
      _ ≤ 1 := by exact_mod_cast hsum
  haveI : Module.Free ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) := Module.Free.of_divisionRing ℂ _
  have hfin : FiniteDimensional ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hfr : Module.finrank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 :=
    Module.finrank_le_of_rank_le (n := 1) (by rw [Nat.cast_one]; exact hrank)
  rw [hE]
  exact ⟨hfin, hfr⟩
end UpperTheory.TNZ.Grp
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpOrd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spOrd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end UpperTheory.TNZ.Grp.P_spOrd
namespace UpperTheory.TNZ.Grp
open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spOrd_alt : _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)
end UpperTheory.TNZ.Grp
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpTop
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spTop_alt (G : Grp k n) : G.Step_spTop_alt := by
  intro hLat hUniq hCount hLift hTw hRes hPiEta hOrd hPiSub hSupp hCusp hProd hTen L V _ _ π hπs hπi Y iY mY τ hτs hτi hτd hsub
  have hc : ∀ a, ∃ μ' : Fin (G.d a) → kˣ →* ℂˣ,
      (∀ j, IsSmoothChar (μ' j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ' j u = G.μ a u) ∧
        IsCuspSupport (τ a) (fun _ => 1) (fun j => detRep (Fin 1) (μ' j)) :=
    fun a => hCusp L.loc k (G.d a) (Y a) (τ a) (hτs a) (hτi a) (G.μ a) (G.smooth a) (hτd a)
  choose ν hν hνc using hc
  have hνs : ∀ a j, IsSmoothChar (ν a j) := fun a j => (hν a j).1
  have hνr : ∀ a j, res (ν a j) = res (G.μ a) := fun a j => P_spTop.res_eq (hν a j).2
  have htw := fun a => hTw Y τ a (hτs a) (hτi a) (hτd a)
  have hPi : (multiProd G.e (G.twD τ)).IsIrreducible :=
    hProd hCusp L.loc k G.s n G.d G.hd Y (G.twD τ) (fun a => (htw a).1) (fun a => (htw a).2.1) G.μ G.smooth
      (fun a => (htw a).2.2) (fun b c hbc => P_spTop.exists_unit_ne (G.dist b c hbc))
  have hπI := hSupp hOrd L V π hπs hπi Y τ hτs hτi ν hνs hνc hsub
  have hPI := hPiSub hOrd L Y τ hτs hτi ν hνs hνc hPi
  obtain ⟨hfd, hle⟩ := hCount L (G.cOf ν) (P_spTop.isSmoothChar_cOf G ν hνs) (hRes ν hνr)
  have hπη : G.HasEtaVec (jacU G.e π) := by
    obtain ⟨v, hv0, hv⟩ := hTen k G.s G.d Y τ G.μ hτd
    refine hLift _ _ (jacU G.e π) (piTensor τ) (isSmooth_jacU G.e hπs) hsub ⟨v, hv0, fun m hm => ?_⟩
    have hm' := hm
    rw [leviK, Subgroup.mem_pi] at hm'
    exact hv m fun a => hm' a (Set.mem_univ a)
  have hPη := hPiEta hLift Y τ hτs hτd
  obtain ⟨e⟩ := hUniq hLat _ (prinSeries (G.cOf ν)) (P_spTop.isSmooth_prinSeries _) hfd hle _ _ π
    (multiProd G.e (G.twD τ)) hπi hPi hπI hPI hπη hPη
  exact ⟨Y, iY, mY, G.twD τ, fun a => (htw a).1, fun a => (htw a).2.1, fun a => (htw a).2.2, ⟨e⟩⟩
end UpperTheory.TNZ.Grp
end
end
end

