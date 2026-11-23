module

public import Mathlib
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwist
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem natInvIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : NatInvIso := by
  intro p _ K O _ _ _ _ G _ _ hK hO i ε hε
  haveI := hO.ring; haveI := hO.compact; haveI := hO.t2
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.FreeTwistH2.exists_free_H2_twist hT hK hO i hε
  have hq := _root_.GlobalTheory.FunctorialityH2.bijective_phi_quot_pow hT hK hO i hε z hz
  have hbij : ∀ (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul O M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M],
      Function.Bijective (phi ε z M) := by
    intro M _ _ _ _ _ _ _ _
    obtain ⟨n, m, e, ⟨E⟩⟩ := _root_.GlobalTheory.dvr_fg_module_structure (O := O) M
    refine bijective_of_retract ε z M (fun _ : Fin n => O) (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i)
      (fun j => LinearMap.proj j ∘ₗ LinearMap.fst O _ _ ∘ₗ E.toLinearMap)
      (fun j => E.symm.toLinearMap ∘ₗ LinearMap.inl O _ _ ∘ₗ LinearMap.single O (fun _ : Fin n => O) j)
      (fun i => LinearMap.proj i ∘ₗ LinearMap.snd O _ _ ∘ₗ E.toLinearMap)
      (fun i => E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i)
      (fun j => _root_.GlobalTheory.linearMap_continuous_of_compactSpace_of_finite _) (fun j => _root_.GlobalTheory.linearMap_continuous_of_compactSpace_of_finite _) (fun i => _root_.GlobalTheory.linearMap_continuous_of_compactSpace_of_finite _) (fun i => ?_) ?_
      (fun j => ?_) (fun i => hq (e i))
    · have := _root_.GlobalTheory.linearMap_continuous_of_compactSpace_of_finite (M := O) (M' := M) ((E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i) ∘ₗ
          (IsLocalRing.maximalIdeal O ^ e i).mkQ)
      exact (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff.2 this
    · intro x
      conv_rhs => rw [← E.symm_apply_apply x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← map_sum, ← map_add (f := _)]
      congr 1
      ext <;> simp [Finset.univ_sum_single]
    · show Function.Bijective (phi ε z O)
      rw [show ⇑(phi ε z O) = fun a : O => a • z from funext (phi_self ε z)]
      exact hz
  refine ⟨⟨fun M _ _ _ _ _ h => by
      haveI := h.csmul; haveI := h.t2; haveI := h.fg
      exact (LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm, ?_⟩⟩
  intro M M' _ _ _ _ _ _ _ _ _ _ h h' f hf w
  haveI := h.csmul; haveI := h.t2; haveI := h.fg
  haveI := h'.csmul; haveI := h'.t2; haveI := h'.fg
  obtain ⟨m, rfl⟩ := (hbij M).2 w
  show (LinearEquiv.ofBijective (phi ε z M') (hbij M')).symm _ =
    f ((LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm _)
  rw [phi_natural ε z M M' f hf (twist_map ε f) m]
  rw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.NullOverS

theorem topBasis_c_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (i : ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) : TB.c i x ∈ I ^ n := by
  have key : ∀ r : A, TB.c i (r * x) ∈ I ^ n := by
    refine Submodule.span_induction (p := fun x _ => ∀ r : A, TB.c i (r * x) ∈ I ^ n) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩ r
      rw [mul_comm, TB.c_mul]
      exact Ideal.mul_mem_right _ _ hj
    · intro r; simp
    · intro y z _ _ hy hz r
      rw [mul_add, map_add (f := _)]; exact Ideal.add_mem _ (hy r) (hz r)
    · intro a y _ hy r
      rw [smul_eq_mul, ← mul_assoc]; exact hy _
  simpa using key 1

theorem topBasis_c_i₀ {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have h := TB.c_mul TB.i₀ a 1
  rw [mul_one, ← TB.b_i₀, TB.c_self, mul_one] at h
  exact h

end GlobalTheory.NullOverS

theorem GlobalTheory.NullOverS.null_of_mul_null : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S),
    (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) →
    ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  intro l _ K bk ι TB d Y hY σ hσ N a b
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem l K bk N
  have hdet : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  obtain ⟨m, t, q, hq⟩ := _root_.GlobalTheory.BSP.BddDen.main l K bk Y.det hdet n
  obtain ⟨n', hn'⟩ := hn m
  refine (Set.finite_iUnion fun c : Fin d => hσ n' c b).subset ?_
  intro i hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hi ⊢
  by_contra hc
  push_neg at hc
  apply hi
  apply hn'
  have h1 : (t • adjugate Y * (Y * (σ i).map bk.ev)) a b = t * Y.det * bk.ev (σ i a b) := by
    rw [← Matrix.mul_assoc, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  have h2 : bk.ev (X ^ m * σ i a b) = (t • adjugate Y * (Y * (σ i).map bk.ev)) a b -
      bk.ev ((l : bk.S) ^ n) * (q * bk.ev (σ i a b)) := by
    rw [h1, map_mul, map_pow, map_pow, map_natCast]
    linear_combination (-(bk.ev (σ i a b))) * hq
  rw [← GlobalTheory.NullOverS.topBasis_c_i₀ TB (X ^ m * σ i a b), h2, map_sub]
  refine Ideal.sub_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine GlobalTheory.NullOverS.topBasis_c_mem_map TB _ _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc c)
  · rw [TB.c_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.FontCmp

namespace GlobalTheory.Per.CrysSubQuot

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem of_shortExact [FiniteDimensional LL V]
    {ρ₀ : Representation LL G V₀} {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    {i : V₀ →ₗ[LL] V} {p : V →ₗ[LL] V'} (hi : IsEquivariant ρ₀ ρ i) (hp : IsEquivariant ρ ρ' p)
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p)
    [Module.Finite LL ↥(Dcris PD ρ)] [Module.Finite LL ↥(Dcris PD ρ')]
    (a : finrank LL ↥(Dcris PD ρ₀) ≤ finrank Qp K₀ * finrank LL V₀)
    (c : finrank LL ↥(Dcris PD ρ') ≤ finrank Qp K₀ * finrank LL V')
    (h : IsCrys PD ρ) :
    IsCrys PD ρ₀ ∧ IsCrys PD ρ' ∧ Function.Surjective (DcrisMap PD hp) := by
  obtain ⟨e1, e2⟩ := GlobalTheory.RegularRing.left_exact PD hi hp h1 h2 h3
  have h4 := (DcrisMap PD hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (DcrisMap PD hp)).finrank_le
  unfold IsCrys at h ⊢
  rw [← h5, mul_add] at h
  refine ⟨by omega, by omega, ?_⟩
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  omega

end Generic

theorem crys_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsCrys (P.PD K) ρ' → IsCrys (P.PD K) ρ) ∧ (Function.Surjective f → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ, AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  obtain ⟨hle, hfin⟩ := GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings l P AI T K LL
  have he : IsEquivariant ρ ρ' f := hf
  have := hfin V ρ
  have := hfin V' ρ'
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have hq : IsEquivariant ρ' (ρ'.quotient (LinearMap.range f) hst) (LinearMap.range f).mkQ :=
      fun g v => rfl
    have := hfin _ (ρ'.quotient (LinearMap.range f) hst)
    exact (of_shortExact (P.PD K) he hq hi (LinearMap.exact_map_mkQ_range f)
      (LinearMap.range f).mkQ_surjective (hle V ρ) (hle _ _) h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    have hq : IsEquivariant (ρ.subrepresentation (LinearMap.ker f) hst) ρ (LinearMap.ker f).subtype :=
      fun g v => rfl
    obtain ⟨-, h1, h2⟩ := of_shortExact (P.PD K) hq he (LinearMap.ker f).injective_subtype
      (LinearMap.exact_subtype_ker_map f) hs (hle _ _) (hle V' ρ') h
    refine ⟨h1, fun y hy => ?_⟩
    obtain ⟨x, hx⟩ := h2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end GlobalTheory.Per.CrysSubQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.TypePrimeEta

theorem sum_two_mul_Icc (r : ℕ) : ∑ a ∈ Finset.Icc 1 r, 2 * a = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem padicValNat_pow_sub_one_le (g g' a : ℕ) (hg : g.Prime) (hg' : 2 ≤ g') (hgg : g' ≤ g ^ 2)
    (ha : 1 ≤ a) : padicValNat g (g' ^ a - 1) ≤ 2 * a := by
  haveI : Fact g.Prime := ⟨hg⟩
  have h1 : 1 < g' ^ a := Nat.one_lt_pow (by omega) (by omega)
  have hpos : 0 < g' ^ a - 1 := by omega
  have hle : g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := Nat.le_of_dvd hpos (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hlt : g ^ padicValNat g (g' ^ a - 1) < g ^ (2 * a) := by
    calc g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := hle
      _ < g' ^ a := by omega
      _ ≤ (g ^ 2) ^ a := Nat.pow_le_pow_left hgg a
      _ = g ^ (2 * a) := by rw [← pow_mul]
  by_contra h
  have h := Nat.lt_of_not_le h
  have := Nat.pow_le_pow_right hg.pos h.le
  omega

theorem val_card_le (g g' r f : ℕ) (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g')
    (hgg : g' ≤ g ^ 2) :
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g)) ^ f *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g')) ^ f) ≤ 2 * f * r ^ 2 := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : Fact g'.Prime := ⟨hg'⟩
  have h0 : ∀ q : ℕ, [Fact q.Prime] → Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) ≠ 0 :=
    fun q _ => Nat.card_pos.ne'
  obtain ⟨h1, h2⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.padicValCardGeneralLinear g g' r hne
  have hpow (a n : ℕ) : padicValNat g (a ^ n) = n * padicValNat g a := by
    simpa only [← Nat.padicValNat_def] using (Nat.multiplicity_pow (p := g) a n)
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ (h0 g)) (pow_ne_zero _ (h0 g')), hpow, hpow, h1, h2]
  have hs : ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1) ≤ r * (r + 1) := by
    rw [← sum_two_mul_Icc]
    exact Finset.sum_le_sum fun a ha =>
      padicValNat_pow_sub_one_le g g' a hg hg'.two_le hgg (Finset.mem_Icc.1 ha).1
  have hd : r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
  have he : r * (r - 1) + r * (r + 1) = 2 * r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  calc f * (r * (r - 1) / 2) + f * ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)
      ≤ f * (r * (r - 1)) + f * (r * (r + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hs)
    _ = 2 * f * r ^ 2 := by rw [← mul_add, he]; ring

theorem val_cardG0g_le (D : D7) (k k' : Fin 2) (hkk : k ≠ k')
    (hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ)) :
    padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ≤ 2 * D.R.f * D.R.r ^ 2 := by
  have hg := D.host.g_prime k
  have hg' := D.host.g_prime k'
  have hgg : D.host.g k' ≤ D.host.g k ^ 2 := by
    have h1 : (0 : ℝ) < D.host.g k' := by exact_mod_cast hg'.pos
    have h0 : (0 : ℝ) < (D.host.g k : ℝ) ^ 2 := pow_pos (by exact_mod_cast hg.pos) 2
    have h2 : Real.log (D.host.g k' : ℝ) ≤ Real.log ((D.host.g k : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    have := (Real.log_le_log_iff h1 h0).1 h2
    exact_mod_cast this
  have hk : (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) := by
    fin_cases k <;> fin_cases k' <;> simp_all
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne hgg
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_comm]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne.symm hgg

theorem first_le (f r t CT N r' e n : ℕ) (C : ℝ) (hC : 8 * (CT : ℝ) ≤ C) (hN2 : 2 ≤ N)
    (hN : N ≤ n + 1) (hr4 : 4 * r' ≤ N ^ 2) (hn : r + t = n) :
    ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ) ≤
      4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
  have hn1 : (1 : ℝ) ≤ n := by have : 1 ≤ n := by omega
                               exact_mod_cast this
  have hnR : (n : ℝ) = r + t := by rw [← hn]; push_cast; ring
  have a1 : (4 : ℝ) * r' ≤ (N : ℝ) ^ 2 := by exact_mod_cast hr4
  have a2 : (N : ℝ) ≤ 2 * n := by
    have : N ≤ 2 * n := by omega
    exact_mod_cast this
  have a0 : (0 : ℝ) ≤ N := by positivity
  have a3 : (N : ℝ) ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ a0 a2 2
  have hNr : 4 * ((N : ℝ) * r') ≤ 4 * (2 * (n : ℝ) ^ 3) := by
    calc 4 * ((N : ℝ) * r') = N * (4 * r') := by ring
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left a1 a0
      _ = N ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := pow_le_pow_left₀ a0 a2 3
      _ = 4 * (2 * (n : ℝ) ^ 3) := by ring
  have hs : (N : ℝ) + r' ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have he0 : (0 : ℝ) ≤ e := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hr0 : (0 : ℝ) ≤ r' := by positivity
  have hm : ((e : ℝ) + t + 1) * (N + r') ≤ ((e : ℝ) + t + n) * (3 * (n : ℝ) ^ 2) :=
    mul_le_mul (by linarith) hs (by positivity) (by positivity)
  have hX : (N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r') ≤ 5 * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [pow_nonneg (show (0:ℝ) ≤ n by linarith) 2]
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((n : ℝ) + e + t) := by positivity
  have hCT : (0 : ℝ) ≤ CT := by positivity
  have hCX : (CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r')) ≤
      C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hCT, mul_le_mul_of_nonneg_right hC hY]
  calc ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ)
      = 4 * (f : ℝ) * n * ((CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r'))) := by
        push_cast; rw [hnR]; ring
    _ ≤ 4 * (f : ℝ) * n * (C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t))) :=
        mul_le_mul_of_nonneg_left hCX (by positivity)
    _ = 4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by ring

end GlobalTheory.TypePrimeEta

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime]

def emb (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp (σ.toAlgHom.comp L.1.val)

def phiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (emb P σ L) (AlgHom.id ℚ_[l] P.R.BdR) (fun _ _ => Commute.all _ _)

def PhiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    Fin a → P.R.BdR :=
  fun i => phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) x)

variable (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ)

theorem emb_apply (c : ↥L.1) : emb P σ L c = algebraMap (Om l) P.R.BdR (σ (c : Om l)) := rfl

theorem phiS_tmul (c : ↥L.1) (b : P.R.BdR) :
    phiS P σ L (c ⊗ₜ b) = algebraMap (Om l) P.R.BdR (σ (c : Om l)) * b := by
  simp [phiS, emb]

theorem PhiS_tmul (v : Fin a → ↥L.1) (b : P.R.BdR) :
    PhiS P σ L a (v ⊗ₜ b) = fun i => algebraMap (Om l) P.R.BdR (σ (v i : Om l)) * b := by
  funext i
  simp [PhiS, phiS_tmul]

theorem PhiS_add (x y : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (x + y) = PhiS P σ L a x + PhiS P σ L a y := by
  funext i
  simp [PhiS]

theorem PhiS_zero : PhiS P σ L a 0 = 0 := by
  funext i
  simp [PhiS]

theorem PhiS_sum {ι : Type} (s : Finset ι) (x : ι → (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (∑ i ∈ s, x i) = ∑ i ∈ s, PhiS P σ L a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PhiS_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, PhiS_add, ih]

theorem PhiS_sm (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) r x) = fun i => phiS P σ L r * PhiS P σ L a x i := by
  funext i
  simp only [PhiS]
  rw [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self, map_mul]

theorem PhiS_mulR (b : P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) b x) = fun i => b * PhiS P σ L a x i := by
  rw [← GlobalTheory.DRFil.sm_one_tmul, PhiS_sm, phiS_tmul]
  funext i
  simp

end GlobalTheory.HodgeAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DivLift

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mk_inv_smul_liftQ (L : Lattice (O := O) ρ) (a : O) (ha : algebraMap O LL a ≠ 0)
    (y : ↥L.T) :
    (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y)) : V ⧸ L.T) =
      Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • (y : V)) := by
  obtain ⟨y0, hy0, hs⟩ : ∃ y0 : ↥L.T, (y0 : V) = Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y) ∧
      (Submodule.Quotient.mk y0 : ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) =
        Submodule.Quotient.mk y :=
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk y)).choose_spec⟩
  rw [← hy0]
  have hmem := (Submodule.Quotient.eq _).1 hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  have ht' : a • (t : V) = (y0 : V) - (y : V) := congrArg Subtype.val ht
  rw [Submodule.Quotient.eq, ← smul_sub, ← ht', ← algebraMap_smul LL a, smul_smul,
    inv_mul_cancel₀ ha, one_smul]
  exact t.2

theorem inv_smul_liftQ_mem_Z1D [TopologicalSpace G] (L : Lattice (O := O) ρ) (a : O)
    (ha : algebraMap O LL a ≠ 0) (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T))
    (c : G → ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (hc : c ∈ quotientCocycles L _ hI) :
    (fun g => (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) :
      V ⧸ L.T)) ∈ divisibleCocycles L := by
  refine ⟨hc.1.comp (fun x => (Submodule.Quotient.mk
    ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ x) : V ⧸ L.T)), fun g h => ?_⟩
  have hgh := hc.2 g h
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (c g)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (c h)
  have h1 : c (g * h) = Submodule.Quotient.mk (x + actT L g y) := by
    rw [hgh, ← hx, ← hy]; rfl
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + actD L g (Submodule.Quotient.mk _)
  rw [h1, ← hx, ← hy, mk_inv_smul_liftQ L a ha, mk_inv_smul_liftQ L a ha,
    mk_inv_smul_liftQ L a ha]
  show _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk (ρ g ((algebraMap O LL a)⁻¹ • (y : V)))
  rw [← Submodule.Quotient.mk_add, map_smul, ← smul_add]
  rfl

end Gen

theorem pow_inv_smul_liftQ_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  intro l _ K LL _ _ _ O _ _ _ A' LA' r hI' c'
  have he : algebraMap O LL (((l : ℕ) : O) ^ r) = ((l : ℕ) : LL) ^ r := by
    rw [map_pow, map_natCast]
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have := inv_smul_liftQ_mem_Z1D LA' (((l : ℕ) : O) ^ r) (by rw [he]; exact pow_ne_zero _ hl)
    hI' c'.1 c'.2
  rwa [he] at this

end GlobalTheory.DivLift
end

