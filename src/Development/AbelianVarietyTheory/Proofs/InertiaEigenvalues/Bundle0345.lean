module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0001
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import GroundTheory.LocalFields.KroneckerWeber
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrth

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem stable_span_smul_top (L : Lattice (O := O) ρ) (a : O) :
    StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [mem_span_smul_top] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨actT L g y, map_smul _ _ _⟩

theorem factor_actQ (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T} (hI : StableSub L I)
    (hJ : StableSub L J) (hIJ : I ≤ J) (g : G) (x : ↥L.T ⧸ I) :
    Submodule.factor hIJ (actQ L I hI g x) = actQ L J hJ g (Submodule.factor hIJ x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
  rfl

theorem factor_mem_Z1Q [TopologicalSpace G] (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T}
    (hI : StableSub L I) (hJ : StableSub L J) (hIJ : I ≤ J) {z : G → ↥L.T ⧸ I}
    (hz : z ∈ quotientCocycles L I hI) : (fun g => Submodule.factor hIJ (z g)) ∈ quotientCocycles L J hJ := by
  refine ⟨hz.1.comp _, fun g h => ?_⟩
  simp only [hz.2 g h, map_add (f := _), factor_actQ L hI hJ hIJ]

end Gen

theorem mem_BD_of_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ BD LA' := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm c hc horth
  obtain ⟨hDom, hDVR, hFrac⟩ := hO.1
  haveI := hDom; haveI := hDVR; haveI := hFrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set π := algebraMap O LL ϖ with hπdef
  have hπ : π ≠ 0 := by
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  by_contra hcB
  obtain ⟨r, hr⟩ := GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem l K LL O hO A' LA' ϖ hϖ c hc
  let I : ℕ → Submodule O ↥LA.T := fun k => Ideal.span {ϖ ^ (r + k)} • ⊤
  have hI : ∀ k, StableSub LA (I k) := fun k => stable_span_smul_top LA _
  let Φ : ∀ k, (↥(GK K) → ↥LA.T ⧸ I k) → ↥(GK K) × ↥(GK K) → LL := fun k z x =>
    m (Formalism.MainNotions.LocalSituation.liftQ LA (I k) (z x.1)) (A'.ρ x.1 (liftD LA' (c x.2)))
  let Y : ∀ k, Set (↥(GK K) → ↥LA.T ⧸ I k) := fun k =>
    {z | z ∈ quotientCocycles LA (I k) (hI k) ∧ ¬ CobO (P.PD K) L1 (Φ k z)}
  have hle : ∀ k, I (k + 1) ≤ I k := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hle0 : ∀ k, I k ≤ I 0 := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  let f : ∀ k, (↥(GK K) → ↥LA.T ⧸ I (k + 1)) → (↥(GK K) → ↥LA.T ⧸ I k) := fun k z g =>
    Submodule.factor (hle k) (z g)

  have hmemPow : ∀ (j : ℕ) (x : ↥LA.T), x ∈ (Ideal.span {ϖ ^ j} • ⊤ : Submodule O ↥LA.T) →
      ∃ t ∈ LA.T, (x : A.V) = π ^ j • t := by
    intro j x hx
    obtain ⟨y, rfl⟩ := (mem_span_smul_top LA _ x).1 hx
    exact ⟨y, y.2, by rw [Submodule.coe_smul, hπdef, ← map_pow, algebraMap_smul]⟩
  have hliftMem : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), Formalism.MainNotions.LocalSituation.liftQ LA J x ∈ LA.T :=
    fun J x => (Submodule.Quotient.mk_surjective J x).choose.2
  have hspec : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), ∃ y : ↥LA.T,
      (y : A.V) = Formalism.MainNotions.LocalSituation.liftQ LA J x ∧ Submodule.Quotient.mk y = x := fun J x =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective J x).choose_spec⟩
  have hlift2 : ∀ k (x : ↥LA.T ⧸ I k) (y : ↥LA.T), x = Submodule.Quotient.mk y →
      ∃ t ∈ LA.T, Formalism.MainNotions.LocalSituation.liftQ LA (I k) x - (y : A.V) = π ^ (r + k) • t := by
    intro k x y hxy
    obtain ⟨y0, hy0, hmk0⟩ := hspec (I k) x
    have hmem : y0 - y ∈ I k := (Submodule.Quotient.eq _).1 (hmk0.trans hxy)
    obtain ⟨t, ht, he⟩ := hmemPow (r + k) _ hmem
    exact ⟨t, ht, by rw [← hy0, ← he, Submodule.coe_sub]⟩
  have hcong : ∀ (k : ℕ) (a b : A.V) (y : A'.V) (t : A.V), t ∈ LA.T → a - b = π ^ k • t →
      π ^ k • y ∈ LA'.T → m a y - m b y ∈ Set.range (algebraMap O LL) := by
    intro k a b y t ht hab hy
    obtain ⟨e, he⟩ := (hm.2 _).1 hy t ht
    have : m a y - m b y = m t (π ^ k • y) := by
      rw [← LinearMap.sub_apply, ← map_sub, hab, LinearMap.map_smul₂, (m t).map_smul]
    exact ⟨e, by rw [this, he]⟩
  have hcobO : ∀ z z' : ↥(GK K) × ↥(GK K) → LL, (∀ x, z x - z' x ∈ Set.range (algebraMap O LL)) →
      (CobO (P.PD K) L1 z → CobO (P.PD K) L1 z') := by
    intro z z' hzz hz
    have : (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
        fun x => Submodule.Quotient.mk (z' x) := by
      funext x
      rw [Submodule.Quotient.eq, hL1]
      obtain ⟨e, he⟩ := hzz x
      exact ⟨e, he⟩
    unfold CobO at hz ⊢
    rwa [← this]
  have hT'pow : ∀ (k : ℕ) (g h : ↥(GK K)), π ^ (r + k) • A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
    intro k g h
    rw [← map_smul, add_comm, pow_add, mul_smul]
    apply LA'.stable
    rw [hπdef, ← map_pow, algebraMap_smul]
    exact LA'.T.smul_mem _ (hr h)

  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow hT l K LL O hO A LA ϖ hϖ (r + k) (hI k)).subset (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := by
    intro k
    have hI' : StableSub LA' (Ideal.span {ϖ ^ (r + k)} • ⊤ : Submodule O ↥LA'.T) :=
      stable_span_smul_top LA' _
    obtain ⟨c', hc'Z, hc'B, hc'l⟩ :=
      GlobalTheory.T.exists_torsionCocycle_finite_level_lift l K LL O hO A' LA' ϖ hϖ c hc hcB r hr (r + k) (by omega) hI'
    have h2 := (GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate hT l P K LL O hO L1 hL1 A A' LA LA' m hm ϖ hϖ (r + k) (hI k) hI').2 c' hc'Z
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hc'B
    apply h2
    intro z hz
    have hzY : z ∉ Y k := by rw [hemp]; exact fun h => h
    have hC : CobO (P.PD K) L1 (Φ k z) := by
      by_contra hn; exact hzY ⟨hz, hn⟩
    refine hcobO _ _ ?_ hC
    intro x
    obtain ⟨t, ht, hteq⟩ := hc'l x.2
    obtain ⟨e, he⟩ := (hm.2 _).1 (LA'.stable x.1 t ht) _ (hliftMem (I k) (z x.1))
    refine ⟨-e, ?_⟩
    rw [map_neg, ← he]
    simp only [Φ, hteq, map_add (f := _), map_smul, smul_eq_mul, ← hπdef]
    rw [inv_pow]
    field_simp
    ring
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_Z1Q LA (hI (k + 1)) (hI k) (hle k) hz, fun hc' => hnc (hcobO _ _ ?_ hc')⟩
    intro x
    obtain ⟨t, ht, hteq⟩ := hlift2 k (f k z x.1) ⟨_, hliftMem (I (k + 1)) (z x.1)⟩ (by
      obtain ⟨y0, hy0, hmk0⟩ := hspec (I (k + 1)) (z x.1)
      have hy : (⟨_, hliftMem (I (k + 1)) (z x.1)⟩ : ↥LA.T) = y0 := Subtype.ext hy0.symm
      rw [hy]
      show Submodule.factor (hle k) (z x.1) = _
      rw [← hmk0]
      rfl)
    exact hcong (r + k) _ _ _ t ht hteq (hT'pow k x.1 x.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' (fun k => ↥(GK K) → ↥LA.T ⧸ I k) f Y hfin hne hmap
  let w : ℕ → ↥(GK K) → ↥LA.T := fun k g => (Submodule.Quotient.mk_surjective (I k) (s k g)).choose
  have hwk : ∀ k g, (Submodule.Quotient.mk (w k g) : ↥LA.T ⧸ I k) = s k g := fun k g =>
    (Submodule.Quotient.mk_surjective (I k) (s k g)).choose_spec
  have hI'I : ∀ k, I k ≤ (Ideal.span {ϖ ^ k} • ⊤ : Submodule O ↥LA.T) := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hI' : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun n =>
    stable_span_smul_top LA _
  have hwZ : ∀ n, (fun g => (Submodule.Quotient.mk (w n g) :
      ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI' n) := by
    intro n
    have := factor_mem_Z1Q LA (hI n) (hI' n) (hI'I n) (hs n).1.1
    convert this using 1
    funext g
    rw [← hwk n g]
    rfl
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ I k := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    rw [hwk k g, ← (hs k).2]
    show _ = Submodule.factor (hle k) (s (k + 1) g)
    rw [← hwk (k + 1) g]
    rfl
  obtain ⟨d, hdZ, hd⟩ := GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow l K LL O hO A LA ϖ hϖ hI' w hwZ (fun n g => hI'I n (hstep n g))
  have htele : ∀ n g, w n g - w 0 g ∈ I 0 := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      have := (I 0).add_mem (hle0 n (hstep n g)) ih
      rwa [sub_add_sub_cancel] at this
  apply (hs 0).1.2
  refine hcobO _ _ ?_ (horth d hdZ)
  intro x
  obtain ⟨t1, ht1, hdt⟩ := hd r x.1
  have he : t1 + (w r x.1 - w 0 x.1) ∈ I 0 := (I 0).add_mem ht1 (htele r x.1)
  obtain ⟨u, hu, hue⟩ := hmemPow (r + 0) _ he
  obtain ⟨t3, ht3, ht3e⟩ := hlift2 0 (s 0 x.1) (w 0 x.1) (hwk 0 x.1).symm
  refine hcong (r + 0) _ _ _ (u - t3) (LA.T.sub_mem hu ht3) ?_ (hT'pow 0 x.1 x.2)
  rw [smul_sub, ← hue, ← ht3e, hdt]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

end GlobalTheory.TateOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.FiniteTwistInvariants

variable {O : Type} [CommRing O] [IsDomain O]

theorem length_quot_ne_top [IsDiscreteValuationRing O] (a : O) (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  exact ENat.coe_ne_top n

theorem fix_frac_zero {Γ : Type} {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) O)
    (hker : ∀ v : Fin r → O, (∀ g, (M g).mulVec v = v) → v = 0)
    (x : Fin r → FractionRing O) (hx : ∀ g, ((M g).map (algebraMap O (FractionRing O))).mulVec x = x) :
    x = 0 := by
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose u hu using hbi
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hu' : (fun j => algebraMap O (FractionRing O) (u j)) = algebraMap O (FractionRing O) b • x := by
    funext j; rw [hu j]; simp [Algebra.smul_def]
  have h0 : u = 0 := by
    refine hker u fun g => ?_
    funext j
    apply hinj
    rw [RingHom.map_mulVec]
    show ((M g).map (algebraMap O (FractionRing O))).mulVec (fun j => algebraMap O (FractionRing O) (u j)) j = _
    rw [hu', Matrix.mulVec_smul, hx g]
    exact (congrFun hu' j).symm
  have hb0 : algebraMap O (FractionRing O) b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O (FractionRing O))]
    exact fun h => nonZeroDivisors.ne_zero hb (hinj h)
  have : algebraMap O (FractionRing O) b • x = 0 := by
    rw [← hu', h0]; funext j; simp
  exact (smul_eq_zero.mp this).resolve_left hb0

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

theorem exists_finset_ker {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Γ → V →ₗ[K] V) (h : ∀ x, (∀ g, f g x = 0) → x = 0) :
    ∃ s : Finset Γ, ∀ x, (∀ g ∈ s, f g x = 0) → x = 0 := by
  classical
  let S : Set (Submodule K V) := Set.range fun s : Finset Γ => ⨅ g ∈ s, LinearMap.ker (f g)
  obtain ⟨p, ⟨s, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min S ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨s, fun x hx => h x fun g => ?_⟩
  have hle : (⨅ g' ∈ insert g s, LinearMap.ker (f g')) ≤ ⨅ g' ∈ s, LinearMap.ker (f g') := by
    rw [Finset.iInf_insert]; exact inf_le_right
  have heq : (⨅ g' ∈ insert g s, LinearMap.ker (f g')) = ⨅ g' ∈ s, LinearMap.ker (f g') := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hxs : x ∈ ⨅ g' ∈ s, LinearMap.ker (f g') := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]; exact hx
  rw [← heq] at hxs
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hxs
  exact hxs g (Finset.mem_insert_self g s)

variable {O : Type} [CommRing O] [IsDomain O]

theorem exists_killer {ι : Type} [Fintype ι] {r : ℕ} (A : ι → Matrix (Fin r) (Fin r) O)
    (h : ∀ x : Fin r → FractionRing O, (∀ q, ((A q).map (algebraMap O (FractionRing O))).mulVec x = 0) → x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ x : Fin r → FractionRing O,
      (∀ q, ((A q).map (algebraMap O (FractionRing O))).mulVec x ∈ stdG O (FractionRing O) r) →
        c • x ∈ stdG O (FractionRing O) r := by
  classical
  set K := FractionRing O
  have hinj := IsFractionRing.injective O K
  let B : Matrix (ι × Fin r) (Fin r) K := fun p j => algebraMap O K (A p.1 p.2 j)
  have hB : ∀ x p, (B.mulVec x) p = (((A p.1).map (algebraMap O K)).mulVec x) p.2 := fun _ _ => rfl
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    refine h x fun q => ?_
    funext i
    rw [← hB x (q, i), hx]; rfl
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set P' := LinearMap.toMatrix' P
  have hPB : P' * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hP, LinearMap.toMatrix'_id]
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin r × (ι × Fin r) => P' p.1 p.2)
  choose Q hQ using hbi
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩
  choose y hy using hx
  let Y : ι × Fin r → O := fun p => y p.1 p.2
  have hY : (fun p => algebraMap O K (Y p)) = B.mulVec x := by
    funext p
    rw [hB]
    exact congrFun (hy p.1) p.2
  refine ⟨(Matrix.of fun j p => Q (j, p)).mulVec Y, ?_⟩
  funext j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
  rw [RingHom.map_mulVec]
  have hQ' : (Matrix.of fun j p => Q (j, p)).map (algebraMap O K) = algebraMap O K b • P' := by
    ext j p
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hQ (j, p), Algebra.smul_def]
  have hYf : (⇑(algebraMap O K) ∘ Y) = B.mulVec x := hY
  rw [hQ', hYf, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec, Pi.smul_apply,
    Pi.smul_apply, algebraMap_smul]

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

variable {O : Type} [CommRing O] [IsDomain O]

theorem stdG_eq_span (r : ℕ) :
    stdG O (FractionRing O) r = Submodule.span O (Set.range fun j : Fin r => (Pi.single j 1 : Fin r → FractionRing O)) := by
  ext x
  rw [Submodule.mem_span_range_iff_exists_fun]
  show x ∈ LinearMap.range _ ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, funext fun k => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨u, rfl⟩
    refine ⟨u, funext fun k => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem WKG_mk {Γ : Type} [Group Γ] {r : ℕ} (M : Γ →* Matrix (Fin r) (Fin r) O) (g : Γ) (x : Fin r → FractionRing O) :
    WKG M g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((M g).map (algebraMap O (FractionRing O))).mulVec x) := rfl

theorem length_invariants_lt_top [IsDiscreteValuationRing O] {Γ Γ' : Type} [Group Γ] [Group Γ'] {r : ℕ}
    (M : Γ →* Matrix (Fin r) (Fin r) O) (f : Γ' →* Γ)
    (hker : ∀ v : Fin r → O, (∀ g, (M (f g)).mulVec v = v) → v = 0) :
    Module.length O ↥(Representation.invariants ((WKG M).comp f)) < ⊤ := by
  classical
  set K := FractionRing O
  let A : Γ' → Matrix (Fin r) (Fin r) O := fun g => M (f g) - 1
  have hAm : ∀ g, (A g).map (algebraMap O K) = (M (f g)).map (algebraMap O K) - 1 := by
    intro g
    show (algebraMap O K).mapMatrix (M (f g) - 1) = _
    rw [map_sub, map_one]; rfl
  have hK : ∀ x : Fin r → K, (∀ g, ((A g).map (algebraMap O K)).mulVec x = 0) → x = 0 := by
    intro x hx
    refine fix_frac_zero (fun g => M (f g)) hker x fun g => ?_
    have := hx g
    rwa [hAm, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  obtain ⟨s, hs⟩ := exists_finset_ker (fun g => Matrix.toLin' ((A g).map (algebraMap O K)))
    (fun x hx => hK x fun g => by simpa [Matrix.toLin'_apply] using hx g)
  obtain ⟨c, hc0, hc⟩ := exists_killer (fun q : s => A q.1)
    (fun x hx => hs x fun g hg => by simpa [Matrix.toLin'_apply] using hx ⟨g, hg⟩)
  have hinj := IsFractionRing.injective O K
  have ha : algebraMap O K c ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O K)]
    exact fun h => hc0 (hinj h)
  have hW : ∀ x ∈ Representation.invariants ((WKG M).comp f), c ^ 1 • x = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine hc x fun q => ?_
    have h1 := hx q.1
    rw [MonoidHom.comp_apply, WKG_mk, Submodule.Quotient.eq] at h1
    show ((A q.1).map (algebraMap O K)).mulVec x ∈ _
    rwa [hAm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hle := length_le_of_killed (LL := K) (stdG O K r) _ (stdG_eq_span r) c ha 1 _ hW
  have hL := length_quot_ne_top c hc0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hL
  refine lt_of_le_of_lt hle ?_
  rw [← hm]
  norm_cast
  exact ENat.coe_lt_top _

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG2 i r ρ π → ∀ w ∈ placesOver D.host.E (D.nd.l i), Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))) < ⊤ := by
  intro D i r ρ π hG2 w hw
  have hH0 := (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.2.2.2.2.1
  show Module.length _ ↥(Representation.invariants ((WKG (WpO D.nd i ρ π)).comp (decS D.nd w))) < ⊤
  refine length_invariants_lt_top (WpO D.nd i ρ π) (decS D.nd w) fun v hv => ?_
  set C := TruncatedSeriesCountingIdentities.CoefExt.self i w hw
  set Bw := D.nbr i w hw
  let φ : D.nd.O i →+* ↥C.LL.1 :=
    (TruncatedSeriesCountingIdentities.CoefExt.inc C).comp ((algebraMap (Br.Ow Bw) (Br.LLw Bw)).comp Bw.eO.toRingHom)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := (TruncatedSeriesCountingIdentities.CoefExt.inc C).injective hab
    exact Br.toLL_inj Bw h1
  have hloc : ∀ gK, TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) gK = (WpO D.nd i ρ π (decS D.nd w (Br.ι Bw gK))).map φ := fun _ => rfl
  have hmem : (fun j => φ (v j)) ∈ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) := by
    simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    intro gK
    rw [sub_eq_zero]
    show Matrix.toLinAlgEquiv' _ _ = _
    rw [Matrix.toLinAlgEquiv'_apply, hloc]
    funext j
    rw [show (fun j => φ (v j)) = ⇑φ ∘ v from rfl, ← RingHom.map_mulVec, hv]
  rw [hH0, Submodule.mem_bot] at hmem
  funext j
  exact hφ (by simpa using congrFun hmem j)

end GlobalTheory.FiniteTwistInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrdIsEqCardInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := _root_.GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEqStatement
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ = zIdem τ' → RepIso τ.ρ τ'.ρ := by
  first | exact @GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | exact GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | (intros; apply GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple <;> assumption)
end

