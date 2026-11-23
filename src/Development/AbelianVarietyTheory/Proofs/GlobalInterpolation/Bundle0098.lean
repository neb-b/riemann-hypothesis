module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexMulVec
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.IdxDet

open GlobalTheory.LatBasisAt

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (w : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt w a ↔ a ∈ locRing w := by
  rw [mem_locRing]
  constructor
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [← h]; field_simp⟩
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [h]; field_simp⟩

theorem val_le_one (P : HeightOneSpectrum (𝓞 E)) (a : locRing P) : P.valuation E (a : E) ≤ 1 :=
  GlobalTheory.CharValCompare.intAt_iff.1 ((intAt_iff_mem P _).2 a.2)

theorem val_unit (P : HeightOneSpectrum (𝓞 E)) (u : (locRing P)ˣ) :
    P.valuation E ((u : locRing P) : E) = 1 := by
  have h : P.valuation E ((u : locRing P) : E) * P.valuation E (((u⁻¹ : (locRing P)ˣ) : locRing P) : E) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, map_one]
  refine le_antisymm (val_le_one P _) ?_
  rw [← h]
  exact mul_le_of_le_one_right' (val_le_one P _)

theorem val_irreducible (P : HeightOneSpectrum (𝓞 E)) [IsDiscreteValuationRing (locRing P)]
    {p : locRing P} (hp : Irreducible p) : P.valuation E (p : E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ1 : π ∈ locRing P := by
    rw [← intAt_iff_mem, GlobalTheory.CharValCompare.intAt_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hπ0 : (⟨π, hπ1⟩ : locRing P) ≠ 0 := by
    intro h
    have : π = 0 := congrArg Subtype.val h
    rw [this, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hp
  have h1 : π * ((u : locRing P) : E) = (p : E) ^ k := by
    simpa using congrArg Subtype.val hu
  have h2 := congrArg (P.valuation E) h1
  rw [map_mul, val_unit, mul_one, hπ, map_pow] at h2
  have hp0 : P.valuation E (p : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hp.ne_zero (Subtype.ext h)
  have hle := val_le_one P p
  rw [← WithZero.exp_log hp0] at h2 hle ⊢
  generalize WithZero.log (P.valuation E (p : E)) = a at h2 hle ⊢
  rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  congr 1
  have : a ∣ 1 := ⟨-k, by linarith⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one this) with h | h
  · omega
  · exact h

theorem relIndex_mulVec : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (P : HeightOneSpectrum (𝓞 E)) (M : Matrix ι ι E) (L₀ L₁ : AddSubgroup (ι → E)), M.det ≠ 0 → (∀ x, x ∈ L₀ ↔ ∀ i, IntAt P (x i)) → (∀ x, x ∈ L₁ ↔ ∃ y ∈ L₀, x = M.mulVec y) → L₁ ≤ L₀ → ((L₁.relIndex L₀ : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ ordE P M.det := by
  intro E _ _ ι _ _ P M L₀ L₁ hdet h0 h1 hle
  haveI := P.isPrime
  haveI := P.isMaximal
  haveI : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot (locRing P)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (locRing P)
  have hent : ∀ i j, M i j ∈ locRing P := by
    intro i j
    have hs : (Pi.single j 1 : ι → E) ∈ L₀ := by
      rw [h0]
      intro k
      rw [intAt_iff_mem, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have := (h0 _).1 (hle ((h1 _).2 ⟨_, hs, rfl⟩)) i
    rw [intAt_iff_mem] at this
    simpa using this
  let N : Matrix ι ι (locRing P) := Matrix.of fun i j => ⟨_, hent i j⟩
  have hN : N.map (algebraMap (locRing P) E) = M := by
    ext i j; rfl
  have hNd : ((N.det : locRing P) : E) = M.det := by
    rw [← hN]
    exact RingHom.map_det (algebraMap (locRing P) E) N
  have hne : N.det ≠ 0 := by
    intro h
    rw [h] at hNd
    exact hdet hNd.symm
  have hinj : Function.Injective (Matrix.toLin' N) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hv
  obtain ⟨m, ⟨v, hv⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (locRing P) ι) hp _ hinj
  rw [LinearMap.det_toLin'] at hv
  have hord : ordE P M.det = m := by
    have e1 : M.det * ((v : locRing P) : E) = (p : E) ^ m := by
      rw [← hNd]; exact_mod_cast congrArg Subtype.val hv
    have e2 := congrArg (P.valuation E) e1
    rw [map_mul, val_unit, mul_one, map_pow, val_irreducible P hp, ← WithZero.exp_nsmul] at e2
    unfold ordE
    rw [e2, WithZero.log_exp]
    simp
  have hq : Nat.card (locRing P ⧸ Ideal.span {p}) = Ideal.absNorm P.asIdeal := by
    rw [← hp.maximalIdeal_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (locRing P)).toEquiv).symm
  let e : (ι → locRing P) →+ (ι → E) :=
    { toFun := fun x i => (x i : E)
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hei : Function.Injective e := by
    intro x y hxy
    funext i
    exact Subtype.ext (congrFun hxy i)
  have hW0 : L₀ = AddSubgroup.map e ⊤ := by
    ext x
    rw [h0]
    constructor
    · intro hx
      exact ⟨fun i => ⟨_, (intAt_iff_mem P _).1 (hx i)⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩ i
      exact (intAt_iff_mem P _).2 (y i).2
  have hcomm : ∀ y, M.mulVec (e y) = e (Matrix.toLin' N y) := by
    intro y
    funext i
    rw [← hN]
    exact (RingHom.map_mulVec (algebraMap (locRing P) E) N y i).symm
  have hW1 : L₁ = AddSubgroup.map e (LinearMap.range (Matrix.toLin' N)).toAddSubgroup := by
    ext x
    rw [h1, hW0]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, (hcomm y).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, trivial, rfl⟩, (hcomm y).symm⟩
  have : L₁.relIndex L₀ = Ideal.absNorm P.asIdeal ^ m := by
    rw [hW1, hW0, AddSubgroup.relIndex_map_map_of_injective _ _ hei, AddSubgroup.relIndex_top_right, ← hq]
    exact hc
  rw [this, hord, zpow_natCast, Nat.cast_pow]

end GlobalTheory.IdxDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexPerDvd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.IdxBound

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_of_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (M : Submodule (𝓞 E) W) (x : W)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ M := fun s => Iff.rfl
  have hne : I ≠ ⊤ := fun e => hx (by simpa using (hI 1).1 (e ▸ Submodule.mem_top))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := (mem_locP ⟨m, hm.isPrime, hm0⟩ M x).1 (h _)
  exact hs (hle ((hI s).2 hsx))

theorem mem_localization_of_smul_mem {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W)
    {x : W} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (h : s • x ∈ localization₂ P.asIdeal M) : x ∈ localization₂ P.asIdeal M := by
  obtain ⟨t, ht, htx⟩ := (mem_locP P M _).1 h
  refine (mem_locP P M _).2 ⟨t * s, fun h' => (P.isPrime.mem_or_mem h').elim ht hs, ?_⟩
  rwa [mul_smul]

theorem per_apply_mem {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {y : HomE E a b} (hy : y ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ P.asIdeal N) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s', hs', hv'⟩ := (mem_locP P N v).1 hv
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    obtain ⟨s, hs, hr'⟩ := (mem_locP P _ r).1 (hA ▸ le_locP P AA hr)
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hr'
    refine mem_localization_of_smul_mem P _ hs (mem_localization_of_smul_mem P _ hs' (le_locP P _ ?_))
    have h1 : x (s' • v) ∈ N' := hx _ hv'
    have h2 : s' • s • (r • x) v = t • x (s' • v) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, ← smul_assoc s r, ← ht, algebraMap_smul, smul_comm]
    rw [h2]
    exact N'.smul_mem t h1
  | zero => simp
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | smul r z _ hz => simpa using Submodule.smul_mem _ r hz

theorem mem_localization_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hN : N.FG)
    {y : HomE E a b} (hy : ∀ v ∈ N, y v ∈ localization₂ P.asIdeal N') : y ∈ localization₂ P.asIdeal (perO AA N N') := by
  classical
  obtain ⟨S, rfl⟩ := hN
  choose! s hs hsy using fun v (hv : v ∈ S) => (mem_locP P N' _).1 (hy v (Submodule.subset_span hv))
  have hP : ∏ v ∈ S, s v ∉ P.asIdeal := fun h => by
    obtain ⟨v, hv, h'⟩ := (P.isPrime.prod_mem_iff).1 h
    exact hs v hv h'
  have hh : (∏ v ∈ S, s v) • y ∈ homO (Submodule.span (𝓞 E) (S : Set (Sp E a))) N' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rw [← Finset.prod_erase_mul S s hv, LinearMap.smul_apply, mul_smul]
      exact N'.smul_mem _ (hsy v hv)
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul r v _ hv => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem r hv
  obtain ⟨t, ht, h1⟩ := (mem_locP P AA 1).1 (hA ▸ le_locP P _ (Submodule.one_le.1 le_rfl))
  refine mem_localization_of_smul_mem P _ hP (mem_localization_of_smul_mem P _ ht (le_locP P _ (Submodule.subset_span ⟨_, h1, _, hh, ?_⟩)))
  rw [smul_assoc t (1 : E), one_smul]

theorem smul_mem_per {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' N'' : Submodule (𝓞 E) (Sp E b)}
    {w : 𝓞 E} (h : ∀ y ∈ N', (w : E) • y ∈ N'') {y : HomE E a b} (hy : y ∈ perO AA N N') : w • y ∈ perO AA N N'' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, hr, w • x, fun v hv => h _ (hx v hv), (smul_comm _ _ _).symm⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz

theorem apply_mem_of_std {N' : Submodule (𝓞 E) (Sp E b)} {P : HeightOneSpectrum (𝓞 E)} {y : HomE E a b}
    (hy : ∀ i, y (Pi.single i 1) ∈ localization₂ P.asIdeal N') {v : Sp E a} (hv : v ∈ stdAt E a P) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s, hs, hsv⟩ := (mem_locP P _ v).1 hv
  choose t ht using fun i => Submodule.mem_one.1 (Submodule.mem_pi.1 hsv i (Set.mem_univ _))
  refine mem_localization_of_smul_mem P _ hs ?_
  have e : s • v = ∑ i, t i • (Pi.single i 1 : Sp E a) := by
    ext j
    rw [← ht j]
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LinearMap.map_smul_of_tower, e, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ (hy i)

theorem relIndex_per_dvd : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → A.AAUnit (divs ϖ) → ϖ ≠ 0 → (∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p) → IsSdLat N → IsSdLat N'' → (∀ P ∈ divs ϖ, localization₂ P.asIdeal N = stdAt X.E a P) → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → (per A N N'').toAddSubgroup.relIndex (per A N d.1.N).toAddSubgroup ∣ p ^ ((divs ϖ).card * a) := by
  intro X A a b SG ϖ p N d N'' _ _ hU h0 hp hN _ hstd ⟨h1, _, h3⟩
  have he : ∀ (P : ↥(divs ϖ)) (i : Fin a), (Pi.single i 1 : Sp X.E a) ∈ localization₂ P.1.asIdeal N := fun P i => by
    rw [hstd P.1 P.2]
    exact le_locP P.1 _ (by simpa using single_mem_stdLat (E := X.E) i 1)
  have hm : ∀ (x : (per A N d.1.N).toAddSubgroup) (P : ↥(divs ϖ)) (i : Fin a), x.1 (Pi.single i 1) ∈ d.1.at P.1 :=
    fun x P i => per_apply_mem (hU P.1 P.2) x.2 (he P i)
  let φ : (per A N d.1.N).toAddSubgroup →+ ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) :=
    AddMonoidHom.mk' (fun x P i => d.1.f P (x.1 (Pi.single i 1))) fun x y => by
      funext P i
      exact d.2.f_add P _ (hm x P i) _ (hm y P i)
  have hker : φ.ker ≤ (per A N N'').toAddSubgroup.addSubgroupOf (per A N d.1.N).toAddSubgroup := by
    intro x hx
    refine mem_of_locP (per A N N'') x.1 fun Q => ?_
    by_cases hQ : Q ∈ divs ϖ
    · refine mem_localization_perO (hU Q hQ) hN.1.fg fun v hv => apply_mem_of_std (fun i => ?_) (hstd Q hQ ▸ le_locP Q N hv)
      exact (h3 ⟨Q, hQ⟩ _).2 ⟨hm x ⟨Q, hQ⟩ i, congrFun (congrFun hx ⟨Q, hQ⟩) i⟩
    · exact mem_localization_of_smul_mem Q _ (fun h => hQ ((mem_divs h0 Q).2 h)) (le_locP Q _ (smul_mem_per h1 x.2))
  have hc : Nat.card ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ ((divs ϖ).card * a) := by
    have : ∀ P : ↥(divs ϖ), Nat.card (Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ a := fun P => by
      rw [Nat.card_fun, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hp P.1 P.2]
      simp
    rw [Nat.card_pi, Finset.prod_congr rfl fun P _ => this P]
    simp [← pow_mul, mul_comm]
  refine (AddSubgroup.index_dvd_of_le hker).trans ?_
  rw [AddSubgroup.index_ker, ← hc]
  exact AddSubgroup.card_addSubgroup_dvd_card _

end GlobalTheory.MomT.IdxBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RingHomEqOfComapEqUnramifiedDegreeOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem ringHom_eq_of_comap_eq_unramified_degree_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (φ ψ : E →+* K)
    (w : HeightOneSpectrum (𝓞 K)) (Q : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hN : Ideal.absNorm Q.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2)
    (hφ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal)
    (hψ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom ψ r ∈ w.asIdeal) :
    φ = ψ := by
  set f := RingOfIntegers.mapRingHom φ with hf
  set g := RingOfIntegers.mapRingHom ψ with hg
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal := hN ▸ Ideal.absNorm_mem Q.asIdeal
  have hQp := Q.isPrime

  have h1 : ∀ x : 𝓞 E, ∃ a : ℤ, x - (a : 𝓞 E) ∈ Q.asIdeal := by
    intro x
    haveI : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := mem_zmultiples_of_prime_card (g := (1 : 𝓞 E ⧸ Q.asIdeal))
      (g' := Ideal.Quotient.mk Q.asIdeal x) hc one_ne_zero
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    refine ⟨a, Ideal.Quotient.eq.1 ?_⟩
    rw [← ha, map_intCast, zsmul_one]
  have h2 : Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 = Q.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q.asIdeal) (i := 1)
      (I := Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2) Q.ne_bot ?_ ?_
    · simpa using h
    · refine lt_of_le_of_ne le_sup_right fun h => hsq ?_
      have h' : ((p : ℕ) : 𝓞 E) ∈ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 :=
        Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      rw [← h] at h'
      exact h'
    · rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hpQ) (Ideal.pow_le_self two_ne_zero)
  have h3 : ∀ n : ℕ, Q.asIdeal ≤ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rcases n with _ | n
      · simp
      refine h2.ge.trans (sup_le le_sup_left ?_)
      rw [sq]
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.mul_sup, ← pow_succ']
      exact sup_le_sup_right Ideal.mul_le_right _
  have hmap : ∀ (k : 𝓞 E →+* 𝓞 K), (∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ k r ∈ w.asIdeal) →
      ∀ (n : ℕ) (z : 𝓞 E), z ∈ Q.asIdeal ^ n → k z ∈ w.asIdeal ^ n := by
    intro k hk n z hz
    have h := Ideal.mem_map_of_mem k hz
    rw [Ideal.map_pow] at h
    refine Ideal.pow_right_mono ?_ n h
    exact Ideal.map_le_iff_le_comap.2 fun r hr => (hk r).1 hr
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    simpa using (hφ _).1 hpQ
  have h4 : ∀ (n : ℕ) (x : 𝓞 E), f x - g x ∈ w.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := h1 x
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h3 (n + 1) ha)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have hx : x = c * p + z + a := by rw [hyz]; ring
      have he : f x - g x = (f c - g c) * p + (f z - g z) := by
        rw [hx]; simp only [map_add (f := _), map_mul, map_natCast, map_intCast]; ring
      rw [he]
      refine add_mem ?_ (sub_mem (hmap f hφ _ _ hz) (hmap g hψ _ _ hz))
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih c) hpw
  have h5 : ∀ x : 𝓞 E, f x = g x := by
    intro x
    have hb := Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top
    have : f x - g x ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← hb]; exact Ideal.mem_iInf.2 fun n => h4 n x
    exact sub_eq_zero.1 (Ideal.mem_bot.1 this)
  refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
  exact congrArg (algebraMap (𝓞 K) K) (h5 x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubAddLeSpread
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT

theorem sub_add_le_spread {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    lam.w a - lam.w b + (N : ℤ) ≤ lam.spread := by
  have hN : 0 < N := a.pos
  have h1 : lam.w a ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.2 (Nat.zero_le _))
  have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b := lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  linarith

theorem alcoveAt_of_ok : ∀ (Z : Dat), Z.Ok → ∀ (u : Z.Pr.Word) (j : ℕ), j ≤ Z.R.m → AlcoveAt Z.W u j := by
  intro Z hZ u j hj τ a b
  have h1 := hZ.sizes.two_spread_lt u j hj τ
  have h2 := sub_add_le_spread (Z.W.lamTrue u j τ) a b
  linarith

end GlobalTheory.KerT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnderEqIffMapLe
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem under_eq_iff_map_le (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro rfl
    exact le_rfl
  · intro h
    apply HeightOneSpectrum.ext
    exact (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top h).symm

theorem under_eq_iff (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ (Q = P ∨ Q = P') := by
  rw [under_eq_iff_map_le, h, Q.isPrime.mul_le]
  refine or_congr ⟨fun h => ?_, fun h => h ▸ le_rfl⟩ ⟨fun h => ?_, fun h => h ▸ le_rfl⟩
  · exact HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
  · exact HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h).symm

theorem not_mul_le_sq (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P') :
    ¬ P.asIdeal * P'.asIdeal ≤ P.asIdeal ^ 2 := by
  intro h
  rw [← Ideal.dvd_iff_le, sq, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at h
  exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h).symm)

theorem val_eq_inv_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)),
    χ.TrivOn F → χ.UnrAt P → χ.UnrAt P' → P ≠ P' →
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal → χ.val P' = (χ.val P)⁻¹ := by
  intro F E _ _ _ _ _ χ v P P' hχ h1 h2 hne hv
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hab : aboveF (L := E) F v = {P, P'} := by
    ext Q
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff v P P' hv Q
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → χ.UnrAt Q →
      ¬ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal ^ 2 →
      χ.locK Q (upF F (Units.mk0 π h0)) = χ.val Q := by
    intro Q hQ hunr hu
    refine χ.val_eq hunr _ ?_
    subst hQ
    show Valued.v ((algebraMap F E π : E) : Q.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.MuConj.valuation_up Q hu, hπ]
  have h := hχ.1 v (Units.mk0 π h0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hne,
    key P ((under_eq_iff v P P' hv _).2 (Or.inl rfl)) h1 (hv ▸ not_mul_le_sq P P' hne),
    key P' ((under_eq_iff v P P' hv _).2 (Or.inr rfl)) h2
      (by rw [hv, mul_comm]; exact not_mul_le_sq P' P hne.symm)] at h
  exact eq_inv_of_mul_eq_one_right h

end GlobalTheory.HeckeSplit
end

