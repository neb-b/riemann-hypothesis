module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0027

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLat
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT

theorem inj_mod_of_surj_mod {M : Type} [AddCommGroup M] [Module.Finite ℤ M] (f : M →ₗ[ℤ] M) (q : ℕ)
    (hs : ∀ a, ∃ z b, a = f z + q • b) (z b : M) (h : f z = q • b) : ∃ z', z = q • z' := by
  let K : Submodule ℤ M := LinearMap.range (q • (LinearMap.id : M →ₗ[ℤ] M))
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = q • b := fun a =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hle : K ≤ K.comap f := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hK a).1 ha
    exact (hK _).2 ⟨f b, map_nsmul f q b⟩
  let g := K.mapQ K f hle
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := K.mkQ_surjective a
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨K.mkQ z, ?_⟩
    show K.mkQ (f z) = _
    rw [map_add (f := _), show K.mkQ (q • b) = 0 from (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, rfl⟩), add_zero]
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hg
  have h0 : g (K.mkQ z) = g 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, h⟩)
  exact (hK z).1 ((Submodule.Quotient.mk_eq_zero K).1 (hi h0))

theorem surj_mod_pow {M L : Type} [AddCommGroup M] [AddCommGroup L] (σ : M →+ L) (p : ℕ)
    (h : ∀ a, ∃ z b, a = σ z + p • b) (n : ℕ) (a : L) : ∃ z b, a = σ z + (p ^ n) • b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨z, b, rfl⟩ := ih
    obtain ⟨z', b', rfl⟩ := h b
    exact ⟨z + (p ^ n) • z', b', by rw [map_add (f := _), map_nsmul, smul_add, pow_succ, mul_smul, add_assoc]⟩

theorem perfect_mod {M L : Type} [AddCommGroup M] [AddCommGroup L] [Module.Free ℤ L] (σ : M →ₗ[ℤ] L) (q : ℕ)
    (EF : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hE : Function.Bijective EF) (hs : ∀ a, ∃ z b, a = σ z + q • b)
    (hk : ∀ z b, σ z = q • b → ∃ z', z = q • z') :
    (∀ φ : M →+ ZMod q, ∃ y, ∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = φ z) ∧
      ∀ y, (∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = 0) → ∃ y', y = q • y' := by
  let B := Module.Free.chooseBasis ℤ L
  constructor
  · intro φ
    choose zz cc hzc using hs
    let s : L →ₗ[ℤ] M := B.constr ℤ fun i => zz (B i)
    let t : L →ₗ[ℤ] L := B.constr ℤ fun i => cc (B i)
    have hst : ∀ a, a = σ (s a) + q • t a := by
      have : (LinearMap.id : L →ₗ[ℤ] L) = σ ∘ₗ s + q • t := B.ext fun i => by
        simpa [s, t] using hzc (B i)
      intro a
      simpa using LinearMap.congr_fun this a
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => ((φ (zz (B i))).cast : ℤ)
    have hψ : ∀ a, ((ψ a : ℤ) : ZMod q) = φ (s a) := by
      have : (Int.castAddHom (ZMod q)).toIntLinearMap ∘ₗ ψ = φ.toIntLinearMap ∘ₗ s := B.ext fun i => by
        simp [ψ, s]
      intro a
      simpa using LinearMap.congr_fun this a
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine ⟨zz a₀, fun z => ?_⟩
    obtain ⟨z', hz'⟩ := hk (z - s (σ z)) (t (σ z)) (by
      rw [map_sub, sub_eq_iff_eq_add']
      exact hst (σ z))
    have h1 : φ z = φ (s (σ z)) := by
      rw [sub_eq_iff_eq_add.1 hz', map_add (f := _), map_nsmul]
      simp [← sub_eq_iff_eq_add.1 hz']
    have h2 : σ (zz a₀) = a₀ - q • cc a₀ := eq_sub_iff_add_eq.2 (hzc a₀).symm
    rw [h1, ← hψ, ← ha₀, h2]
    simp
  · intro y hy
    have hd : ∀ a, (q : ℤ) ∣ EF (σ y) a := by
      intro a
      obtain ⟨z, b, rfl⟩ := hs a
      rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
      exact dvd_add ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hy z)) (dvd_mul_right _ _)
    choose d hd using hd
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => d (B i)
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine hk y a₀ (hE.1 (B.ext fun i => ?_))
    rw [map_nsmul, ha₀, hd]
    simp [ψ]

theorem exists_levPairing {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La)
    (hu : IsPolLattice c p EF u) :
    ∃ (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n)
      (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)),
      (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) ∧
      (∀ z z', e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) ∧
      (∀ a : La, ∃ (z : Fin N → 𝓞 E) (b : La), a = ∑ k, z k • u k + (p ^ n) • b) ∧
      Function.Surjective π ∧
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') ∧
      (∀ y, e y y = 0) ∧
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) ∧
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) ∧
      (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') := by
  have := hu.free
  have := hu.finite
  let σ₀ : (Fin N → 𝓞 E) →ₗ[𝓞 E] La := Fintype.linearCombination (𝓞 E) u
  let σ : (Fin N → 𝓞 E) →ₗ[ℤ] La := σ₀.toAddMonoidHom.toIntLinearMap
  have hσ : ∀ z, σ z = ∑ k, z k • u k := fun z => Fintype.linearCombination_apply _ _ _
  have hσa : ∀ (a : 𝓞 E) z, σ (a • z) = a • σ z := fun a z => map_smul σ₀ a z
  have hs : ∀ a, ∃ z b, a = σ z + (p ^ n) • b :=
    surj_mod_pow σ.toAddMonoidHom p (fun a => by
      obtain ⟨z, b, h⟩ := hu.span a
      exact ⟨z, b, h.trans (by rw [← hσ]; rfl)⟩) n
  have hrk : Module.finrank ℤ La = Module.finrank ℤ (Fin N → 𝓞 E) := by
    rw [hu.rank, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let φ := LinearEquiv.ofFinrankEq La (Fin N → 𝓞 E) hrk
  have hk : ∀ z b, σ z = (p ^ n) • b → ∃ z', z = (p ^ n) • z' := fun z b h =>
    inj_mod_of_surj_mod (φ.toLinearMap ∘ₗ σ) (p ^ n) (fun a => by
      obtain ⟨z, b, h⟩ := hs (φ.symm a)
      refine ⟨z, φ b, ?_⟩
      have := congrArg φ h
      rwa [φ.apply_symm_apply, map_add, map_nsmul] at this) z (φ b) (by
      show φ (σ z) = _
      rw [h, map_nsmul])
  obtain ⟨hsu, hin⟩ := perfect_mod σ (p ^ n) EF hu.unimod hs hk
  let K : Submodule ℤ La := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n :=
    AddMonoidHom.toMultiplicative (K.mkQ ∘ₗ σ).toAddMonoidHom
  have hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (σ z) := fun z => rfl
  let e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n) :=
    { toFun := fun y => (Int.castAddHom (ZMod (p ^ n))).comp (EF (σ y) ∘ₗ σ).toAddMonoidHom
      map_zero' := by ext z; simp
      map_add' := fun y y' => by ext z; simp }
  have he : ∀ y z, e y z = ((EF (σ y) (σ z) : ℤ) : ZMod (p ^ n)) := fun y z => rfl
  have hone : ∀ a : La, lev p n a = 1 ↔ ∃ b, a = (p ^ n) • b := fun a => by
    show (Submodule.Quotient.mk a : La ⧸ K) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  refine ⟨π, e, fun z => by rw [hπ, hσ], fun z z' => by rw [he, hσ, hσ], fun a => ?_, fun t => ?_, fun y => ?_,
    fun y => ?_, fun a y z => ?_, fun ψ => ?_, fun y hy => ?_⟩
  · simpa only [hσ] using hs a
  · obtain ⟨a, ha⟩ := K.mkQ_surjective (Multiplicative.toAdd t)
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have h0 : K.mkQ ((p ^ n) • b) = 0 := (hone _).2 ⟨b, rfl⟩
    rw [map_add (f := _), h0, add_zero] at ha
    exact ha
  · rw [hπ, hone]
    exact ⟨fun ⟨b, hb⟩ => hk y b hb, fun ⟨y', hy'⟩ => ⟨σ y', by rw [hy', map_nsmul]⟩⟩
  · rw [he, hu.alt, Int.cast_zero]
  · rw [he, he, hσa, hσa, hu.adj]
  · obtain ⟨y, hy⟩ := hsu ψ
    exact ⟨y, AddMonoidHom.ext hy⟩
  · exact hin y fun z => (he y z).symm.trans (by rw [hy]; rfl)

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Invres
section
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

lemma unimod {S V ι : Type} [CommRing S] [CommRing V] [Algebra S V] [Fintype ι] (f : ι → V)
    (b : ι → S) (h1 : 1 = ∑ j, b j • f j)
    (hmul : ∀ i j, f j * f i ∈ Submodule.span S (Set.range f)) :
    ∃ e : ι → S, algebraMap S V (∑ j, e j * b j) = 1 := by
  let A : Submodule S V := Submodule.span S (Set.range f)
  let J : Ideal S := Ideal.span (Set.range b)
  have hJ : A ≤ J • A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : f i = ∑ j, b j • (f j * f i) := by
      conv_lhs => rw [← one_mul (f i), h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul
      (Ideal.subset_span ⟨j, rfl⟩) (hmul i j)
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J A
    (Submodule.fg_span (Set.finite_range f)) hJ
  have h1A : (1 : V) ∈ A := by
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => A.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr := hr0 1 h1A
  rw [Algebra.smul_def, mul_one] at hr
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (J.neg_mem hr1)
  refine ⟨e, ?_⟩
  simp only [smul_eq_mul] at he
  rw [he, neg_sub, map_sub, hr, map_one, sub_zero]

theorem invres : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ K K' : AddSubgroup N, K ≤ K' → ∀ g ∈ AA.carrier, (∀ x ∈ K', ∀ k ∈ K, g (x + k) = g x) → ∃ g' ∈ invFun AA.carrier K, ∀ x ∈ K', g' x = g x := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA K K' _ g hg hinv
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨f, hf, hfree⟩, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  have hB : ∀ b ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K), b ∈ invFun AA.carrier K := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q ((x + k : N) : N ⧸ K) = q (x : N ⧸ K)
    rw [QuotientAddGroup.mk_add_of_mem x hk]
  have hdec : ∀ a ∈ AA.carrier, ∃ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) ∧
      a = ∑ j, b j * f j := by
    intro a ha
    obtain ⟨b, ⟨hb, hab⟩, -⟩ := hfree a ha
    exact ⟨b, fun j => hB _ (hb j), hab⟩
  let S : Subalgebra R (N → C) := (invFun AA.carrier K).toSubalgebra ⟨AA.one_mem, fun _ _ _ => rfl⟩
    (fun x y hx hy => ⟨AA.mul_mem _ _ hx.1 hy.1, fun z k hk => by
      simp only [Pi.mul_apply, hx.2 z k hk, hy.2 z k hk]⟩)
  let A : Submodule S (N → C) := Submodule.span S (Set.range f)
  have hA : ∀ a ∈ AA.carrier, a ∈ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hdec a ha
    exact Submodule.sum_mem _ fun j _ =>
      A.smul_mem (⟨b j, hb j⟩ : S) (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hb, h1⟩ := hdec 1 AA.one_mem
  obtain ⟨e, he⟩ := unimod f (fun j => (⟨b j, hb j⟩ : S)) h1
    (fun i j => hA _ (AA.mul_mem _ _ (hf j) (hf i)))
  have he' : ∀ x, ∑ j, (e j : N → C) x * b j x = 1 := by
    intro x
    have : ((∑ j, e j * (⟨b j, hb j⟩ : S) : S) : N → C) x = 1 := congrFun he x
    simpa using this
  obtain ⟨c, hc, hgc⟩ := hdec g hg
  refine ⟨((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C), (∑ j, e j * (⟨c j, hc j⟩ : S) : S).2,
    fun x hx => ?_⟩
  let ρ : (N → C) →ₗ[C] (K → C) := LinearMap.funLeft C C fun k : K => x + (k : N)
  have hρ : ∀ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) →
      ρ (∑ j, b j * f j) = ∑ j, b j x • ρ (f j) := by
    intro b hb
    funext k
    simp only [ρ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [(hb j).2 x k k.2]
  have hli : LinearIndependent C fun j => ρ (f j) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · have hsurj : Function.Surjective ρ :=
        LinearMap.funLeft_surjective_of_injective _ _ _
          (fun k k' h => Subtype.ext (add_left_cancel h))
      rw [← LinearMap.range_eq_top.2 hsurj, ← Submodule.map_top, ← span_top_of_isLat (C := C) AA.lat,
        Submodule.map_span_le]
      intro a ha
      obtain ⟨b', hb', rfl⟩ := hdec a ha
      rw [hρ b' hb']
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp
  have hkey : ∀ j, c j x = g x * b j x := by
    have h2 : ∑ j, (c j x - g x * b j x) • ρ (f j) = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hρ c hc, ← hρ b hb, ← hgc, ← h1]
      funext k
      simp [ρ, LinearMap.funLeft_apply, hinv x hx k k.2]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 j)
  have : ((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C) x = ∑ j, (e j : N → C) x * c j x := by
    simp
  rw [this]
  simp only [hkey]
  calc ∑ j, (e j : N → C) x * (g x * b j x) = g x * ∑ j, (e j : N → C) x * b j x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = g x := by rw [he', mul_one]

end PositivityTheory.HtPt.Rc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MaSerre
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

open ChCoh

theorem coh_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∀ c, x c ≠ 0 → ∃ (n : ℕ) (b : Fin n → E), ∀ p : Cpt M.ξ, InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range b) := by
  intro o _ Ω _ _ κ _ x M E _ _ L hL c hc
  obtain ⟨n, b, h⟩ := finite_gen (A := chRing o x c) (E := E) ((chRing o x c).val : chRing o x c →+* Ω)
    (Pt := {p : Cpt M.ξ // InChart M.ξ x c p}) (fun q => regAt M.ξ q.1)
    (fun _ _ => rfl)
    (fun q a => (regat_loc o Ω κ x M c q.1 q.2).1 _ a.2)
    (fun q a ha => by
      obtain ⟨u, hu, v, hv, hvu, e⟩ := ((regat_loc o Ω κ x M c q.1 q.2).2 a).1 ha
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hvu, e⟩)
    (fun P hP => by
      obtain ⟨p, ⟨hp, hu⟩, -⟩ := prime_pt o Ω κ x M c hc P hP
      exact ⟨⟨p, hp⟩, hu⟩)
    (fun q => (reg_local M.X Ω M.ξ).1 q.1)
    (fun q => L q.1)
    (fun p => by
      obtain ⟨U, hU, n, b, hb⟩ := hL p.1 trivial
      obtain ⟨f, hf, hfu, hfU⟩ := basic o Ω κ x M c p.1 U p.2 hU
      exact ⟨⟨f, hf⟩, n, b, hfu, fun q hq => hb q.1 trivial (hfU q.1 q.2 hq)⟩)
  exact ⟨n, b, fun p hp => h ⟨p, hp⟩⟩

section

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E)

theorem twist_mem {c j : κ} {t : Set E}
    (ht : ∀ p : Cpt M.ξ, InChart M.ξ x j p → L p = Submodule.span (regAt M.ξ p) t) {e : E}
    (he : ∀ p : Cpt M.ξ, InChart M.ξ x c p → e ∈ L p) :
    ∃ m : ℕ, ∀ p : Cpt M.ξ, InChart M.ξ x j p → (x c / x j) ^ m • e ∈ L p := by
  by_cases hj : x j = 0
  · exact ⟨0, fun p hp => (hp.1 hj).elim⟩
  let ι : chRing o x j →+* Ω := (chRing o x j).val
  have hsm : ∀ (a : chRing o x j) (e : E), a • e = ι a • e := fun _ _ => rfl
  let f : chRing o x j := ⟨x c / x j, Algebra.subset_adjoin ⟨c, rfl⟩⟩
  have hrad : f ∈ (satIdeal (Submodule.span (chRing o x j) t) 1 e).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hn
    obtain ⟨q, ⟨hq, hu⟩, -⟩ := prime_pt o Ω κ x M j hj P hP
    have hf : unitAt M.ξ q (x c / x j) := not_not.1 fun h => hn ((hu f).2 h)
    have hc : x c ≠ 0 := fun h => hf.1 (by rw [h, zero_div])
    have hqc : InChart M.ξ x c q := ⟨hc, fun k => by
      have : x k / x c = x k / x j * (x c / x j)⁻¹ := by field_simp
      rw [this]
      exact mul_mem (hq.2 k) hf.2.2⟩
    have hmem : e ∈ Submodule.span (regAt M.ξ q) t := ht q hq ▸ he q hqc
    obtain ⟨v, hv, hve⟩ := clear_denoms ι hsm (S := regAt M.ξ q) (fun a ha => by
      obtain ⟨u, hu, v, hv, hvu, e⟩ := ((regat_loc o Ω κ x M j q hq).2 a).1 ha
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hvu, e⟩) t hmem
    exact (hu v).1 (hJP ⟨0, by simpa using hve⟩) hv
  obtain ⟨m, k, hk⟩ := hrad
  refine ⟨m, fun q hq => ?_⟩
  rw [ht q hq]
  have h1 := mem_of_mem_spanA ι hsm (S := regAt M.ξ q)
    (fun a => (regat_loc o Ω κ x M j q hq).1 _ a.2) hk
  rw [hsm, one_pow, one_mul, map_pow] at h1
  exact h1

end

theorem serre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) := by
  intro o _ Ω _ _ κ _ x M E _ _ L hL
  have h1 : ∀ c, ∃ (n : ℕ) (b : Fin n → E), ∀ p : Cpt M.ξ, InChart M.ξ x c p →
      L p = Submodule.span (regAt M.ξ p) (Set.range b) := fun c => by
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun p hp => (hp.1 hc).elim⟩
    · exact coh_chart o Ω κ x M E L hL c hc
  choose n b hb using h1
  have h2 : ∀ s : (Σ c, Fin (n c)) × κ, ∃ m : ℕ, ∀ p : Cpt M.ξ, InChart M.ξ x s.2 p →
      (x s.1.1 / x s.2) ^ m • b s.1.1 s.1.2 ∈ L p := fun s =>
    twist_mem M L (hb s.2) fun p hp => by
      rw [hb _ p hp]
      exact Submodule.subset_span ⟨_, rfl⟩
  choose m hm using h2
  obtain ⟨d, hd⟩ := (Set.finite_range m).bddAbove
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (n c))
  refine ⟨d, N, fun k => x (e.symm k).1 ^ d • b (e.symm k).1 (e.symm k).2, fun j p hp => ?_⟩
  apply le_antisymm
  · rw [hb j p hp]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨e ⟨j, k⟩, ?_⟩
    dsimp only
    rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hp.1), one_smul]
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    set s := e.symm k
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (hd ⟨(s, j), rfl⟩ : m (s, j) ≤ d)
    have h3 := (L p).smul_mem (⟨(x s.1 / x j) ^ r, pow_mem (hp.2 _) _⟩ : regAt M.ξ p) (hm (s, j) p hp)
    have h4 : (x j ^ d)⁻¹ • x s.1 ^ d • b s.1 s.2 =
        (x s.1 / x j) ^ r • (x s.1 / x j) ^ m (s, j) • b s.1 s.2 := by
      rw [smul_smul, smul_smul, ← pow_add, add_comm r, ← hr, div_pow, div_eq_inv_mul]
    change (x j ^ d)⁻¹ • x s.1 ^ d • b s.1 s.2 ∈ L p
    rw [h4]
    exact h3

end PositivityTheory.HtPt.Ma
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinMany
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {A : Type} [Fintype A] {κa : A → Type} (w : ∀ a, κa a → Ω)

theorem inChart_prod_of_forall (p : Cpt ξ) (h : ∀ a, ∃ l, InChart ξ (w a) l p) :
    ∃ c, InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p := by
  choose c hc using h
  refine ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => (hc a).1, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun a _ => (hc a).2 (c' a)

theorem inChart_of_inChart_prod [DecidableEq A] {p : Cpt ξ} {c : ∀ a, κa a}
    (h : InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p) (a : A) : InChart ξ (w a) (c a) p := by
  obtain ⟨h0, h1⟩ := h
  have hne : ∀ b, w b (c b) ≠ 0 := fun b => (Finset.prod_ne_zero_iff.1 h0) b (Finset.mem_univ b)
  refine ⟨hne a, fun l => ?_⟩
  have key : (∏ b, w b (Function.update c a l b)) / (∏ b, w b (c b)) = w a l / w a (c a) := by
    rw [← Finset.prod_div_distrib, Fintype.prod_eq_single a]
    · simp
    · intro b hb
      simp [Function.update_of_ne hb, div_self (hne b)]
  rw [← key]
  exact h1 _

end PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

namespace PositivityTheory.HtPt.Mb.LJoinMany

theorem join_finitely_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M A _ κa _ w hw
  classical
  haveI := Fintype.ofFinite A
  have hW : ∃ l : (∀ a, κa a), (∏ a, w a (l a)) ≠ 0 := by
    choose c hc using hw
    exact ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => hc a⟩
  have hcl : Subfield.closure (Set.range (RingHom.id Ω) ∪
      {z | ∃ l l' : (∀ a, κa a), z = (∏ a, w a (l a)) / ∏ a, w a (l' a)}) = ⊤ :=
    eq_top_iff.2 fun z _ => Subfield.subset_closure (Or.inl ⟨z, rfl⟩)
  obtain ⟨M', f, hf⟩ := PositivityTheory.HtPt.Mb.join_exists o Ω κ x M Ω (RingHom.id Ω) (∀ a, κa a)
    (fun c => ∏ a, w a (c a)) (fun _ => rfl) hW hcl
  refine ⟨κ × (∀ a, κa a), inferInstance, _, M', f, hf, ?_, ?_⟩
  · intro a p'
    obtain ⟨-, c, hc⟩ := PositivityTheory.HtPt.Mb.join_charts o Ω κ (∀ a, κa a) x Ω (RingHom.id Ω)
      (fun c => ∏ a, w a (c a)) M' (fun _ => rfl) p'
    exact ⟨c a, JoinMany.inChart_of_inChart_prod _ w hc a⟩
  · intro p hp
    exact PositivityTheory.HtPt.Mb.join_iso o Ω κ x M (∀ a, κa a) (fun c => ∏ a, w a (c a)) M' f hf p
      (JoinMany.inChart_prod_of_forall _ w p hp)

end PositivityTheory.HtPt.Mb.LJoinMany


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.join_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinMany.join_finitely_many
end

