module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.Mem.Chr

section General

variable (L : Type) [Field L] [NumberField L]

def unitIdl : Subgroup (Ideles L) where
  carrier := {a | ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}
  one_mem' := fun v => by
    show Valued.v (1 : v.adicCompletion L) = 1
    exact map_one _
  mul_mem' := fun {a b} ha hb v => by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v) = 1
    rw [map_mul, ha v, hb v, one_mul]
  inv_mem' := fun {a} ha v => by
    have h : (a : AdeleRing (𝓞 L) L).2 v * ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 L) L => z.2 v) a.mul_inv
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion L) _) h
    rw [map_mul, ha v, one_mul, map_one] at h2
    exact h2

def finPartI : Ideles L →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)))

variable {L}

def locF (F : Type) [Field F] [NumberField F] [Algebra F L] (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : Ideles L :=
  ∏ Q ∈ aboveF (L := L) F v, localIdele L Q (atFin Q (upF F k))

def ConjPl (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : L, v'.valuation L (c x) = v.valuation L x

structure IsConjI (c : L ≃+* L) (C : Ideles L →* Ideles L) : Prop where
  cont : Continuous C
  diag : ∀ k : Lˣ, C (diagUnits L k) = diagUnits L (Units.map (MonoidHomClass.toMonoidHom c) k)
  inf : ∀ (w : InfinitePlace L) (k : Lˣ), C (infIdele L w (atInf w k)) =
    infIdele L (w.comap (c.symm : L →+* L)) (atInf _ (Units.map (MonoidHomClass.toMonoidHom c) k))
  infRange : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), ∃ y', C (infIdele L w y) = infIdele L (w.comap (c.symm : L →+* L)) y'
  loc : ∀ v v', ConjPl c v v' → ∀ k : Lˣ, C (localIdele L v (atFin v k)) =
    localIdele L v' (atFin v' (Units.map (MonoidHomClass.toMonoidHom c) k))
  locRange : ∀ v v', ConjPl c v v' → ∀ x, ∃ x', C (localIdele L v x) = localIdele L v' x'
  val : ∀ v v', ConjPl c v v' → ∀ a : Ideles L,
    Valued.v ((C a : AdeleRing (𝓞 L) L).2 v') = Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ∧
    Valued.v ((C a : AdeleRing (𝓞 L) L).2 v' - 1) = Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1)

def TameLoc (v : HeightOneSpectrum (𝓞 L)) (θ : (v.adicCompletion L)ˣ →* ℂˣ) : Prop :=
  (∀ x, ‖((θ x : ℂˣ) : ℂ)‖ = 1) ∧
    ∀ x, IsUnitAt v x → Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) → θ x = 1

def detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) : Submodule (𝓞 L) L :=
  Submodule.span (𝓞 L) {z | ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧ z = (Matrix.of x).det}

def ordSub (w : HeightOneSpectrum (𝓞 L)) (A : Submodule (𝓞 L) L) : ℤ :=
  sInf {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n}

def SplitsC (L : Type) [Field L] [NumberField L] (p : ℕ) : Prop :=
  {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard = Module.finrank ℚ L

structure CMData (F : Type) [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L) {I : Type} (φ : I → L →+* ℂ) : Prop where
  real : IsTotallyReal F
  cplx : IsTotallyComplex L
  rank : Module.finrank F L = 2
  ne : c ≠ 1
  bij : Function.Bijective fun i => InfinitePlace.mk (φ i)

end General

instance framePsiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def congG : Set (Ideles H.E) :=
  {a | a ∈ unitIdl H.E ∧ ∀ k v, OverP H (H.g k) v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1}

def KD : Subgroup (Ideles H.E) :=
  Subgroup.closure (congG H ∪ {a | ∃ v k, a = locF H.F v k})

abbrev DtT : Type := Ideles H.E ⧸ KD H


open Classical in
def tildeD (χ : HChar H.E) : DtT H →* ℂˣ :=
  if h : KD H ≤ (χ.1.comp (finPartI H.E)).ker then QuotientGroup.lift (KD H) (χ.1.comp (finPartI H.E)) h else 1

def UOT : Subgroup (DtT H) := (unitIdl H.E).map (QuotientGroup.mk' (KD H))

def IsRationalUnitaryDeterminantMap (f : (letI := H.cmStar; unitary H.E) →* DtT H) : Prop :=
  letI := H.cmStar
  ∀ (k : H.Eˣ) (z : unitary H.E), (z : H.E) * H.conj (k : H.E) = k → QuotientGroup.mk (diagUnits H.E k) = f z


open Classical in
def e1T : (letI := H.cmStar; unitary H.E) →* DtT H := if h : ∃ f, IsRationalUnitaryDeterminantMap H f then h.choose else 1

def relDetT (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : DtT H ⧸ UOT H :=
  QuotientGroup.mk (QuotientGroup.mk (∏ᶠ w : HeightOneSpectrum (𝓞 H.E),
    localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M') - ordSub w (detSub M)).toNat))

def IsTwist (S : Set ℕ) (ξ : HChar H.E) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) ∧ ξ.TrivOn H.F ∧ (∀ v, ξ.TameAt v) ∧
    ∀ v, ¬ ξ.UnrAt v → IsSplitPl H v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ Ideal.absNorm v.asIdeal ∉ S

structure HFrame (e : Fin R.m → R.Psi → ℚ) where
  P : PiBar H
  W : Omg H
  mu0 : Fin R.m → HChar H.E
  eta : HChar H.E
  chiPsi : HChar H.E
  del : HChar H.E
  del' : HChar H.E
  isMu0 : ∀ j, IsMu0 P W (e j) j.1 (mu0 j)
  isEta : IsEtaT H eta
  isChi : IsChiPsi H chiPsi
  isDel : IsDelta (H := H) H.pde del
  isDel' : IsDelta (H := H) H.pde' del'

structure DtPack where
  Dt : Type
  [instDt : CommGroup Dt]
  muTil : ℕ → Dt →* ℂˣ
  chiD : Dt →* ℂˣ
  UO : Subgroup Dt
  chiD_UO : ∀ x ∈ UO, chiD x = 1
  e1Dt : letI := H.cmStar; unitary H.E →* Dt
  rest_detCharacter_on_unitary_eq : letI := H.cmStar; ∀ z : unitary H.E,
    ((chiD (e1Dt z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹
  relDet : letI := H.cmStar; ∀ N, SDLat H.E N → SDLat H.E N → Dt ⧸ UO
  relDet_self : letI := H.cmStar; ∀ N L, relDet N L L = 1
  relDet_mul : letI := H.cmStar; ∀ N L L' L'', relDet N L L' * relDet N L' L'' = relDet N L L''
  relDet_smul : letI := H.cmStar; ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDet N L L' =
      QuotientGroup.mk (e1Dt ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩)

section API

variable {L : Type} [Field L] [NumberField L]

theorem finPartI_fst (a : Ideles L) : (finPartI L a : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem finPartI_snd (a : Ideles L) : (finPartI L a : AdeleRing (𝓞 L) L).2 = (a : AdeleRing (𝓞 L) L).2 := rfl

theorem finPartI_eq_self {a : Ideles L} (h : ∀ w : InfinitePlace L, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    finPartI L a = a :=
  Units.ext (Prod.ext (funext fun w => (h w).symm) rfl)

theorem finPartI_mem_unitIdl {a : Ideles L} : finPartI L a ∈ unitIdl L ↔ a ∈ unitIdl L := Iff.rfl

theorem det_mem_detSub {N : ℕ} {M : Submodule (𝓞 L) (Fin N → L)} (x : Fin N → Fin N → L) (hx : ∀ i, x i ∈ M) :
    (Matrix.of x).det ∈ detSub M :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem ordF_unif_self (w : HeightOneSpectrum (𝓞 L)) : ordF w (unif w) = 1 := by
  have h : Valued.v (((unif w : Lˣ) : L) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  simp [ordF, h]

theorem ordSub_span_singleton (w : HeightOneSpectrum (𝓞 L)) (u : Lˣ) :
    ordSub w (Submodule.span (𝓞 L) {(u : L)}) = ordF w u := by
  refine IsLeast.csInf_eq ⟨⟨u, Submodule.mem_span_singleton_self _, rfl⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hk
  have hk0 : w.valuation L (k : L) ≠ 0 := by simp
  have hu0 : w.valuation L (u : L) ≠ 0 := by simp
  have hle : w.valuation L (k : L) ≤ w.valuation L (u : L) := by
    rw [← ha, Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (w.valuation_le_one a)
  unfold ordF
  exact neg_le_neg ((WithZero.log_le_log hk0 hu0).2 hle)

end API

section Inhabitant

end Inhabitant

theorem mem_KD_of_congG {a : Ideles H.E} (h : a ∈ congG H) : a ∈ KD H :=
  Subgroup.subset_closure (Or.inl h)

theorem locF_mem_KD (v : HeightOneSpectrum (𝓞 H.F)) (k : (H.F)ˣ) : locF H.F v k ∈ KD H :=
  Subgroup.subset_closure (Or.inr ⟨v, k, rfl⟩)

theorem tildeD_mk {χ : HChar H.E} (h : KD H ≤ (χ.1.comp (finPartI H.E)).ker) (a : Ideles H.E) :
    tildeD H χ (QuotientGroup.mk a) = χ.1 (finPartI H.E a) := by
  unfold tildeD
  rw [dite_eq_left h]
  rfl

theorem mem_UOT {x : DtT H} : x ∈ UOT H ↔ ∃ a : Ideles H.E,
    (∀ v, Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v) = 1) ∧ QuotientGroup.mk a = x := Iff.rfl

theorem isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants (h : ∃ f, IsRationalUnitaryDeterminantMap H f) : IsRationalUnitaryDeterminantMap H (e1T H) := by
  unfold e1T
  rw [dite_eq_left h]
  exact h.choose_spec

theorem relDetT_self (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : relDetT H N M M = 1 := by
  unfold relDetT
  simp

theorem isTwist_one (S : Set ℕ) : IsTwist H S 1 :=
  ⟨⟨1, one_pos, one_pow 1⟩, isClsF_one.triv, fun _ _ _ _ => rfl, fun v hv => absurd (isClsF_one.unr v) hv⟩


end GlobalTheory.Mem.Chr
