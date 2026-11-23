module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

abbrev chRing (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω) (c : κ) :
    Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x c)

structure PModel (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of Ω) ⟶ X

  s : X ⟶ Spec (CommRingCat.of o)
  hover : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap o Ω))
  all : ∀ q : X, genPt ξ ⤳ q
  tie : CoordTie o ξ x

variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]

def joinCo {κ κ' : Type} (i : Ω →+* Ω') (x : κ → Ω) (w : κ' → Ω') : κ × κ' → Ω' := fun q => i (x q.1) * w q.2

def Lat.IsCohOn {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (T : Set (Cpt ξ)) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ (n : ℕ) (b : Fin n → E),
    ∀ q ∈ T, q.1 ∈ U → L q = Submodule.span (regAt ξ q) (Set.range b)

def ctrSet (o : Type) [CommRing o] [Algebra o Ω] {κ : Type} (x : κ → Ω) (i : Ω →+* Ω')
    (ξ' : Spec (CommRingCat.of Ω') ⟶ X') : Set (Cpt ξ') :=
  {p' | ∃ c, x c ≠ 0 ∧ ∀ a ∈ chRing o x c, i a ∈ regAt ξ' p'}

def IsCtrOf {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (i : Ω →+* Ω') (p : Cpt ξ)
    (p' : Cpt ξ') : Prop :=
  (∀ a ∈ regAt ξ p, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ p, unitAt ξ' p' (i a) → unitAt ξ p a

def Lat.pullLoc {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (i : Ω →+* Ω') (j : E →+ F) : Lat ξ' F := fun p' =>
  Submodule.span (regAt ξ' p') {e' | ∃ p : Cpt ξ, IsCtrOf i p p' ∧ ∃ e ∈ L p, e' = j e}

def IsExtOver (i : Ω →+* Ω') (j : E →+ F) : Prop :=
  (∀ (a : Ω) (e : E), j (a • e) = i a • j e) ∧
    ∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)

structure IsoAt (ξ' : Spec (CommRingCat.of Ω') ⟶ X') {ξ : Spec (CommRingCat.of Ω) ⟶ X} (f : X' ⟶ X) (i : Ω →+* Ω')
    (p : Cpt ξ) : Prop where

  existsUnique : ∃! p' : Cpt ξ', f p'.1 = p.1

  regAt_eq : ∀ p' : Cpt ξ', f p'.1 = p.1 → regAt ξ' p' = (regAt ξ p).map i

  dom : Dominates ξ' ξ f i

structure NormAt (ξ' : Spec (CommRingCat.of Ω') ⟶ X') {ξ : Spec (CommRingCat.of Ω) ⟶ X} (f : X' ⟶ X) (i : Ω →+* Ω')
    (p : Cpt ξ) : Prop where

  exists_max : ∀ p' : Cpt ξ', f p'.1 = p.1 →
    ∃ (P : Ideal (integralClosure ((regAt ξ p).map i) Ω').toSubring) (_ : P.IsMaximal),
      regAt ξ' p' = (LocalSubring.ofPrime _ P).toSubring

  existsUnique : ∀ (P : Ideal (integralClosure ((regAt ξ p).map i) Ω').toSubring) (_ : P.IsMaximal),
    ∃! p' : Cpt ξ', f p'.1 = p.1 ∧ regAt ξ' p' = (LocalSubring.ofPrime _ P).toSubring

  dom : Dominates ξ' ξ f i

def genFib (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) := {p | ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)}

def locFib (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : ℕ) : Set (Cpt ξ) := {p | ∀ n : ℕ, n.Coprime q → unitAt ξ p (n : Ω)}

def invFib (ξ : Spec (CommRingCat.of Ω) ⟶ X) (m : ℕ) : Set (Cpt ξ) := {p | unitAt ξ p (m : Ω)}


def Lat.predualIn {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ (Module.Dual Ω E)) (V : Submodule Ω E) : Lat ξ E :=
  fun p =>
  { carrier := {v | v ∈ V ∧ ∀ w ∈ L p, w v ∈ regAt ξ p}
    add_mem' := fun ha hb => ⟨V.add_mem ha.1 hb.1, fun w hw => by simpa using add_mem (ha.2 w hw) (hb.2 w hw)⟩
    zero_mem' := ⟨V.zero_mem, fun w _ => by simp⟩
    smul_mem' := fun c v hv => ⟨V.smul_mem (c : Ω) hv.1, fun w hw => by
      have : w (c • v) = (c : Ω) * w v := by
        show w ((c : Ω) • v) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem c.2 (hv.2 w hw)⟩ }

section API

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}

theorem IsCtrOf.refl (p : Cpt ξ) : IsCtrOf (RingHom.id Ω) p p := ⟨fun _ h => h, fun _ _ h => h⟩

theorem IsCtrOf.unitAt_iff {i : Ω →+* Ω'} {p : Cpt ξ} {p' : Cpt ξ'} (h : IsCtrOf i p p') {a : Ω}
    (ha : a ∈ regAt ξ p) : unitAt ξ' p' (i a) ↔ unitAt ξ p a :=
  ⟨h.2 a ha, fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 _ hu.2.1, by rw [← map_inv₀]; exact h.1 _ hu.2.2⟩⟩

theorem IsCtrOf.unitAt_spec {R : Type} [CommRing R] {φ : R →+* Ω} (hφ : Function.Injective φ)
    (p : Cpt (CptModel.pt φ)) (a : R) : unitAt (CptModel.pt φ) p (φ a) ↔ a ∉ p.1.asIdeal := by
  constructor
  · rintro ⟨h0, -, h⟩ hc
    obtain ⟨r, s, hs, -, e⟩ := (CptModel.mem_regAt_iff φ p _).1 h
    have : s = a * r := hφ (by rw [map_mul, ← e, mul_inv_cancel_left₀ h0])
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : φ a ≠ 0 := (map_ne_zero_iff _ hφ).2 fun h => hc (h ▸ Ideal.zero_mem _)
    exact ⟨h0, ⟨_, CptModel.genMap_toStalk φ p a⟩,
      (CptModel.mem_regAt_iff φ p _).2 ⟨1, a, hc, h0, by rw [map_one, inv_mul_cancel₀ h0]⟩⟩

theorem IsCtrOf.unique_spec {R : Type} [CommRing R] {φ : R →+* Ω} (hφ : Function.Injective φ) {i : Ω →+* Ω'}
    {p q : Cpt (CptModel.pt φ)} {p' : Cpt ξ'} (hp : IsCtrOf i p p') (hq : IsCtrOf i q p') : p = q := by
  refine Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun a => not_iff_not.1 ?_))
  exact ((IsCtrOf.unitAt_spec hφ p a).symm.trans
    ((hp.unitAt_iff ⟨_, CptModel.genMap_toStalk φ p a⟩).symm.trans
      (hq.unitAt_iff ⟨_, CptModel.genMap_toStalk φ q a⟩))).trans (IsCtrOf.unitAt_spec hφ q a)

theorem Lat.pullLoc_eq_span_of_ctr {L : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p₀ : Cpt ξ} {p' : Cpt ξ'}
    (h : IsCtrOf i p₀ p') (hu : ∀ p : Cpt ξ, IsCtrOf i p p' → ∀ e ∈ L p, e ∈ L p₀) :
    L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) := by
  refine congrArg _ (Set.ext fun e' => ⟨?_, ?_⟩)
  · rintro ⟨p, hp, e, he, rfl⟩
    exact ⟨e, hu p hp e he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨p₀, h, e, he, rfl⟩

theorem NormAt.isLocalRing_regAt (p : Cpt ξ) : IsLocalRing (regAt ξ p) :=
  IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem NormAt.ofPrime_of_isLocalRing (A : Subring Ω) [IsLocalRing A] (P : Ideal A) (hP : P.IsMaximal) :
    (LocalSubring.ofPrime A P).toSubring = A := by
  obtain rfl := IsLocalRing.eq_maximalIdeal hP
  refine le_antisymm ?_ (LocalSubring.le_ofPrime A _)
  intro a ha
  obtain ⟨⟨u, s⟩, e⟩ := IsLocalization.surj (IsLocalRing.maximalIdeal A).primeCompl
    (⟨a, ha⟩ : (LocalSubring.ofPrime A (IsLocalRing.maximalIdeal A)).toSubring)
  have hs : IsUnit (s : A) := by
    by_contra h
    exact s.2 h
  obtain ⟨v, hv⟩ := hs.exists_right_inv
  have e' : a * ((s : A) : Ω) = (u : Ω) := congrArg Subtype.val e
  have hv' : ((s : A) : Ω) * (v : Ω) = 1 := congrArg Subtype.val hv
  have : a = (u : Ω) * v := by rw [← e', mul_assoc, hv', mul_one]
  rw [this]
  exact A.mul_mem u.2 v.2

theorem NormAt.of_unique {f : X' ⟶ X} {i : Ω →+* Ω'} {p : Cpt ξ} (hd : Dominates ξ' ξ f i) (p₀ : Cpt ξ')
    (h₀ : f p₀.1 = p.1) (hu : ∀ q : Cpt ξ', f q.1 = p.1 → q = p₀)
    (e : (integralClosure ((regAt ξ p).map i) Ω').toSubring = regAt ξ' p₀) : NormAt ξ' f i p := by
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map i) Ω').toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p₀
  refine ⟨fun q hq => ?_, fun P hP => ⟨p₀, ⟨h₀, ((NormAt.ofPrime_of_isLocalRing _ P hP).trans e).symm⟩,
    fun q hq => hu q hq.1⟩, hd⟩
  rw [hu q hq]
  exact ⟨_, IsLocalRing.maximalIdeal.isMaximal _,
    ((NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).trans e).symm⟩

theorem NormAt.regAt_field (p : Cpt (CptModel.pt (RingHom.id Ω))) : regAt _ p = ⊤ :=
  eq_top_iff.2 fun a _ => ⟨_, CptModel.genMap_toStalk (RingHom.id Ω) p a⟩

theorem NormAt.dominates_field_iff (φ i : Ω →+* Ω') :
    Dominates (CptModel.pt (RingHom.id Ω')) (CptModel.pt (RingHom.id Ω)) (CptModel.pt φ) i ↔ φ = i := by
  unfold Dominates
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  exact ⟨fun h => congrArg CommRingCat.Hom.hom h, fun h => h ▸ rfl⟩

theorem NormAt.of_isAlgebraic [Algebra Ω Ω'] [Algebra.IsAlgebraic Ω Ω'] (p : Cpt (CptModel.pt (RingHom.id Ω))) :
    NormAt (CptModel.pt (RingHom.id Ω')) (CptModel.pt (algebraMap Ω Ω')) (algebraMap Ω Ω') p := by
  refine NormAt.of_unique ((NormAt.dominates_field_iff _ _).2 rfl) (CptModel.self _)
    (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
    (fun q _ => Subtype.ext (Subsingleton.elim (α := PrimeSpectrum Ω') _ _)) ?_
  rw [NormAt.regAt_field, NormAt.regAt_field, eq_top_iff]
  intro a _
  let g : Ω →+* (⊤ : Subring Ω).map (algebraMap Ω Ω') :=
    (algebraMap Ω Ω').codRestrict _ fun b => ⟨b, trivial, rfl⟩
  have h : IsIntegral Ω a := Algebra.IsIntegral.isIntegral a
  exact IsIntegral.map_of_comp_eq g (RingHom.id Ω') (RingHom.ext fun _ => rfl) h

theorem IsoAt.field_iff (φ i : Ω →+* Ω') (p : Cpt (CptModel.pt (RingHom.id Ω))) :
    IsoAt (CptModel.pt (RingHom.id Ω')) (CptModel.pt φ) i p ↔ φ = i ∧ Function.Surjective i := by
  constructor
  · intro h
    refine ⟨(NormAt.dominates_field_iff _ _).1 h.dom, fun a => ?_⟩
    have e := h.regAt_eq (CptModel.self _) (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
    rw [NormAt.regAt_field] at e
    obtain ⟨b, -, hb⟩ : a ∈ (regAt _ p).map i := e ▸ Subring.mem_top a
    exact ⟨b, hb⟩
  · rintro ⟨h, hs⟩
    refine ⟨⟨CptModel.self _, Subsingleton.elim (α := PrimeSpectrum Ω) _ _,
      fun q _ => Subtype.ext (Subsingleton.elim (α := PrimeSpectrum Ω') _ _)⟩, fun q _ => ?_,
      (NormAt.dominates_field_iff _ _).2 h⟩
    rw [NormAt.regAt_field, NormAt.regAt_field, eq_comm, eq_top_iff]
    intro a _
    obtain ⟨b, rfl⟩ := hs a
    exact ⟨b, trivial, rfl⟩

theorem Lat.IsCohOn.of_isVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsVBOn T r V) :
    L.IsCohOn T := fun p hp => by
  obtain ⟨U, hU, b, -, hb⟩ := h p hp
  exact ⟨U, hU, r, b, fun q hq hqU => (hb q hq hqU).2⟩

theorem Lat.not_inFibre_of_coprime (p : Cpt ξ) {q q' : ℕ} (h : q.Coprime q') (h1 : InFibre ξ q p) :
    ¬ InFibre ξ q' p := by
  intro h2
  haveI := NormAt.isLocalRing_regAt p
  have key : ∀ n : ℕ, IsUnit (n : regAt ξ p) → unitAt ξ p (n : Ω) := by
    intro n hn
    obtain ⟨v, hv⟩ := hn.exists_right_inv
    have hv' : (n : Ω) * (v : Ω) = 1 := by simpa using congrArg Subtype.val hv
    refine ⟨left_ne_zero_of_mul_eq_one hv', natCast_mem _ n, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hv']
    exact v.2
  obtain ⟨a, b, e⟩ := (Nat.Coprime.cast (R := regAt ξ p) h)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one e with h' | h'
  · exact h1 (key _ (isUnit_of_mul_isUnit_right h'))
  · exact h2 (key _ (isUnit_of_mul_isUnit_right h'))

end API

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def LieModel.IsHTFormOver (M : LieModel G ξ E) (N : ℕ) {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)
    (k : R →+* Ω) (w : Module.Dual Ω E) : Prop :=
  ∃ (_ : IsDomain R) (T : Type) (_ : CommGroup T) (Γ : BT.QFGroup R T)
    (i : Γ.G.left ⟶ G.left) (L : Type) (_ : AddCommGroup L) (_ : Module R L)
    (M₀ : LieModel G x L) (j : L → E) (χ : T →* Rˣ) (w₀ : Module.Dual R L),
    Γ.IsTorsionAlong G x N i ∧ (∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left) ∧
      Γ.IsHT i M₀ N χ w₀ ∧ ∀ e, w (j e) = k (w₀ e)

def LieModel.IsHTFormAt (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) (w : Module.Dual Ω E) : Prop :=
  M.IsHTFormOver N (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) (genMap ξ p) w

def LieModel.htLat (M : LieModel G ξ E) (N : ℕ) : Lat ξ (Module.Dual Ω E) := fun p =>
  Submodule.span (regAt ξ p) {w | M.IsHTFormAt N p w}

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def genFibre (O : Type) [CommRing O] [Algebra O Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) :=
  {p | ∀ o : O, o ≠ 0 → unitAt ξ p (algebraMap O Ω o)}

def ConstClosed (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] : Prop :=
  ∀ a : Ω, IsAlgebraic O a → ∃ x y : O, y ≠ 0 ∧ a * algebraMap O Ω y = algebraMap O Ω x

def lineLat (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) : Lat ξ Ω := fun x =>
  Submodule.span (regAt ξ x) {t | ∃ f : Ω, IsCoeffAt A B p q a b x f ∧ t = f⁻¹}

def SplitModAt (A : Lat ξ E) (ϖ : Ω) {N : ℕ} (J : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))) (x y : Cpt ξ) : Prop :=
  (∀ w ∈ A y, ∀ k, J x w k ∈ regAt ξ y ∧ (J x w k - J y w k) / ϖ ∈ regAt ξ y) ∧
    ∃ R : (Fin N → Ω) →ₗ[Ω] E, (∀ k, R (Pi.single k 1) ∈ A y) ∧ ∀ w ∈ A y, ∃ w' ∈ A y, R (J x w) = w + ϖ • w'

def ExactModLat (A B : Lat ξ E) (ϖ : Ω) (N : ℕ) : Prop :=
  ∃ J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω)), ∀ x : Cpt ξ, ¬ unitAt ξ x ϖ → ∃ U : X.Opens, x.1 ∈ U ∧
    ∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → SplitModAt A ϖ J x y ∧ SplitModAt B ϖ J' x y ∧
      ∀ w ∈ A y, ∀ w' ∈ B y, dotProduct (J x w) (J' x w') / ϖ ∈ regAt ξ y

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K] {X : Scheme.{0}}

structure CurveIn (C : ACurve K) (ζ : Spec (CommRingCat.of K) ⟶ X) where

  x : ∀ i : C.I, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ x i = ζ
  ae : ∀ U : X.Opens, centre ζ ∈ U → {i | centre (x i) ∉ U}.Finite

variable {C : ACurve K} {ζ : Spec (CommRingCat.of K) ⟶ X}

def CurveIn.lieLat (Y : CurveIn C ζ) {G : Over X} [GrpObj G] {V : Type} [AddCommGroup V] [Module K V]
    (M : LieModel G ζ V) : C.I → AddSubgroup V := fun i =>
  AddSubgroup.closure {e | ∃ v : epsAt (Y.x i) ⟶ G, IsTanAt G (Y.x i) v ∧
    (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (C.v i).valuationSubring.subtype)) ≫ v.left}

def CurveIn.IsDeg (Y : CurveIn C ζ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω)
    (n : ℤ) : Prop :=
  ∃ (h₀ : genPt ξ ⤳ centre ζ) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (s₀ : Ω) (s : C.I → Ω) (r : C.I → K),
    Λ.IsGenAt ⟨centre ζ, h₀⟩ s₀ ∧ (∀ i, Λ.IsGenAt ⟨centre (Y.x i), h i⟩ (s i)) ∧
      (∀ i, r i ≠ 0 ∧ ValAt ξ ζ (s i / s₀) (r i)) ∧ {i | C.v i (r i) ≠ 1}.Finite ∧
      n = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (r i))

def coordDeg (C : ACurve K) {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → K)
    (a : B → ℤ) : ℤ :=
  ∑ k, a k * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (Finset.univ.sup fun c : ι k => C.v i (w ⟨k, c⟩))

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsGenericFlagSelf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem not_mem_flagStep {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (i : Fin r) :
    b i ∉ flagStep Ω b i := by
  exact hb.notMem_span_image (by simp)

theorem gr_isGenAt {r : ℕ} (L : Lat ξ E) (b b₀ : Fin r → E) (p : Cpt ξ) (hL : L.IsFrameAt b p)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) (c : Ω)
    (hc : b i - c • b₀ i ∈ flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨hb, hLp⟩ := hL
  have hbi : b i ∉ flagStep Ω b i := not_mem_flagStep b hb i
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hbi
    rw [hF]
    simpa using hc
  refine ⟨hc0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨e, he, het⟩
    rw [hLp] at he
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he
    have het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i := het
    set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS
    have hFS : flagStep Ω b₀ i ≤ S := by
      rw [← hF]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k, fun hki => ?_, rfl⟩
      subst hki
      exact lt_irrefl (k : ℕ) hk
    have h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S := S.smul_mem c (hFS het')
    have h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S :=
      S.smul_mem c (Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))
    have h3 : t • (b i - c • b₀ i) ∈ S := S.smul_mem t (hFS hc)
    have heq : (c * (d i : Ω) - t) • b i =
        c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k -
          t • (b i - c • b₀ i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      module
    have key : (c * (d i : Ω) - t) • b i ∈ S := by
      rw [heq]
      exact S.sub_mem (S.sub_mem h1 h2) h3
    have hzero : c * (d i : Ω) - t = 0 := by
      by_contra hne
      apply hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)
      have := S.smul_mem (c * (d i : Ω) - t)⁻¹ key
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    refine Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩
    show (d i : Ω) * c = t
    rw [mul_comm]
    exact sub_eq_zero.mp hzero
  · refine Submodule.span_le.mpr ?_
    rintro _ rfl
    refine Submodule.subset_span ⟨b i, ?_, hc⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem zpow_ratio (Λ : Lat ξ Ω) (p : Cpt ξ) (s t : Ω) (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) (n : ℤ) :
    (t / s) ^ n ∈ regAt ξ p := by
  obtain ⟨hs0, hsp⟩ := hs
  obtain ⟨ht0, htp⟩ := ht
  have h1 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hsp, htp]
    exact Submodule.mem_span_singleton_self t
  have h2 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← htp, hsp]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h2
  have hts : t / s = a := by
    rw [div_eq_iff hs0]
    exact ha.symm
  have hst : s / t = a' := by
    rw [div_eq_iff ht0]
    exact ha'.symm
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hts]
    exact pow_mem a.2 m
  · rw [zpow_negSucc, ← inv_pow, inv_div, hst]
    exact pow_mem a'.2 _

theorem tens_isGenAt {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨s', hs', rfl⟩
    have hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.FlagModel
end
end

