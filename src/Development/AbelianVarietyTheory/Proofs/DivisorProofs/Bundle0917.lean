module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.HeckeLabels

section Abstract

theorem forall_exists_transfer {X X' Z Z' : Type} {L : X → Prop} {L' : X' → Prop} {I : Z → Prop} {I' : Z' → Prop}
    (p : X → X') (q : Z → Z') (p1 : ∀ y, L y → L' (p y)) (p2 : ∀ y', L' y' → ∃ y, L y ∧ p y = y')
    (q1 : ∀ z, I z → I' (q z)) (q2 : ∀ z', I' z' → ∃ z, I z ∧ q z = z') {P : X → Z → Prop} {P' : X' → Z' → Prop}
    (h : ∀ y z, P y z ↔ P' (p y) (q z)) :
    (∀ y, L y → ∃ z, I z ∧ P y z) ↔ ∀ y', L' y' → ∃ z', I' z' ∧ P' y' z' := by
  constructor
  · intro H y' hy'
    obtain ⟨y, hy, rfl⟩ := p2 y' hy'
    obtain ⟨z, hz, e⟩ := H y hy
    exact ⟨q z, q1 z hz, (h y z).1 e⟩
  · intro H y hy
    obtain ⟨z', hz', e⟩ := H _ (p1 y hy)
    obtain ⟨z, hz, rfl⟩ := q2 z' hz'
    exact ⟨z, hz, (h y z).2 e⟩

variable {R : Type} [CommRing R] {n : ℕ}

def StdDiv (O : Subring R) (ε : R) (t : Fin n → R) (m : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∀ i, (ε • B *ᵥ z) i ∈ O) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • y = ε • B *ᵥ z) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z)) ∧
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∃ y : Fin n → R, (∀ i, y i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z))

theorem conj_mem_UJ (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ σ J) :
    h⁻¹ * g * h ∈ Formalism.UG.UJ σ J' := by
  have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
  show Formalism.UG.cT σ (h⁻¹ * g * h).1 * J' * (h⁻¹ * g * h).1 = J'
  have e : h.1 * (h⁻¹ * g * h).1 = g.1 * h.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹ * g * h).1) * J * (h.1 * (h⁻¹ * g * h).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ h.1 * (Formalism.UG.cT σ g.1 * J * g.1) * h.1 := by
        rw [e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg', hh]

theorem inv_frame (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') : Formalism.UG.cT σ (h⁻¹).1 * J' * (h⁻¹).1 = J := by
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹).1) * J * (h.1 * (h⁻¹).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_reps {G : Type} [Group G] {K : Subgroup G} {g : G}
    (hK : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) :
    ∃ R : Finset G, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Yt3.exists_reps hK

theorem relIndex_conj_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J U L : Subgroup G}
    (hJ : IsCompact (J : Set G)) (hU : IsOpen (U : Set G)) (hL : ∀ k ∈ L, k ∈ U → k ∈ J) {g : G} (hg : g ∈ L) :
    ((J ⊓ L).map (MulAut.conj g).toMonoidHom).relIndex (J ⊓ L) ≠ 0 := by
  let U' : Subgroup G := U.comap (MulAut.conj g⁻¹).toMonoidHom
  have hU' : IsOpen (U' : Set G) := hU.preimage (show Continuous fun u : G => g⁻¹ * u * g⁻¹⁻¹ by fun_prop)
  have : CompactSpace J := isCompact_iff_compactSpace.1 hJ
  have h1 : U'.relIndex J ≠ 0 := by
    have : Finite (J ⧸ U'.subgroupOf J) :=
      Subgroup.quotient_finite_of_isOpen _ (hU'.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  have h2 : U'.relIndex (J ⊓ L) ≠ 0 := fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  rw [← Subgroup.inf_relIndex_right] at h2
  refine fun h => h2 (Subgroup.relIndex_eq_zero_of_le_left ?_ h)
  rintro k ⟨hk, hk'⟩
  have h3 : g⁻¹ * k * g⁻¹⁻¹ ∈ L := mul_mem (mul_mem (inv_mem hg) hk'.2) (inv_mem (inv_mem hg))
  exact ⟨g⁻¹ * k * g⁻¹⁻¹, ⟨hL _ h3 hk, h3⟩, by simp [mul_assoc]⟩

end Abstract

section Place

open GlobalTheory.PlaceComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : CMData F E) (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}

theorem divG_iff {e : AF F ⊗[F] E} (he : ∀ w, w ≠ v → evF E w (finP F E e) = 0)
    {h : GL (Fin V.rank) (Fv F v ⊗[F] E)} (hh : IsFrameAt V v h) (ϖ : E) (d : Fin V.rank → ℤ)
    (g : HA (AF F) hc.sig V.gram) :
    DivG hc V e ϖ d g ↔ StdDiv (ordAt E v) (evF E v (finP F E e)) (fun i => inclR (Fv F v) (ϖ ^ d i))
      (h⁻¹ * locMat hc V v g * h).1 := by
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1 *ᵥ ((h⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1 *ᵥ (h.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let q : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun z i => evF E v (z i)
  let p : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun y => (h⁻¹).1 *ᵥ q y
  have p1 : ∀ y, y ∈ lamHat F V → ∀ i, p y i ∈ ordAt E v := fun y hy => (hh _).1 ((mem_lamHat_iff V _).1 hy v)
  have p2 : ∀ y' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y' i ∈ ordAt E v) → ∃ y, y ∈ lamHat F V ∧ p y = y' :=
    fun y' hy' => ⟨_, GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hh (h.1 *ᵥ y')).2 (by rwa [hback'])), by
      simp only [p, q, evF_sgT_self]; exact hback' y'⟩
  have q1 : ∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∀ i, q z i ∈ ordAt E v :=
    fun z hz i => (IntLocal.mem_intA_iff F E _).1 (hz i) v
  have q2 : ∀ z' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, z' i ∈ ordAt E v) →
      ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧ q z = z' :=
    fun z' hz' => ⟨_, fun i => GlobalTheory.PlaceDiv.sgT_mem_intA v (hz' i), funext fun i => evF_sgT_self v _⟩
  have qv : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z, q (A *ᵥ z) = A.map (evF E v) *ᵥ q z :=
    fun A z => funext fun i => RingHom.map_mulVec (evF E v) A z i
  have qe : ∀ X, q (fun a => finP F E e * X a) = evF E v (finP F E e) • q X :=
    fun X => funext fun i => map_mul (evF E v) _ _
  have key : ∀ X Y : Fin V.rank → Af F ⊗[F] E, ((fun a => finP F E e * X a) = fun a => finP F E e * Y a) ↔
      evF E v (finP F E e) • p X = evF E v (finP F E e) • p Y := by
    intro X Y
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨fun H => by rw [H], fun H => funext fun a => evF_ext fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      have := congrArg (h.1 *ᵥ ·) H
      simp only [hback] at this
      exact congrFun this a
    · rw [map_mul, map_mul, he w hw, zero_mul, zero_mul]
  have pB : ∀ (B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z,
      p (B *ᵥ z) = ((h⁻¹).1 * B.map (evF E v)) *ᵥ q z := fun B z => by
    simp only [p, qv, Matrix.mulVec_mulVec]
  have pg : ∀ y, p (finMat hc.sig V.gram g *ᵥ y) = (h⁻¹ * locMat hc V v g * h).1 *ᵥ p y := fun y => by
    simp only [p, qv, Units.val_mul, ← Matrix.mulVec_mulVec, hback, locMat_val]
  have qt : ∀ z : Fin V.rank → Af F ⊗[F] E, q (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) =
      (fun i => inclR (Fv F v) (ϖ ^ d i)) * q z := fun z => funext fun i => by
    show evF E v _ = _ * evF E v _
    rw [map_mul, evF_finP_incl]
  have c1 : ∀ X : Fin V.rank → Af F ⊗[F] E, (fun a => finP F E e * X a) ∈ lamHat F V ↔
      ∀ i, (evF E v (finP F E e) • p X) i ∈ ordAt E v := by
    intro X
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨p1 _, fun H => (mem_lamHat_iff V _).2 fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      exact (hh _).2 H
    · simp only [map_mul, he w hw, zero_mul]
      exact zero_mem _
  have sB : ∀ B' : Matrix (Fin V.rank) (Fin V.rank) (Fv F v ⊗[F] E),
      ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E), (h⁻¹).1 * B.map (evF E v) = B' := fun B' => by
    refine ⟨(h.1 * B').map (sgT E v), ?_⟩
    have : ((h.1 * B').map (sgT E v)).map (evF E v) = h.1 * B' := Matrix.ext fun i j => evF_sgT_self v _
    rw [this, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold DivG StdDiv
  rw [Function.Surjective.exists sB]
  refine exists_congr fun B => and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro H z' hz'
      obtain ⟨z, hz, rfl⟩ := q2 z' hz'
      rw [← pB, ← c1]
      exact H z hz
    · intro H z hz
      rw [c1, pB]
      exact H _ (q1 z hz)
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pB]
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pg, pB, qt]
  · exact forall_exists_transfer q p q1 q2 p1 p2 fun z y => by rw [key, pg, pB, qt]

end Place

section CM

open GlobalTheory.PlaceComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_div_iff (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    {e f : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (hf : IsIdemOf E v f) (hef : e * f = e)
    (ϖ : E) (d : ℕ → ℤ) {n : ℕ} (hn : V.rank = n) :
    (∃ g, Supp hc V f g ∧ DivG hc V e ϖ (fun i => d i.1) g) ↔
      ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
        StdDiv (ordAt E v) (evF E v (finP _ E e)) (fun i => inclR (Fv _ v) (ϖ ^ d i.1)) u.1 := by
  subst hn
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  have he : ∀ w, w ≠ v → evF E w (finP _ E e) = 0 := fun w hw => by
    rw [← hef, map_mul, map_mul, hf.2.2 w hw, mul_zero]
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨_, conj_mem_UJ _ hon (locMat_mem hc V v g), (divG_iff hc V he hfr ϖ _ g).1 hg⟩
  · rintro ⟨u, hu, hd⟩
    obtain ⟨g, hg, e1⟩ := (GlobalTheory.SuppLocal.supp_local _ E hc V v f hf).2.2 _ (conj_mem_UJ _ (inv_frame _ hon) hu)
    refine ⟨g, hg, (divG_iff hc V he hfr ϖ _ g).2 ?_⟩
    have : h⁻¹ * locMat hc V v g * h = u := by rw [e1]; group
    rwa [this]

end CM

section Host

open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Host

end GlobalTheory.HeckeLabels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

variable {p : ℕ} [Fact p.Prime]

def InT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β y : G.C) (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R (z.1 : R ⊗[ℚ] G.C)).unop =
      algebraMap R (R ⊗[ℚ] G.C) (z.2 : R) * inC G R β ∧
    Commute (z.1 : R ⊗[ℚ] G.C) (inC G R y)

def psiAway (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
  (MulAut.conj x).toMonoidHom.prodMap (MonoidHom.id _)

def psiP (G : HTGroup p) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ →* Gr G 1 :=
  (inclG G 1).comp ((MonoidHom.snd _ _).prod (Pi.monoidHom fun w =>
    (Units.map ((G.locW w).toRingHom.toMonoidHom)).comp (MonoidHom.fst _ _)))

@[simp] theorem psiAway_apply (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :
    psiAway G x z = (x * z.1 * x⁻¹, z.2) := rfl

def dg (D : Type) [Ring D] [Algebra ℚ D] (p : ℕ) [Fact p.Prime] :
    Dˣ × ℚˣ →* ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
  ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] AfP p ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).prod
    ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] ℚ_[p] ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom))

theorem toAfF_eq_psiAway (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) :
    ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x ((dg G.C p (y : G.Cˣ × ℚˣ)).1) := rfl

theorem formGroupToPadicPointsDegreeOne_eq_unitaryPoints (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    toP1 G β y = psiP G ((dg G.C p (y : G.Cˣ × ℚˣ)).2) := by
  simp only [toP1, psiP, MonoidHom.comp_apply]
  congr 1
  refine Prod.ext rfl (funext fun w => Units.ext ?_)
  change G.rho w _ = G.locW w ((1 : ℚ_[p]) ⊗ₜ _)
  change _ = (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (1 : ℚ_[p])) * (G.rho w).toRatAlgHom _
  rw [map_one, one_mul]
  rfl

theorem form_mul_inv {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β : D) (a e : Dˣ) (α η : ℚˣ)
    (ha : (a : D) * β * (σ a).unop = algebraMap ℚ D α * β) (he : (e : D) * β * (σ e).unop = algebraMap ℚ D η * β) :
    ((a * e⁻¹ : Dˣ) : D) * β * (σ ((a * e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((α * η⁻¹ : ℚˣ) : ℚ) * β := by
  have hs : (σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hs' : (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (e : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have hη : algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ D (η : ℚ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have key : ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * β := by
    calc ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop
        = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * (((e⁻¹ : Dˣ) : D) * (algebraMap ℚ D (η : ℚ) * β) *
            (σ ((e⁻¹ : Dˣ) : D)).unop) := by
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul]
          rw [show (η : ℚ) * ((η⁻¹ : ℚˣ) : ℚ) = 1 by simp, one_smul]
      _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((((e⁻¹ : Dˣ) : D) * e) * β *
            ((σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop)) := by
          rw [← he]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs, one_mul, mul_one]
  have hsm : (σ ((a * e⁻¹ : Dˣ) : D)).unop = (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  rw [hsm, Units.val_mul, Units.val_mul, map_mul]
  calc (a : D) * ((e⁻¹ : Dˣ) : D) * β * ((σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop)
      = (a : D) * (((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop) * (σ (a : D)).unop := by
        simp only [mul_assoc]
    _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((a : D) * β * (σ (a : D)).unop) := by
        rw [key, ← mul_assoc (a : D), ← Algebra.commutes ((η⁻¹ : ℚˣ) : ℚ) (a : D)]; simp only [mul_assoc]
    _ = _ := by
        rw [ha, ← mul_assoc, ← map_mul, mul_comm ((η⁻¹ : ℚˣ) : ℚ), map_mul]

theorem conj_back {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x g : Sˣ)
    (t c : A) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hg : (g : S) * (σ g).unop = algebraMap A S c) :
    ((x⁻¹ * g * x : Sˣ) : S) * b * (σ ((x⁻¹ * g * x : Sˣ) : S)).unop = algebraMap A S c * b := by
  have h1 : (σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = algebraMap A S t * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ (x : S)).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by rw [hx, ← Algebra.commutes, mul_assoc]
  have hσ : (σ ((x⁻¹ * g * x : Sˣ) : S)).unop =
      (σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop := by
    simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [hσ]
  calc ((x⁻¹ * g * x : Sˣ) : S) * b * ((σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)
      = ((x⁻¹ : Sˣ) : S) * ((g : S) * ((x : S) * b * (σ (x : S)).unop) * (σ (g : S)).unop) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = ((x⁻¹ : Sˣ) : S) * (algebraMap A S t * ((g : S) * (σ (g : S)).unop)) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        rw [hx, ← Algebra.commutes t (g : S)]; simp only [mul_assoc]
    _ = algebraMap A S (c * t) * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
        rw [hg, ← map_mul, ← Algebra.commutes, mul_assoc, mul_comm t c]
    _ = algebraMap A S c * b := by rw [hb, map_mul, mul_assoc]

theorem inT_psiAway_inv_of_commute : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y₀ : grp G β) (c : G.GAf), c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c →
    InT G (AfP p) β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (psiAway G x⁻¹ (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
  intro p _ G β x t hx y₀ c hc
  have hxx : ((x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) = x := inv_inv x
  refine ⟨?_, ?_⟩
  · have hg : (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (starT G.star (AfP p) (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
          AfP p ⊗[ℚ] G.C)).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) := c.2
    have h := conj_back (starT G.star (AfP p)) (inC G (AfP p) β) x _ (t : AfP p) _ hx hg
    simp only [psiAway_apply, hxx]
    exact h
  · have hU := congrArg (fun g : G.GAf => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)) hc
    simp only [Subgroup.coe_mul, Prod.fst_mul] at hU
    rw [toAfF_eq_psiAway, psiAway_apply] at hU
    simp only [psiAway_apply, hxx]
    set c1 := (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    set Y := (dg G.C p (y₀ : G.Cˣ × ℚˣ)).1.1
    have hUU : (x⁻¹ * c1 * x) * Y = Y * (x⁻¹ * c1 * x) := by
      calc (x⁻¹ * c1 * x) * Y = x⁻¹ * (c1 * (x * Y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * Y * x⁻¹) * c1) * x := by rw [hU]
        _ = Y * (x⁻¹ * c1 * x) := by group
    exact congrArg Units.val hUU

end GlobalTheory.TorCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalCharacterIdealPowers
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

theorem continuous_gAf_fst (G : HTGroup p) :
    @Continuous G.GAf (AfP p ⊗[ℚ] G.C) _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C))
      (fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_gAf_snd_inv (G : HTGroup p) :
    Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

theorem exists_compact_of_isTest (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (h₁ : G.GAf) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f (h₁⁻¹ * g * h₁) ≠ 0 → g ∈ Q := by
  obtain ⟨S, hS⟩ := hf.2.2.2
  have hK : IsCompact (L.K : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => h₁ * (q.1 * s * q.2) * h₁⁻¹) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ := hS _ hg
  refine Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, ?_⟩
  show h₁ * (k₁ * s * k₂) * h₁⁻¹ = g
  rw [← he]; group

theorem exists_compact_toAfF : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (h₁ : G.GAf), ∃ (Ω : Set (AfP p ⊗[ℚ] G.C)) (Ω' : Set (AfP p)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) Ω ∧ IsCompact Ω' ∧ ∀ y : grp G β,
    f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ Ω ∧
    algebraMap ℚ (AfP p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹) ∈ Ω' := by
  intro p _ G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  obtain ⟨Q, hQ, hmem⟩ := exists_compact_of_isTest G L f hf h₁
  refine ⟨(fun g : G.GAf => ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * x) '' Q,
    (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) '' Q,
    hQ.image ((continuous_const.mul (continuous_gAf_fst G)).mul continuous_const),
    hQ.image (continuous_gAf_snd_inv G), fun y hy => ⟨⟨_, hmem _ hy, ?_⟩, ⟨_, hmem _ hy, ?_⟩⟩⟩
  · show ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      ((x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
        AfP p ⊗[ℚ] G.C) * x = _
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  · show (((Units.map (algebraMap ℚ (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).2))⁻¹ : (AfP p)ˣ) : AfP p) = _
    rw [← map_inv, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomials
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem eval₂_expand {Rg S : Type} [CommRing Rg] [CommRing S] (mA mB : ℕ)
    (ψ : MvPolynomial (Fin (mA * mB)) Rg →+* S) (β : Fin mA → S) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial.eval₂Hom (ψ.comp MvPolynomial.C)
        (fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * β i) F =
      MvPolynomial.eval₂Hom ψ β (expand mA mB F) := by
  rw [expand, ← MvPolynomial.coe_eval₂Hom (MvPolynomial.C.comp MvPolynomial.C), ← RingHom.comp_apply,
    MvPolynomial.comp_eval₂Hom]
  congr 1
  ext r <;> simp

theorem expand_isHomogeneous {Rg : Type} [CommRing Rg] (mA mB : ℕ) {F : MvPolynomial (Fin mB) Rg} {d : ℕ}
    (hF : F.IsHomogeneous d) : (expand mA mB F).IsHomogeneous d := by
  have h := hF.eval₂ (τ := Fin mA)
    (MvPolynomial.C.comp MvPolynomial.C : Rg →+* MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg))
    (fun j => ∑ i : Fin mA, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i)
    (fun r => MvPolynomial.isHomogeneous_C _ _)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [expand] using h

theorem germ_eval_comb : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  intro Rg _ A₀ T X f N mA mB a g φ p _ d F hF z q hq
  have hT : p z ∈ (⊤ : T.Opens) := trivial
  let ψ : MvPolynomial (Fin (mA * mB)) Rg →+* X.presheaf.stalk z :=
    (MapIff.gsH p z ⊤ hT).comp (ringOf g)
  have hC : ψ.comp MvPolynomial.C = gc (p ≫ g ≫ affπ Rg (mA * mB)) z := by
    ext r
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg (mA * mB)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [ψ, RingHom.comp_apply, ringOf, gc, MapIff.gsH, RingHom.coe_comp, Function.comp_apply]
    rw [n2, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    rfl
  have hcomb : comb a φ p (matOf g) z q =
      fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * gs φ z (N.U q) ((a i).f q) := by
    funext j
    simp only [comb, ψ, RingHom.comp_apply, ringOf_X, matOf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MapIff.gsH_apply]
  rw [← hC, hcomb, eval₂_expand, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hd : ∑ i, ν i = d := by
    have := expand_isHomogeneous mA mB hF (MvPolynomial.mem_support_iff.1 hν)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  have hp : gs φ z (N.U q) (∏ i, (a i).f q ^ ν i) = ∏ i, gs φ z (N.U q) ((a i).f q) ^ ν i := by
    rw [← MapIff.gsH_apply φ z _ hq, map_prod]
    simp only [map_pow, MapIff.gsH_apply]
  simp only [ψ, RingHom.comp_apply, monSec, if_pos hd]
  rw [MapIff.gsH_apply]
  exact congrArg (fun x => gs p z ⊤ (ringOf g (AddMonoidAlgebra.coeff (expand mA mB F) ν)) * x) hp.symm

end GlobalTheory.FormsLocus
end
end

