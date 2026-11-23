module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def FilA (a : ℤ) : AddSubgroup P.R.BdR := ((P.PD (botExt l)).Fil a).toAddSubgroup

theorem mem_Fil_iff (K : FinExt l) {a : ℤ} {x : P.R.BdR} : x ∈ Fil P a ↔ x ∈ (P.PD K).Fil a := by
  have := P.PD_Fil (botExt l) K a
  change x ∈ ((P.PD (botExt l)).Fil a : Set P.R.BdR) ↔ x ∈ ((P.PD K).Fil a : Set P.R.BdR)
  rw [this]

variable {P}

theorem Fil_zero_mem (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := (FilA P a).zero_mem
theorem Fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a := (FilA P a).add_mem hx hy
theorem Fil_neg {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : -x ∈ Fil P a := (FilA P a).neg_mem hx
theorem Fil_sum {a : ℤ} {ι : Type*} {s : Finset ι} {f : ι → P.R.BdR} (h : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a := (FilA P a).sum_mem h
theorem Fil_mul {a b : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy
theorem Fil_mul_left {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P 0) (hy : y ∈ Fil P a) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem Fil_mul_right {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P 0) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem one_mem_Fil : (1 : P.R.BdR) ∈ Fil P 0 := (P.PD (botExt l)).one_mem
theorem Fil_act (g : GQ l) {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at this

variable (P)

def S0 : Subring P.R.BdR where
  carrier := Fil P 0
  zero_mem' := Fil_zero_mem 0
  one_mem' := one_mem_Fil
  add_mem' := Fil_add
  neg_mem' := Fil_neg
  mul_mem' := Fil_mul_left

theorem mem_S0_of_sum_eq {x : P.R.BdR} : x ∈ S0 P ↔ x ∈ Fil P 0 := Iff.rfl

theorem om_mem_Fil (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  rw [mem_Fil_iff P (adjExt x)]
  have h := ((P.PD (adjExt x)).Fil 0).smul_mem ⟨x, mem_adjExt x⟩ (P.PD (adjExt x)).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact h

theorem kd_mem_Fil (c : ↥(MaximalUnramifiedExtension l)) : kd P c ∈ Fil P 0 := om_mem_Fil P _

theorem q_mem_Fil (q : ℚ_[l]) : algebraMap ℚ_[l] P.R.BdR q ∈ Fil P 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
  exact om_mem_Fil P _

theorem iota_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem iota_act (g : GQ l) (b : P.R.B) : P.ιB (P.actQ g b) = P.actQdR g (P.ιB b) := by
  have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rwa [P.PD_actB, P.PD_ι, P.PD_ι, P.PD_actdR] at this

theorem iota_kur (c : ↥(MaximalUnramifiedExtension l)) : P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P c := by
  have := (P.PD (adjExt (c : Om l))).ι.commutes ⟨c, mem_adjExt _, c.2⟩
  rw [P.PD_ι] at this
  exact this

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := rfl
theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  simp [fr, pow_add, AlgHom.mul_apply]
theorem fr_one (c : ↥(MaximalUnramifiedExtension l)) : fr l 1 c = frobUr l c := by simp [fr]
theorem fr_q (m : ℕ) (q : ℚ_[l]) : fr l m (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q :=
  (frobUr l ^ m).commutes q
theorem fr_comm {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l r (fr l m c) = fr l m c := by
  rw [← fr_add, add_comm, fr_add, h]
theorem fr_mul {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (k : ℕ) : fr l (r * k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, fr_add, h, ih]
theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l (m % r) c = fr l m c := by
  conv_rhs => rw [← Nat.mod_add_div m r, fr_add, fr_mul h]

theorem phi_iter_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, phiB_algebraMap, add_comm, fr_add, fr_one]

def evHom (m : ℕ) : P.R.B →+* P.R.BdR :=
  (P.ιB : P.R.B →+* P.R.BdR).comp ((P.φB ^ m : P.R.B →ₐ[ℚ_[l]] P.R.B) : P.R.B →+* P.R.B)

theorem evHom_apply (m : ℕ) (b : P.R.B) : evHom P m b = ev P m b := by
  simp [evHom, ev, AlgHom.coe_pow]

theorem ev_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P (fr l m c) := by
  rw [ev, phi_iter_kur, iota_kur]

theorem ev_act (m : ℕ) (g : GQ l) (b : P.R.B) : ev P m (P.actQ g b) = P.actQdR g (ev P m b) := by
  rw [ev, ev, ← iota_act]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]

theorem act_kd {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQdR (g : GQ l) (kd P c) = kd P c := by
  change P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c : Om l)
  rw [P.actQdR_Om, mem_GK.1 g.2 _ hc]

theorem act_kur {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c :=
  P.actQ_Kur _ c c (mem_GK.1 g.2 _ hc)

theorem act_ks {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    actSt P (g : GQ l) (ks P c) = ks P c := by
  change actSt P (g : GQ l) (Polynomial.C _) = Polynomial.C _
  rw [actSt_C, act_kur P g hc]

theorem tz_add (a b : ℤ) : tz P (a + b) = tz P a * tz P b := by simp [tz, zpow_add]
theorem tz_zero : tz P 0 = 1 := by simp [tz]
theorem tz_one : tz P 1 = P.ιB P.tB := by simp [tz]

theorem fund {b : P.R.B} (h : P.φB b = b) (h0 : P.ιB b ∈ Fil P 0) : ∃ c : ℚ_[l], algebraMap ℚ_[l] P.R.B c = b :=
  (P.PD (botExt l)).fund b (by rw [P.PD_φ, h]) (by rw [P.PD_ι]; exact h0)

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def SerLoc (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
    ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v

def TameOcc (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
    Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
    ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
      Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def InjPrimeTo {A B : Type} [MonoidWithZero A] [Monoid B] (l : ℕ) (ι : A →* B) : Prop :=
  ∀ x y : A, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y

abbrev labSig (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (k : Fin 2) (v : D.nd.PlG k) : (ZMod (D.host.g k))[X] :=
  D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameFixed (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
    ∃ φ : G D.host.E D.nd.Om,
      redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k

def TameAnyAt (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) (w : PlE D.host) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
    (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
      ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
        (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
          ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂

def FullLab (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), (labSig D Sig k v).natDegree =
    D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameSum (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → FullLab D Sig →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i Sig ρ k ∧
      ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i Sig ρ k w

def WildOne (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L

def FrobDense (D : D7) : Prop :=
  ∀ T : Set (PlE D.host), T.Finite → Dense {s : G D.host.E D.nd.Om | ∃ w : PlE D.host, w ∉ T ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) s}

def PointPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (π : D.naut.CG D.R.r), HasParamX D.nd D.naut i x [⟨D.R.r, π, 1⟩] →
    D.naut.csd π ∧ D.naut.ralg π

def RedVia (D : D7) (i : D.nd.Loc) (k : Fin 2)
    (ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i)) : Prop :=
  ∀ (p : (D.nd.O i)[X]) (s : Multiset (Fb (D.host.g k) (D.host.g_prime k))),
    p.map (iotaO D.nd D.naut i) = (s.map fun x => X - C (D.ntypes.teichC k x)).prod →
    p.map ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) = (s.map fun x => X - C (ι x)).prod

def TwistInv (D : D7) : Prop :=
  (∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π) ∧
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π

def CharLaws (D : D7) : Prop :=
  ∀ (w : PlE D.host) (a χ χ' : D.naut.LP w), D.naut.lpDim χ = 1 → D.naut.lpDim χ' = 1 →
    D.naut.lpChar (D.naut.lpChar a χ) χ' = D.naut.lpChar a (D.naut.lpChar χ χ') ∧
    D.naut.lpChar a (D.naut.lpUnr w {1}) = a

def MultOne (D : D7) : Prop :=
  ∀ (a : ℕ) (π π' : D.naut.CG a), 1 ≤ a → (∀ w, D.naut.locG π w = D.naut.locG π' w) → π = π'

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal

namespace GlobalTheory.TwSys

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsTameInertiaElementAtTwistPrime (i : X.Tw) (z : GE N) : Prop :=
  ∃ v ∈ X.pD i, ∃ A : ValuationSubring N.Om, IsPlaceOver A v ∧ z ∈ Ine (F := D.host.E) A ∧
    IsUnit (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) ∧
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal →
      ∃ n : ℕ, Nat.Coprime n (X.l i * Ideal.absNorm v.asIdeal) ∧ z ^ n ∈ U

def Over (P v : PlE D.host) : Prop := v = P ∨ IsConjPl D.host P v

def GoodChar (i : X.Tw) (M : ℕ) (P : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) : Prop :=
  IsOpen (d.ker : Set (GE N)) ∧ AntiHom X.cc d ∧ TrivAbove d (X.l i) ∧
    (∀ v, ¬ Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, d σ = 1) ∧
    (∀ v, Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := D.host.E) A, d σ = c)

def AdmFam (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  IsOpen (H : Set (GE N)) ∧ H.Normal ∧
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) ∧
    ∀ P, P ∉ S → IsSplitPl D.host P → DecV N P ≤ H → GoodChar X i M P (d P)

def SlopeTestRemainingChoices (i : X.Tw) (M : ℕ) (A : Finset (PlE D.host)) {ι : Type} (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ q v, Over (P q) v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % (2 * X.l i ^ M) = 1) ∧
    (∀ q q', Over (P q) (P q') → q = q') ∧ ∀ q, GoodChar X i M (P q) (d q)

def Steps (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (z : GE N) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ a (σ : GE N), IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ H) ∧
    ∀ a b (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (.inl b) σ = Multiplicative.ofAdd (if a = b then 1 else 0)

def IsQ {ι : Type} (P : ι → PlE D.host) (Q : Finset (PlE D.host)) : Prop := ∀ v, v ∈ Q ↔ ∃ q, Over (P q) v

abbrev Del (i : X.Tw) (M : ℕ) (ι : Type) : Type := Multiplicative (ι → ZMod (X.l i ^ M))

abbrev abelian₂ (i : X.Tw) (M : ℕ) (ι : Type) : Type := MonoidAlgebra (X.O0 i) (Del X i M ι)

def delAll (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* Del X i M ι where
  toFun g := Multiplicative.ofAdd fun q => Multiplicative.toAdd (d q g)
  map_one' := by simp; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl


open Classical in
def toLam (i : X.Tw) (M : ℕ) (ι : Type) : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] abelian₂ X i M ι :=
  MvPolynomial.aeval fun q => MonoidAlgebra.of (X.O0 i) (Del X i M ι) (Multiplicative.ofAdd (Pi.single q 1)) - 1

def repOn {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O) (κ : G →* Λˣ)
    (B : Type) [AddCommGroup B] [Module Λ B] : Representation Λ G (Fin r → B) where
  toFun g := ((κ g : Λˣ) : Λ) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))
  map_one' := by simp [matAct_one]
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul, matAct_mul]
    rw [smul_mul_smul_comm]

variable {X} (bkP : BKPh X)


open Classical in
def bkOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (v : PlE D.host) : Submodule Λ (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span Λ {x | ∃ (z : Z1 ((repOn ρ κ B).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin r → X.O0 i) (b : B),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) ∧
      (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin r → B) g a = algebraMap (X.O0 i) Λ (y g a) • b) ∧
      x = Submodule.Quotient.mk z}
  else ⊥

def selOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (Q : Finset (PlE D.host)) : Submodule Λ (H1 (repOn ρ κ B)) :=
  Formalism.GaloisCohomology.SelAll (repOn ρ κ B) N.plOm
    (Formalism.GaloisCohomology.bkCond (repOn ρ κ B) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ B))

def delInv (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* (abelian₂ X i M ι)ˣ :=
  ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits.comp (delAll X i M d))⁻¹

def Computes (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) : Prop :=
  ∃ e : ∀ (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B],
      (∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) →
      (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[abelian₂ X i M ι] ↥(selOn bkP i (Tgl i s) (delInv i M d) B Q)),
    ∀ (B B' : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module (abelian₂ X i M ι) B'] [TopologicalSpace B'] [DiscreteTopology B']
      (hB : ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) (hB' : ∀ b : B', ∃ n : ℕ, (X.l i ^ n) • b = 0)
      (f : B →ₗ[abelian₂ X i M ι] B') (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ)))
      (z : Z1 (repOn (Tgl i s) (delInv i M d) B)) (z' : Z1 (repOn (Tgl i s) (delInv i M d) B')),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e B hB x).1 = Submodule.Quotient.mk z → (e B' hB' x').1 = Submodule.Quotient.mk z'

def valE (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) : ℝ≥0∞ :=
  ((IsDiscreteValuationRing.addVal R x : ℕ∞) : ℝ≥0∞) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ≥0∞)

def SelPoly (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (F : MvPolynomial ι (X.O0 i)) : Prop :=
  ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ) (ψ : GE N →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
    (∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
    sLen bkP i s k Q ψ =
      valE (X.Ok i k) (X.l i) (MvPolynomial.eval₂ (phiK X i k) (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) F)

def GalHyp (i : X.Tw) (s : X.Sig i) : Prop :=
  IsotypicValuationAtRing bkP i s ∧ ValuationStabilityAtRing X i s ∧ SelfDual i s ∧ NoJump bkP i s ∧ True ∧ Gen.adm3 D ∧ 100 ≤ D.R.r

end GlobalTheory.TwSys

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
section
noncomputable section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {D : D7} (i : D.nd.Loc)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
def lenCob {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(C ⊓ (ReciprocityTheory.Gal.B1 (WKG M) : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
def InCut (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (f : GE D.nd → KOG (D.nd.O i) k) : Prop :=
  locFun i M w hw f ∈ Submodule.span (Br.OLL D.nbr i w hw) (GlobalTheory.Pass.cutCoc i w hw r Xs M)

end GlobalTheory.Cut

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatKOSmulOne
section
noncomputable section

namespace GlobalTheory.Cut.Check

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Mat
variable {O : Type} [CommRing O] [IsDomain O] {k : ℕ}

theorem matKO_mk (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

theorem matKO_smul_one (a : O) (x : KOG O k) :
    matKO (a • (1 : Matrix (Fin k) (Fin k) O)) x = a • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [matKO_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    funext j
    have : ∀ x, (a • (1 : Matrix (Fin k) (Fin k) O)) j x = if j = x then a else 0 := fun x => by
      simp [Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, this, Pi.smul_apply]
    simp [apply_ite, Algebra.smul_def]

theorem WKG_eq_matKO {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = matKO (M g) x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl
end Mat

variable {D : D7} (i : D.nd.Loc)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, by funext x; simp⟩

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem cocW_quad {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {v} (hq : QuadAt i r Xs v)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    matKO (ψ fun x' => rO D.nd i r (S.p x') γ) (c γ) = c γ := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, h0, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') γ :=
      ⟨1, fun _ => 1, fun _ => γ, fun _ => one_mem _, by funext x; simp⟩
    have hn : InR' D.nd r S (-1) :=
      ⟨1, fun _ => -1, fun _ => 1, fun _ => neg_mem (one_mem _), by funext x; simp⟩
    have hY : InY D.nd r S ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) :=
      ⟨2, ![fun x' => rO D.nd i r (S.p x') γ, -1], fun _ => γ,
        fun j => by fin_cases j; exacts [hg, hn], by simp [Fin.sum_univ_two, sub_eq_add_neg]⟩
    have := h0 _ hY fun x' hx => by
      have hq' := hq _ hx γ hγ
      have e : ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) x' =
          (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • (((rO D.nd i r (S.p x') γ - 1) *
            (rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i))) *
              Eel D.nd S x') := by
        simp only [yg, Pi.sub_apply, Pi.mul_apply, mul_sub, sub_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
          smul_smul, Units.inv_mul, one_smul, mul_assoc, one_mul, mul_one]
        abel
      rw [e, hq']; simp
    rw [map_sub, sub_eq_zero, h1 _ hg _ (inY_yg i r S γ)] at this
    exact this
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add (f := _)]
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul]

end GlobalTheory.Cut.Check

end
end

