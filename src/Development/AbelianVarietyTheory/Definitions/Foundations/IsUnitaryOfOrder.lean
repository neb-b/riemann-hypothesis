module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002

@[expose] public section

noncomputable section
section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

def hcharSub : Subgroup (Ideles L →* ℂˣ) where
  carrier := {χ | Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1}
  one_mem' := ⟨continuous_const, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun k => by
    rw [MonoidHom.mul_apply, ha.2 k, hb.2 k, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨ha.1.inv, fun k => by rw [MonoidHom.inv_apply, ha.2 k, inv_one]⟩

abbrev HChar : Type := ↥(hcharSub L)

variable {L}

def atFin (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* (v.adicCompletion L)ˣ :=
  Units.map (algebraMap L (v.adicCompletion L)).toMonoidHom

def atInf (w : InfinitePlace L) : Lˣ →* (w.Completion)ˣ :=
  Units.map (algebraMap L w.Completion).toMonoidHom

def IsUnitAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = 1

def IsUnifAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = WithZero.exp (-1 : ℤ)

def ordF (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ℤ := -WithZero.log (v.valuation L (k : L))

def infDiag : Lˣ →* Ideles L := ∏ w : InfinitePlace L, (infIdele L w).comp (atInf w)

theorem exists_unif (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ, IsUnifAt v (atFin v k) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π h0, ?_⟩
  show Valued.v ((π : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

def unif (v : HeightOneSpectrum (𝓞 L)) : Lˣ := Classical.choose (exists_unif v)

theorem unif_spec (v : HeightOneSpectrum (𝓞 L)) : IsUnifAt v (atFin v (unif v)) :=
  Classical.choose_spec (exists_unif v)

namespace HChar

variable (χ : HChar L)

def loc (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* ℂˣ := χ.1.comp (localIdele L v)

def locInf (w : InfinitePlace L) : (w.Completion)ˣ →* ℂˣ := χ.1.comp (infIdele L w)

def locK (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* ℂˣ := (χ.loc v).comp (atFin v)

def inf : Lˣ →* ℂˣ := χ.1.comp infDiag

def LevelLe (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x →
    Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ.loc v x = 1

def UnrAt (v : HeightOneSpectrum (𝓞 L)) : Prop := ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ.loc v x = 1

def TameAt (v : HeightOneSpectrum (𝓞 L)) : Prop := χ.LevelLe v 1

def val (v : HeightOneSpectrum (𝓞 L)) : ℂˣ := χ.locK v (unif v)

def valTw (s : ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  (χ.val v : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))

def IsUnitary : Prop := ∀ x : Ideles L, ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1

def OrderDvd (n : ℕ) : Prop := χ ^ n = 1

def HasInf {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

def HasInfQ {I : Type} [Fintype I] (φ : I → L →+* ℂ) (a : I → ℚ) : Prop :=
  ∃ n : I → ℤ, (∀ i, (n i : ℚ) = 2 * a i) ∧ χ.HasInf φ n

def IsAbsPow (s : ℝ) : Prop :=
  (∀ v, χ.UnrAt v) ∧ (∀ v, ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ∧
    ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)

def ProductRule : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 L)), (∀ v, v ∉ S → χ.UnrAt v) → ∀ k : Lˣ,
    χ.inf k * (∏ v ∈ S, χ.locK v k) * (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1

@[simp] theorem val_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ * χ').val v = χ.val v * χ'.val v := rfl
@[simp] theorem val_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ⁻¹).val v = (χ.val v)⁻¹ := rfl
@[simp] theorem inf_mul (χ χ' : HChar L) (k : Lˣ) : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
@[simp] theorem inf_inv (χ : HChar L) (k : Lˣ) : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl

end HChar

section Res

variable (F : Type) [Field F] [NumberField F] [Algebra F L]

theorem finite_aboveF (v : HeightOneSpectrum (𝓞 F)) :
    {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 F) = v}.Finite := by
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
  refine (hfin.preimage (f := HeightOneSpectrum.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro P rfl
  exact ⟨P.isPrime, ⟨rfl⟩⟩

def aboveF (v : HeightOneSpectrum (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 L)) := (finite_aboveF F v).toFinset


open Classical in
def aboveInf (w : InfinitePlace F) : Finset (InfinitePlace L) :=
  Finset.univ.filter fun w' => w'.comap (algebraMap F L) = w

def upF : Fˣ →* Lˣ := Units.map (algebraMap F L).toMonoidHom

variable {F}

def HChar.resFin (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* ℂˣ :=
  ∏ P ∈ aboveF (L := L) F v, (χ.locK P).comp (upF F)

def HChar.resInf (χ : HChar L) (w : InfinitePlace F) : Fˣ →* ℂˣ :=
  ∏ w' ∈ aboveInf (L := L) F w, ((χ.locInf w').comp (atInf w')).comp (upF F)

variable (F)

def HChar.TrivOn (χ : HChar L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), χ.resFin v k = 1) ∧ ∀ (w : InfinitePlace F) (k : Fˣ), χ.resInf w k = 1

def etaFin (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : ℂˣ :=
  if (aboveF (L := L) F v).card = 1 then (-1) ^ ordF v k else 1

def etaInf (w : InfinitePlace F) (k : Fˣ) : ℂˣ := if (w.embedding (k : F)).re < 0 then -1 else 1

def HChar.ResEta (χ : HChar L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), χ.resFin v k = etaFin (L := L) F v k) ∧
    ∀ (w : InfinitePlace F) (k : Fˣ), χ.resInf w k = etaInf F w k

end Res

end GlobalTheory.Mem.Chr

end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def embPsi (g : R.Psi) : H.E →+* ℂ := H.emb (g : R.GG)

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

def etaAlg (χ : HChar H.E) (v : HeightOneSpectrum (𝓞 H.E)) : ℂ := χ.valTw (1 / 2) v

def EtaTExists : Prop := ∃ χ : HChar H.E, IsEtaT H χ

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : Formalism.BasicNotions.Host R} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -e τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹

def Mu0Exists (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) : Prop := ∃ χ : HChar H.E, IsMu0 P W e j χ

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

def DeltaExists (p : ℕ) : Prop := ∃ χ : HChar H.E, IsDelta (H := H) p χ

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

end GlobalTheory.Mem.Chr

end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

namespace HChar

theorem resFin_apply (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    χ.resFin v k = ∏ P ∈ aboveF (L := L) F v, χ.locK P (upF F k) := by
  simp [HChar.resFin]

theorem resInf_apply (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    χ.resInf w k = ∏ w' ∈ aboveInf (L := L) F w, χ.locInf w' (atInf w' (upF F k)) := by
  simp [HChar.resInf]

theorem LevelLe.mul {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h : χ.LevelLe v n) (h' : χ'.LevelLe v n) :
    (χ * χ').LevelLe v n := fun x hx hx' => by
  change χ.1 (localIdele L v x) * χ'.1 (localIdele L v x) = 1
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx hx', h' x hx hx', one_mul]

theorem LevelLe.inv {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h : χ.LevelLe v n) :
    (χ⁻¹).LevelLe v n := fun x hx hx' => by
  change (χ.1 (localIdele L v x))⁻¹ = 1
  change (χ.loc v x)⁻¹ = 1
  rw [h x hx hx', inv_one]

end HChar

end General

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem isUnitAt_nat {p a : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : OverP H p w) (ha : a.Coprime p) {x : H.Eˣ}
    (hx : (x : H.E) = (a : H.E)) : IsUnitAt w (atFin w x) := by
  have hna : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro hmem
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr ha)
    have h1 : (1 : 𝓞 H.E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 H.E) = (u : 𝓞 H.E) * ((a : ℕ) : 𝓞 H.E) + (v : 𝓞 H.E) * ((p : ℕ) : 𝓞 H.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 H.E)) huv
        push_cast at this
        exact this.symm
      rw [e]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hmem) (w.asIdeal.mul_mem_left _ hw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have h := valued_algebraMap_eq_one H.E w _ hna
  show Valued.v (algebraMap H.E (w.adicCompletion H.E) (x : H.E)) = 1
  rw [hx]
  simpa using h

theorem HChar.isUnitary_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := fun x => by
  have h1 : (χ.1 x) ^ n = 1 := by
    have := congrArg (fun ξ : HChar L => ξ.1 x) h
    exact this
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

theorem IsDelta.unitary {p : ℕ} {χ : HChar H.E} (h : IsDelta (H := H) p χ) : χ.IsUnitary := by
  obtain ⟨n, hn, ho⟩ := h.fin
  exact HChar.isUnitary_of_order hn ho

end GlobalTheory.Mem.Chr

end
