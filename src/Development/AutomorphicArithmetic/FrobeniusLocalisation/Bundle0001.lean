module

public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
section
noncomputable section

namespace UpperTheory.HF.Formalism.HC.HostRaw

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def unitsOne (f : ℕ) : Subgroup (ZMod H.condN)ˣ := (ZMod.unitsMap (Nat.gcd_dvd_right f H.condN)).ker

def imgOne (f : ℕ) : Subgroup φ.GG := (H.unitsOne f).map H.art

def condE : ℕ := sInf {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}

def sl (l : ℕ) : ℕ := max 1 (H.condE.factorization l)

def inertG (l : ℕ) : Subgroup φ.GG := H.imgOne (ordCompl[l] H.condN)

def el (l : ℕ) : ℕ := Nat.card (H.inertG l)


open Classical in
def artL (l : ℕ) : φ.GG :=
  if h : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] then H.art h.choose else 1

def decG (l : ℕ) : Subgroup φ.GG := H.inertG l ⊔ Subgroup.zpowers (H.artL l)

def nw (l : ℕ) : ℕ := (H.inertG l).relIndex (H.decG l)

def ram : Finset ℕ := (NumberField.discr H.E).natAbs.primeFactors

def ramI : Finset ℕ := H.ram.erase H.d

def smallR : Finset ℕ := H.small ∩ H.ram

def rad : ℕ := ∏ l ∈ H.ram, l

def QSc : ℕ := ∏ l ∈ H.smallR, l ^ H.sl l

theorem mem_unitsOne {f : ℕ} (hf : f ∣ H.condN) (u : (ZMod H.condN)ˣ) :
    u ∈ H.unitsOne f ↔ (u : ZMod H.condN).val ≡ 1 [MOD f] := by
  rw [unitsOne, MonoidHom.mem_ker, ← Units.val_eq_one, ZMod.unitsMap_val, ZMod.cast_eq_val,
    ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.gcd_eq_left hf]

theorem mem_imgOne {f : ℕ} (hf : f ∣ H.condN) (g : φ.GG) :
    g ∈ H.imgOne f ↔ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD f] ∧ g = H.art u := by
  simp only [imgOne, Subgroup.mem_map, H.mem_unitsOne hf, eq_comm]

theorem imgOne_eq_bot_iff {f : ℕ} (hf : f ∣ H.condN) :
    H.imgOne f = ⊥ ↔ ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD f] → H.art u = 1 := by
  rw [Subgroup.eq_bot_iff_forall]
  constructor
  · intro h u hu; exact h _ ((H.mem_imgOne hf _).2 ⟨u, hu, rfl⟩)
  · intro h g hg; obtain ⟨u, hu, rfl⟩ := (H.mem_imgOne hf _).1 hg; exact h u hu

theorem mem_inertG (l : ℕ) (g : φ.GG) :
    g ∈ H.inertG l ↔ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ g = H.art u :=
  H.mem_imgOne (Nat.ordCompl_dvd _ _) g

theorem imgOne_anti {f g : ℕ} (hfg : f ∣ g) (hg : g ∣ H.condN) : H.imgOne g ≤ H.imgOne f := fun x hx => by
  obtain ⟨u, hu, rfl⟩ := (H.mem_imgOne hg _).1 hx
  exact (H.mem_imgOne (hfg.trans hg) _).2 ⟨u, hu.of_dvd hfg, rfl⟩

theorem el_pos (l : ℕ) : 0 < H.el l := Nat.card_pos

end UpperTheory.HF.Formalism.HC.HostRaw

end
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
section
noncomputable section

namespace UpperTheory.HF.Formalism.HC

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC

namespace Frame

open _root_.Formalism.HC.Frame

variable (φ : Frame)

end Frame

namespace HostRaw

open _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def frobG (p : ℕ) : φ.GG :=
  if h : Nat.Coprime p H.condN then H.art (ZMod.unitOfCoprime p h) else 1

def Inert (p : ℕ) : Prop := p.Prime ∧ jacobiSym (-(H.d : ℤ)) p = -1

theorem frobG_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) : H.frobG p = H.art (ZMod.unitOfCoprime p h) := dif_pos h

end HostRaw

end UpperTheory.HF.Formalism.HC

end
end

